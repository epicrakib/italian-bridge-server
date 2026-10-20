'use strict';
const http = require('http');
const { WebSocketServer, WebSocket } = require('ws');
const { ItalianBridgeEngine, TARGETS } = require('./engine');

const PORT = Number(process.env.PORT || 8787);
const HOST = process.env.HOST || '0.0.0.0';
const COLLECT_MS = 680;
const REVEAL_MS = 3000;
const ROOM_TTL_MS = 30 * 60 * 1000;
const RECONNECT_GRACE_MS = 90 * 1000;
const AI_DELAY_MS = 650;
const AI_NAMES = ['Rakib','Rashed','Shiblu','Siful'];

const rooms = new Map();

function safeSend(ws, payload) {
  if (ws && ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify(payload));
}
function roomCode() {
  for (let i = 0; i < 50; i++) {
    const c = String(Math.floor(1000 + Math.random() * 9000));
    if (!rooms.has(c)) return c;
  }
  throw new Error('Could not allocate room code');
}
function cleanName(name) { return String(name || 'Player').trim().slice(0, 18) || 'Player'; }
function cleanAvatar(a) { return /^a(?:[1-9]|1[0-9]|2[0-8])$/.test(String(a)) ? String(a) : 'a1'; }
function publicLobby(room) {
  return {
    roomCode: room.code,
    targetScore: room.targetScore,
    started: room.started,
    players: room.players.map(p => p ? { seat:p.seat, clientId:p.clientId, name:p.name, avatar:p.avatar, connected:!!p.connected, isAI:!!p.isAI } : null)
  };
}
function event(room, type, data={}) {
  room.eventId++;
  room.event = { id: room.eventId, type, data, at: Date.now() };
}
function makeViewState(room, viewer) {
  const e = room.engine;
  const s = e.getState();
  const fullHands = s.hands;
  s.viewerId = viewer;
  s.handCounts = fullHands.map(h => h.length);
  s.hands = fullHands.map((h,p) => p === viewer ? h : []);
  s.deck = [];
  if (!s.trumpRevealed) s.hiddenTrumpCard = null;
  s.legalCardIds = (s.phase === 'playing' && s.currentPlayer === viewer) ? e.legalCards(viewer).map(c => c.id) : [];
  s.legalBidValues = (s.phase === 'bidding' && e.biddingPlayer() === viewer) ? e.legalBidValues(viewer) : [];
  s.mustBidViewer = s.phase === 'bidding' && e.mustBid(viewer);
  s.canRevealTrump = e.canRevealTrump(viewer);
  s.canDeclareSideOff = !!(e.sideOffEligible[viewer] && !e.sideOffDeclared[viewer]);
  s.sideOffEligible = e.sideOffEligible.map((v,p) => p === viewer ? v : false);
  s.sideOffCount = e.sideOffCount.map((v,p) => p === viewer ? v : (e.sideOffDeclared[p] ? 1 : 0));
  s.event = room.event;
  s.roomCode = room.code;
  return s;
}
function sendLobby(room) {
  const payload = { type:'lobby_state', lobby:publicLobby(room) };
  for (const p of room.players) if (p && p.ws) safeSend(p.ws, payload);
}
function isAISeat(room, seat) {
  const p = room.players[Number(seat)];
  return !!(p && p.isAI);
}
function queueAI(room, delay=AI_DELAY_MS) {
  if (!room || !room.started || !room.engine || room.aiTimer) return;
  room.aiTimer = setTimeout(async()=>{
    room.aiTimer = null;
    try { await runAI(room); } catch (err) { console.error('AI turn failed', room.code, err && err.message ? err.message : err); }
  }, delay);
}
async function runAI(room) {
  if (!room.started || !room.engine) return;
  if (room.transitionLock) { queueAI(room, 350); return; }
  const e = room.engine;

  // AI announces Side Off automatically, just like offline computer players.
  if (['playing','trick_complete'].includes(e.phase)) {
    for (let seat=0; seat<4; seat++) {
      if (isAISeat(room,seat) && e.sideOffEligible[seat] && !e.sideOffDeclared[seat]) {
        e.declareSideOff(seat);
        event(room,'side-off',{player:seat});
        sendGame(room);
        return;
      }
    }
  }

  if (e.phase === 'shuffle' && isAISeat(room,e.dealer)) {
    if (e.shuffleCount < 1) {
      e.shufflePreparedDeck(); event(room,'shuffle',{player:e.dealer,count:e.shuffleCount}); sendGame(room); return;
    }
    e.dealInitialFive(); event(room,'deal-initial',{dealer:e.dealer}); sendGame(room); return;
  }
  if (e.phase === 'bidding') {
    const seat=e.biddingPlayer();
    if (isAISeat(room,seat)) {
      const before=e.phase, bid=e.estimateBid(seat), blind=e.aiWantsBlind(seat,bid);
      e.placeBid(seat,bid,blind);
      event(room,before==='bidding'&&e.phase!=='bidding'&&e.highBidBlind?'deal-rest':'bid',{player:seat,bid,blind});
      sendGame(room); return;
    }
  }
  if (e.phase === 'choose_trump' && isAISeat(room,e.highBidder)) {
    const seat=e.highBidder, suit=e.chooseTrumpAI(seat);
    e.setTrump(seat,suit); event(room,'deal-rest',{player:seat}); sendGame(room); return;
  }
  if (e.phase === 'playing' && isAISeat(room,e.currentPlayer)) {
    const seat=e.currentPlayer;
    if (e.canRevealTrump(seat) && e.aiShouldRevealTrump(seat)) {
      await performAction(room,seat,'reveal',{}); return;
    }
    const cardId=e.aiChooseCard(seat);
    if (cardId) { await performAction(room,seat,'play',{cardId}); return; }
  }
}
function sendGame(room) {
  for (const p of room.players) if (p && p.ws) safeSend(p.ws, { type:'game_state', state:makeViewState(room,p.seat) });
  queueAI(room);
}

function attachPlayer(room, seat, ws, clientId, name, avatar) {
  const p = room.players[seat] || { seat, clientId, name:cleanName(name), avatar:cleanAvatar(avatar), connected:true, ws:null, disconnectedAt:0 };
  p.clientId = clientId; p.name = cleanName(name || p.name); p.avatar = cleanAvatar(avatar || p.avatar); p.connected = true; p.ws = ws; p.disconnectedAt = 0; p.isAI = false;
  room.players[seat] = p;
  ws.meta = { roomCode:room.code, clientId, seat };
  room.updatedAt = Date.now();
  return p;
}
function findSeatByClient(room, clientId) { return room.players.findIndex(p => p && p.clientId === clientId); }
function autoBidTimeout(room) {
  if (!room.started || !room.engine || room.transitionLock) return;
  const e = room.engine;
  if (e.phase === 'bidding' && e.bidDeadline && Date.now() >= e.bidDeadline) {
    try {
      const before = e.phase, player = e.biddingPlayer();
      e.handleBidTimeout();
      event(room, before === 'bidding' && e.phase !== 'bidding' && e.highBidBlind ? 'deal-rest' : 'bid-timeout', { player });
      sendGame(room);
    } catch (_) {}
  }
}
async function performAction(room, seat, action, data={}) {
  if (!room.started || !room.engine) throw new Error('Match has not started');
  if (room.transitionLock && !['ping'].includes(action)) throw new Error('Please wait for the table animation');
  const e = room.engine;
  if (action === 'shuffle') {
    if (e.phase !== 'shuffle' || seat !== e.dealer) throw new Error('Only the dealer can shuffle');
    e.shufflePreparedDeck(); event(room,'shuffle',{player:seat,count:e.shuffleCount}); sendGame(room); return;
  }
  if (action === 'deal') {
    if (e.phase !== 'shuffle' || seat !== e.dealer || e.shuffleCount < 1) throw new Error('Shuffle before dealing');
    e.dealInitialFive(); event(room,'deal-initial',{dealer:seat}); sendGame(room); return;
  }
  if (action === 'bid') {
    const before=e.phase; e.placeBid(seat,data.bid==null?null:Number(data.bid),!!data.blind);
    event(room, before==='bidding'&&e.phase!=='bidding'&&e.highBidBlind?'deal-rest':'bid',{player:seat,bid:data.bid,blind:!!data.blind}); sendGame(room); return;
  }
  if (action === 'trump') {
    e.setTrump(seat,data.suit); event(room,'deal-rest',{player:seat}); sendGame(room); return;
  }
  if (action === 'play') {
    e.playCard(seat,data.cardId); event(room,'card-play',{player:seat,cardId:data.cardId}); sendGame(room); return;
  }
  if (action === 'sideoff') {
    e.declareSideOff(seat); event(room,'side-off',{player:seat}); sendGame(room); return;
  }
  if (action === 'reveal') {
    if (!e.canRevealTrump(seat)) throw new Error('Trump cannot be revealed now');
    e.revealBlindTrump(seat); const revealed=e.revealedTrumpCard?{...e.revealedTrumpCard}:null, bidder=e.highBidder;
    room.transitionLock=true; event(room,'trump-reveal',{player:seat,card:revealed,bidder}); sendGame(room);
    setTimeout(()=>{try{e.completeTrumpReveal();room.transitionLock=false;event(room,'trump-return',{bidder,card:revealed});sendGame(room)}catch(_){room.transitionLock=false}},REVEAL_MS); return;
  }
  if (action === 'collect') {
    if (e.phase !== 'trick_complete') throw new Error('Trick is not ready to collect');
    const winner=e.pendingTrickWinner; room.transitionLock=true; event(room,'collect',{winner}); sendGame(room);
    setTimeout(()=>{try{e.resolveTrick();room.transitionLock=false;event(room,e.phase==='match_complete'?'match-win':e.phase==='hand_complete'?'hand-score':'trick-resolved',{});sendGame(room)}catch(_){room.transitionLock=false}},COLLECT_MS+90); return;
  }
  if (action === 'nextInvalid') { e.cancelInvalidAndAdvance(true); event(room,'shuffle-ready',{dealer:e.dealer}); sendGame(room); return; }
  if (action === 'nextHand') { e.advanceDealerAndStart(true); event(room,'shuffle-ready',{dealer:e.dealer}); sendGame(room); return; }
  if (action === 'newMatch') {
    if (seat !== 0) throw new Error('Only the host can start a new match');
    const names=room.players.map(p=>p.name), avatars=room.players.map(p=>p.avatar), dealer=e.next(e.dealer);
    room.engine=new ItalianBridgeEngine({playerNames:names,avatars,targetScore:room.targetScore,dealer});
    room.engine.players.forEach((p,i)=>p.human=!isAISeat(room,i)); room.engine.prepareManualHand(); event(room,'shuffle-ready',{dealer:room.engine.dealer}); sendGame(room); return;
  }
  throw new Error('Unknown action');
}

const server = http.createServer((req,res)=>{
  if (req.url === '/health') { res.writeHead(200,{'content-type':'application/json'}); return res.end(JSON.stringify({ok:true,rooms:rooms.size,at:Date.now()})); }
  res.writeHead(200,{'content-type':'text/plain'}); res.end('Italian Bridge Online Server');
});
const wss = new WebSocketServer({ server });

wss.on('connection', ws => {
  ws.isAlive = true;
  ws.on('pong',()=>ws.isAlive=true);
  safeSend(ws,{type:'hello',server:'Italian Bridge Online',version:'0.2.0'});
  ws.on('message', raw => {
    let m; try{m=JSON.parse(raw.toString())}catch(_){return safeSend(ws,{type:'error',message:'Invalid message'})}
    const clientId=String(m.clientId||'').slice(0,64); if(!clientId) return safeSend(ws,{type:'error',message:'Missing client id'});
    try {
      if (m.type === 'create_room') {
        const code=roomCode(); const room={code,hostClientId:clientId,targetScore:TARGETS.includes(Number(m.targetScore))?Number(m.targetScore):50,players:[null,null,null,null],started:false,engine:null,eventId:0,event:null,transitionLock:false,aiTimer:null,createdAt:Date.now(),updatedAt:Date.now()};
        rooms.set(code,room); attachPlayer(room,0,ws,clientId,m.name,m.avatar); safeSend(ws,{type:'room_created',roomCode:code,seat:0,lobby:publicLobby(room)}); sendLobby(room); return;
      }
      const code=String(m.roomCode||''); const room=rooms.get(code); if(!room) throw new Error('Room not found');
      room.updatedAt=Date.now();
      if (m.type === 'join_room') {
        if (room.started) throw new Error('Match already started');
        let seat=findSeatByClient(room,clientId); if(seat<0) seat=[1,2,3].find(i=>!room.players[i]); if(!(seat>0)) throw new Error('Room is full');
        attachPlayer(room,seat,ws,clientId,m.name,m.avatar); safeSend(ws,{type:'room_joined',roomCode:code,seat,lobby:publicLobby(room)}); sendLobby(room); return;
      }
      if (m.type === 'reconnect') {
        const seat=findSeatByClient(room,clientId); if(seat<0) throw new Error('Your seat is no longer reserved');
        attachPlayer(room,seat,ws,clientId,m.name,m.avatar); safeSend(ws,{type:'room_reconnected',roomCode:code,seat,lobby:publicLobby(room)}); event(room,'player-reconnected',{player:seat}); room.started?sendGame(room):sendLobby(room); return;
      }
      const seat=findSeatByClient(room,clientId); if(seat<0) throw new Error('You are not in this room');
      if (m.type === 'add_ai') {
        if (seat!==0 || room.started) throw new Error('Only the host can add AI before start');
        const aiSeat=Number(m.seat);
        if (![1,2,3].includes(aiSeat)) throw new Error('Invalid AI seat');
        if (room.players[aiSeat]) throw new Error('That seat is already occupied');
        room.players[aiSeat]={seat:aiSeat,clientId:`AI-${room.code}-${aiSeat}`,name:AI_NAMES[aiSeat]||`AI ${aiSeat}`,avatar:`a${((aiSeat*7+5)%28)+1}`,connected:true,ws:null,disconnectedAt:0,isAI:true};
        event(room,'ai-added',{player:aiSeat}); sendLobby(room); return;
      }
      if (m.type === 'remove_ai') {
        if (seat!==0 || room.started) throw new Error('Only the host can remove AI before start');
        const aiSeat=Number(m.seat), p=room.players[aiSeat];
        if (![1,2,3].includes(aiSeat) || !p || !p.isAI) throw new Error('No AI player in that seat');
        room.players[aiSeat]=null; event(room,'ai-removed',{player:aiSeat}); sendLobby(room); return;
      }
      if (m.type === 'set_target') {
        if (seat!==0 || room.started) throw new Error('Only the host can change target before start');
        if (!TARGETS.includes(Number(m.targetScore))) throw new Error('Invalid target score');
        room.targetScore=Number(m.targetScore); sendLobby(room); return;
      }
      if (m.type === 'start_room') {
        if (seat!==0) throw new Error('Only the host can start');
        if (room.players.filter(Boolean).length!==4) throw new Error('Four players are required');
        if (room.players.some(p=>!p.connected)) throw new Error('All players must be connected');
        const names=room.players.map(p=>p.name), avatars=room.players.map(p=>p.avatar);
        room.engine=new ItalianBridgeEngine({playerNames:names,avatars,targetScore:room.targetScore}); room.engine.players.forEach((p,i)=>p.human=!isAISeat(room,i)); room.engine.prepareManualHand(); room.started=true; event(room,'shuffle-ready',{dealer:room.engine.dealer}); sendLobby(room); sendGame(room); return;
      }
      if (m.type === 'action') { return performAction(room,seat,m.action,m.data||{}).catch(err=>safeSend(ws,{type:'error',message:err.message||'Action failed'})); }
      if (m.type === 'leave_room') {
        const p=room.players[seat]; if(p){p.connected=false;p.ws=null;p.disconnectedAt=Date.now()}
        if (seat===0 && !room.started) { for(const x of room.players) if(x&&x.ws) safeSend(x.ws,{type:'room_closed'}); if(room.aiTimer)clearTimeout(room.aiTimer); rooms.delete(code); }
        else { if(room.started){event(room,'player-disconnected',{player:seat});sendGame(room)}else { room.players[seat]=null; sendLobby(room); } }
        try{ws.close()}catch(_){} return;
      }
      if (m.type === 'ping') return safeSend(ws,{type:'pong',at:Date.now()});
    } catch(err) { safeSend(ws,{type:'error',message:err.message||'Server error'}); }
  });
  ws.on('close',()=>{
    const meta=ws.meta; if(!meta)return; const room=rooms.get(meta.roomCode); if(!room)return; const seat=findSeatByClient(room,meta.clientId); if(seat<0)return; const p=room.players[seat]; if(p&&p.ws===ws){p.connected=false;p.ws=null;p.disconnectedAt=Date.now(); if(room.started){event(room,'player-disconnected',{player:seat});sendGame(room)}else sendLobby(room)}
  });
});

setInterval(()=>{
  const now=Date.now();
  for (const room of rooms.values()) {
    autoBidTimeout(room);
    const connected=room.players.some(p=>p&&p.connected);
    if (!connected && now-room.updatedAt>ROOM_TTL_MS) { if(room.aiTimer)clearTimeout(room.aiTimer); rooms.delete(room.code); }
    for (const p of room.players) if(p&&!p.connected&&p.disconnectedAt&&now-p.disconnectedAt>RECONNECT_GRACE_MS) p.reservationExpired=true;
  }
  for (const ws of wss.clients) { if(ws.isAlive===false){try{ws.terminate()}catch(_){}} else {ws.isAlive=false;try{ws.ping()}catch(_){}} }
},1000);

server.listen(PORT,HOST,()=>console.log(`Italian Bridge Online Server listening on ${HOST}:${PORT}`));
