(function(global){
  'use strict';

  const SUITS=['C','D','H','S'];
  const SUIT_SYMBOL={C:'♣',D:'♦',H:'♥',S:'♠'};
  const RANK_LABEL={11:'J',12:'Q',13:'K',14:'A'};
  const TARGETS=[50,60,80,100];
  function rankLabel(r){return RANK_LABEL[r]||String(r)}
  function cardLabel(c){return rankLabel(c.rank)+SUIT_SYMBOL[c.suit]}
  function clone(x){return x==null?x:JSON.parse(JSON.stringify(x))}

  class ItalianBridgeEngine{
    constructor(opts={}){
      this.playerNames=opts.playerNames||['Rakib','Rashed','Shiblu','Siful'];
      const av=Array.isArray(opts.avatars)?opts.avatars:['a1','a2','a3','a4'];
      this.players=[
        {id:0,seat:'bottom',team:0,human:true,name:this.playerNames[0],avatar:av[0]||'a1'},
        {id:1,seat:'left',team:1,human:false,name:this.playerNames[1],avatar:av[1]||'a2'},
        {id:2,seat:'top',team:0,human:false,name:this.playerNames[2],avatar:av[2]||'a3'},
        {id:3,seat:'right',team:1,human:false,name:this.playerNames[3],avatar:av[3]||'a4'},
      ];
      this.targetScore=TARGETS.includes(Number(opts.targetScore))?Number(opts.targetScore):50;
      this.totals=[0,0];
      this.matchWinner=null;
      this.targetTie=false;
      this.handNumber=0;
      this.dealer=Number.isInteger(opts.dealer)?opts.dealer:Math.floor(Math.random()*4);
      this.history=[];
      this.phase='idle';
      this.resetHandState();
    }

    resetHandState(){
      this.hands=[[],[],[],[]]; this.deck=[];
      this.bidOrder=[]; this.bidPos=0; this.bids=[];
      this.highBid=null; this.highBidder=null; this.highBidBlind=false;
      this.trump=null; this.trumpRevealed=false; this.hiddenTrumpCard=null; this.revealedTrumpCard=null;
      this.revealPendingPlayer=null; this.mustTrumpPlayer=null;
      this.contractTeam=null; this.currentPlayer=null; this.leader=null;
      this.trick=[]; this.tricksWon=[0,0]; this.trickCountByPlayer=[0,0,0,0];
      this.trumpLeadOccurred=false; this.trickStartedWithTrumpKnown=false;
      this.invalidReason=null; this.lastTrickWinner=null; this.lastTrick=[]; this.pendingTrickWinner=null;
      this.handScore=null;
      this.shuffleCount=0; this.bidDeadline=0;
      this.sideOffCount=[0,0,0,0]; this.sideOffEligible=[false,false,false,false]; this.sideOffDeclared=[false,false,false,false];
    }

    next(i){return(i+1)%4}
    partner(i){return(i+2)%4}
    sameTeam(a,b){return this.players[a].team===this.players[b].team}
    setTargetScore(n){n=Number(n);if(!TARGETS.includes(n))throw new Error('Game point must be 50, 60, 80 or 100');this.targetScore=n;return n}

    buildDeck(){const d=[];for(const suit of SUITS)for(let rank=2;rank<=14;rank++)d.push({suit,rank,id:suit+rank});return d}
    randomInt(max){
      if(max<=1)return 0;
      try{
        const c=(typeof globalThis!=='undefined'&&globalThis.crypto&&globalThis.crypto.getRandomValues)?globalThis.crypto:null;
        if(c){const a=new Uint32Array(1),lim=Math.floor(0x100000000/max)*max;let v;do{c.getRandomValues(a);v=a[0]}while(v>=lim);return v%max}
      }catch(e){}
      return Math.floor(Math.random()*max);
    }
    shuffle(deck){for(let i=deck.length-1;i>0;i--){const j=this.randomInt(i+1);[deck[i],deck[j]]=[deck[j],deck[i]]}return deck}
    // Italian Bridge deals whole packets: 5 to one player, then 5 to the next; later 4+4 in the same way.
    dealPacket(count,hiddenPlayer=null,hiddenIndex=-1){
      let p=this.next(this.dealer);
      for(let n=0;n<4;n++){
        for(let i=0;i<count;i++){
          const c=this.deck.shift();
          if(!c)throw new Error('Deck exhausted while dealing');
          if(p===hiddenPlayer&&i===hiddenIndex&&this.hiddenTrumpCard==null)this.hiddenTrumpCard=c;else this.hands[p].push(c);
        }
        p=this.next(p);
      }
    }

    prepareManualHand(){
      this.resetHandState(); this.handNumber+=1; this.deck=this.buildDeck(); this.phase='shuffle'; return this.getState();
    }
    shufflePreparedDeck(){
      if(this.phase!=='shuffle'||this.deck.length!==52)throw new Error('Deck is not ready to shuffle');
      this.shuffle(this.deck);this.shuffleCount+=1;return this.getState();
    }
    dealInitialFive(){
      if(this.phase!=='shuffle')throw new Error('Not ready to deal');
      if(this.shuffleCount<1)this.shufflePreparedDeck();
      this.dealPacket(5);this.sortAllHands();
      let p=this.next(this.dealer);for(let n=0;n<4;n++){this.bidOrder.push(p);p=this.next(p)}
      this.phase='bidding';this.bidDeadline=Date.now()+30000;return this.getState();
    }
    startHand(){this.prepareManualHand();this.shufflePreparedDeck();return this.dealInitialFive()}

    biddingPlayer(){return this.phase==='bidding'?this.bidOrder[this.bidPos]:null}
    minBid(){return this.highBid==null?7:this.highBid+1}
    mustBid(player){return this.phase==='bidding'&&player===this.dealer&&this.highBid==null&&this.bidPos===3}
    legalBidValues(player){if(this.phase!=='bidding'||player!==this.biddingPlayer())return[];const out=[];for(let b=Math.max(7,this.minBid());b<=13;b++)out.push(b);return out}

    placeBid(player,bid,blind=false){
      if(this.phase!=='bidding')throw new Error('Not bidding phase');
      if(player!==this.biddingPlayer())throw new Error('Not this player\'s turn to bid');
      if(bid==null){
        if(this.mustBid(player))throw new Error('Dealer must bid at least 7 when everyone else passes');
        this.bids.push({player,bid:null,blind:false});
      }else{
        bid=Number(bid);
        if(!Number.isInteger(bid)||bid<7||bid>13)throw new Error('Bid must be 7–13');
        if(this.highBid!=null&&bid<=this.highBid)throw new Error('Bid must be higher than current bid');
        this.highBid=bid;this.highBidder=player;this.highBidBlind=!!blind;
        this.bids.push({player,bid,blind:!!blind});
      }
      this.bidPos+=1;
      if(this.bidPos<4)this.bidDeadline=Date.now()+30000;else this.bidDeadline=0;
      if(this.bidPos>=4){
        if(this.highBid==null){this.highBid=7;this.highBidder=this.dealer;this.highBidBlind=false}
        this.contractTeam=this.players[this.highBidder].team;
        if(this.highBidBlind){this.dealBlindRemainder();this.finishFullDeal();}
        else this.phase='choose_trump';
      }
      return this.getState();
    }

    handleBidTimeout(){
      if(this.phase!=='bidding')return this.getState();
      const p=this.biddingPlayer();
      if(this.mustBid(p))return this.placeBid(p,7,true);
      return this.placeBid(p,null,false);
    }

    dealBlindRemainder(){
      // First post-bid packet is 4 cards per player. The blind bidder's SECOND card in their packet is held face-down.
      this.dealPacket(4,this.highBidder,1);
      this.dealPacket(4);
      this.trump=null;this.trumpRevealed=false;
    }

    setTrump(player,suit){
      if(this.phase!=='choose_trump')throw new Error('Not choosing trump');
      if(player!==this.highBidder)throw new Error('Only highest bidder chooses trump');
      if(!SUITS.includes(suit))throw new Error('Invalid trump suit');
      this.trump=suit;this.trumpRevealed=true;
      this.dealPacket(4);this.dealPacket(4);this.finishFullDeal();
      return this.getState();
    }

    fullHand(player){
      const h=[...this.hands[player]];
      if(this.highBidBlind&&!this.trumpRevealed&&this.hiddenTrumpCard&&player===this.highBidder)h.push(this.hiddenTrumpCard);
      return h;
    }
    actualTrumpSuit(){return this.trumpRevealed?this.trump:(this.hiddenTrumpCard?this.hiddenTrumpCard.suit:null)}

    computeSideOff(){
      for(let p=0;p<4;p++){
        const h=this.fullHand(p), present=new Set(h.map(c=>c.suit));
        const missing=SUITS.filter(s=>!present.has(s)).length;
        this.sideOffCount[p]=missing;this.sideOffEligible[p]=missing===1;
      }
    }

    finishFullDeal(){
      this.sortAllHands();this.computeSideOff();
      const invalid=this.validateFullDeal();
      if(invalid){this.invalidReason=invalid;this.phase='invalid';return}
      this.phase='playing';this.leader=this.next(this.dealer);this.currentPlayer=this.leader;
    }

    validateFullDeal(){
      for(let p=0;p<4;p++){
        const hand=this.fullHand(p);
        if(hand.filter(c=>c.rank===14).length===4)return `${this.players[p].name} has all four Aces.`;
        if(hand.filter(c=>c.rank>=11).length===0)return `${this.players[p].name} has no honour card (J, Q, K or A).`;
        if(this.sideOffCount[p]>=2)return `${this.players[p].name} is two sides off. Deal cancelled.`;
      }
      const actualTrump=this.actualTrumpSuit();
      if(actualTrump){
        for(let team=0;team<2;team++){
          const members=this.players.filter(p=>p.team===team).map(p=>p.id);
          const count=members.reduce((sum,p)=>sum+this.fullHand(p).filter(c=>c.suit===actualTrump).length,0);
          if(count===0){const names=members.map(p=>this.players[p].name).join(' + ');return this.highBidBlind?`${names} have no cards in the hidden trump suit.`:`${names} have no ${SUIT_SYMBOL[actualTrump]} trump card.`}
        }
      }
      return null;
    }

    cancelInvalidAndAdvance(manual=false){if(this.phase!=='invalid')throw new Error('Deal is not invalid');this.dealer=this.next(this.dealer);return manual?this.prepareManualHand():this.startHand()}
    sortHand(hand){const order={S:0,H:1,D:2,C:3};hand.sort((a,b)=>order[a.suit]-order[b.suit]||b.rank-a.rank)}
    sortAllHands(){this.hands.forEach(h=>this.sortHand(h))}
    hasSuit(player,suit){return this.hands[player].some(c=>c.suit===suit)}
    hasTrumpAce(player){return !!this.trump&&this.hands[player].some(c=>c.suit===this.trump&&c.rank===14)}

    declareSideOff(player){
      if(!this.sideOffEligible[player])throw new Error('Side Off is not available for this hand');
      if(this.sideOffDeclared[player])return this.getState();
      this.sideOffDeclared[player]=true;return this.getState();
    }

    canRevealTrump(player){
      if(!this.highBidBlind||this.trumpRevealed||!this.hiddenTrumpCard||this.phase!=='playing'||player!==this.currentPlayer)return false;
      if(this.hands[player].length===0&&player===this.highBidder)return true;
      if(this.trick.length===0)return false;
      const lead=this.trick[0].card.suit;
      return !this.hasSuit(player,lead);
    }

    revealBlindTrump(player){
      if(!this.canRevealTrump(player))throw new Error('Trump can only be shown when you cannot follow the led suit');
      this.trump=this.hiddenTrumpCard.suit;this.trumpRevealed=true;this.revealedTrumpCard=clone(this.hiddenTrumpCard);
      this.revealPendingPlayer=player;this.phase='trump_reveal';
      return this.getState();
    }

    completeTrumpReveal(){
      if(this.phase!=='trump_reveal'||!this.hiddenTrumpCard)throw new Error('No trump reveal is pending');
      const revealer=this.revealPendingPlayer;
      this.hands[this.highBidder].push(this.hiddenTrumpCard);this.sortHand(this.hands[this.highBidder]);
      this.hiddenTrumpCard=null;this.revealedTrumpCard=null;this.revealPendingPlayer=null;
      this.mustTrumpPlayer=this.hasSuit(revealer,this.trump)?revealer:null;
      this.phase='playing';this.currentPlayer=revealer;
      return this.getState();
    }

    isCardLegal(player,cardId){
      if(this.phase!=='playing'||player!==this.currentPlayer)return false;
      const card=this.hands[player].find(c=>c.id===cardId);if(!card)return false;
      if(this.trick.length>0){
        const lead=this.trick[0].card.suit;
        if(this.hasSuit(player,lead)&&card.suit!==lead)return false;
      }
      if(this.mustTrumpPlayer===player&&this.trump&&this.hasSuit(player,this.trump)&&card.suit!==this.trump)return false;

      if(this.trumpRevealed&&this.trump){
        if(this.trick.length>0){
          const lead=this.trick[0].card.suit;
          if(!this.trumpLeadOccurred&&this.trickStartedWithTrumpKnown&&lead===this.trump&&this.hasTrumpAce(player)){
            if(!(card.suit===this.trump&&card.rank===14))return false;
          }
        }else{
          if(!this.trumpLeadOccurred&&card.suit===this.trump&&this.hasTrumpAce(player)&&card.rank!==14)return false;
        }
      }
      return true;
    }

    legalCards(player){if(this.phase!=='playing'||player!==this.currentPlayer)return[];return this.hands[player].filter(c=>this.isCardLegal(player,c.id))}
    currentWinningPlay(){if(!this.trick.length)return null;const lead=this.trick[0].card.suit;let best=this.trick[0];for(let i=1;i<this.trick.length;i++)if(this.cardBeats(this.trick[i].card,best.card,lead))best=this.trick[i];return best}
    cardBeats(a,b,lead){
      if(a.suit===b.suit)return a.rank>b.rank;
      if(this.trumpRevealed&&this.trump){if(a.suit===this.trump&&b.suit!==this.trump)return true;if(b.suit===this.trump&&a.suit!==this.trump)return false}
      if(a.suit===lead&&b.suit!==lead)return true;return false;
    }

    playCard(player,cardId){
      if(!this.isCardLegal(player,cardId))throw new Error('Illegal card');
      const idx=this.hands[player].findIndex(c=>c.id===cardId);const card=this.hands[player].splice(idx,1)[0];
      if(this.trick.length===0)this.trickStartedWithTrumpKnown=!!this.trumpRevealed;
      this.trick.push({player,card});if(this.mustTrumpPlayer===player)this.mustTrumpPlayer=null;
      if(this.trick.length<4){this.currentPlayer=this.next(player);return{trickComplete:false,state:this.getState()}}
      const winner=this.currentWinningPlay().player;this.pendingTrickWinner=winner;this.lastTrick=clone(this.trick);this.lastTrickWinner=winner;this.currentPlayer=null;this.phase='trick_complete';
      return{trickComplete:true,handComplete:false,winner,state:this.getState()};
    }

    resolveTrick(){
      if(this.phase!=='trick_complete'||this.trick.length!==4)throw new Error('No completed trick to collect');
      const lead=this.trick[0].card.suit,winner=this.pendingTrickWinner!=null?this.pendingTrickWinner:this.currentWinningPlay().player;
      if(this.trumpRevealed&&this.trickStartedWithTrumpKnown&&lead===this.trump&&!this.trumpLeadOccurred)this.trumpLeadOccurred=true;
      this.trickCountByPlayer[winner]+=1;this.tricksWon[this.players[winner].team]+=1;
      this.trick=[];this.pendingTrickWinner=null;this.trickStartedWithTrumpKnown=false;this.leader=winner;this.currentPlayer=winner;
      if(this.hands.every(h=>h.length===0)&&!this.hiddenTrumpCard){this.finishHand();return{handComplete:true,winner,state:this.getState()}}
      this.phase='playing';return{handComplete:false,winner,state:this.getState()};
    }

    finishHand(){
      const ct=this.contractTeam,dt=1-ct,cTricks=this.tricksWon[ct],dTricks=this.tricksWon[dt],made=cTricks>=this.highBid;
      const contractScore=made?(this.highBid>=10?13:this.highBid):-this.highBid;
      const defenderScore=(dTricks>=4&&dTricks<=7)?4:-4;
      const scores=[0,0];scores[ct]=contractScore;scores[dt]=defenderScore;this.totals[0]+=scores[0];this.totals[1]+=scores[1];
      this.targetTie=false;this.matchWinner=null;
      const hit0=this.totals[0]>=this.targetScore,hit1=this.totals[1]>=this.targetScore;
      if(hit0||hit1){
        if(hit0&&!hit1)this.matchWinner=0;else if(hit1&&!hit0)this.matchWinner=1;
        else if(this.totals[0]!==this.totals[1])this.matchWinner=this.totals[0]>this.totals[1]?0:1;else this.targetTie=true;
      }
      this.handScore={contract:this.highBid,bidder:this.highBidder,blind:this.highBidBlind,trump:this.trump,contractTeam:ct,contractTricks:cTricks,defenderTricks:dTricks,made,scores,totals:[...this.totals],targetScore:this.targetScore,matchWinner:this.matchWinner};
      this.history.push({hand:this.handNumber,dealer:this.dealer,contract:this.highBid,bidder:this.highBidder,blind:this.highBidBlind,trump:this.trump,tricks:[...this.tricksWon],scores:[...scores],totals:[...this.totals]});
      this.phase=this.matchWinner!=null?'match_complete':'hand_complete';
    }

    advanceDealerAndStart(manual=false){if(this.phase!=='hand_complete')throw new Error('Hand is not complete');this.dealer=this.next(this.dealer);return manual?this.prepareManualHand():this.startHand()}

    estimateBid(player){
      const hand=this.hands[player],hcp=hand.reduce((s,c)=>s+({14:4,13:3,12:2,11:1}[c.rank]||0),0),counts={C:0,D:0,H:0,S:0};hand.forEach(c=>counts[c.suit]++);
      const maxLen=Math.max(...Object.values(counts)),lenBonus=maxLen>=5?6:maxLen===4?4:maxLen===3?2:0,aces=hand.filter(c=>c.rank===14).length;
      const strength=hcp+lenBonus+aces*.7+Math.random()*1.4;let bid=null;
      if(strength>=6)bid=7;if(strength>=9)bid=8;if(strength>=12)bid=9;if(strength>=15)bid=10;if(strength>=17.5)bid=11;if(strength>=19.5)bid=12;if(strength>=21)bid=13;
      const min=this.minBid();if(bid!=null&&bid<min){if(strength>=8+(min-7)*2.1&&min<=13)bid=min;else bid=null}if(this.mustBid(player)&&bid==null)bid=7;return bid;
    }
    aiWantsBlind(player,bid){if(bid==null)return false;const chance=bid<=9?.18:.07;return Math.random()<chance}
    chooseTrumpAI(player){const hand=this.hands[player];let best='C',bestScore=-1;for(const s of SUITS){const cards=hand.filter(c=>c.suit===s);let score=cards.length*2.4;for(const c of cards)score+=({14:4.2,13:2.8,12:1.7,11:.9}[c.rank]||0);score+=Math.random()*.4;if(score>bestScore){bestScore=score;best=s}}return best}
    aiShouldRevealTrump(player){if(!this.canRevealTrump(player))return false;if(this.hands[player].length===0)return true;const cur=this.currentWinningPlay();const partnerWinning=cur&&this.sameTeam(player,cur.player);return Math.random()<(partnerWinning?.12:.5)}
    aiChooseCard(player){
      const legal=this.legalCards(player);if(!legal.length)return null;if(legal.length===1)return legal[0].id;
      const team=this.players[player].team,contractSide=team===this.contractTeam,byLow=(a,b)=>a.rank-b.rank,byHigh=(a,b)=>b.rank-a.rank;
      const nonTrump=legal.filter(c=>!this.trumpRevealed||c.suit!==this.trump),trumps=this.trumpRevealed?legal.filter(c=>c.suit===this.trump):[];
      if(this.trick.length===0){const aces=legal.filter(c=>c.rank===14&&(!this.trumpRevealed||c.suit!==this.trump)).sort(byHigh);if(aces.length&&Math.random()<.72)return aces[0].id;const kings=legal.filter(c=>c.rank===13&&(!this.trumpRevealed||c.suit!==this.trump)).sort(byHigh);if(kings.length&&Math.random()<.5)return kings[0].id;if(contractSide&&this.highBid>=9&&trumps.length>=2){const s=[...trumps].sort(byHigh);if(this.isCardLegal(player,s[0].id))return s[0].id}return[...(nonTrump.length?nonTrump:legal)].sort(byLow)[0].id}
      const current=this.currentWinningPlay(),partnerWinning=current&&this.sameTeam(player,current.player);if(partnerWinning)return[...legal].sort(byLow)[0].id;
      const winning=legal.filter(c=>this.cardBeats(c,current.card,this.trick[0].card.suit)).sort(byLow);if(winning.length)return winning[0].id;return[...legal].sort(byLow)[0].id;
    }

    getState(){return{
      players:clone(this.players),targetScore:this.targetScore,totals:[...this.totals],matchWinner:this.matchWinner,targetTie:this.targetTie,handNumber:this.handNumber,dealer:this.dealer,
      phase:this.phase,hands:clone(this.hands),deck:clone(this.deck),bidOrder:[...this.bidOrder],bidPos:this.bidPos,bids:clone(this.bids),highBid:this.highBid,highBidder:this.highBidder,highBidBlind:this.highBidBlind,
      trump:this.trump,trumpRevealed:this.trumpRevealed,hiddenTrumpCard:clone(this.hiddenTrumpCard),revealedTrumpCard:clone(this.revealedTrumpCard),revealPendingPlayer:this.revealPendingPlayer,mustTrumpPlayer:this.mustTrumpPlayer,
      contractTeam:this.contractTeam,currentPlayer:this.currentPlayer,leader:this.leader,trick:clone(this.trick),tricksWon:[...this.tricksWon],trickCountByPlayer:[...this.trickCountByPlayer],
      trumpLeadOccurred:this.trumpLeadOccurred,trickStartedWithTrumpKnown:this.trickStartedWithTrumpKnown,invalidReason:this.invalidReason,lastTrickWinner:this.lastTrickWinner,lastTrick:clone(this.lastTrick),pendingTrickWinner:this.pendingTrickWinner,handScore:clone(this.handScore),
      shuffleCount:this.shuffleCount,bidDeadline:this.bidDeadline,sideOffCount:[...this.sideOffCount],sideOffEligible:[...this.sideOffEligible],sideOffDeclared:[...this.sideOffDeclared],history:clone(this.history)
    }}
    serialize(){return JSON.stringify(this.getState())}
    restore(state){
      if(typeof state==='string')state=JSON.parse(state);
      this.players=clone(state.players);this.playerNames=this.players.map(p=>p.name);this.players.forEach((p,i)=>{if(!p.avatar)p.avatar='a'+(i+1)});
      this.targetScore=TARGETS.includes(Number(state.targetScore))?Number(state.targetScore):50;this.totals=[...(state.totals||[0,0])];this.matchWinner=state.matchWinner==null?null:state.matchWinner;this.targetTie=!!state.targetTie;
      this.handNumber=state.handNumber||0;this.dealer=state.dealer||0;this.phase=state.phase||'idle';this.hands=clone(state.hands||[[],[],[],[]]);this.deck=clone(state.deck||[]);this.bidOrder=[...(state.bidOrder||[])];this.bidPos=state.bidPos||0;
      this.bids=clone(state.bids||[]);this.highBid=state.highBid==null?null:state.highBid;this.highBidder=state.highBidder==null?null:state.highBidder;this.highBidBlind=!!state.highBidBlind;
      this.trump=state.trump||null;this.trumpRevealed=state.trumpRevealed!=null?!!state.trumpRevealed:!!state.trump;this.hiddenTrumpCard=clone(state.hiddenTrumpCard||null);this.revealedTrumpCard=clone(state.revealedTrumpCard||null);this.revealPendingPlayer=state.revealPendingPlayer==null?null:state.revealPendingPlayer;this.mustTrumpPlayer=state.mustTrumpPlayer==null?null:state.mustTrumpPlayer;
      this.contractTeam=state.contractTeam==null?null:state.contractTeam;this.currentPlayer=state.currentPlayer==null?null:state.currentPlayer;this.leader=state.leader==null?null:state.leader;this.trick=clone(state.trick||[]);this.tricksWon=[...(state.tricksWon||[0,0])];this.trickCountByPlayer=[...(state.trickCountByPlayer||[0,0,0,0])];
      this.trumpLeadOccurred=!!state.trumpLeadOccurred;this.trickStartedWithTrumpKnown=!!state.trickStartedWithTrumpKnown;this.invalidReason=state.invalidReason||null;this.lastTrickWinner=state.lastTrickWinner==null?null:state.lastTrickWinner;this.lastTrick=clone(state.lastTrick||[]);this.pendingTrickWinner=state.pendingTrickWinner==null?null:state.pendingTrickWinner;this.handScore=clone(state.handScore||null);
      this.shuffleCount=Number(state.shuffleCount||0);this.bidDeadline=Number(state.bidDeadline||0);this.sideOffCount=[...(state.sideOffCount||[0,0,0,0])];this.sideOffEligible=[...(state.sideOffEligible||[false,false,false,false])];this.sideOffDeclared=[...(state.sideOffDeclared||[false,false,false,false])];this.history=clone(state.history||[]);return this;
    }
    setNames(names){if(!Array.isArray(names)||names.length!==4)return;names.forEach((n,i)=>{this.players[i].name=String(n||this.players[i].name).trim().slice(0,18)||this.players[i].name});this.playerNames=this.players.map(p=>p.name)}
    setAvatars(avatars){if(!Array.isArray(avatars)||avatars.length!==4)return;avatars.forEach((a,i)=>{if(/^a(?:[1-9]|[1-3][0-9]|4[0-8])$/.test(String(a)))this.players[i].avatar=String(a)})}
  }

  const api={ItalianBridgeEngine,SUITS,SUIT_SYMBOL,TARGETS,rankLabel,cardLabel};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
  global.ItalianBridge=api;
})(typeof window!=='undefined'?window:globalThis);
