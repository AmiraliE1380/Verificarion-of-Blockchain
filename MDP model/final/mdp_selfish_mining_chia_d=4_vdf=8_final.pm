mdp

// x is fraction of space controlled by adv.
const double x = 0.2;
//y or gamma is the probability of honest mining on adv blocks during a race condition
const double y = 0;
//cq is chain quality, will initially be set to 0.5 and will estimate the real value after 10 steps
const double cq = 0.7155;


// max deapth of chains/branches
const int d = 4;
const int dd = 4;


// n is total number of blocks adv. mines on, including 4 blocks in the public chain
formula n = (4+min(c11+c12,1)+min(c21+c22,1)+min(c31+c32,1)+min(c41+c42,1)); // number of blocks adv mines on top of
formula total = ((n - 1)*x+1); // total mining power of the network  //TODO: change this


module selfish_mining_general_strategy

 	// cij is the jth private chain at deapth 4-i
 	c11 : [0..d] init 0;
 	c12 : [0..d] init 0;
 	
 	c21 : [0..d] init 0;
 	c22 : [0..d] init 0;
 	
 	c31 : [0..d] init 0;
 	c32 : [0..d] init 0;
 	
 	c41 : [0..dd] init 0;
 	c42 : [0..dd] init 0;

	// In this implementation when a chain is at its maximum length, new blocks will be discarded.
	// This case will not happend because when a branch reaches its full length, MDP will release it
	// Because its the best strategy
 	
  	// bi is the status of the public block at deapth 3 - i
  	// if bi=0 the block belongs to honest miner, if bi=1 it belongs to the selfish miner
  	b1 : [0..1] init 0;
  	b2 : [0..1] init 0;
  	b3 : [0..1] init 0;


  	// act=1 specifies states where selfish miner can make a decision (publishing a tree or nothing)
  	act : [0..1] init 0;

  	// honest_mined=1 iff the last mined block is honest
  	honest_mined : [0..1] init 0;

	// adv and honest are the number of adv and honest finilized blocks in a transition
	honest : [0..3] init 0;
	adv : [0..3] init 0;
	


  	[] honest_mined=0 -> (1-x)/total : (honest_mined'=1) & (adv'=0) & (honest'=0) +
		1*x/total : (c11'=min(d,c11+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0) +
				1*x/total *min(c11,1) : (c12'=min(d,c12+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0) +
		1*x/total : (c21'=min(d,c21+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0) +
				1*x/total *min(c21,1) : (c22'=min(d,c22+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0) +
		1*x/total : (c31'=min(d,c31+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0) +
				1*x/total *min(c31,1) : (c32'=min(d,c32+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0) +
		1*x/total : (c41'=min(dd,c41+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0) +
				1*x/total  *min(c41,1) : (c42'=min(dd,c42+1)) & (honest_mined'=0) & (adv'=0) & (honest'=0); //does not publish



	// branch 41 //Done!
	// publish a block from branch 41
	[] honest_mined=0 & c41>0 -> 
		(1-x)/total : (honest_mined'=1) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c21+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=min(d,c22+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0)+
		
		1*x/total : (c21'=min(d,c31+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0)+
		
		1*x/total *min(c21,1) : (c22'=min(d,c32+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0)+
		
		1*x/total : (c31'=min(d,c42+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c32'=0) & (c41'=c41-1) & (c42'=0)+
		
		1*x/total *min(c31,1) : (c32'=1) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c41'=c41-1) & (c42'=0)+
		
		1*x/total : (c41'=c41) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c42'=0)+
		
		1*x/total  *min(c41,1) : (c42'=1) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1);

	


	// publish 2 blocks from branch 41
	[] honest_mined=0 & c41>1 -> 
		(1-x)/total : (honest_mined'=1) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c31+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=min(d,c32+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0) +
		
		1*x/total : (c21'=min(d,c42+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0) +
		
		1*x/total *min(c21,1) : (c22'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c42) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0) +
		
		1*x/total : (c31'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0) +
		
		1*x/total *min(c31,1) : (c32'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c41'=c41-2) & (c42'=0)+
		
		1*x/total : (c41'=c41-1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c42'=0) +
		
		1*x/total  *min(c41,1) : (c42'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2);

	
	
	
	

	// publish 3 blocks from branch 41
	[] honest_mined=0 & c41>2 -> 
		(1-x)/total : (honest_mined'=1) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-3) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c42+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-3) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-3) & (c42'=0) +
		
		1*x/total : (c21'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c12'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-3) & (c42'=0) +
		
		1*x/total *min(c21,1) : (c22'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c12'=0) & (c21'=0) & (c31'=0) & (c32'=0) & (c41'=c41-3) & (c42'=0) +
		
		1*x/total : (c31'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c32'=0) & (c41'=c41-3) & (c42'=0) +
		
		1*x/total *min(c31,1) : (c32'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c41'=c41-3) & (c42'=0)+
		
		1*x/total : (c41'=c41-2) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c42'=0) +
		
		1*x/total  *min(c41,1) : (c42'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-3);

	
	
	
	
	
	
	
	// new
	// publish 4 blocks from branch 41
	[] honest_mined=0 & c41>3 -> (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c42+1)) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total : (c21'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total *min(c21,1) : (c22'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total : (c31'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total *min(c31,1) : (c32'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c41'=0) & (c42'=0)+
		
		1*x/total : (c41'=c41-2) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c42'=0) +
		
		1*x/total  *min(c41,1) : (c42'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0);








	// branch 42 //Done!
	// publish a block from branch 42
	[] honest_mined=0 & c42>0 -> 
		(1-x)/total : (honest_mined'=1) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c21+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=min(d,c22+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0)+
		
		1*x/total : (c21'=min(d,c31+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0)+
		
		1*x/total *min(c21,1) : (c22'=min(d,c32+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0)+
		
		1*x/total : (c31'=min(d,c41+1)) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c32'=0) & (c41'=c42-1) & (c42'=0)+
		
		1*x/total *min(c31,1) : (c32'=1) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c41'=c42-1) & (c42'=0)+
		
		1*x/total : (c41'=c42) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c42'=0)+
		
		1*x/total  *min(c41,1) : (c42'=1) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
					(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1);

	


	// publish 2 blocks from branch 42
	[] honest_mined=0 & c42>1 -> 
		(1-x)/total : (honest_mined'=1) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c31+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=min(d,c32+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0) +
		
		1*x/total : (c21'=min(d,c41+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0) +
		
		1*x/total *min(c21,1) : (c22'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c41) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0) +
		
		1*x/total : (c31'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0) +
		
		1*x/total *min(c31,1) : (c32'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c41'=c42-2) & (c42'=0)+
		
		1*x/total : (c41'=c41-1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c42'=0) +
		
		1*x/total  *min(c41,1) : (c42'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2);
	
	
	
	

	// publish 3 blocks from branch 42
	[] honest_mined=0 & c42>2 -> 
		(1-x)/total : (honest_mined'=1) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-3) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c41+1)) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-3) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-3) & (c42'=0) +
		
		1*x/total : (c21'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c12'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-3) & (c42'=0) +
		
		1*x/total *min(c21,1) : (c22'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c12'=0) & (c21'=0) & (c31'=0) & (c32'=0) & (c41'=c42-3) & (c42'=0) +
		
		1*x/total : (c31'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c32'=0) & (c41'=c42-3) & (c42'=0) +
		
		1*x/total *min(c31,1) : (c32'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c41'=c42-3) & (c42'=0)+
		
		1*x/total : (c41'=c42-2) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c42'=0) +
		
		1*x/total  *min(c41,1) : (c42'=1) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
					(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-3);

	
	
	
	
	
	
	
	// new
	// publish 4 blocks from branch 42
	[] honest_mined=0 & c42>3 -> (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total : (c11'=min(d,c42+1)) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total *min(c11,1) : (c12'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total : (c21'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total *min(c21,1) : (c22'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total : (c31'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
		
		1*x/total *min(c31,1) : (c32'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c41'=0) & (c42'=0)+
		
		1*x/total : (c41'=c41-2) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c42'=0) +
		
		1*x/total  *min(c41,1) : (c42'=1) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
					(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0);






////////////////////////////////////////////////////////////////////


	// branch 42 //Done!
	// publish a block from branch 42
	[] act=1 & honest_mined=0 & c42>0 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0);

	// publish 2 blocks from branch 42
	[] act=1 & honest_mined=0 & c42>1 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0);

	// publish 3 blocks from branch 42
	[] act=1 & honest_mined=0 & c42>2 -> (act'=0) & (adv'=b1+b2+b3) & (honest'=3-(b1+b2+b3)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	
	
	// new
	// publish 4 blocks from branch 42
	[] act=1 & honest_mined=0 & c41>3 -> (act'=0) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// branch 31 //Done!
	// publish the single block of branch 31, race of two single block branches
	[] act=1 & honest_mined=0 & c31=1 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
			
			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=c42) & (c41'=0) & (c42'=0);

	// consider the case where c31>0 but publishes one block only //????

	// publish 2 blocks from branch 31
	[] act=1 & honest_mined=0 & c31>1 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c31-2) & (c42'=0);

	// publish 3 blocks from branch 31
	[] act=1 & honest_mined=0 & c31>2 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c32) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// new
	// publish 4 blocks from branch 31
	[] act=1 & honest_mined=0 & c31>3 -> (act'=0) & (adv'=b1+b2+1) & (honest'=3-(b1+b2+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);




	// branch 32 //Done!
	// publish the single block of branch 32
	[] act=1 & honest_mined=0 & c32=1 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
			
			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=c42) & (c41'=0) & (c42'=0);

	// consider the case where c32>0 but publishes one block only

	// publish 2 blocks from branch 32
	[] act=1 & honest_mined=0 & c32>1 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c31-2) & (c42'=0);

	// publish 3 blocks from branch 32
	[] act=1 & honest_mined=0 & c32>2 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// new
	// publish 4 blocks from branch 32
	[] act=1 & honest_mined=0 & c32>3 -> (act'=0) & (adv'=b1+b2+1) & (honest'=3-(b1+b2+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);









	// branch 21	//Done!
	// publish two blocks of branch 21
	[] act=1 & honest_mined=0 & c21=2 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c22) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=c22) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=c42) & (c41'=0) & (c42'=0);


	// publish 3 blocks from branch 21
	[] act=1 & honest_mined=0 & c21>2 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c22) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c21-3) & (c42'=0);

	// publish 4 blocks from branch 21
	[] act=1 & honest_mined=0 & c21>3 -> (act'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);






	// branch 22	//Done!
	// publish two blocks of branch 22
	[] act=1 & honest_mined=0 & c21=2 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=c42) & (c41'=0) & (c42'=0);


	// publish 3 blocks from branch 22
	[] act=1 & honest_mined=0 & c22>2 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c22-3) & (c42'=0);

	// publish 4 blocks from branch 22
	[] act=1 & honest_mined=0 & c22>3 -> (act'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);







	// branch 11	//Done!
	// publish 3 blocks of branch 11
	[] act=1 & honest_mined=0 & c11=3 -> x : (act'=0) & (adv'=1) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=1) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=c42) & (c41'=0) & (c42'=0);


	// publish 4 blocks from branch 11
	[] act=1 & honest_mined=0 & c11>3 -> (act'=0) & (adv'=1) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// branch 12
	// publish 3 blocks of branch 12
	[] act=1 & honest_mined=0 & c12=3 -> x : (act'=0) & (adv'=1) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=1) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=c42) & (c41'=0) & (c42'=0);


	// publish 4 blocks from branch 12
	[] act=1 & honest_mined=0 & c12>3 -> (act'=0) & (adv'=1) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);







	// Actions after honest mined and honest_mined=1

	// Dont publish, accept new honest block
	[] act=1 & honest_mined=1 -> (act'=0) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=c42) & (c41'=0) & (c42'=0); //does not publish




	// branch 41	//Done!
	// publish 1 block from branch 41
	[] act=1 & honest_mined=1 & c41=1 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// publish 2 blocks from branch 41
	[] act=1 & honest_mined=1 & c41>1 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0);

	// publish 3 blocks from branch 41
	[] act=1 & honest_mined=1 & c41>2 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+b3) & (honest'=3-(b1+b2+b3)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);



	// new
	// publish 4 blocks from branch 41
	[] act=1 & honest_mined=1 & c41>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// branch 42	//Done!
	// publish 1 block from branch 42
	[] act=1 & honest_mined=1 & c42=1 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// publish 2 blocks from branch 42
	[] act=1 & honest_mined=1 & c42>1 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0);

	// publish 3 blocks from branch 42
	[] act=1 & honest_mined=1 & c42>2 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+b3) & (honest'=3-(b1+b2+b3)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);



	// new
	// publish 4 blocks from branch 42
	[] act=1 & honest_mined=1 & c41>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	




	// branch 31	//Done!
	// publish 2 block from branch 31
	[] act=1 & honest_mined=1 & c31=2 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c32) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=c32) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// publish 3 blocks from branch 31
	[] act=1 & honest_mined=1 & c31>2 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c32) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// new
	// publish 4 blocks from branch 31
	[] act=1 & honest_mined=1 & c31>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+1) & (honest'=3-(b1+b2+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	




	// branch 32
	// publish 2 block from branch 32
	[] act=1 & honest_mined=1 & c32=2 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=c31) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// publish 3 blocks from branch 32
	[] act=1 & honest_mined=1 & c32>2 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// new
	// publish 4 blocks from branch 32
	[] act=1 & honest_mined=1 & c32>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+1) & (honest'=3-(b1+b2+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);



	

	




	// branch 21	//Done!	
	// publish 3 blocks from branch 21
	[] act=1 & honest_mined=1 & c21=3 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// publish 4 blocks from branch 21
	[] act=1 & honest_mined=1 & c21>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);



	




	// branch 22
	// publish 3 blocks from branch 22
	[] act=1 & honest_mined=1 & c22=3 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// publish 4 blocks from branch 22
	[] act=1 & honest_mined=1 & c22>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+1) & (honest'=2-(b1+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	





	// branch 11	// Done!
	// publish 4 blocks from branch 11
	[] act=1 & honest_mined=1 & c11=4 -> x : (act'=0) & (honest_mined'=0) & (adv'=2) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=2) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// branch 12	// Done!
	// publish 4 blocks from branch 12
	[] act=1 & honest_mined=1 & c12=4 -> x : (act'=0) & (honest_mined'=0) & (adv'=2) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=2) & (honest'=0) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c11'=0) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=c42) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	

endmodule

rewards
	[] true : honest * (1-cq);
	[] true : adv * (-cq);
endrewards
