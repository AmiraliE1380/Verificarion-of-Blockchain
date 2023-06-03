mdp

// x is fraction of space controlled by adv.
const double x = 0.2;
//y or gamma is the probability of honest mining on adv blocks during a race condition
const double y = 0.5;
//cq is chain quality, will initially be set to 0.5 and will estimate the real value after 10 steps
const double cq = 0.5;


// di is the max deapth of chains/branches at deapth 4-i of the public chain
const int d1 = 5;
const int d2 = 4;
const int d3 = 3;
const int d4 = 3;


// n is total number of blocks adv. mines on, including 4 blocks in the public chain
formula n = (4+min(c11+c12,1)+min(c21+c22,1)+min(c31+c32,1)+min(c41+c42,1)); // number of blocks adv mines on top of
formula total = ((n - 1)*x+1); // total mining power of the network  //TODO: change this


module selfish_mining_general_strategy

 	// cij is the jth private chain at deapth 4-i
 	c11 : [0..d1] init 0;
 	c12 : [0..d1] init 0;
 	
 	c21 : [0..d2] init 0;
 	c22 : [0..d2] init 0;
 	
 	c31 : [0..d3] init 0;
 	c32 : [0..d3] init 0;
 	
 	c41 : [0..d4] init 0;
 	c42 : [0..d4] init 0;
 	
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
	


  	[] act=0 -> (1-x)/total : (honest_mined'=1) & (act'=1) & (adv'=0) & (honest'=0);
	

	[] act=0 & c11=0 -> 1*x/total : (c11'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c11>0 -> 1*x/total : (c11'=min(d1,c11+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c12'=min(d1,c12+1)) & (act'=1) & (adv'=0) & (honest'=0);
	

	[] act=0 & c21=0 -> 1*x/total : (c21'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c21>0 -> 1*x/total : (c21'=min(d2,c21+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c22'=min(d2,c22+1)) & (act'=1) & (adv'=0) & (honest'=0);
	
	
	[] act=0 & c31=0 -> 1*x/total : (c31'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c31>0 -> 1*x/total : (c31'=min(d3,c31+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c32'=min(d3,c32+1)) & (act'=1) & (adv'=0) & (honest'=0);
	

	[] act=0 & c41=0 -> 1*x/total : (c41'=1) & (act'=1) & (adv'=0) & (honest'=0);

	[] act=0 & c41>0 -> 1*x/total : (c41'=min(d4,c41+1)) & (act'=1) & (adv'=0) & (honest'=0) +
			1*x/total : (c42'=min(d4,c42+1)) & (act'=1) & (adv'=0) & (honest'=0);
	

	// TODO: MAYBE NEED TO CHANGE THIS
  	[] act=1 & honest_mined=0 -> (act'=0); //does not publish



	// branch 41 //Done!
	// publish a block from branch 41
	[] act=1 & & honest_mined=0 & c41>0 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c42) & (c32'=0) & (c41'=c41-1) & (c42'=0);

	// publish 2 blocks from branch 41
	[] act=1 & & honest_mined=0 & c41>1 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c42) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c41-2) & (c42'=0);

	// publish 3 blocks from branch 41
	[] act=1 & & honest_mined=0 & c41>2 -> (act'=0) & (adv'=b1+b2+b3) & (honest'=3-(b1+b2+b3)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c42) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);




	// branch 42 //Done!
	// publish a block from branch 42
	[] act=1 & & honest_mined=0 & c42>0 -> (act'=0) & (adv'=b0) & (honest'=1-b0) & (b1'=b2) & (b2'=b3) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=c32) & (c31'=c41) & (c32'=0) & (c41'=c42-1) & (c42'=0);

	// publish 2 blocks from branch 42
	[] act=1 & & honest_mined=0 & c42>1 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=c32) & (c21'=c41) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c42-2) & (c42'=0);

	// publish 3 blocks from branch 42
	[] act=1 & & honest_mined=0 & c42>2 -> (act'=0) & (adv'=b1+b2+b3) & (honest'=3-(b1+b2+b3)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c41) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);




	// branch 31
	// publish the single block of branch 31
	[] act=1 & honest_mined=0 & c31=1 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
			
			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// consider the case where c31>0 but publishes one block only

	// publish 2 blocks from branch 31
	[] act=1 & & honest_mined=0 & c31>1 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c31-2) & (c42'=0);

	// publish 3 blocks from branch 31
	[] act=1 & & honest_mined=0 & c31>2 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c32) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);



	// branch 32
	// publish the single block of branch 32
	[] act=1 & honest_mined=0 & c32=1 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
			
			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// consider the case where c32>0 but publishes one block only

	// publish 2 blocks from branch 32
	[] act=1 & & honest_mined=0 & c32>1 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c31-2) & (c42'=0);

	// publish 3 blocks from branch 32
	[] act=1 & & honest_mined=0 & c32>2 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	// YOU WHERE HERE!
	// branch 21
	// publish two blocks of branch 21
	[] act=1 & honest_mined=0 & c21=2 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
			
			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// consider the case where c31>0 but publishes one block only

	// publish 2 blocks from branch 31
	[] act=1 & & honest_mined=0 & c31>1 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c32) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c31-2) & (c42'=0);

	// publish 3 blocks from branch 31
	[] act=1 & & honest_mined=0 & c31>2 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c32) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

//////////////////////////////////////////////////////////////////////// not completed from here on /////////////////////////////////////////////////////////

	// branch 32
	// publish the single block of branch 32
	[] act=1 & honest_mined=0 & c32=0 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0) +
			
			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);

	// consider the case where c32>0 but publishes one block only

	// publish 2 blocks from branch 32
	[] act=1 & & honest_mined=0 & c32>1 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c11'=c21) & (c12'=c22) & (c21'=c31) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=c31-2) & (c42'=0);

	// publish 3 blocks from branch 32
	[] act=1 & & honest_mined=0 & c32>2 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c11'=c31) & (c12'=0) & (c21'=0) & (c22'=0) & (c31'=0) & (c32'=0) & (c41'=0) & (c42'=0);





	

endmodule

rewards
	[] honest>0 : honest * (-b);
	[] adv>0 : adv * (1-b); 
endrewards