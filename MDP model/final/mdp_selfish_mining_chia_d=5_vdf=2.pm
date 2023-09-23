mdp

// x is fraction of space controlled by adv.
const double x = 0.2;
//y or gamma is the probability of honest mining on adv blocks during a race condition
const double y = 0.1;
//cq is chain quality, will initially be set to 0.5 and will estimate the real value after 10 steps
const double cq = 0.74;


// max deapth of chains/branches
const int d = 5;


// n is total number of blocks adv. mines on, including 4 blocks in the public chain
formula n = (2); // number of blocks adv mines on top of
formula total = ((n - 1)*x+1); // total mining power of the network  //TODO: change this


module selfish_mining_general_strategy

 	// cij is the jth private chain at deapth 4-i
 	
 	c31 : [0..d] init 0;
 	c41 : [0..d] init 0;

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
	


	// fix this part
  	[] act=0 -> (1-x)/total : (honest_mined'=1) & (act'=1) & (adv'=0) & (honest'=0) +
	

	
	1*x/total : (c31'=min(d,c31+1)) & (honest_mined'=0) & (act'=1) & (adv'=0) & (honest'=0) +
	1*x/total : (c41'=min(d,c41+1)) & (honest_mined'=0) & (act'=1) & (adv'=0) & (honest'=0);

	// TODO: MAYBE NEED TO CHANGE THIS
  	[] act=1 & honest_mined=0 -> (act'=0); //does not publish



	// branch 41 //Done!
	// publish a block from branch 41
	[] act=1 & honest_mined=0 & c41>0 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
			(c31'=0)& (c41'=c41-1);

	// publish 2 blocks from branch 41
	[] act=1 & honest_mined=0 & c41>1 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c31'=0) & (c41'=c41-2);

	// publish 3 blocks from branch 41
	[] act=1 & honest_mined=0 & c41>2 -> (act'=0) & (adv'=b1+b2+b3) & (honest'=3-(b1+b2+b3)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0)& (c41'=0);

	
	
	// new
	// publish 4 blocks from branch 41
	[] act=1 & honest_mined=0 & c41>3 -> (act'=0) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0) & (c41'=0);

	// publish 5 blocks from branch 41
	[] act=1 & honest_mined=0 & c41>4 -> (act'=0) & (adv'=b1+b2+b3+2) & (honest'=5-(b1+b2+b3+2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0)& (c41'=0);









	// branch 31 //Done!
	// publish the single block of branch 31, race of two single block branches
	[] act=1 & honest_mined=0 & c31=1 -> x : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c31'=0)& (c41'=0) +

			(1-x)*y : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=0) &
			(c31'=0) & (c41'=0) +
			
			(1-x)*(1-y) : (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c31'=c41) & (c41'=0);

	// consider the case where c31>0 but publishes one block only //????

	// publish 2 blocks from branch 31
	[] act=1 & honest_mined=0 & c31>1 -> (act'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=1) & (b3'=1) &
			(c31'=0)  & (c41'=c31-2);

	// publish 3 blocks from branch 31
	[] act=1 & honest_mined=0 & c31>2 -> (act'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0)  & (c41'=0);





	// new
	// publish 4 blocks from branch 31
	[] act=1 & honest_mined=0 & c31>3 -> (act'=0) & (adv'=b1+b2+1) & (honest'=3-(b1+b2+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0)  & (c41'=0);

	// publish 5 blocks from branch 31
	[] act=1 & honest_mined=0 & c31>4 -> (act'=0) & (adv'=b1+b2+2) & (honest'=4-(b1+b2+2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0)  & (c41'=0);











	






	// Actions after honest mined and honest_mined=1

	// Dont publish, accept new honest block
	[] act=1 & honest_mined=1 -> (act'=0) & (honest_mined'=0) & (adv'=b1) & (honest'=1-b1) & (b1'=b2) & (b2'=b3) & (b3'=0) &
			(c31'=c41) & (c41'=0); //does not publish




	// branch 41	//Done!
	// publish 1 block from branch 41
	[] act=1 & honest_mined=1 & c41=1 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c31'=0) &  (c41'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=0) &
			(c31'=0) &  (c41'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c31'=0) &  (c41'=0);

	// publish 2 blocks from branch 41
	[] act=1 & honest_mined=1 & c41>1 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=1) & (b3'=1) &
			(c31'=0) &  (c41'=c41-2);

	// publish 3 blocks from branch 41
	[] act=1 & honest_mined=1 & c41>2 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+b3) & (honest'=3-(b1+b2+b3)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0)  & (c41'=0);



	// new
	// publish 4 blocks from branch 41
	[] act=1 & honest_mined=1 & c41>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+b3+1) & (honest'=4-(b1+b2+b3+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0) & (c41'=0);

	// publish 5 blocks from branch 41
	[] act=1 & honest_mined=1 & c41>4 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+b3+2) & (honest'=5-(b1+b2+b3+2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0) &  (c41'=0);



	




	// branch 31	//Done!
	// publish 2 block from branch 31
	[] act=1 & honest_mined=1 & c31=2 -> x : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0) &  (c41'=0) +

			(1-x)*y : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=0) &
			(c31'=0) & (c41'=0) +

			(1-x)*(1-y) : (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=b3) & (b2'=0) & (b3'=0) &
			(c31'=0) &  (c41'=0);

	// publish 3 blocks from branch 31
	[] act=1 & honest_mined=1 & c31>2 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2) & (honest'=2-(b1+b2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0) & (c41'=0);





	// new
	// publish 4 blocks from branch 31
	[] act=1 & honest_mined=1 & c31>3 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+1) & (honest'=3-(b1+b2+1)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0) & (c41'=0);

	// publish 5 blocks from branch 31
	[] act=1 & honest_mined=1 & c31>4 -> (act'=0) & (honest_mined'=0) & (adv'=b1+b2+2) & (honest'=4-(b1+b2+2)) & (b1'=1) & (b2'=1) & (b3'=1) &
			(c31'=0) & (c41'=0);







	

	




	






endmodule

//rewards
//	[] true : honest;// * (1-cq);
	//[] true : adv;// * (-cq);
//endrewards

rewards
	[] true : honest * (1-cq);
	[] true : adv * (-cq);
endrewards
