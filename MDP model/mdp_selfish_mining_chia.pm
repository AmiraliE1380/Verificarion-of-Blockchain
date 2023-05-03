mdp

// formulae 
// left fork free (left neighbour is philosopher 2)
//formula lfree = (p2>=0 & p2<=4) | p2=6 | p2=10;
// right fork free (left neighbour is philosopher 3)
//formula rfree = (p3>=0 & p3<=3) | p3=5 | p3=7 | p3=11;

// x is fraction of space controlled by adv.
const double x = 0.05;

// di is the max deapth of tree i
const int d1 = 5;
const int d2 = 4;
const int d3 = 3;
const int d4 = 3;

// wi is the max width of tree i
const int w1 = 2;
const int w2 = 2;
const int w3 = 2;
const int w4 = 3;


// n is total number of blocks adv. mines on, including 4 blocks in the public chain
formula n = (n11+n12+n13+n14+n21+n22+n23+n31+n32+n41+n42+4);
formula total = ((n - 1)*x+1); // total mining power of the network


module selfish_mining_general_strategy

 	// nij is the number of private blocks in tree i at level j
 	n11 : [0..w1] init 0;
 	n12 : [0..w1] init 0;
 	n13 : [0..w1] init 0;
 	n14 : [0..w1] init 0;
 	n15 : [0..w1] init 0;
  
 	n21 : [0..w2] init 0;
	n22 : [0..w2] init 0;
	n23 : [0..w2] init 0;
 	n24 : [0..w2] init 0;
  
 	n31 : [0..w3] init 0;
  	n32 : [0..w3] init 0;
  	n33 : [0..w3] init 0;
  
 	n41 : [0..w4] init 0;
  	n42 : [0..w4] init 0;
  	n43 : [0..w4] init 0;
  
  	// bi is the status of the public block at deapth 3 - i
  	// if bi=0 the block belongs to honest miner, if bi=1 it belongs to the selfish miner
  	b1 : [0..1] init 0;
  	b2 : [0..1] init 0;
  	b3 : [0..1] init 0;

  	// b0 is the block which will definitely enter the main chain
  	b0 : [0..1] init 0;
  
  	// act=1 specifies states where selfish miner can make a decision (publishing a tree or nothing)
  	act : [0..1] init 0;

  	// honest_mined=1 iff the last mined block is honest
  	honest_mined : [0..1] init 0;

  	[] act=0 -> (1-x)/total : (honest_mined'=1) & (act'=1) +
      		1*x/total : (n11'=min(w1,n11+1)) & (act'=1) +
      		n11*x/total : (n12'=min(w1,n12+1)) & (act'=1) +
      		n12*x/total : (n13'=min(w1,n13+1)) & (act'=1) +
      		n13*x/total : (n14'=min(w1,n14+1)) & (act'=1) +
      		n14*x/total : (n15'=min(w1,n15+1)) & (act'=1) +
      
      	1*x/total : (n21'=min(w2,n21+1)) & (act'=1) +
      		n21*x/total : (n22'=min(w2,n22+1)) & (act'=1) +
      		n22*x/total : (n23'=min(w2,n23+1)) & (act'=1) +
      		n23*x/total : (n24'=min(w2,n24+1)) & (act'=1) +
      
      	1*x/total : (n31'=min(w3,n31+1)) & (act'=1) +
      		n31*x/total : (n32'=min(w3,n32+1)) & (act'=1) +
      		n32*x/total : (n33'=min(w3,n33+1)) & (act'=1) +
      
      	1*x/total : (n41'=min(w4,n41+1)) & (act'=1) +
      		n41*x/total : (n12'=min(w4,n42+1)) & (act'=1) +
      		n42*x/total : (n13'=min(w4,n43+1)) & (act'=1);
  


  	[] act=1 -> (act'=0); //does not publish

  	//publish a block from t4
  	//do we need to add gaurd n42=0?
  	[] act=1 & n41>0 -> (act'=0) & (b0'=b1) & (b1'=b2) & (b2'=b3) & (b3'=1) &
      		(n11'=n21) & (n12'=n22) & (n13'=n23) & (n14'=n24) & (n15'=0) &
      		(n21'=n31) & (n22'=n32) & (n23'=n33) & (n24'=0) &
      		(n31'=n41-1) & (n32'=0) & (n33'=0) & 
      		(n41'=0) & (n42'=0) & (n43'=0); 

  	//publish 2 blocks from t4
  	[] act=1 & n42>0 -> (act'=0) & (b0'=b2) & (b1'=b3) & (b2'=1) & (b3'=1) &
      		(n11'=n31) & (n12'=n32) & (n13'=n33) & (n14'=0) & (n15'=0) &
      		(n21'=n41-1) & (n22'=0) & (n23'=0) & (n24'=0) &
      		(n31'=0) & (n32'=0) & (n33'=0) &
     		(n41'=0) & (n42'=0) & (n43'=0);

  	//publish 3 blocks from t4
  	[] act=1 & n43>0 -> (act'=0) & (b0'=b3) & (b1'=1) & (b2'=1) & (b3'=1) &
      		(n11'=n31) & (n12'=n32) & (n13'=n33) & (n14'=0) & (n15'=0) &
      		(n21'=n41-1) & (n22'=n42 - 1);

  
    


  	//consider the states where honest_mined=1



  p1: [0..11];
[] p1=0 -> (p1'=1); // trying
  [] p1=1 -> 0.5 : (p1'=2) + 0.5 : (p1'=3); // draw randomly
  [] p1=2 &  lfree -> (p1'=4); // pick up left
  [] p1=3 &  rfree -> (p1'=5); // pick up right
  [] p1=4 &  rfree -> (p1'=8); // pick up right (got left)
  [] p1=4 & !rfree -> (p1'=6); // right not free (got left)
  [] p1=5 &  lfree -> (p1'=8); // pick up left (got right)
  [] p1=5 & !lfree -> (p1'=7); // left not free (got right)
  [] p1=6  -> (p1'=1); // put down left
  [] p1=7  -> (p1'=1); // put down right
  [] p1=8  -> (p1'=9); // move to eating (got forks)
  [] p1=9  -> (p1'=10); // finished eating and put down left 
  [] p1=9  -> (p1'=11); // finished eating and put down right
  [] p1=10 -> (p1'=0); // put down right and return to think
  [] p1=11 -> (p1'=0); // put down left and return to think


  

  [] n0=0 & n1=0 -> x : (n1'=1) & (adv'=0) & (honest'=0) +
      (1-x) : (adv'=0) & (honest'=1);


  [] n0>0 & n1=0 -> n0*x/((n0-1)*x+1) : (n0'=0) & (adv'=2) & (honest'=0) +
      n0*(1-x)/((n0+1)*((n0-1)*x+1)) : (n0'=0) & (adv'=1) & (honest'=1) +
      (1-x)/((n0+1)*((n0-1)*x+1)) : (n0'=0) & (adv'=0) & (honest'=2);


  [] n1>0 & n2=0 -> (1-x)/total : (n0'=n1) & (n1'=0) & (adv'=0) & (honest'=0) +
      (n0+1)*x/total : (n1'=min(w,n1+1)) & (adv'=0) & (honest'=0) +
      n1*x/total : (n2'=min(w,n2+1)) & (adv'=0) & (honest'=0) +
      n2*x/total : (n3'=min(w,n3+1)) & (adv'=0) & (honest'=0) +
      n3*x/total : (n4'=min(w,n4+1)) & (adv'=0) & (honest'=0) +
      n4*x/total : (n5'=min(w,n5+1)) & (adv'=0) & (honest'=0) +
      n5*x/total : (n6'=min(w,n6+1)) & (adv'=0) & (honest'=0) +
      n6*x/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) &
          (n4'=n5) & (n5'=n6) & (n6'=1) & (adv'=1)
          & (honest'=0);
      
  

  [] n2>0 & n3=0 -> (1-x)/total : (n0'=0) & (n1'=0) & (n2'=0) & (adv'=2) & (honest'=0) +
      (n0+1)*x/total : (n1'=min(w,n1+1)) & (adv'=0) & (honest'=0) +
      n1*x/total : (n2'=min(w,n2+1)) & (adv'=0) & (honest'=0) +
      n2*x/total : (n3'=min(w,n3+1)) & (adv'=0) & (honest'=0) +
      n3*x/total : (n4'=min(w,n4+1)) & (adv'=0) & (honest'=0) +
      n4*x/total : (n5'=min(w,n5+1)) & (adv'=0) & (honest'=0) +
      n5*x/total : (n6'=min(w,n6+1)) & (adv'=0) & (honest'=0) +
      n6*x/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) &
          (n4'=n5) & (n5'=n6) & (n6'=1) & (adv'=1)
          & (honest'=0);


  [] n3>0 -> (1-x)/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) & (n4'=n5)
          & (n5'=n6) & (n6'=0) & (adv'=1) & (honest'=0) +
      (n0+1)*x/total : (n1'=min(w,n1+1)) & (adv'=0) & (honest'=0) +
      n1*x/total : (n2'=min(w,n2+1)) & (adv'=0) & (honest'=0) +
      n2*x/total : (n3'=min(w,n3+1)) & (adv'=0) & (honest'=0) +
      n3*x/total : (n4'=min(w,n4+1)) & (adv'=0) & (honest'=0) +
      n4*x/total : (n5'=min(w,n5+1)) & (adv'=0) & (honest'=0) +
      n5*x/total : (n6'=min(w,n6+1)) & (adv'=0) & (honest'=0) +
      n6*x/total : (n0'=n1) & (n1'=n2) & (n2'=n3) & (n3'=n4) &
          (n4'=n5) & (n5'=n6) & (n6'=1) & (adv'=1)
          & (honest'=0);

endmodule

rewards
      	//[] true : honest;
      	[] finilize_block=1 : adv;
  	//instead of true, you can write another gaurd
endrewards
