/***************************************
 *  Model 4 for OTNS *
 ***************************************/
//Will everything that can happen on the otns simulator be possible on this model?

//Roles
abstract sig Role{}
one sig ED,REED,Router,Leader extends Role {}

//Nodes
one sig None{} 

abstract var sig Node{
	var role : one Role,
	--                  type of msg -> Content -> from
	var inbox :  Type -> (Partition +None) -> Node,
	var partition_id:set Partition, 
	var in_range:set Node

}
var sig FTD extends Node{
	//var childs: set Node, 
	//var connected_ds:set Router, --do a check to see if they form a connected Domain set
	//routing_table: Node(next_hop) -> Node (destination)	
}

var sig MTD extends Node{ 
	//var parent: lone Node,
}

//Network
sig Partition{
	var leader: set Node
}

fun elems:Partition ->Node{
 	~ partition_id
}

abstract sig Type {
}
one sig Preq,Presp,Creq,Lreq,LAreq,LAresp,Lresp, Cresp,Adv extends Type {}


/*************************************
 *          System Specification          *
 *************************************/


fact Init
{
	no inbox
	no partition_id
	no leader
	no (Node.role &Leader)
	no Node
	no in_range
}

fact Common_configuration
{
	always {
		~in_range in in_range
		no (in_range & iden)
	}
}

 
/*************************************
 *                 Transitions                *
 *************************************/

pred Nop{
	role'=role
	inbox'=inbox
	partition_id'=partition_id	
	leader'=leader
	Node'=Node
	in_range'=in_range
}

/**1º process -  4 messages exchange**/

//Multicast 
pred send_ParentRequest[n :Node] {
	
	inbox'= inbox + (n.in_range-> Preq ->None->n) 
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}

// 2- Response from router to child applicant. (Unicast)
pred send_ParentResponse [n :FTD] {
	//PC
	--The FTD is already in a partition
	some n.partition_id
		
	some  msg_from:(None.(Preq.(n.inbox)))  {
		inbox'= inbox + (msg_from ->Presp ->None->n) -  (n -> Preq-> None->msg_from)	
	}
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}

//3- Send request to a specific father 
pred send_ChildRequest [n :Node] {
	//PC There is a Presp in the inbox
	
	some  msg_from:(None.(Presp.(n.inbox)))   {
		inbox'= inbox + (msg_from ->Creq ->None->n) -  (n -> Presp -> None->msg_from)	
	}
		

	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}

// 4- The father accepts the son
pred send_ChildResponse [n :FTD] {
	one n.partition_id

	some  msg_from: (None.(Creq.(n.inbox))) {
		inbox'= inbox + (msg_from ->Cresp ->n.partition_id->n) -  (n -> Creq -> None->msg_from)	
	}
			
	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node

}

----------

pred change_to_leader[n:FTD]{
	--PC	 Ainda não tem partição 
	--n.role != Leader 
	no n.partition_id
	
	role '= role - (n->n.role) + (n->Leader)--passa a leader

	some p:Partition{
		no p.elems
		partition_id'=partition_id +(n->p) - (n->n.partition_id)
		leader'=leader + (p->n)
	}	
	inbox'=inbox
	in_range'= in_range
	Node'=Node
}


pred reset[n:Node]{
	n.role'=REED
	no n.inbox'
	no n.partition_id'
	all nd:Node -n |{
		nd.inbox'=nd.inbox
		nd.partition_id'=nd.partition_id
		nd.role'=nd.role
	}
	leader'= leader - (n.partition_id->n)
	in_range'= in_range --it can be changed.
	Node'=Node
}




// A Thread Device will always attach as an End Device
pred join_to_partition[n:Node]{
	 //PC Have a Child response in the inbox
	 
	some  msg_from:Node , p :Partition | {
 		( Cresp ->p->msg_from ) in n.inbox 
		partition_id'=partition_id	++ (n->p)  
		inbox'= inbox -  (n -> Cresp -> p->msg_from)	
	}
 	n in FTD => role'=role - (n->n.role) +(n->REED) 
		     else role'=role 
	leader'=leader - (Partition -> n) --if the node is leader of any partition it is no longer.
	in_range'= in_range
	Node'=Node
}


--Multicast 
pred send_Advertisement[n:FTD]{
	n.role in (Leader +Router)
	some n.in_range
	
	inbox'= inbox + (n.in_range-> Adv -> n.partition_id->n) 

	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}



/*
	Rules to merge:
		1.Se uma partição apenas tiver 1 elemento, esta cede e junta-se
		2. Weight Value maior  
		3. Partition ID Maior 

*/

--Para dar merge tem de ter um Advertisement na inbox
pred merge_partitions[n:FTD]{
	--PC Is there any partition in my range other than my own.
		//To merge you must have an Advertisement in the inbox
	some n.partition_id

	some  msg_from:Node, p:Partition {
		(Adv->p->msg_from) in n.inbox
		p!= n.partition_id => remove_elemPartition[ n.partition_id,n, p]  and role'=role -  (n->n.role ) + (n->REED )
					 else( partition_id'=partition_id and leader'=leader  and role'=role)
		inbox'= inbox  -  (n -> Adv -> p->msg_from)	
	}
	in_range'= in_range
	Node'=Node

}

pred remove_elemPartition[old_parts:one Partition,node:set Node,newPart:one Partition]{
	some (old_parts.leader & node ) => leader'=leader - (old_parts->node) else  leader'=leader
	partition_id'=partition_id -(node->old_parts) + (node->newPart)
}

/** 2º process - 3 or 2 messages exchange**/
/*   Link Establishment Process Between Routers		

	Link synchronization is performed in the following circumstances:
		- As part of the attachment process,
		- When a REED becomes an active Router.
		- When a Router receives a message from a neighboring device for which it does not
		   33 have a stored frame counter.
*/


/**Multicast process**/

// Sent in multicast to all routers
pred send_LinkRequest[n:FTD]{
	n.role in REED
	one n.partition_id
	
	inbox'= inbox + ((n.in_range & role.(REED + Router+Leader)) ->Lreq ->None -> n) 
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}

//2 - Accept a link Request and Router request for the son to become part of your family 
pred send_LinkAcceptReq[n:FTD]{
	one n.partition_id
	
	some  msg_from: (None.(Lreq.(n.inbox)))  {
		inbox'= inbox + (msg_from ->LAreq ->None->n) -  (n -> Lreq -> None->msg_from)	
	}

	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}

--3 - Positive Response  for the father
pred send_LinkAcceptResp[n:FTD]{
	one n.partition_id
	
	some  msg_from: (None.(LAreq.(n.inbox))) {
		inbox'= inbox + (msg_from -> LAresp->None->n) -  (n -> LAreq -> None-> msg_from)	
	}
	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node

}


/**Unicast process**/ 

// Sent to a router
pred send_LinkReq[src:FTD,dest:FTD]{
	one src.partition_id
	inbox'= inbox + (dest ->Lreq ->None ->src) 
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}
// Response from  a router
pred send_LinkResp[src:FTD,dest:FTD]{
	one src.partition_id
       (src -> Lreq -> None->dest)	in inbox
	
	inbox'= inbox + (dest ->Lresp ->None->src) -  (src -> Lreq -> None->dest)	

	role'=role
	partition_id'=partition_id	
	leader'=leader
	in_range'= in_range
	Node'=Node
}


//Add a node in the network (Always equals)
pred addNode{
	
	some n:Node' {
		n not in Node
		Node'=Node+n 
		role'=role + n->( n in FTD' => REED else ED )
		in_range in in_range' 
	}
	 
	inbox'= inbox
	partition_id'=partition_id	
	leader'=leader
	
}
//Add a node in the network  (changes depending on Node and neibours of this node)
pred addNode[n:Node, new_neighbors:set Node]{
	addNode
	Node'=Node + n
	n.in_range'=new_neighbors
}

//Move a node  (Always equals)
pred move{
	inbox'= inbox
	role'=role
	partition_id'=partition_id	
	leader'=leader
	Node'=Node
}
//Move a node - (changes depending on Node and neibours of this node)
pred move[n:Node, new_neighbors:set Node]{
	move
	in_range'=in_range - ( n->Node )-(Node->n) + (n->new_neighbors)+(new_neighbors->n) 
	
}

//Changes the node role to Router
pred change_to_router[n:FTD]{
	--PC	 
	some n.partition_id 
	some  msg_from:Node { 
		(LAresp->None->n) in msg_from.inbox or (Lresp->None->msg_from) in n.inbox
		inbox'=inbox -  (msg_from->LAresp->None->n) - (n->Lresp->None->msg_from)
	}
			
	role '= role - (n->n.role) + (n->Router) --becomes Router
	partition_id'=partition_id
	in_range'= in_range
	Node'=Node
	leader'=leader
}

/*************************************
 *                 Simulation                 *
 *************************************/

fact transitions{
	always (Nop or 
			(some n:Node |{
				(send_ParentRequest[n] or send_ChildRequest[n] or
				join_to_partition[n])
				
			}) or 
			(some  ftd:FTD|{			
				send_ParentResponse[ftd] or  send_ChildResponse[ftd] or 
				change_to_leader[ftd] or
				send_LinkRequest[ftd] or send_LinkAcceptReq[ftd] or send_LinkAcceptResp[ftd] or 
				send_Advertisement[ftd] or merge_partitions[ftd] or change_to_router[ftd]
			}) or 
		         (some n1:FTD | some n2: FTD-n1 | send_LinkReq[n1,n2] or send_LinkResp[n1,n2]) or 
			  (addNode) or (move)
		    )
}
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      change_to_leader[n2];
      send_ParentRequest[n1];
      send_ParentResponse[n2];
      send_ChildRequest[n1];
      send_ChildResponse[n2];
      join_to_partition[n1] 
}}}  for 2 but 9..9 steps

/*
	//Some examples from OTNS parser 
	
	//Cenário 1

run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      change_to_leader[n2];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 10..10 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      change_to_leader[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1] 
}}}  for 2 but exactly 2 Partition, 15..15 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      change_to_leader[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      join_to_partition[n1] or merge_partitions[n1];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1] 
}}}  for 2 but exactly 2 Partition, 20..20 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      change_to_leader[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      join_to_partition[n1] or merge_partitions[n1];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      change_to_router[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n1] or send_Advertisement[n1] 
}}}  for 2 but exactly 2 Partition, 25..25 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      change_to_leader[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      join_to_partition[n1] or merge_partitions[n1];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      change_to_router[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 2 Partition, 29..29 steps
*/

/*
	// Cenário 2
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        move[n3,n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2] 
}}}}  for 3 but exactly 0 Partition, 10..10 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        move[n3,n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        change_to_leader[n3];
        send_ParentRequest[n3] or send_Advertisement[n3];
        change_to_leader[n2];
        send_ParentRequest[n2] or send_Advertisement[n2] 
}}}}  for 3 but exactly 2 Partition, 15..15 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        move[n3,n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        change_to_leader[n3];
        send_ParentRequest[n3] or send_Advertisement[n3];
        change_to_leader[n2];
        send_ParentRequest[n2] or send_Advertisement[n2];
        change_to_leader[n1];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n3] or send_Advertisement[n3];
        move[n2,n1] 
}}}}  for 3 but exactly 3 Partition, 20..20 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        move[n3,n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        change_to_leader[n3];
        send_ParentRequest[n3] or send_Advertisement[n3];
        change_to_leader[n2];
        send_ParentRequest[n2] or send_Advertisement[n2];
        change_to_leader[n1];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n3] or send_Advertisement[n3];
        move[n3,n1+n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentResponse[n1] or send_ChildRequest[n1];
        send_ParentResponse[n3] or send_ChildRequest[n3];
        send_ParentResponse[n2] or send_ChildRequest[n2] 
}}}}  for 3 but exactly 3 Partition, 25..25 steps
run {
  some n1:FTD' { addNode[n1,none];
    some n2:FTD'-n1 { addNode[n2,n1];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        move[n3,n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        change_to_leader[n3];
        send_ParentRequest[n3] or send_Advertisement[n3];
        change_to_leader[n2];
        send_ParentRequest[n2] or send_Advertisement[n2];
        change_to_leader[n1];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n3] or send_Advertisement[n3];
        move[n3,n1+n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentResponse[n1] or send_ChildRequest[n1];
        send_ParentResponse[n3] or send_ChildRequest[n3];
        send_ParentResponse[n2] or send_ChildRequest[n2];
        send_ParentResponse[n3] or send_ChildRequest[n3];
        join_to_partition[n2] or merge_partitions[n2];
        send_LinkReq[n2,n3] or send_LinkResp[n2,n3] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
        send_LinkReq[n3,n2] or send_LinkResp[n3,n2] or send_LinkAcceptReq[n3] or send_LinkAcceptResp[n3];
        change_to_router[n2] 
}}}}  for 3 but exactly 3 Partition, 30..30 steps
*/

/*
	// Cenário 3

run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1] 
}}}  for 2 but exactly 1 Partition, 10..10 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2] 
}}}  for 2 but exactly 1 Partition, 15..15 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1] 
}}}  for 2 but exactly 1 Partition, 20..20 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      move[n2,none];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,none];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 25..25 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      move[n2,none];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,none];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 30..30 steps
*/

/*
	// Cenário 4

run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 10..10 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2] 
}}}  for 2 but exactly 1 Partition, 15..15 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 20..20 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      move[n2,n1];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        send_ParentRequest[n3] or send_Advertisement[n3] 
}}}}  for 3 but exactly 1 Partition, 25..25 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      move[n2,n1];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentResponse[n2] or send_ChildRequest[n2];
        send_ParentResponse[n1] or send_ChildRequest[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentResponse[n3] or send_ChildRequest[n3] 
}}}}  for 3 but exactly 1 Partition, 30..30 steps
*/

/*
	// Cenário 5
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1] 
}}}  for 2 but exactly 1 Partition, 10..10 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      move[n2,n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2] 
}}}  for 2 but exactly 1 Partition, 15..15 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      move[n2,n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 20..20 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      move[n2,n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 25..25 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      change_to_leader[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      move[n2,n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n1] or send_Advertisement[n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentRequest[n2] or send_Advertisement[n2] 
}}}  for 2 but exactly 1 Partition, 30..30 steps
*/


/*
	// Cenário 6

run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1] 
}}}  for 2 but exactly 1 Partition, 10..10 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2] 
}}}  for 2 but exactly 1 Partition, 15..15 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      move[n2,n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2] 
}}}}  for 3 but exactly 1 Partition, 20..20 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      move[n2,n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentResponse[n1] or send_ChildRequest[n1];
        send_ParentResponse[n2] or send_ChildRequest[n2] 
}}}}  for 3 but exactly 1 Partition, 25..25 steps
run {
  some n1:FTD' { addNode[n1,none];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    change_to_leader[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    send_ParentRequest[n1] or send_Advertisement[n1];
    some n2:FTD'-n1 { addNode[n2,n1];
      send_ParentRequest[n2] or send_Advertisement[n2];
      send_ParentResponse[n1] or send_ChildRequest[n1];
      send_ParentRequest[n1] or send_Advertisement[n1];
      move[n2,n1];
      send_ParentResponse[n2] or send_ChildRequest[n2];
      send_ChildResponse[n1];
      join_to_partition[n2] or merge_partitions[n2];
      move[n2,n1];
      send_LinkReq[n2,n1] or send_LinkResp[n2,n1] or send_LinkAcceptReq[n2] or send_LinkAcceptResp[n2];
      send_LinkReq[n1,n2] or send_LinkResp[n1,n2] or send_LinkAcceptReq[n1] or send_LinkAcceptResp[n1];
      change_to_router[n2];
      some n3:FTD'-(n2+n1) { addNode[n3,n1+n2];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentRequest[n2] or send_Advertisement[n2];
        send_ParentRequest[n3] or send_Advertisement[n3];
        send_ParentResponse[n1] or send_ChildRequest[n1];
        send_ParentResponse[n2] or send_ChildRequest[n2];
        send_ParentResponse[n1] or send_ChildRequest[n1];
        send_ParentRequest[n1] or send_Advertisement[n1];
        send_ParentResponse[n3] or send_ChildRequest[n3];
        send_ChildResponse[n1];
        join_to_partition[n3] or merge_partitions[n3] 
}}}}  for 3 but exactly 1 Partition, 30..30 steps

*/

/*************************************
 *                 Fairness                    *
 *************************************/
pred sendAdvEnable[n:FTD]{
	n.role in (Leader +Router)
	some n.in_range
}

pred merge_partitionEnabled[n:Node] {
	some n.partition_id
	some (n.inbox & (Adv->Partition->(Node-n))) 
}

pred changeToLeaderEnabled[n:FTD]{
	no n.partition_id
}

pred joinToPartitionEnabled[n:Node]{
	some (n.inbox & (Cresp->Partition->(Node-n))) 
}


pred send_ParentRequestEnabled[n:Node]{

}



pred send_ParentResponseEnabled[n:FTD]{
	some n.partition_id
	some (n.inbox & (Preq->None->(Node-n))) 

}

pred send_ChildRequestEnabled [n:Node]{
	some (n.inbox & (Presp->None->(Node-n))) 
}


pred send_ChildResponseEnabled[n:FTD]{
	some n.partition_id
	some (n.inbox &  (Creq->None->(Node-n))) 

}

pred change_to_RouterEnabled[n:FTD]{
	some n.partition_id
	some (((Node-n)->LAresp->None->n)  & inbox)

}
pred fairness {
	all  n:FTD| {
		eventually always sendAdvEnable[n] implies always eventually send_Advertisement[n]
		eventually always changeToLeaderEnabled[n] implies always eventually change_to_leader[n]
		eventually always send_ParentResponseEnabled[n] implies always eventually send_ParentResponse[n]
		eventually always send_ChildResponseEnabled[n] implies always eventually send_ChildResponse[n]
		eventually always change_to_RouterEnabled[n] implies always eventually change_to_router[n]
	}
	all n:Node |{
		eventually always merge_partitionEnabled[n] implies always eventually merge_partitions[n]
		eventually always joinToPartitionEnabled[n] implies always eventually join_to_partition[n]
		always eventually send_ParentRequest[n]
		eventually always send_ChildRequestEnabled[n] implies always eventually send_ChildRequest[n]
	}
}	


/*************************************
 *      Proprieties to be checked       *
 *************************************/
/*check lonePartition {
	always all n:Node | lone n.partition_id
}for   3 but  exactly  3 Partition,0 int, 15 steps

check  greedyLeader{
	always all p:Partition | lone p.leader  -- once  one n.partition_id => always some   n.partition_id

}for   3 but  exactly  3 Partition, 0 int, 9 steps


-- Liveness
check convergeToOnePartition{
 	fairness  and some FTD and  (all n:Node | (Node-n) in n.^in_range  and eventually always not reset[n]) =>  eventually  always (some p:Partition | Node in p.elems)  
}for   2 but  exactly  2 Partition,  0 int, 9 steps
*/

/*
check  FTDisAlwaysREEDafteraAddOperation{
	(all n:FTD | some n2:Node-n  {
 	 	always eventually addNode[n,n2] implies always  n.role' in REED
	})
}for  1..9 steps */



/*************************************
 *           Theme Functions              *
 *************************************/

fun reed : set Node  { 
	role.REED 
}
fun router : set Node  { 
	role.Router
}
fun th_leader:set Node{
	role.Leader
}

fun msg_in_inbox: set ( Type -> (Partition +None) -> Node ) {
	Node.inbox
}
/*
fun requests_in_inbox: set (Node -> Type -> (Partition +None))  {
	Node.inbox :> (Preq + Creq+ Lreq + LAreq) 
}

fun responses_in_inbox: set (Node -> Type -> (Partition +None))  {
	Node.inbox :> (Presp + Cresp + LAresp)
} 
*/



/*
fun fed : set Node  { 
	role.FED 
}

fun med : set Node  { 
	role.MED 
}
fun sed : set Node  { 
	role.SED 
}

fun router : set Node  { 
	role.Router
}

fun border_router : set Node  { 
	role.BorderRouter
}
fun th_leader:set Node{
	role.Leader
}

--network_of_partition
fun net : set Partition -> one ThreadNetwork{
	~partitions
}
*/



