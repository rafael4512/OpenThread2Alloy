/***************************************
 *  Model 3 for OpenThread Protocol *
 ***************************************/


//Roles
abstract sig Role{}
one sig REED,Router,Leader extends Role {}

//Nodes
one sig None{} 

abstract sig Node{
	var role : one Role,
	--                  type of msg -> Content -> from
	var inbox :  Type -> (Partition +None) -> Node,
	var partition_id:set Partition, 
	in_range:set Node 

}
sig FTD extends Node {}

sig MTD extends Node{ 
	//var parent: lone Node,
}

//Network is  represented by a set of Partitions
sig Partition{
	var leader: set Node
}

fun elems:Partition ->Node{
 	~ partition_id
}


abstract sig Type {}
one sig Preq,Presp,Creq,Lreq,LAreq,LAresp, Cresp,Adv extends Type {}


/*************************************
 *          System Specification          *
 *************************************/


fact Init
{
	no inbox
	no partition_id
	no leader
	no (Node.role &Leader)
}

fact Common_configuration
{
	//in_Range é relação reflexiva e não contem a identidade
	~in_range in in_range
	no (in_range & iden)
}

 

fact FTD_configuration 
{
	all n:FTD | n.role = REED
}



fact MTD_configuration {	}


/*************************************
 *                 Transitions                *
 *************************************/

pred Nop{
	role'=role
	inbox'=inbox
	partition_id'=partition_id	
	leader'=leader
}

//1- Request to ask a router to be the father (Multicast) 
pred send_ParentRequest[n :Node] {
	
	inbox'= inbox + (n.in_range-> Preq ->None->n) 
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
}

// 2- Router response for the candidate child. (Unicast)
pred send_ParentResponse [n :FTD] {
	//PC  The Node N has to belong to a partition.
	some n.partition_id
		
	some  msg_from:(None.(Preq.(n.inbox)))  {
		inbox'= inbox + (msg_from ->Presp ->None->n) -  (n -> Preq-> None->msg_from)	
	}
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
}


/*
	3- Send request to a specific father 
	How to choose between two parente responses? (4.7.2 section of spec)
*/

pred send_ChildRequest [n :Node] {
	--PC  There is a Presp in the inbox 
	some  msg_from:(None.(Presp.(n.inbox)))   {
		inbox'= inbox + (msg_from ->Creq ->None->n) -  (n -> Presp -> None->msg_from)	
	}

	role'=role
	partition_id'=partition_id	
	leader'=leader
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

}

----------

pred changed_to_leader[n:FTD]{
	--PC
	--n.role != Leader 
	no n.partition_id
	
	role '= role - (n->n.role) + (n->Leader)--becomes leader

	some p:Partition{
		no p.elems
		partition_id'=partition_id	+(n->p) - (n->n.partition_id)
		leader'=leader + (p->n)
	}	
	inbox'=inbox
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
}




-- A Thread Device will always attach as an End Device
pred join_to_partition[n:Node]{
	 
	some  msg_from:Node , p :Partition | {
 		( Cresp ->p->msg_from ) in n.inbox 
		partition_id'=partition_id	++ (n->p)  -- ++ removes previous partition
		inbox'= inbox -  (n -> Cresp -> p->msg_from)	
	}
 	n in FTD => role'=role - (n->n.role) +(n->REED) 
		     else role'=role 
	leader'=leader - (Partition -> n) -- if the node is leader of any partition it ceases to be

}

/*
	Rules to merge:
		1.Se uma partição apenas tiver 1 elemento, esta cede e junta-se
		2. Weight Value maior  
		3. Partition ID Maior 

*/



--Multicast 
pred send_Advertisement[n:FTD]{
	n.role in (Leader +Router)
	some n.in_range
	
	inbox'= inbox + (n.in_range-> Adv -> n.partition_id->n) 

	role'=role
	partition_id'=partition_id	
	leader'=leader
}

-- Only merge when process an Advertisement! 
pred merge_partitions[n:FTD]{	
	some n.partition_id

	some  msg_from:Node, p:Partition {
		(Adv->p->msg_from) in n.inbox
		p!= n.partition_id => remove_elemPartition[ n.partition_id,n, p]  and role'=role -  (n->n.role ) + (n->REED )
					 else( partition_id'=partition_id and leader'=leader  and role'=role)
		inbox'= inbox  -  (n -> Adv -> p->msg_from)	
	}
}

pred remove_elemPartition[old_parts:one Partition,node:set Node,newPart:one Partition]{
	some (old_parts.leader & node ) => leader'=leader - (old_parts->node) else  leader'=leader
	partition_id'=partition_id -(node->old_parts) + (node->newPart)
}

/*
	- Link Establishment Process Between Routers		

	   Link synchronization is performed in the following circumstances:
		- As part of the attachment process,
		- When a REED becomes an active Router.
		- When a Router receives a message from a neighboring device for which it does not
		   33 have a stored frame counter.
*/


-- Sent in multicast to all routers
pred send_LinkRequest[n:FTD]{
	n.role in REED
	one n.partition_id

	inbox'= inbox + ((n.in_range & role.(REED + Router+Leader)) ->Lreq ->None -> n) 
	
	role'=role
	partition_id'=partition_id	
	leader'=leader
}

--2 - Accept a link Request and Router request for the son to become part of your family 
pred send_LinkAcceptReq[n:FTD]{
	one n.partition_id
	
	some  msg_from: (None.(Lreq.(n.inbox)))  {
		inbox'= inbox + (msg_from ->LAreq ->n.partition_id->n) -  (n -> Lreq -> None->msg_from)	
	}

	role'=role
	partition_id'=partition_id	
	leader'=leader
}

--3 - Positive Response  for the father
pred send_LinkAcceptResp[n:FTD]{
	one n.partition_id
	
	some  msg_from: (None.(LAreq.(n.inbox))) {
		inbox'= inbox + (msg_from -> LAresp->n.partition_id->n) -  (n -> LAreq -> None-> msg_from)	
	}
	role'=role - (n->n.role) + (n->Router)
	partition_id'=partition_id	
	leader'=leader
}





/*************************************
 *                 Simulation                 *
 *************************************/



fact transitions{
	always (Nop or 
			some n:Node |{
				send_ParentRequest[n] or send_ChildRequest[n] or
				join_to_partition[n] or
				reset[n]
				
			} or 
			some  ftd:FTD|{			
				send_ParentResponse[ftd] or  send_ChildResponse[ftd] or 
				changed_to_leader[ftd] or
				send_LinkRequest[ftd] or send_LinkAcceptReq[ftd] or send_LinkAcceptResp[ftd] or 
				send_Advertisement[ftd] or merge_partitions[ftd] 
			} 
		    )
}

/*
run{ 
	some in_range
} for  3 but exactly 1 FTD ,exactly 2 Partition, 8..13 steps

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

pred fairness {
	all  n:FTD| {
		eventually always sendAdvEnable[n] implies always eventually send_Advertisement[n]
		eventually always changeToLeaderEnabled[n] implies always eventually changed_to_leader[n]
		eventually always send_ParentResponseEnabled[n] implies always eventually send_ParentResponse[n]
		eventually always send_ChildResponseEnabled[n] implies always eventually send_ChildResponse[n]
	}
	all n:Node |{
		eventually always merge_partitionEnabled[n] implies always eventually merge_partitions[n]
		eventually always joinToPartitionEnabled[n] implies always eventually join_to_partition[n]
		always eventually send_ParentRequest[n]
		eventually always send_ChildRequestEnabled[n] implies always eventually send_ChildRequest[n]
	}
}	


/*
run { fairness  and
	all n:Node| (Node-n) in n.^in_range
}  for 3 but 2 Node, exactly 2 FTD,  0 int 
*/


/*************************************
 *      Proprieties to be checked       *
 *************************************/
check lonePartition {
	always all n:Node | lone n.partition_id
}for   3 but  exactly  3 Partition,0 int, 15 steps

check  greedyLeader{
	always all p:Partition | lone p.leader  

}for   3 but  exactly  3 Partition, 0 int, 9 steps

-- Liveness
check convergeToOnePartition{
 	fairness  and some FTD and  (all n:Node | (Node-n) in n.^in_range  and eventually always not reset[n]) =>  eventually  always (some p:Partition | Node in p.elems)  
}for   2 but  exactly  2 Partition,  0 int, 9 steps


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
