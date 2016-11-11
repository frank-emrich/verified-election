class NodeData<T> {
  var index: int;
  var content: T;
}



class Node<T> {
  var tail: Node<T>;
  var data: NodeData<T>;
  
  ghost var nodeFP: set<Node<T>>;
  ghost var dataFP: set<NodeData<T>>;
  
  
  
  function LocallyConsistent(base:Node<T>, next: Node<T>): bool 
  reads base, base.nodeFP, base.dataFP
  requires base != null 
  {
    base.data != null && base.tail == next 
      && (next != null ==> next in base.nodeFP 
            && base.nodeFP > next.nodeFP && base.nodeFP == {base} + next.nodeFP 
            && base.dataFP > next.dataFP && base.dataFP == {base.data} + next.dataFP)
      && (next == null ==> base.nodeFP == {base} && base.dataFP == {base.data})
  }


  
  
  function Consistent(): bool 
  reads this, nodeFP, dataFP;
  ensures Consistent() ==> (null !in nodeFP && null !in dataFP 
                        && (forall n | n in nodeFP && n != this :: n.nodeFP < nodeFP )
                        && (forall n | n in nodeFP :: n.data != null &&  n.Consistent()))
  decreases nodeFP 
  {
    LocallyConsistent(this,tail) &&  (tail != null ==> tail.Consistent())
  }

  function Sorted(): bool 
  reads this, nodeFP, dataFP  
  {
    Consistent() 
      && (tail != null ==> tail.data != null 
                             && data.index <= tail.data.index && tail.Sorted())
  }



  


  method restoreSorted() 
  requires Consistent() && (tail != null ==> tail.Sorted())
  ensures Sorted() 
    && nodeFP == old(nodeFP) && dataFP == old(dataFP)  
    && (data == old(data) || (tail != null && data == old(tail.data)))
  modifies nodeFP 
  {
    var cur: Node<T> := this;
    ghost var seen: seq<Node<T>> := [];
    
    while(cur.tail != null && cur.data.index > cur.tail.data.index)
    invariant cur != null && Consistent()  && (cur.tail != null ==> cur.tail.Sorted())
      && (forall n | n in seen :: n in nodeFP && n !in cur.nodeFP)
      && (forall i,j | 0 <= i < |seen| -1 && j == i+1  :: 
            LocallyConsistent(seen[i],seen[j]) && seen[i].data.index <= seen[j].data.index)
      && (seen != [] ==> seen[0] == this && LocallyConsistent(seen[|seen|-1],cur))
      && (cur == this <==> seen == [])
      
      && (|seen| > 0 ==> seen[|seen|-1].data.index < cur.data.index)
      && (|seen| > 0 && cur.tail != null ==> 
            seen[|seen|-1].data.index <= cur.tail.data.index)
      
      && (dataFP == old(dataFP))
      && (forall n | n in nodeFP ::n in old(nodeFP) && n.nodeFP == old(n.nodeFP))
      && (data == old(data) || (tail != null && data == old(tail.data)))
      && (this == cur && tail != null ==> tail == old(tail) && tail.data == old(tail.data))
    decreases cur.nodeFP 
    {
      cur.data, cur.tail.data := cur.tail.data, cur.data;
      cur.tail.dataFP := cur.tail.dataFP - {cur.data} + {cur.tail.data};
      seen := seen + [cur];
      cur := cur.tail;
      ConsistencyPropagation(seen);
        
    }
    IsSortedPropagation(seen);
  }

  
  

  lemma ConsistencyPropagation(nodes: seq<Node<T>>) 
  requires (nodes != [] ==> null !in nodes && nodes[|nodes|-1].Consistent()) 
    && (forall i,j | 0 <= i < |nodes| -1 && j == i+1 :: 
          LocallyConsistent(nodes[i],nodes[j]))        
  ensures nodes != [] ==> nodes[0].Consistent()
  {
    var j: int := |nodes|;
    while(j > 0) 
    invariant 0 <= j <= |nodes| && ( 0 <= j < |nodes| -1  ==>  nodes[j].Consistent())
    {
      j := j -1;
    }
  }
  
  
  
  lemma IsSortedPropagation(nodes: seq<Node<T>>) 
  requires nodes != [] ==> (null !in nodes &&  nodes[|nodes|-1].Sorted())
  requires (forall i,j | 0 <= i < |nodes| -1 && j == i+1 :: nodes[j].data != null
              && LocallyConsistent(nodes[i], nodes[j]) 
              && nodes[i].data.index <= nodes[j].data.index)
  ensures  nodes != [] ==> nodes[0].Sorted()
  {
    var j: int := |nodes|;
    while(j > 0) 
    invariant 0 <= j <= |nodes| && ( 0 <= j < |nodes| -1  ==>  nodes[j].Sorted())
    {
      j := j - 1;
    }
  }

}


class VoteSystem {

  method updateVotes(list: Node<string>, candidate: string, newVoteCount: int) 
                                   returns (updated: NodeData<string>)
  requires list != null && list.Sorted() 
    && (exists d | d in list.dataFP :: 
          d != null &&  d.content == candidate && d.index <= newVoteCount) 
    && (forall d1,d2 | d1 in list.dataFP && d2 in list.dataFP :: 
          d1.content == d2.content ==> d1 == d2) 
  ensures list.nodeFP == old(list.nodeFP) && list.dataFP == old(list.dataFP) 
    && (forall d | d in list.dataFP && d != updated :: 
          d.index == old(d.index) && d.content == old(d.content)) 
    &&  updated != null && updated in list.dataFP 
    &&  updated.index == newVoteCount && updated.content == candidate 
    &&  list.Sorted()
  modifies list.nodeFP, list.dataFP
  {
    var cur: Node<string> := list;
    ghost var seen: seq<Node> := [];
    
    while(cur.data.content != candidate) 
    invariant cur != null && cur.Sorted() && null !in seen 
      && (forall n | n in seen :: n in list.nodeFP && n !in cur.nodeFP)
      && (forall i,j | 0 <= i < |seen| -1 && j == i+1 :: seen[j].data != null
            && list.LocallyConsistent(seen[i], seen[j])
            && seen[i].data.index <= seen[j].data.index)
      && (seen != [] ==> seen[0] == list
             && list.LocallyConsistent(seen[|seen|-1],cur) && seen[|seen|-1].Sorted())
       && (seen == [] <==> cur == list) /* Until here identical to Restore Sortedness*/
   
      && (cur.data.content == candidate 
            || (exists d | d in cur.dataFP ::  d.content == candidate)) 
      
      && (forall n | n in seen :: n.data !in cur.dataFP) 
    decreases cur.dataFP 
    {
      seen := seen + [cur];
      cur := cur.tail;
    }
    updated := cur.data;
    cur.data.index :=  newVoteCount;
    cur.restoreSorted();
    list.IsSortedPropagation(seen);
  }
  
}
