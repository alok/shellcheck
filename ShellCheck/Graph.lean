/-
  Copyright 2024
  Lean 4 port of fgl (Functional Graph Library) for ShellCheck

  This module provides a simple graph implementation with:
  - Labeled nodes and edges
  - Graph construction from node/edge lists
  - DFS and topological sort
  - Dominator computation
  - Post-dominator computation
-/

import Std.Data.HashMap

namespace ShellCheck.Graph

/-- A node identifier -/
abbrev Node := Nat

/-- A labeled node -/
structure LNode (α : Type) where
  node : Node
  label : α
  deriving Repr, BEq, Inhabited

/-- A labeled edge -/
structure LEdge (β : Type) where
  src : Node   -- source node
  dst : Node   -- destination node
  label : β
  deriving Repr, BEq, Inhabited

/-- A graph with labeled nodes and edges.
    Uses adjacency lists for efficient traversal. -/
structure Gr (α β : Type) where
  nodes : Array (LNode α)
  edges : Array (LEdge β)
  -- Maps from node id to index in nodes array
  nodeIndex : Std.HashMap Node Nat
  -- Adjacency map: node -> list of (neighbor, edge_index)
  successors : Std.HashMap Node (Array (Node × Nat))
  predecessors : Std.HashMap Node (Array (Node × Nat))
  deriving Inhabited

/-- Create an empty graph -/
def empty : Gr α β := {
  nodes := #[]
  edges := #[]
  nodeIndex := {}
  successors := {}
  predecessors := {}
}

/-- Helper to zip with index, returns (element, index) pairs -/
def zipWithIndex {α : Type} (l : List α) : List (α × Nat) :=
  l.zip (List.range l.length)

/-- Build a graph from lists of labeled nodes and labeled edges -/
def mkGraph (nodeLst : List (LNode α)) (edgeLst : List (LEdge β)) : Gr α β :=
  let nodeArr := nodeLst.toArray
  let edgeArr := edgeLst.toArray

  -- Build node index
  let nodeIdx := (zipWithIndex nodeLst).foldl (fun m (n, i) => m.insert n.node i) ({} : Std.HashMap Node Nat)

  -- Build adjacency maps
  let succ := (zipWithIndex edgeLst).foldl (fun m (e, i) =>
    let existing := m.getD e.src #[]
    m.insert e.src (existing.push (e.dst, i))
  ) ({} : Std.HashMap Node (Array (Node × Nat)))

  let pred := (zipWithIndex edgeLst).foldl (fun m (e, i) =>
    let existing := m.getD e.dst #[]
    m.insert e.dst (existing.push (e.src, i))
  ) ({} : Std.HashMap Node (Array (Node × Nat)))

  { nodes := nodeArr
    edges := edgeArr
    nodeIndex := nodeIdx
    successors := succ
    predecessors := pred }

/-- Get all labeled nodes -/
def labNodes (g : Gr α β) : List (Node × α) :=
  g.nodes.toList.map fun n => (n.node, n.label)

/-- Get all labeled edges -/
def labEdges (g : Gr α β) : List (Node × Node × β) :=
  g.edges.toList.map fun e => (e.src, e.dst, e.label)

/-- Get successors of a node -/
def suc (g : Gr α β) (n : Node) : List Node :=
  match g.successors.get? n with
  | some arr => arr.toList.map (·.1)
  | none => []

/-- Get predecessors of a node -/
def pre (g : Gr α β) (n : Node) : List Node :=
  match g.predecessors.get? n with
  | some arr => arr.toList.map (·.1)
  | none => []

/-- Get the label of a node -/
def lab (g : Gr α β) (n : Node) : Option α :=
  match g.nodeIndex.get? n with
  | some i => g.nodes[i]?.map (·.label)
  | none => none

/-- Check if a node exists in the graph -/
def hasNode (g : Gr α β) (n : Node) : Bool :=
  g.nodeIndex.contains n

/-- Get all node IDs -/
def nodes (g : Gr α β) : List Node :=
  g.nodes.toList.map (·.node)

/-- Get number of nodes -/
def order (g : Gr α β) : Nat :=
  g.nodes.size

/-- Get number of edges -/
def size (g : Gr α β) : Nat :=
  g.edges.size

/-- Depth-first search from a starting node.
    Returns nodes in DFS order (preorder). -/
partial def dfs (g : Gr α β) (start : Node) : List Node :=
  let rec go (visited : Std.HashMap Node Bool) (stack : List Node) (acc : List Node) :
      List Node :=
    match stack with
    | [] => acc.reverse
    | n :: rest =>
        if visited.contains n then
          go visited rest acc
        else
          let visited' := visited.insert n true
          let succs := suc g n
          go visited' (succs ++ rest) (n :: acc)
  go {} [start] []

/-- DFS from multiple starting nodes -/
partial def dfsFromList (g : Gr α β) (starts : List Node) : List Node :=
  let rec go (visited : Std.HashMap Node Bool) (stack : List Node) (acc : List Node) :
      List Node :=
    match stack with
    | [] => acc.reverse
    | n :: rest =>
        if visited.contains n then
          go visited rest acc
        else
          let visited' := visited.insert n true
          let succs := suc g n
          go visited' (succs ++ rest) (n :: acc)
  go {} starts []

/-- Topological sort using Kahn's algorithm.
    Returns nodes in topological order.
    Only works correctly on DAGs. -/
partial def topsort (g : Gr α β) : List Node :=
  let allNodes := nodes g

  -- Calculate in-degrees
  let inDegree := allNodes.foldl (fun m n =>
    let preds := pre g n
    m.insert n preds.length
  ) ({} : Std.HashMap Node Nat)

  -- Find nodes with no incoming edges
  let noIncoming := allNodes.filter fun n =>
    match inDegree.get? n with
    | some 0 => true
    | _ => false

  -- Process nodes
  let rec process (queue : List Node) (inDeg : Std.HashMap Node Nat) (result : List Node) :
      List Node :=
    match queue with
    | [] => result.reverse
    | n :: rest =>
        let succs := suc g n
        let (newQueue, newInDeg) := succs.foldl (fun (q, deg) s =>
          match deg.get? s with
          | some d =>
              let newD := d - 1
              let deg' := deg.insert s newD
              if newD == 0 then (s :: q, deg') else (q, deg')
          | none => (q, deg)
        ) (rest, inDeg)
        process newQueue newInDeg (n :: result)

  process noIncoming inDegree []

/-- Reverse graph (flip all edges) -/
def grev (g : Gr α β) : Gr α β :=
  let reversedEdges := g.edges.toList.map fun e =>
    { src := e.dst, dst := e.src, label := e.label : LEdge β }
  mkGraph g.nodes.toList reversedEdges

/-- Compute dominators from a start node.
    Returns a list of (node, dominator_list) pairs.
    A node d dominates node n if every path from start to n goes through d. -/
partial def dom (g : Gr α β) (start : Node) : List (Node × List Node) :=
  let reachable := dfs g start

  -- Initialize: start dominated only by itself, others by all reachable nodes
  let initDom := reachable.foldl (fun m n =>
    if n == start then m.insert n [start]
    else m.insert n reachable
  ) ({} : Std.HashMap Node (List Node))

  -- Iterate until fixed point
  let rec iterate (domMap : Std.HashMap Node (List Node)) (fuel : Nat) :
      Std.HashMap Node (List Node) :=
    match fuel with
    | 0 => domMap
    | fuel' + 1 =>
        let (changed, newDom) := reachable.foldl (fun (ch, m) n =>
          if n == start then (ch, m)
          else
            let preds := pre g n |>.filter (domMap.contains ·)
            if preds.isEmpty then (ch, m)
            else
              -- Intersection of all predecessors' dominators, plus self
              let predDoms := preds.map fun p => domMap.getD p []
              let intersection := match predDoms with
                | [] => []
                | h :: t => t.foldl (fun acc d => acc.filter (d.contains ·)) h
              let newDoms := (n :: intersection).eraseDups
              let oldDoms := domMap.getD n []
              if newDoms.length != oldDoms.length then
                (true, m.insert n newDoms)
              else
                (ch, m.insert n oldDoms)
        ) (false, domMap)

        if changed then iterate newDom fuel' else newDom

  let finalDom := iterate initDom (reachable.length * 2)
  reachable.map fun n => (n, finalDom.getD n [])

/-- Compute post-dominators from an exit node.
    A node d post-dominates n if every path from n to exit goes through d. -/
def postDom (g : Gr α β) (exitNode : Node) : List (Node × List Node) :=
  dom (grev g) exitNode

/-- Convert dominator list to an array for efficient lookup -/
def domToArray (domList : List (Node × List Node)) (maxNode : Nat) : Array (List Node) :=
  let arr := (Array.range (maxNode + 1)).map fun _ => ([] : List Node)
  domList.foldl (fun a (n, ds) =>
    if n < a.size then a.set! n ds else a
  ) arr

/-- Check if node a dominates node b -/
def dominates (domArray : Array (List Node)) (a b : Node) : Bool :=
  match domArray[b]? with
  | some doms => doms.contains a
  | none => false

-- Theorems (stubs)

theorem empty_has_no_nodes : (empty : Gr α β).nodes.size = 0 := rfl

theorem empty_has_no_edges : (empty : Gr α β).edges.size = 0 := rfl

theorem mkGraph_preserves_nodes (ns : List (LNode α)) (es : List (LEdge β)) :
    (mkGraph ns es).nodes.size = ns.length := sorry

theorem mkGraph_preserves_edges (ns : List (LNode α)) (es : List (LEdge β)) :
    (mkGraph ns es).edges.size = es.length := sorry

theorem labNodes_length_eq_order (g : Gr α β) :
    (labNodes g).length = order g := sorry

theorem labEdges_length_eq_size (g : Gr α β) :
    (labEdges g).length = size g := sorry

theorem suc_empty_for_isolated (g : Gr α β) (n : Node) :
    (¬ g.successors.contains n) → suc g n = [] := sorry

theorem pre_empty_for_source (g : Gr α β) (n : Node) :
    (¬ g.predecessors.contains n) → pre g n = [] := sorry

theorem dfs_includes_start (g : Gr α β) (start : Node) :
    hasNode g start → start ∈ dfs g start := sorry

theorem dfs_subset_of_nodes (g : Gr α β) (start : Node) :
    ∀ n ∈ dfs g start, n ∈ nodes g := sorry

theorem topsort_permutation (g : Gr α β) :
    (topsort g).length ≤ (nodes g).length := sorry

theorem grev_involutive (g : Gr α β) :
    grev (grev g) = g := sorry

theorem grev_preserves_nodes (g : Gr α β) :
    nodes (grev g) = nodes g := sorry

theorem dom_reflexive (g : Gr α β) (start n : Node) :
    n ∈ dfs g start →
    n ∈ ((dom g start).lookup n).getD [] := sorry

theorem dom_start_dominates_all (g : Gr α β) (start : Node) :
    ∀ (n : Node), n ∈ dfs g start →
      start ∈ ((dom g start).lookup n).getD [] := sorry

theorem postDom_exit_postdominates_all (g : Gr α β) (exit : Node) :
    ∀ (n : Node), n ∈ dfs (grev g) exit →
      exit ∈ ((postDom g exit).lookup n).getD [] := sorry

/-- Domination is transitive -/
theorem dom_transitive (g : Gr α β) (start a b c : Node) :
    a ∈ ((dom g start).lookup b).getD [] →
    b ∈ ((dom g start).lookup c).getD [] →
    a ∈ ((dom g start).lookup c).getD [] := sorry

/-- Dominators form a tree structure -/
theorem dom_tree_property (g : Gr α β) (start a b : Node) :
    a ∈ ((dom g start).lookup b).getD [] →
    b ∈ ((dom g start).lookup a).getD [] →
    a = b := sorry

end ShellCheck.Graph
