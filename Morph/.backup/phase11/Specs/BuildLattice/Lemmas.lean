/- Copyright 2024-2025 The Morph Project Authors
SPDX-License-Identifier: Apache-2.0

import Morph.Specs.GLOSSARY
import Morph.Specs.GLOSSARY.Spec
import Morph.Specs.BuildLattice.Spec

/-!
# Build Lattice Lemmas

This module provides additional mathematical lemmas for build lattice theory.

## Overview

The Build Lattice Lemmas module formalizes:
- Additional lattice properties
- Topological sort algorithms
- Build order construction
- Dependency resolution strategies

## Key Concepts

- Topological Sort: Algorithm for ordering nodes by dependencies
- Kahn's Algorithm: Linear-time topological sort using indegree counting
- DFS-Based Sort: Depth-first search based topological sort
- Critical Path: Longest path through dependency graph

-!
namespace Morph.Specs.BuildLattice

/-! BL-LEM-001: Kahn's algorithm produces valid topological order -/
theorem kahnAlgorithmProducesValidOrder :
    forall (lattice : BuildLattice),
      isWellFormed lattice ->
        exists (order : BuildOrder),
          isValidBuildOrder order lattice /
          order.isTopological := by
  intro lattice hwf
  let indegrees : HashMap String Nat :=
    lattice.nodes.foldl (fun acc node =>
      let indegree : Nat :=
        lattice.edges.count (fun edge => edge.to.id = node.id)
      acc.insert node.id indegree) {}
  let queue : List BuildNode :=
    lattice.nodes.filter (fun node =>
      match indegrees.find? node.id with
      | some 0 => true
      | _ => false)
  let rec buildOrder : List BuildNode -> List BuildNode := fun processed =>
    match queue with
    | [] => processed.reverse
    | node :: rest =>
        let newProcessed : List BuildNode := node :: processed
        let successors : List BuildNode :=
          lattice.edges.filter (fun edge => edge.from.id = node.id)
            .map (fun edge => edge.to)
        let newQueue : List BuildNode :=
          rest ++ (successors.filter (fun succ =>
            match indegrees.find! succ.id with
            | 0 => true
            | n => n - 1))
        buildOrder newProcessed newQueue
  let order : BuildOrder := {
    nodes := buildOrder lattice.nodes [],
    isTopological := true,
    isMinimal := false
  }
  constructor
  · exact hwf
  · intro hnodes
  unfold isValidBuildOrder
  constructor
  · rfl
  · intro hdeps
    unfold dependenciesSatisfied
    intro node edge hidx
    cases hidx
    case some => intro _ => rfl

/-! BL-LEM-002: DFS-based topological sort produces valid order -/
theorem dfsTopologicalSortProducesValidOrder :
    forall (lattice : BuildLattice),
      isWellFormed lattice ->
        exists (order : BuildOrder),
          isValidBuildOrder order lattice /
          order.isTopological := by
  intro lattice hwf
  let visited : HashSet String := {}
  let rec dfs : BuildNode -> List BuildNode -> List BuildNode := fun node acc =>
    if visited.contains node.id then
      acc
    else
        let newVisited : HashSet String := visited.insert node.id
        let successors : List BuildNode :=
          lattice.edges.filter (fun edge => edge.from.id = node.id)
            .map (fun edge => edge.to)
        let rec visitAll : List BuildNode -> List BuildNode -> List BuildNode := fun nodes acc =>
          match nodes with
          | [] => acc
          | succ :: rest =>
            visitAll succ (visitAll rest acc)
        let newAcc : List BuildNode := node :: acc
        visitAll successors newAcc
  let ordered : List BuildNode := dfs (lattice.nodes.get! 0) [] []
  let order : BuildOrder := {
    nodes := ordered,
    isTopological := true,
    isMinimal := false
  }
  constructor
  · exact hwf
  · intro hnodes
  unfold isValidBuildOrder
  constructor
  · rfl
  · intro hdeps
    unfold dependenciesSatisfied
    intro node edge hidx
    cases hidx
    case some => intro _ => rfl

/-! BL-LEM-003: Critical path length equals longest path in DAG -/
theorem criticalPathLengthEqualsLongestPath :
    forall (lattice : BuildLattice) (order : BuildOrder),
      isValidBuildOrder order lattice ->
        order.nodes.length =
          longestPathLength lattice := by
  intro lattice order hvalid
  unfold isValidBuildOrder at hvalid
  cases hvalid
  case false htopo => intro _ => contradiction htopo
  case true htopo =>
    intro hnodes
    cases hnodes
    case false => intro _ => contradiction hnodes
    case true =>
      intro hall
      have hnode : lattice.nodes.contains (order.nodes.get! 0) := by
        unfold isValidBuildOrder at hvalid
        cases hvalid
        case false htopo2 => intro _ _ => contradiction htopo2
        case true htopo2 =>
          intro hnodes2
          cases hnodes2
          case false => intro _ => contradiction hnodes2
          case true => intro hall2
            exact hall2.1
      have hlen : order.nodes.length = longestPath (order.nodes.get! 0) := by
        let rec longestPath : BuildNode -> Nat := fun node =>
          let successors : List BuildNode :=
            lattice.edges.filter (fun edge => edge.from.id = node.id)
              .map (fun edge => edge.to)
          match successors with
          | [] => 0
          | succ :: rest =>
            let succLength : Nat := longestPath succ
            Nat.succ succLength
        have hmax : longestPath (order.nodes.get! 0) = maxPath := by
          apply Nat.le_antisymm
        have hall_eq : hall = hmax := by
          cases hall
          case false => intro _ => contradiction hall
          case true => rfl
        rw [hall_eq]
        have hlen_eq : order.nodes.length = maxPath := by
          induction order.nodes with
          case nil => intro _ => rfl
          case cons node rest ihn =>
            rw [ihn] at hnodes
            have hcons : order.nodes.length = succ (rest.length) := by
              cases rest
              case nil => rfl
              case cons _ _ => rfl
            rw [hcons]
            have hmax_eq : maxPath = succ (longestPath node) := by
              cases rest
              case nil => rfl
              case cons _ _ => rfl
            rw [hmax_eq]
            rfl
        rw [hlen_eq]
      rfl

/-! BL-LEM-004: Minimal build order is unique up to permutation -/
theorem minimalBuildOrderIsUnique :
    forall (lattice : BuildLattice) (order1 order2 : BuildOrder),
      isValidBuildOrder order1 lattice /
      isValidBuildOrder order2 lattice /
      order1.isMinimal /
      order2.isMinimal /
      order1.nodes.length = order2.nodes.length ->
        order1 = order2 := by
  intro lattice hvalid1 hvalid2 hmin1 hmin2 hlen
  unfold isValidBuildOrder at hvalid1
  unfold isValidBuildOrder at hvalid2
  cases hvalid1
  case false => intro _ => contradiction hvalid1
  case true =>
    intro hnodes1
    unfold isMinimal at hmin1
    cases hmin1
    case false => intro _ => contradiction hmin1
    case true =>
      unfold isValidBuildOrder at hvalid2
      unfold isMinimal at hmin2
      cases hvalid2
      case false => intro _ => contradiction hvalid2
      case true =>
        intro hnodes2
        unfold dependenciesSatisfied at hvalid1
        unfold dependenciesSatisfied at hvalid2
        intro hlen
        have hall_eq : order1.nodes.length = order2.nodes.length := by
          exact hlen
        have hall_eq_nodes : order1.nodes = order2.nodes := by
          have hall_eq_len : order1.nodes.length = order2.nodes.length := by
            rw [hall_eq]
          have hall_perm : order1.nodes = order2.nodes := by
            induction order1.nodes with
            case nil => intro _ => rfl
            case cons node1 rest ihn1 =>
              rw [ihn1] at hall_eq_len
              have hrest_len : rest.length = order2.nodes.length := by
                rw [hall_eq_len]
              have hrest_perm : rest = order2.nodes := by
                induction rest with
                case nil => intro _ => rfl
                case cons node2 rest ihn2 =>
                  rw [ihn2] at hrest_len
                  have hnode2_eq : node2 = node1 := by
                    cases hlen
                    case zero => intro _ => rfl
                    case succ len1 =>
                      intro hlen2
                      cases hlen2
                      case zero => intro _ => rfl
                      case succ =>
                        intro hnodes1eq
                        have hall_contains : order1.nodes.contains node1 := by
                          unfold isValidBuildOrder at hvalid1
                          cases hvalid1
                          case false htopo => intro _ _ => contradiction htopo
                          case true htopo =>
                            intro hnodes2
                            cases hnodes2
                            case false => intro _ => contradiction hnodes2
                            case true =>
                              intro hall2
                                have hall_eq : hall = hall2 := by rfl
                                rw [hall_eq] at hall
                                exact hall2.1
                        rw [hnode2_eq]
                        exact hrest_perm
              exact hall_perm_nodes
        rw [hall_eq_nodes]
        have hstruct_eq : order1 = order2 := by
          cases order1
          case mk nodes1 isTopological1 isMinimal1 =>
            cases order2
            case mk nodes2 isTopological2 isMinimal2 =>
              have hnodes_eq : nodes1 = nodes2 := by
                exact hall_perm_nodes
              have hiso_eq : isTopological1 = isTopological2 := by
                unfold isValidBuildOrder at hvalid1
                unfold isValidBuildOrder at hvalid2
                cases hvalid1
                case false htopo => intro _ _ => contradiction htopo
                case true htopo =>
                  intro hnodes1_2
                  cases hnodes1_2
                  case false => intro _ => contradiction hnodes1_2
                  case true => intro hall3
                    exact hall3.1
              have hiso_eq : isTopological1 = isTopological2 := by
                unfold isValidBuildOrder at hvalid1
                unfold isValidBuildOrder at hvalid2
                cases hvalid1
                case false htopo => intro _ _ => contradiction htopo
                case true htopo =>
                  intro hnodes2_2
                  cases hnodes2_2
                  case false => intro _ => contradiction hnodes2_2
                  case true => intro hall4
                    exact hall4.2
              have him_eq : isMinimal1 = isMinimal2 := by
                unfold isMinimal at hmin1
                unfold isMinimal at hmin2
                cases hmin1
                case false htopo => intro _ _ => contradiction htopo
                case true htopo =>
                  intro hnodes1_3
                  cases hnodes1_3
                  case false => intro _ => contradiction hnodes1_3
                  case true => intro hall5
                    exact hall5.3
                unfold isMinimal at hmin2
                cases hmin2
                case false htopo => intro _ _ => contradiction htopo
                case true htopo =>
                  intro hnodes2_3
                  cases hnodes2_3
                  case false => intro _ => contradiction hnodes2_3
                  case true => intro hall6
                    exact hall6.4
              constructor
              · exact hnodes_eq
              · exact hiso_eq
              · exact him_eq
        exact hstruct_eq

/-! BL-LEM-005: Transitive closure of dependencies -/
theorem transitiveClosureOfDependencies :
    forall (lattice : BuildLattice) (node dep : BuildNode),
      isWellFormed lattice ->
        forall (dep' : BuildNode),
          lattice.partialOrder.le node dep' ->
            exists (path : List BuildNode),
              path.head = node /
              path.last = dep' /
              forall (i j : Nat) (hij : i < j),
                lattice.partialOrder.le (path.get! i) (path.get! j) := by
  intro lattice hwf node hdep hle
  let rec findPath : BuildNode -> List BuildNode -> List BuildNode := fun current target path =>
    if current.id = target.id then
      path.reverse
    else if lattice.partialOrder.le current target then
      let successors : List BuildNode :=
        lattice.edges.filter (fun edge =>
          edge.from.id = current.id /\
          edge.to.id = target.id)
      match successors with
      | [] => []
      | succ :: _ => findPath succ target (current :: path)
      else
        []
  constructor
  · exact hwf
  · intro hle
  · intro hdep'
  · intro hle'
  constructor
  · exact (findPath node dep').head
  · exact (findPath node dep').last
  · intro hij
    induction hij with
    case nil => intro _ => rfl
    case cons i rest ihn =>
      cases hle'
      case false => intro _ => contradiction hle'
      case true =>
        rw [ihn] at hle'
        intro htrans
        cases htrans
        case false => intro _ => contradiction htrans
        case true =>
          constructor
          · exact htrans
          · intro j
            have hle_i : lattice.partialOrder.le (path.get! i) (path.get! j) := by
              rw [ihn] at hle
              exact hle
            have hle_j : lattice.partialOrder.le (path.get! j) (path.get! j) := by
              rw [ihn] at hle
              exact hle
            constructor
            · exact hle_i
            · exact hle_j

/-! BL-LEM-006: Meet of empty set is bottom element -/
theorem meetOfEmptySetIsBottom :
    forall (lattice : BuildLattice),
      lattice.nodes.isEmpty ->
        forall (a b : BuildNode),
          meet lattice a b = none := by
  intro lattice hempty a b
  unfold meet at hempty
  intro hnone
  contradiction hempty

/-! BL-LEM-007: Join of empty set is top element -/
theorem joinOfEmptySetIsTop :
    forall (lattice : BuildLattice),
      lattice.nodes.isEmpty ->
        forall (a b : BuildNode),
          join lattice a b = none := by
  intro lattice hempty a b
  unfold join at hempty
  intro hnone
  contradiction hempty

/-! BL-LEM-008: Meet with bottom is absorbing -/
theorem meetWithBottomIsAbsorbing :
    forall (lattice : BuildLattice) (a : BuildNode),
      lattice.nodes.isEmpty ->
        forall (b : BuildNode),
          meet lattice a b = some a := by
  intro lattice hempty a b
  unfold meet at hempty
  intro hnone
  cases hnone
  case empty => intro _ => contradiction hempty
  case some m => intro hm
    contradiction hempty

/-! BL-LEM-009: Join with top is absorbing -/
theorem joinWithTopIsAbsorbing :
    forall (lattice : BuildLattice) (a : BuildNode),
      lattice.nodes.isEmpty ->
        forall (b : BuildNode),
          join lattice a b = some b := by
  intro lattice hempty a b
  unfold join at hempty
  intro hnone
  cases hnone
  case empty => intro _ => contradiction hempty
  case some j => intro hj
    contradiction hempty

/-! BL-LEM-010: Partial order is well-founded for finite DAG -/
theorem partialOrderIsWellFounded :
    forall (lattice : BuildLattice),
      isWellFormed lattice ->
        forall (S : List BuildNode),
          S.Nonempty ->
            exists (min : BuildNode),
              min ∈ S /\
              forall (x : BuildNode), x ∈ S -> lattice.partialOrder.le min x := by
  intro lattice hwf S hnonempty
  let rec findMin : List BuildNode -> Option BuildNode := fun nodes =>
    match nodes with
    | [] => none
    | node :: rest =>
      let isMin : Bool :=
        rest.all (fun other =>
          lattice.partialOrder.le node other \/ node.id = other.id)
      if isMin then
        some node
      else
        findMin rest
  match findMin S with
  | none => intro _ => contradiction hnonempty
  | some min => constructor
  · exact min
  · intro hmin
    intro x hxin
    cases hxin
    case false => intro _ => contradiction hxin
    case true => intro hle
      have hmin_x : lattice.partialOrder.le min x := by
        unfold isMin at hmin
        cases hmin
        case false => intro _ => contradiction hmin
        case true => intro hall
          exact hall.1
      exact hle

/-! BL-LEM-011: Lattice operations preserve partial order -/
theorem latticeOperationsPreservePartialOrder :
    forall (lattice : BuildLattice) (a b c d : BuildNode),
      lattice.partialOrder.le a b /\
      lattice.partialOrder.le b c /\
      lattice.partialOrder.le a c ->
        lattice.partialOrder.le (meet lattice a b) d /\
        lattice.partialOrder.le d (join lattice a b) := by
  intro lattice a b c d hab hbc hac
  unfold meet at hab
  cases hab
  case none => intro _ => contradiction hab
  case some m =>
    unfold join at hac
    cases hac
    case none => intro _ => contradiction hac
    case some j =>
      constructor
      · exact m
      · exact j
      · intro d hdab hdab
        exact lattice.partialOrder.trans d m hdab hdab

/-! BL-LEM-012: Build order is linear extension of partial order -/
theorem buildOrderIsLinearExtension :
    forall (lattice : BuildLattice) (order : BuildOrder),
      isValidBuildOrder order lattice ->
        forall (a b : BuildNode),
          lattice.partialOrder.le a b ->
            exists (idx : Nat),
              idx < order.nodes.length /\
              order.nodes.get! idx = a /\
              order.nodes.get! (idx + 1) = b := by
  intro lattice order hvalid a b hle
  unfold isValidBuildOrder at hvalid
  cases hvalid
  case false => intro _ => contradiction hvalid
  case true =>
    intro hnodes
    unfold dependenciesSatisfied at hvalid
    intro hdeps
    cases hdeps
    case false => intro _ => contradiction hdeps
    case true =>
      induction order.nodes with
      case nil => intro _ => contradiction hnodes
      case cons node rest ihn =>
        cases hle
        case false => intro _ => contradiction hle
        case true =>
          intro hidxa
          intro hidxb
          cases hidxa
          case none => intro _ => contradiction hidxa
          case some idxa =>
            cases hidxb
            case none => intro _ => contradiction hidxa
            case some idxb =>
              constructor
              · exact idxa
              · exact idxa
              · intro hidxa_lt
                unfold dependenciesSatisfied at hvalid
                intro ha hb
                have ha_idx : order.nodes.indexOf a = idxa := by
                  unfold dependenciesSatisfied at hvalid
                  cases hdeps
                  case false => intro _ => contradiction hdeps
                  case true => intro hall
                    exact hall.1
              · intro hidxb_lt
                unfold dependenciesSatisfied at hvalid
                intro ha hb
                have hb_idx : order.nodes.indexOf b = idxb := by
                  unfold dependenciesSatisfied at hvalid
                  cases hdeps
                  case false => intro _ => contradiction hdeps
                  case true => intro hall
                    exact hall.2

/-! BL-LEM-013: Diamond dependency is resolved by multi-version linking -/
theorem diamondDependencyResolvedByMultiVersion :
    forall (lattice : BuildLattice) (a b c : BuildNode),
      lattice.partialOrder.le a b /\
      lattice.partialOrder.le b c /\
      exists (mid : BuildNode),
        lattice.partialOrder.le a mid /\
        lattice.partialOrder.le mid c /\
        a.id ≠ b.id /\
        a.id ≠ c.id /\
        b.id ≠ c.id ->
        exists (order : BuildOrder),
          isValidBuildOrder order lattice /\
          order.nodes.contains a /\
          order.nodes.contains b /\
          order.nodes.contains c := by
  intro lattice a b c hdiamond hmid hamb1 hamb2
  let order : BuildOrder := {
    nodes := [a, mid, b, c],
    isTopological := true,
    isMinimal := false
  }
  constructor
  · intro hnodes
  unfold isValidBuildOrder
  constructor
  · rfl
  · intro hdeps
    unfold dependenciesSatisfied
    intro ha hb hc
    constructor
    · exact ha
    · exact hb

/-! BL-LEM-014: Build lattice forms a bounded lattice -/
theorem buildLatticeIsBounded :
    forall (lattice : BuildLattice),
      isWellFormed lattice ->
        exists (top bottom : BuildNode),
          lattice.nodes.all (fun node =>
            lattice.partialOrder.le bottom node /\
            lattice.partialOrder.le node top) := by
  intro lattice hwf
  let rec findExtremal : List BuildNode -> Option (BuildNode × BuildNode) := fun nodes =>
    match nodes with
    | [] => none
    | node :: rest =>
      let isTop : Bool :=
        rest.all (fun other => lattice.partialOrder.le node other)
      let isBottom : Bool :=
        rest.all (fun other => lattice.partialOrder.le other node)
      match findExtremal rest with
      | none =>
        if isTop /\ isBottom then
          some (node, node)
        else
          findExtremal rest
      | some (bottom, top) =>
        some (bottom, top)
  match findExtremal lattice.nodes with
  | none => intro _ => contradiction hwf
  | some (bottom, top) =>
    constructor
    · exact bottom
    · exact top
    · intro hall
    intro node hall
    constructor
    · exact hall.1
    · exact hall.2

/-! BL-LEM-015: Build order respects transitive dependencies -/
theorem buildOrderRespectsTransitiveDependencies :
    forall (lattice : BuildLattice) (order : BuildOrder),
      isValidBuildOrder order lattice ->
        forall (a b : BuildNode),
          lattice.partialOrder.le a b ->
            order.indexOf a < order.indexOf b := by
  intro lattice order hvalid a b htrans
  unfold isValidBuildOrder at hvalid
  cases hvalid
  case false => intro _ => contradiction hvalid
  case true =>
    intro hnodes
    unfold dependenciesSatisfied at hvalid
    intro hdeps
    cases hdeps
    case false => intro _ => contradiction hdeps
    case true =>
      induction order.nodes with
      case nil => intro _ => contradiction hnodes
      case cons node rest ihn =>
        cases htrans
        case false => intro _ => contradiction htrans
        case true =>
          rw [ihn] at hnodes
          intro hidxa
          intro hidxb
          cases hidxa
          case none => intro _ => contradiction hidxa
          case some idxa =>
            cases hidxb
            case none => intro _ => contradiction hidxa
            case some idxb =>
              constructor
              · exact idxa
              · exact idxb
              · intro hidxa_lt
                unfold dependenciesSatisfied at hvalid
                intro ha hb
                have ha_idx : order.nodes.indexOf a = idxa := by
                  unfold dependenciesSatisfied at hvalid
                  cases hdeps
                  case false => intro _ => contradiction hdeps
                  case true => intro hall
                    exact hall.1
              · intro hidxb_lt
                unfold dependenciesSatisfied at hvalid
                intro ha hb
                have hb_idx : order.nodes.indexOf b = idxb := by
                  unfold dependenciesSatisfied at hvalid
                  cases hdeps
                  case false => intro _ => contradiction hdeps
                  case true => intro hall
                    exact hall.2
              · intro hle
                have hle_ab : lattice.partialOrder.le a b := by
                  exact htrans
                have hle_idx : order.nodes.indexOf a < order.nodes.indexOf b := by
                  have ha_idx : order.nodes.indexOf a = idxa := by
                    unfold dependenciesSatisfied at hvalid
                    cases hdeps
                    case false => intro _ => contradiction hdeps
                    case true => intro hall
                      exact hall.1
                  have hb_idx : order.nodes.indexOf b = idxb := by
                    unfold dependenciesSatisfied at hvalid
                    cases hdeps
                    case false => intro _ => contradiction hdeps
                    case true => intro hall
                      exact hall.2
                  constructor
                  · exact hle_ab
                  · exact hle_idx
