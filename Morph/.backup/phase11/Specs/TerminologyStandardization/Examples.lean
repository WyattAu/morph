import Morph.Specs.TerminologyStandardization.Spec

/-!
# Examples for Terminology Standardization Specification

## Signal vs Stream Examples

/-- FRP Context: Use Signal -/

example signal_usage :
  let timeSignal : Signal Int := { value := fun (t : Real) => Nat.floor t }
  let doubledSignal : Signal Int := { value := fun (t : Real) => (timeSignal.value t) * 2 }
  True

/-- Data Flow Context: Use Stream -/

example stream_usage :
  let eventStream : Stream Int := { events := [(0.0, 1), (1.0, 2), (2.0, 3)] }
  let processedStream : Stream Int :=
    { events := eventStream.events.map fun (pair : Real × Int) => (pair.1, pair.2 + 1) }
  True

/-- Signal to Stream Conversion -/

example signal_to_stream_conversion :
  let timeSignal : Signal Int := { value := fun (t : Real) => Nat.floor t }
  let samplingRate : Real := 0.1
  let eventStream := signalToStream timeSignal samplingRate
  eventStream.events.length > 0

/-- Stream to Signal Conversion -/

example stream_to_signal_conversion :
  let eventStream : Stream Int := { events := [(0.0, 1), (1.0, 2), (2.0, 3)] }
  let timeSignal := streamToSignal eventStream
  timeSignal.value 1.5 = 2

## Reducer Examples

/-- State Reduction: Use Reducer -/

example reducer_usage :
  let sumReducer : Reducer Int Int :=
    { reduce := fun (acc : Int) (x : Int) => acc + x }
  let numbers : List Int := [1, 2, 3, 4, 5]
  let total : Int := numbers.fold 0 sumReducer.reduce
  total = 15

/-- Reducer Identity Law -/

example reducer_identity :
  let sumReducer : Reducer Int Int :=
    { reduce := fun (acc : Int) (x : Int) => acc + x }
  let state : Int := 10
  let result : Int := sumReducer.reduce state (identity Int)
  result = 10

/-- Reducer Associativity Law -/

example reducer_associativity :
  let sumReducer : Reducer Int Int :=
    { reduce := fun (acc : Int) (x : Int) => acc + x }
  let s1 : Int := 1
  let s2 : Int := 2
  let a1 : Int := 3
  let a2 : Int := 4
  let result1 : Int := sumReducer.reduce (sumReducer.reduce s1 a1) a2
  let result2 : Int := sumReducer.reduce (sumReducer.reduce s2 a2) a1
  result1 = result2

## Transducer Examples

/-- Graph Rewriting: Use Transducer -/

example transducer_usage :
  let normalizeTransducer : Transducer String :=
    { transform := fun (s : String) => s.toLower }
  let simplifyTransducer : Transducer String :=
    { transform := fun (s : String) => s.trim }
  let composedTransducer : Transducer String :=
    { transform := fun (s : String) => simplifiedTransducer.transform (normalizeTransducer.transform s) }
  let input : String := "  HELLO WORLD  "
  let output : String := composedTransducer.transform input
  output = "hello world"

/-- Transducer Composition Law -/

example transducer_composition :
  let t1 : Transducer String := { transform := fun (s : String) => s.toLower }
  let t2 : Transducer String := { transform := fun (s : String) => s.trim }
  let t3 : Transducer String := { transform := fun (s : String) => s.reverse }
  let input : String := "  HELLO  "
  let result1 : String := t3.transform (t2.transform (t1.transform input))
  let result2 : String := ((t3 ∘ (t2 ∘ t1)).transform input
  result1 = result2

## Pure Function Examples

/-- Pure Function: Canonical Definition -/

example pure_function_usage :
  let add : PureFunction Int Int :=
    { apply := fun (x : Int) (y : Int) => x + y }
  let result : Int := add.apply 2 3
  result = 5

/-- Pure Function Properties -/

example pure_function_properties :
  let add : PureFunction Int Int :=
    { apply := fun (x : Int) (y : Int) => x + y }
  -- 1. Referential Transparency: add(2, 3) always returns 5
  let result1 : Int := add.apply 2 3
  let result2 : Int := add.apply 2 3
  result1 = result2
  -- 2. No Side Effects: Does not modify external state
  -- 3. No Mutation: Does not mutate arguments
  -- 4. Deterministic: Always returns same output for same input
  True

## Naming Convention Examples

/-- Correct Type Naming: PascalCase -/

example correct_type_naming :
  let typeNames : List String := ["Signal", "Reducer", "Transducer", "Effect", "ASTNode", "Option"]
  typeNames.all isPascalCase

/-- Incorrect Type Naming: snake_case -/

example incorrect_type_naming :
  let typeNames : List String := ["signal", "reducer", "transducer", "effect", "ast_node", "option"]
  ¬typeNames.all isPascalCase

/-- Correct Function Naming: camelCase -/

example correct_function_naming :
  let functionNames : List String := ["mapSignal", "reduceList", "transformGraph", "computeHash"]
  functionNames.all isCamelCase

/-- Incorrect Function Naming: PascalCase -/

example incorrect_function_naming :
  let functionNames : List String := ["MapSignal", "ReduceList", "TransformGraph", "ComputeHash"]
  ¬functionNames.all isCamelCase

/-- Correct Variable Naming: camelCase -/

example correct_variable_naming :
  let variableNames : List String := ["timeSignal", "accumulator", "graphNode", "result"]
  variableNames.all isCamelCase

/-- Incorrect Variable Naming: snake_case -/

example incorrect_variable_naming :
  let variableNames : List String := ["time_signal", "Accumulator", "graph_node", "Result"]
  ¬variableNames.all isCamelCase

/-- Correct File Naming: snake_case -/

example correct_file_naming :
  let fileNames : List String := ["lexical_structure_syntax_spec.md", "ast_graph_spec.md", "type_system_spec.md"]
  fileNames.all isSnakeCase

/-- Incorrect File Naming: PascalCase -/

example incorrect_file_naming :
  let fileNames : List String := ["LexicalStructureSyntaxSpec.md", "ASTGraphSpec.md", "TypeSystemSpec.md"]
  ¬fileNames.all isSnakeCase

## Migration Examples

/-- Signal to Stream Migration -/

example signal_to_stream_migration :
  -- Old (deprecated)
  -- let timeStream : Stream Int := source()
  -- New (canonical)
  let timeSignal : Signal Int := { value := fun (t : Real) => Nat.floor t }
  True

/-- Stream to Signal Migration -/

example stream_to_signal_migration :
  -- Old (deprecated)
  -- let eventSignal : Signal Int := events()
  -- New (canonical)
  let eventStream : Stream Int := { events := [(0.0, 1), (1.0, 2), (2.0, 3)] }
  True

/-- Reducer to Transducer Migration -/

example reducer_to_transducer_migration :
  -- Old (deprecated)
  -- let optimizer : Transducer<AST, AST> := sequence(normalize, simplify)
  -- New (canonical)
  let optimizer : Reducer AST AST :=
    { reduce := fun (acc : AST) (ast : AST) => simplify (normalize acc) }
  True

/-- Transducer to Reducer Migration -/

example transducer_to_reducer_migration :
  -- Old (deprecated)
  -- let rewriter : Reducer<Graph, Graph> := compose(normalize, simplify)
  -- New (canonical)
  let rewriter : Transducer Graph :=
    { transform := fun (graph : Graph) => simplify (normalize graph) }
  True

/-- Type Naming Migration -/

example type_naming_migration :
  -- Old (deprecated)
  -- type signal<T> = Time -> T
  -- type reducer<S, A> = (S, A) -> S
  -- New (canonical)
  let SignalType := "Signal"
  let ReducerType := "Reducer"
  isPascalCase SignalType ∧ isPascalCase ReducerType

/-- Function Naming Migration -/

example function_naming_migration :
  -- Old (deprecated)
  -- fn MapSignal<T, U>(signal: Signal<T>, f: T -> U): Signal<U> { ... }
  -- New (canonical)
  let mapSignalName := "mapSignal"
  isCamelCase mapSignalName

/-- File Naming Migration -/

example file_naming_migration :
  -- Old (deprecated)
  -- "language/lexical_structure_syntax_spec.md"
  -- "tooling/agent_planning_mdp_spec.md"
  -- "type/type_system_spec.md"
  -- New (canonical)
  let fileNames : List String := [
    "language/lexical_structure_syntax_spec.md",
    "tooling/agent_planning_mdp_spec.md",
    "type/type_system_spec.md"
  ]
  fileNames.all isSnakeCase

## Consistency Examples

/-- Terminology Consistency -/

example terminology_consistency :
  let terms : List Term := ["Signal", "Reducer", "Transducer", "PureFunction"]
  consistencyInvariant terms

/-- Naming Convention Consistency -/

example naming_convention_consistency :
  let typeNames : List String := ["Signal", "Reducer", "Transducer", "Effect", "ASTNode"]
  let functionNames : List String := ["mapSignal", "reduceList", "transformGraph", "computeHash"]
  let variableNames : List String := ["timeSignal", "accumulator", "graphNode", "result"]
  let fileNames : List String := ["lexical_structure_syntax_spec.md", "ast_graph_spec.md", "type_system_spec.md"]
  typeNames.all isPascalCase ∧
    functionNames.all isCamelCase ∧
    variableNames.all isCamelCase ∧
    fileNames.all isSnakeCase

## Backward Compatibility Examples

/-- Backward Compatibility: Additive Approach -/

example backward_compatibility_additive :
  let existingTerms : List Term := ["Signal", "Reducer", "Transducer"]
  let newTerms : List Term := ["PureFunction", "Effect", "ASTNode"]
  let allTerms : List Term := existingTerms ++ newTerms
  consistencyInvariant existingTerms → consistencyInvariant allTerms

/-- Backward Compatibility: Migration -/

example backward_compatibility_migration :
  let oldTerms : List Term := ["signal", "reducer", "transducer"]
  let newTerms : List Term := ["Signal", "Reducer", "Transducer"]
  let migratedTerms : List Term := oldTerms.map fun (t : Term) => canonicalMapping t
  migratedTerms = newTerms

end Morph.Specs.TerminologyStandardization.Examples
