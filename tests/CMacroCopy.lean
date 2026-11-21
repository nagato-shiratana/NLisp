import NLisp.CMacroCopy

open NLisp.CMacroCopy

private def sampleAtom : Atom := ⟨"sample", none, 1⟩
private def sampleHead : Atom := ⟨"apply", none, 4⟩
private def sampleName : Atom := ⟨"binding", none, 7⟩
private def sampleType : Atom := ⟨"type", none, 10⟩

example : MacroCounterSafeInitializer []
    (.list [.list [.list [.atom sampleAtom]]]) :=
  .singletonWrapped (.list [.list [.atom sampleAtom]])
    (.singletonWrapped (.list [.atom sampleAtom]) (.singletonList sampleAtom))

example : CounterPreservingInitializer []
    (.list [.list [.list [.atom sampleAtom]]]) :=
  macroCounterSafeInitializer_preserving [] _
    (.singletonWrapped (.list [.list [.atom sampleAtom]])
      (.singletonWrapped (.list [.atom sampleAtom]) (.singletonList sampleAtom)))

example : MacroCounterSafeInitializer ["expand"]
    (.list [.atom sampleHead, .list [.atom sampleAtom]]) :=
  .pairChild sampleHead (.list [.atom sampleAtom]) (.singletonList sampleAtom)

example : CounterPreservingInitializer ["expand"]
    (.list [.atom sampleHead, .list [.atom sampleAtom]]) :=
  macroCounterSafeInitializer_preserving ["expand"] _
    (.pairChild sampleHead (.list [.atom sampleAtom]) (.singletonList sampleAtom))

example : MacroCounterSafeInitializer ["expand"]
    (.list [.atom sampleHead, .atom sampleAtom, .list [.atom sampleAtom]]) :=
  .tripleChildren sampleHead sampleAtom (.list [.atom sampleAtom]) (by decide)
    (.singletonList sampleAtom)

example : CounterPreservingInitializer ["expand"]
    (.list [.atom sampleHead, .atom sampleAtom, .list [.atom sampleAtom]]) :=
  macroCounterSafeInitializer_preserving ["expand"] _
    (.tripleChildren sampleHead sampleAtom (.list [.atom sampleAtom]) (by decide)
      (.singletonList sampleAtom))

example : MacroCounterSafeBindingInputs ["expand"]
    [.list [.list [.atom sampleName, .atom sampleType],
      .list [.atom sampleHead, .list [.atom sampleAtom]]]] :=
  .cons (.atom sampleName) (.atom sampleType)
    (.list [.atom sampleHead, .list [.atom sampleAtom]])
    (.pairChild sampleHead (.list [.atom sampleAtom]) (.singletonList sampleAtom)) [] .nil

example : CounterPreservingBindings ["expand"]
    [.list [.list [.atom sampleName, .atom sampleType],
      .list [.atom sampleHead, .list [.atom sampleAtom]]]] :=
  macroCounterSafeBindingInputs_preserving ["expand"] _
    (.cons (.atom sampleName) (.atom sampleType)
      (.list [.atom sampleHead, .list [.atom sampleAtom]])
      (.pairChild sampleHead (.list [.atom sampleAtom]) (.singletonList sampleAtom)) [] .nil)

example : CounterPreservingBindings ["expand"]
    [.list [.list [.atom sampleName, .atom sampleType],
      .list [.atom sampleHead, .atom sampleAtom, .list [.atom sampleAtom]]]] :=
  macroCounterSafeBindingInputs_preserving ["expand"] _
    (.cons (.atom sampleName) (.atom sampleType)
      (.list [.atom sampleHead, .atom sampleAtom, .list [.atom sampleAtom]])
      (.tripleChildren sampleHead sampleAtom (.list [.atom sampleAtom]) (by decide)
        (.singletonList sampleAtom)) [] .nil)

#print axioms macroCounterSafeInitializer_preserving
