import NLisp.BuiltinSemantics

namespace NLisp

/-- A successful String append call preserves the evaluator boundary and the
length-bearing C Text model in one result: the runtime value is the full
concatenation and its byte buffer decodes back to that same string. -/
theorem evaluateStringBuiltin_append_CText
    (program : List GlobalIR.Definition) (store : GlobalIR.Store) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (leftText rightText : String)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left =
      .ok (.string leftText))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right =
      .ok (.string rightText)) :
    evaluateStringBuiltin program store .append (fuel + 1) environment left right =
      .ok (.string (leftText ++ rightText)) ∧
    Lexical.CTextModel.stringAppend (Lexical.CTextModel.ofString leftText)
      (Lexical.CTextModel.ofString rightText) =
        Lexical.CTextModel.ofString (leftText ++ rightText) ∧
    Lexical.decodeUtf8
      (Lexical.CTextModel.stringAppend (Lexical.CTextModel.ofString leftText)
        (Lexical.CTextModel.ofString rightText)).bytes = some (leftText ++ rightText) := by
  refine ⟨?_, Lexical.CTextModel.stringAppend_ofString leftText rightText, ?_⟩
  · simp [evaluateStringBuiltin, leftEvaluates, rightEvaluates,
      StringBuiltinOperation.result, bind, Except.bind, pure, Except.pure]
  · exact Lexical.CTextModel.decode_stringAppend_ofString leftText rightText

/-- A successful GlobalIR string append preserves the canonical UTF-8
well-formedness invariant of both C Text operands in its result. -/
theorem evaluateStringBuiltin_append_preserves_CText_wellFormed
    (program : List GlobalIR.Definition) (store : GlobalIR.Store) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (leftText rightText : String)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left =
      .ok (.string leftText))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right =
      .ok (.string rightText)) :
    evaluateStringBuiltin program store .append (fuel + 1) environment left right =
      .ok (.string (leftText ++ rightText)) ∧
    Lexical.CTextModel.WellFormed
      (Lexical.CTextModel.stringAppend (Lexical.CTextModel.ofString leftText)
        (Lexical.CTextModel.ofString rightText)) ∧
    Lexical.decodeUtf8
      (Lexical.CTextModel.stringAppend (Lexical.CTextModel.ofString leftText)
        (Lexical.CTextModel.ofString rightText)).bytes = some (leftText ++ rightText) := by
  obtain ⟨evaluation, _appendIdentity, decoded⟩ := evaluateStringBuiltin_append_CText
    program store fuel environment left right leftText rightText leftEvaluates rightEvaluates
  exact ⟨evaluation,
    Lexical.CTextModel.stringAppend_preserves_wellFormed _ _
      (Lexical.CTextModel.ofString_wellFormed leftText)
      (Lexical.CTextModel.ofString_wellFormed rightText), decoded⟩

/-- The evaluator and C Text model retain bytes following an embedded NUL
when the registered append builtin combines two successful String values. -/
theorem evaluateStringBuiltin_append_embeddedNul :
    let nul := Char.ofNat 0
    let leftText := String.mk ['a', nul]
    let rightText := String.mk ['b']
    evaluateStringBuiltin [] [] .append 2 [] (.string leftText) (.string rightText) =
      .ok (.string (leftText ++ rightText)) ∧
    (Lexical.CTextModel.stringAppend (Lexical.CTextModel.ofString leftText)
      (Lexical.CTextModel.ofString rightText)).bytes = [97, 0, 98] ∧
    Lexical.decodeUtf8
      (Lexical.CTextModel.stringAppend (Lexical.CTextModel.ofString leftText)
        (Lexical.CTextModel.ofString rightText)).bytes = some (leftText ++ rightText) := by
  dsimp
  have combined := evaluateStringBuiltin_append_CText [] [] 1 []
    (.string (String.mk ['a', Char.ofNat 0])) (.string (String.mk ['b']))
    (String.mk ['a', Char.ofNat 0]) (String.mk ['b']) rfl rfl
  exact ⟨combined.1,
    Lexical.CTextModel.embeddedNul_append_is_lengthBearing.1,
    Lexical.CTextModel.embeddedNul_append_is_lengthBearing.2.2⟩

/-- The registered string equality helper agrees with C's explicit byte
length check plus `memcmp` on canonical UTF-8 text buffers. -/
theorem evaluateStringBuiltin_equal_CText
    (program : List GlobalIR.Definition) (store : GlobalIR.Store) (fuel : Nat)
    (environment : List PolyIR.Value) (left right : PolyIR.Term)
    (leftText rightText : String)
    (leftEvaluates : GlobalIR.evaluate program store fuel environment left =
      .ok (.string leftText))
    (rightEvaluates : GlobalIR.evaluate program store fuel environment right =
      .ok (.string rightText)) :
    evaluateStringBuiltin program store .equal (fuel + 1) environment left right =
      .ok (.bool (decide (leftText = rightText))) ∧
    Lexical.CTextModel.stringEqual (Lexical.CTextModel.ofString leftText)
      (Lexical.CTextModel.ofString rightText) = decide (leftText = rightText) := by
  refine ⟨?_, Lexical.CTextModel.stringEqual_ofString_iff leftText rightText⟩
  simp [evaluateStringBuiltin, leftEvaluates, rightEvaluates,
    StringBuiltinOperation.result, bind, Except.bind, pure, Except.pure]

/-- C-style String equality compares the suffix after an embedded NUL too;
the runtime helper therefore distinguishes `a\0b` from the shorter `a`. -/
theorem evaluateStringBuiltin_equal_embeddedNul_not_prefix :
    let full := String.mk ['a', Char.ofNat 0, 'b']
    evaluateStringBuiltin [] [] .equal 2 [] (.string full) (.string "a") =
      .ok (.bool false) := by
  dsimp
  have fullEvaluates : GlobalIR.evaluate [] [] 1 []
      (.string (String.mk ['a', Char.ofNat 0, 'b'])) =
        .ok (.string (String.mk ['a', Char.ofNat 0, 'b'])) := rfl
  have prefixEvaluates : GlobalIR.evaluate [] [] 1 [] (.string "a") =
      .ok (.string "a") := rfl
  have comparison := evaluateStringBuiltin_equal_CText [] [] 1 []
    (.string (String.mk ['a', Char.ofNat 0, 'b'])) (.string "a")
    (String.mk ['a', Char.ofNat 0, 'b']) "a" fullEvaluates prefixEvaluates
  have different := Lexical.CTextModel.stringEqual_embeddedNul_not_prefix
  rw [Lexical.CTextModel.stringEqual_ofString_iff] at different
  rw [different] at comparison
  exact comparison.1

end NLisp
