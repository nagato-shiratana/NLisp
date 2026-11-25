import NLisp.ExpansionCertificate
import NLisp.Surface
import NLisp.TypeArguments
import NLisp.CNameResolution
import NLisp.CBindingWalk
import NLisp.CheckerCompleteness

namespace NLisp.CertificateSize
open CMacroCopy CExpansion ExpansionCertificate

/- A self-delimiting binary code length for naturals. This models the bits
needed for counters, indices, arities, and list lengths instead of charging
constant space for arbitrary-precision values. -/
def naturalBits (value : Nat) : Nat := 2 * Nat.log2 (value + 1) + 1

def byteStringBits (value : String) : Nat :=
  naturalBits value.toUTF8.data.size + 8 * value.toUTF8.data.size

/- Names stored in association-list environments are charged by their UTF-8
payload and a one-bit entry tag. The values themselves are accounted for by
the enclosing checker state; this measure covers the key scan structure. -/
def nameEnvironmentBits (entries : List (String × α)) : Nat :=
  naturalBits entries.length + entries.foldr
    (fun (name, _value) rest => byteStringBits name + 1 + rest) 1

private theorem nameEnvironmentLength_le_fold (entries : List (String × α)) :
    entries.length ≤ entries.foldr
      (fun (name, _value) rest => byteStringBits name + 1 + rest) 1 := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      rcases head with ⟨name, value⟩
      change tail.length + 1 ≤ byteStringBits name + 1 +
        tail.foldr (fun (entry : String × α) rest => byteStringBits entry.1 + 1 + rest) 1
      have tailBound : tail.length ≤
          tail.foldr (fun (entry : String × α) rest => byteStringBits entry.1 + 1 + rest) 1 := ih
      omega

theorem nameEnvironmentLength_le_bits (entries : List (String × α)) :
    entries.length ≤ nameEnvironmentBits entries := by
  have structural := nameEnvironmentLength_le_fold entries
  unfold nameEnvironmentBits
  exact Nat.le_trans structural (Nat.le_add_left _ _)

theorem lookupScanCost_le_nameEnvironmentBits (name : String)
    (entries : List (String × α)) :
    (CMacroCopy.lookupWithCost name entries).2 ≤ nameEnvironmentBits entries := by
  exact Nat.le_trans (CMacroCopy.lookupWithCost_cost_le_length name entries)
    (nameEnvironmentLength_le_bits entries)

/- Cost model for the C name-resolution environment: count each key
comparison once and charge the UTF-8 name, binding identity, type tag, and
entry/list structure in the encoded input size. -/
def cBindingEnvironmentBits (entries : List NLisp.CNameResolution.Entry) : Nat :=
  naturalBits entries.length + entries.foldr
    (fun entry rest => byteStringBits entry.name + naturalBits entry.identity +
      naturalBits entry.typeTag + 1 + rest) 1

private theorem cBindingEnvironmentLength_le_fold
    (entries : List NLisp.CNameResolution.Entry) :
    entries.length ≤ entries.foldr
      (fun entry rest => byteStringBits entry.name + naturalBits entry.identity +
        naturalBits entry.typeTag + 1 + rest) 1 := by
  induction entries with
  | nil => simp
  | cons entry tail ih =>
      simp only [List.length_cons, List.foldr]
      have entryCost : 1 ≤ byteStringBits entry.name + naturalBits entry.identity +
          naturalBits entry.typeTag + 1 := by
        simp [naturalBits]
      omega

theorem cBindingEnvironmentLength_le_bits
    (entries : List NLisp.CNameResolution.Entry) :
    entries.length ≤ cBindingEnvironmentBits entries := by
  have structural := cBindingEnvironmentLength_le_fold entries
  unfold cBindingEnvironmentBits
  omega

theorem findNameScanCost_le_cBindingEnvironmentBits
    (name : String) (entries : List NLisp.CNameResolution.Entry) :
    (NLisp.CNameResolution.findNameWithCost entries name).2 ≤
      cBindingEnvironmentBits entries := by
  exact Nat.le_trans (NLisp.CNameResolution.findNameWithCost_le_length entries name)
    (cBindingEnvironmentLength_le_bits entries)

private theorem strcmpByteCost_le_encodedBits (query key : String) :
    8 * (query.toUTF8.data.size + key.toUTF8.data.size + 1) ≤
      byteStringBits query + byteStringBits key + 16 := by
  simp [byteStringBits]
  omega

theorem findNameByteCost_bits_le_fold (name : String)
    (entries : List NLisp.CNameResolution.Entry) :
    8 * (NLisp.CNameResolution.findNameWithByteCost entries name).2 ≤
      entries.foldr
        (fun entry rest => byteStringBits name + byteStringBits entry.name + 16 + rest) 0 := by
  induction entries with
  | nil => simp [NLisp.CNameResolution.findNameWithByteCost]
  | cons entry tail ih =>
      by_cases equal : name = entry.name
      · simp [NLisp.CNameResolution.findNameWithByteCost, equal, List.foldr]
        have localBound := strcmpByteCost_le_encodedBits entry.name entry.name
        omega
      · simp only [NLisp.CNameResolution.findNameWithByteCost, if_neg equal,
          List.foldr, Nat.mul_add]
        have localBound := strcmpByteCost_le_encodedBits name entry.name
        omega

private theorem cBindingKeyBits_le_encoding
    (entries : List NLisp.CNameResolution.Entry) :
    entries.foldr (fun entry rest => byteStringBits entry.name + rest) 0 ≤
      entries.foldr
        (fun entry rest => byteStringBits entry.name + naturalBits entry.identity +
          naturalBits entry.typeTag + 1 + rest) 1 := by
  induction entries with
  | nil => simp
  | cons entry tail ih =>
      simp only [List.foldr]
      omega

private theorem lookupByteCostFold_decomposes (name : String)
    (entries : List NLisp.CNameResolution.Entry) :
    entries.foldr
        (fun entry rest => byteStringBits name + byteStringBits entry.name + 16 + rest) 0 =
      entries.length * (byteStringBits name + 16) +
        entries.foldr (fun entry rest => byteStringBits entry.name + rest) 0 := by
  induction entries with
  | nil => simp
  | cons entry tail ih =>
      simp only [List.length_cons, List.foldr, Nat.succ_mul]
      omega

theorem findNameByteCost_le_query_and_environment_bits (name : String)
    (entries : List NLisp.CNameResolution.Entry) :
    8 * (NLisp.CNameResolution.findNameWithByteCost entries name).2 ≤
      entries.length * (byteStringBits name + 16) + cBindingEnvironmentBits entries := by
  calc
    8 * (NLisp.CNameResolution.findNameWithByteCost entries name).2 ≤
        entries.foldr
          (fun entry rest => byteStringBits name + byteStringBits entry.name + 16 + rest) 0 :=
      findNameByteCost_bits_le_fold name entries
    _ = entries.length * (byteStringBits name + 16) +
        entries.foldr (fun entry rest => byteStringBits entry.name + rest) 0 :=
      lookupByteCostFold_decomposes name entries
    _ ≤ entries.length * (byteStringBits name + 16) + cBindingEnvironmentBits entries := by
      unfold cBindingEnvironmentBits
      have keyBits := cBindingKeyBits_le_encoding entries
      omega

def observationLookupBitsBound
    (entries : List NLisp.CNameResolution.Entry)
    (observations : List NLisp.CNameResolution.Observation) : Nat :=
  observations.foldr
    (fun observation rest => entries.length * (byteStringBits observation.name + 16) +
      cBindingEnvironmentBits entries + rest) 0

theorem checkObservationsWithCost_le_observationLookupBitsBound
    (entries : List NLisp.CNameResolution.Entry)
    (observations : List NLisp.CNameResolution.Observation) :
    (NLisp.CNameResolution.checkObservationsWithCost entries observations).2 ≤
      observationLookupBitsBound entries observations := by
  induction observations with
  | nil => simp [NLisp.CNameResolution.checkObservationsWithCost,
      observationLookupBitsBound]
  | cons observation rest ih =>
      change 8 * (NLisp.CNameResolution.findNameWithByteCost entries observation.name).2 +
          (NLisp.CNameResolution.checkObservationsWithCost entries rest).2 ≤
        entries.length * (byteStringBits observation.name + 16) +
          cBindingEnvironmentBits entries + observationLookupBitsBound entries rest
      have lookupBound := findNameByteCost_le_query_and_environment_bits
        observation.name entries
      omega

def siteLookupBitsBound (sites : List NLisp.CBindingWalk.Site) : Nat :=
  sites.foldr
    (fun site rest => site.environment.length * (byteStringBits site.name + 16) +
      cBindingEnvironmentBits site.environment + rest) 0

theorem checkSitesWithLookupCost_le_siteLookupBitsBound
    (sites : List NLisp.CBindingWalk.Site) :
    (NLisp.CBindingWalk.checkSitesWithLookupCost sites).2 ≤ siteLookupBitsBound sites := by
  induction sites with
  | nil => simp [NLisp.CBindingWalk.checkSitesWithLookupCost, siteLookupBitsBound]
  | cons site rest ih =>
      change 8 * (NLisp.CNameResolution.findNameWithByteCost
          site.environment site.name).2 +
          (NLisp.CBindingWalk.checkSitesWithLookupCost rest).2 ≤
        site.environment.length * (byteStringBits site.name + 16) +
          cBindingEnvironmentBits site.environment + siteLookupBitsBound rest
      have lookupBound := findNameByteCost_le_query_and_environment_bits
        site.name site.environment
      omega

def checkWithLookupCostBitsBound (fuel : Nat) (forms : List NLisp.CBindingWalk.Node)
    (builtins : List NLisp.CNameResolution.Entry) : Nat :=
  match NLisp.CBindingWalk.references fuel forms builtins with
  | none => 0
  | some sites => siteLookupBitsBound sites

theorem checkWithLookupCost_le_checkWithLookupCostBitsBound
    (fuel : Nat) (forms : List NLisp.CBindingWalk.Node)
    (builtins : List NLisp.CNameResolution.Entry) :
    (NLisp.CBindingWalk.checkWithLookupCost fuel forms builtins).2 ≤
      checkWithLookupCostBitsBound fuel forms builtins := by
  unfold NLisp.CBindingWalk.checkWithLookupCost checkWithLookupCostBitsBound
  cases NLisp.CBindingWalk.references fuel forms builtins with
  | none => simp
  | some sites => exact checkSitesWithLookupCost_le_siteLookupBitsBound sites

/- The verifier receives the UTF-8 process-certificate artifact as a file.
This is its raw input length in bits; it includes embedded JSON, source,
identifiers, numerals, generated Lean text, and proof terms as serialized. -/
def serializedProcessCertificateBits (artifact : String) : Nat :=
  8 * artifact.toUTF8.data.size

def optionalNaturalBits : Option Nat → Nat
  | none => 1
  | some value => 1 + naturalBits value

def atomBits (atom : Atom) : Nat :=
  1 + byteStringBits atom.name + optionalNaturalBits atom.origin + naturalBits atom.token

/- Lists carry a length prefix; each element and the terminator are charged
separately. The nested recursor follows Tree's actual inductive encoding. -/
noncomputable def treeBits : Tree → Nat :=
  Tree.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (fun atom => 1 + atomBits atom)
    (fun items itemBits => 1 + naturalBits items.length + itemBits)
    1
    (fun _ _ headBits tailBits => 1 + headBits + tailBits)

noncomputable def encodedTreeListContentsBits (trees : List Tree) : Nat :=
  Tree.rec_1
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (fun atom => 1 + atomBits atom)
    (fun items itemBits => 1 + naturalBits items.length + itemBits)
    1
    (fun _ _ headBits tailBits => 1 + headBits + tailBits) trees

theorem treeNodeCount_le_treeBits : ∀ tree, treeNodeCount tree ≤ treeBits tree :=
  Tree.rec
    (motive_1 := fun tree => treeNodeCount tree ≤ treeBits tree)
    (motive_2 := fun trees => treeListNodeCount trees ≤ encodedTreeListContentsBits trees)
    (fun atom => by
      simp only [treeNodeCount, treeBits]
      omega)
    (fun trees ih => by
      simp only [treeNodeCount, treeBits, treeListNodeCount, encodedTreeListContentsBits] at *
      omega)
    (by simp [treeListNodeCount])
    (fun head tail ihHead ihTail => by
      change treeNodeCount head + treeListNodeCount tail ≤
        1 + treeBits head + encodedTreeListContentsBits tail
      have listBound := Nat.add_le_add ihHead ihTail
      omega)

theorem naturalBits_positive (value : Nat) : 0 < naturalBits value := by
  simp [naturalBits]

mutual
  def typeBits : Surface.Ty → Nat
    | .boolean => 1
    | .integer => 1
    | .float => 64
    | .string => 1
    | .character => 1
    | .unit => 1
    | .var index => 1 + naturalBits index
    | .fn parameters result =>
        1 + naturalBits parameters.length + typeListPayloadBits parameters + typeBits result
    | .list element => 1 + typeBits element
    | .option element => 1 + typeBits element

  def typeListPayloadBits : List Surface.Ty → Nat
    | [] => 1
    | type :: rest => 1 + typeBits type + typeListPayloadBits rest
end

noncomputable def treeListBits (trees : List Tree) : Nat :=
  naturalBits trees.length + trees.foldr (fun tree rest => treeBits tree + rest) 1

theorem treeListNodeCount_le_fold (trees : List Tree) :
    treeListNodeCount trees ≤ trees.foldr (fun tree rest => treeBits tree + rest) 1 := by
  induction trees with
  | nil => simp [treeListNodeCount]
  | cons head tail ih =>
      have headBound := treeNodeCount_le_treeBits head
      simp only [treeNodeCount, treeBits, treeListNodeCount, List.foldr] at *
      omega

theorem treeListNodeCount_le_treeListBits (trees : List Tree) :
    treeListNodeCount trees ≤ treeListBits trees := by
  have structural := treeListNodeCount_le_fold trees
  simp only [treeListBits]
  omega

noncomputable def typeListBits (types : List Surface.Ty) : Nat :=
  naturalBits types.length + typeListPayloadBits types

/- The executable type-checker's structural fuel is bounded by the encoded
type representation. This makes the checker traversal component directly
comparable with the input bit-size model. -/
mutual
theorem checkerTypeFuel_le_typeBits (type : Surface.Ty) :
    Surface.checkerTypeFuel type ≤ typeBits type := by
  cases type with
  | boolean => simp [Surface.checkerTypeFuel, typeBits]
  | integer => simp [Surface.checkerTypeFuel, typeBits]
  | float => simp [Surface.checkerTypeFuel, typeBits]
  | string => simp [Surface.checkerTypeFuel, typeBits]
  | character => simp [Surface.checkerTypeFuel, typeBits]
  | unit => simp [Surface.checkerTypeFuel, typeBits]
  | var index => simp [Surface.checkerTypeFuel, typeBits]; omega
  | fn parameters result =>
      have parametersBound := checkerTypesFuel_le_typeListPayload parameters
      have resultBound := checkerTypeFuel_le_typeBits result
      simp only [Surface.checkerTypeFuel, typeBits, typeListPayloadBits]
      omega
  | list element | option element =>
      have elementBound := checkerTypeFuel_le_typeBits element
      simp only [Surface.checkerTypeFuel, typeBits]
      omega
termination_by sizeOf type
decreasing_by all_goals simp_wf; omega

theorem checkerTypesFuel_le_typeListPayload (types : List Surface.Ty) :
    Surface.checkerTypesFuel types ≤ typeListPayloadBits types := by
  cases types with
  | nil => simp [Surface.checkerTypesFuel, typeListPayloadBits]
  | cons head tail =>
      have headBound := checkerTypeFuel_le_typeBits head
      have tailBound := checkerTypesFuel_le_typeListPayload tail
      simp only [Surface.checkerTypesFuel, typeListPayloadBits]
      omega
termination_by sizeOf types
decreasing_by all_goals simp_wf; omega
end

theorem checkerTypesFuel_le_typeListBits (types : List Surface.Ty) :
    Surface.checkerTypesFuel types ≤ typeListBits types := by
  have payloadBound := checkerTypesFuel_le_typeListPayload types
  unfold typeListBits
  omega

theorem typeBits_boolean : typeBits .boolean = 1 := by simp [typeBits]
theorem typeBits_integer : typeBits .integer = 1 := by simp [typeBits]
theorem typeBits_float : typeBits .float = 64 := by simp [typeBits]
theorem typeBits_unit : typeBits .unit = 1 := by simp [typeBits]
theorem typeBits_var (index : Nat) : typeBits (.var index) = 1 + naturalBits index := by
  simp [typeBits]
theorem typeBits_function (parameters : List Surface.Ty) (result : Surface.Ty) :
    typeBits (.fn parameters result) =
      1 + naturalBits parameters.length + typeListPayloadBits parameters + typeBits result := by
  simp [typeBits]
theorem typeBits_list (element : Surface.Ty) : typeBits (.list element) = 1 + typeBits element := by
  simp [typeBits]
theorem typeBits_option (element : Surface.Ty) : typeBits (.option element) = 1 + typeBits element := by
  simp [typeBits]

/- Relate the type-constraint collector's structural recursion budget to the
same encoded type tree used by the certificate-size model. The extra list
term accounts for one traversal node per parameter type. -/
mutual
theorem collectorTypeFuel_le_typeBits (type : Surface.Ty) :
    Surface.collectorTypeFuel type ≤ typeBits type := by
  cases type with
  | boolean => simp [Surface.collectorTypeFuel, typeBits_boolean]
  | integer => simp [Surface.collectorTypeFuel, typeBits_integer]
  | float => simp [Surface.collectorTypeFuel, typeBits_float]
  | string => simp [Surface.collectorTypeFuel, typeBits]
  | character => simp [Surface.collectorTypeFuel, typeBits]
  | unit => simp [Surface.collectorTypeFuel, typeBits_unit]
  | var index => simp [Surface.collectorTypeFuel, typeBits_var]; omega
  | fn parameters result =>
      have parametersBound := collectorTypesFuel_le_typeListPayload parameters
      have resultBound := collectorTypeFuel_le_typeBits result
      rw [typeBits_function]
      simp only [Surface.collectorTypeFuel]
      omega
  | list element =>
      have elementBound := collectorTypeFuel_le_typeBits element
      rw [typeBits_list]
      simp only [Surface.collectorTypeFuel]
      omega
  | option element =>
      have elementBound := collectorTypeFuel_le_typeBits element
      rw [typeBits_option]
      simp only [Surface.collectorTypeFuel]
      omega
termination_by sizeOf type
decreasing_by all_goals simp_wf; omega

theorem collectorTypesFuel_le_typeListPayload (types : List Surface.Ty) :
    Surface.collectorTypesFuel types ≤ typeListPayloadBits types := by
  cases types with
  | nil => simp [Surface.collectorTypesFuel, typeListPayloadBits]
  | cons head tail =>
      have headBound := collectorTypeFuel_le_typeBits head
      have tailBound := collectorTypesFuel_le_typeListPayload tail
      simp only [Surface.collectorTypesFuel, typeListPayloadBits]
      omega
termination_by sizeOf types
decreasing_by all_goals simp_wf; omega
end

theorem collectorTypesFuel_le_typeListBits (types : List Surface.Ty) :
    Surface.collectorTypesFuel types ≤ typeListBits types := by
  have payloadBound := collectorTypesFuel_le_typeListPayload types
  unfold typeListBits
  omega

noncomputable def signatureBits (signature : Surface.Signature) : Nat :=
  1 + naturalBits signature.typeArity + typeListBits signature.parameters +
    typeBits signature.result

theorem checkerSignatureFuel_le_signatureBits (signature : Surface.Signature) :
    Surface.checkerSignatureFuel signature ≤ signatureBits signature := by
  have parametersBound := checkerTypesFuel_le_typeListPayload signature.parameters
  have resultBound := checkerTypeFuel_le_typeBits signature.result
  simp only [Surface.checkerSignatureFuel, signatureBits, typeListBits]
  omega

def integerBits (value : Int) : Nat := 1 + naturalBits value.natAbs

/-- Lean `Float` stores a binary64 payload, so a literal contributes 64 data
bits in this syntax-size model. -/
def floatBits (_value : Float) : Nat := 64

/- Cost model for the type-annotated Surface expression representation. The
integer payload is charged by magnitude, and every de Bruijn/global index by
its encoded natural-number length. -/
noncomputable def expressionBits : Surface.Expr → Nat :=
  Surface.Expr.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (fun index => 1 + naturalBits index)
    (fun index arguments => 1 + naturalBits index + typeListBits arguments)
    (fun _ => 2)
    (fun value => 1 + integerBits value)
    (fun value => 1 + floatBits value)
    (fun value => 1 + value.toUTF8.data.size * 8)
    (fun value => 1 + naturalBits value.toNat)
    1
    (fun parameters result _body bodyBits =>
      1 + typeListBits parameters + typeBits result + bodyBits)
    (fun _function _arguments functionBits argumentsBits => 1 + functionBits + argumentsBits)
    (fun _condition _yes _no conditionBits yesBits noBits =>
      1 + conditionBits + yesBits + noBits)
    (fun _left _right leftBits rightBits => 1 + leftBits + rightBits)
    (fun _left _right leftBits rightBits => 1 + leftBits + rightBits)
    (fun _left _right leftBits rightBits => 1 + leftBits + rightBits)
    (fun _left _right leftBits rightBits => 1 + leftBits + rightBits)
    (fun _left _right leftBits rightBits => 1 + leftBits + rightBits)
    (fun types _initializers _body initializersBits bodyBits =>
      1 + typeListBits types + initializersBits + bodyBits)
    (fun _first _rest firstBits restBits => 1 + firstBits + restBits)
    (fun elementType => 1 + typeBits elementType)
    (fun elementType _head _tail headBits tailBits =>
      1 + typeBits elementType + headBits + tailBits)
    (fun elementType => 1 + typeBits elementType)
    (fun elementType _value valueBits => 1 + typeBits elementType + valueBits)
    (fun _target _empty _full targetBits emptyBits fullBits =>
      1 + targetBits + emptyBits + fullBits)
    (fun _target _empty _full targetBits emptyBits fullBits =>
      1 + targetBits + emptyBits + fullBits)
    (fun _ _ _ leftBits rightBits => 1 + leftBits + rightBits)
    1
    (fun _ _ headBits tailBits => 1 + headBits + tailBits)

theorem expressionBits_add (left right : Surface.Expr) :
    expressionBits (.add left right) = 1 + expressionBits left + expressionBits right := by
  unfold expressionBits
  rfl

theorem expressionBits_sub (left right : Surface.Expr) :
    expressionBits (.sub left right) = 1 + expressionBits left + expressionBits right := by
  unfold expressionBits
  rfl

theorem expressionBits_mul (left right : Surface.Expr) :
    expressionBits (.mul left right) = 1 + expressionBits left + expressionBits right := by
  unfold expressionBits
  rfl

theorem expressionBits_le (left right : Surface.Expr) :
    expressionBits (.le left right) = 1 + expressionBits left + expressionBits right := by
  unfold expressionBits
  rfl

theorem expressionBits_intEq (left right : Surface.Expr) :
    expressionBits (.intEq left right) = 1 + expressionBits left + expressionBits right := by
  unfold expressionBits
  rfl

theorem expressionBits_floatBin (op : Surface.FloatBinOp) (left right : Surface.Expr) :
    expressionBits (.floatBin op left right) =
      1 + expressionBits left + expressionBits right := by
  unfold expressionBits
  rfl

theorem expressionBits_some (type : Surface.Ty) (value : Surface.Expr) :
    expressionBits (.some type value) = 1 + typeBits type + expressionBits value := by
  unfold expressionBits
  rfl

theorem expressionBits_cons (type : Surface.Ty) (head tail : Surface.Expr) :
    expressionBits (.cons type head tail) =
      1 + typeBits type + expressionBits head + expressionBits tail := by
  unfold expressionBits
  rfl

theorem expressionBits_ite (condition yes no : Surface.Expr) :
    expressionBits (.ite condition yes no) =
      1 + expressionBits condition + expressionBits yes + expressionBits no := by
  unfold expressionBits
  rfl

theorem expressionBits_matchList (target empty full : Surface.Expr) :
    expressionBits (.matchList target empty full) =
      1 + expressionBits target + expressionBits empty + expressionBits full := by
  unfold expressionBits
  rfl

theorem expressionBits_matchOption (target empty full : Surface.Expr) :
    expressionBits (.matchOption target empty full) =
      1 + expressionBits target + expressionBits empty + expressionBits full := by
  unfold expressionBits
  rfl

theorem expressionBits_lam (parameters : List Surface.Ty) (result : Surface.Ty)
    (body : Surface.Expr) :
    expressionBits (.lam parameters result body) =
      1 + typeListBits parameters + typeBits result + expressionBits body := by
  unfold expressionBits
  rfl

theorem expressionBits_begin_nil (first : Surface.Expr) :
    expressionBits (.begin first []) = 2 + expressionBits first := by
  simp [expressionBits]
  omega

theorem expressionBits_begin_one (first second : Surface.Expr) :
    expressionBits (.begin first [second]) =
      3 + expressionBits first + expressionBits second := by
  simp [expressionBits]
  omega

theorem expressionBits_begin_two (first second third : Surface.Expr) :
    expressionBits (.begin first [second, third]) =
      4 + expressionBits first + expressionBits second + expressionBits third := by
  simp [expressionBits]
  omega

theorem expressionBits_letMany_nil (types : List Surface.Ty) (body : Surface.Expr) :
    expressionBits (.letMany types [] body) =
      2 + typeListBits types + expressionBits body := by
  simp [expressionBits]
  omega

theorem expressionBits_letMany_one (types : List Surface.Ty) (initializer body : Surface.Expr) :
    expressionBits (.letMany types [initializer] body) =
      3 + typeListBits types + expressionBits initializer + expressionBits body := by
  simp [expressionBits]
  omega

theorem expressionBits_letMany_two (types : List Surface.Ty)
    (first second body : Surface.Expr) :
    expressionBits (.letMany types [first, second] body) =
      4 + typeListBits types + expressionBits first + expressionBits second +
        expressionBits body := by
  simp [expressionBits]
  omega

theorem expressionBits_letMany_three (types : List Surface.Ty)
    (first second third body : Surface.Expr) :
    expressionBits (.letMany types [first, second, third] body) =
      5 + typeListBits types + expressionBits first + expressionBits second +
        expressionBits third + expressionBits body := by
  simp [expressionBits]
  omega

theorem expressionBits_letMany_four (types : List Surface.Ty)
    (first second third fourth body : Surface.Expr) :
    expressionBits (.letMany types [first, second, third, fourth] body) =
      6 + typeListBits types + expressionBits first + expressionBits second +
        expressionBits third + expressionBits fourth + expressionBits body := by
  simp [expressionBits]
  omega

theorem expressionBits_letMany_five (types : List Surface.Ty)
    (first second third fourth fifth body : Surface.Expr) :
    expressionBits (.letMany types [first, second, third, fourth, fifth] body) =
      7 + typeListBits types + expressionBits first + expressionBits second +
        expressionBits third + expressionBits fourth + expressionBits fifth +
        expressionBits body := by
  simp [expressionBits]
  omega

theorem expressionBits_app_nil (function : Surface.Expr) :
    expressionBits (.app function []) = 2 + expressionBits function := by
  simp [expressionBits]
  omega


noncomputable def expressionListPayloadBits (expressions : List Surface.Expr) : Nat :=
  expressions.foldr (fun expression rest => expressionBits expression + rest) 1

noncomputable def expressionListBits (expressions : List Surface.Expr) : Nat :=
  naturalBits expressions.length + expressionListPayloadBits expressions

/-- Each global-reference checker step rescans the complete global signature
table. This scale factor records that repeated cost instead of claiming a
linear expression-only bound. -/
def expressionCheckerScale (globals : List Surface.Signature) : Nat :=
  Surface.checkerSignaturesFuel globals + 2

noncomputable def signatureListBits (signatures : List Surface.Signature) : Nat :=
  naturalBits signatures.length + signatures.foldr
    (fun signature rest => signatureBits signature + rest) 1

theorem checkerSignaturesFuel_le_signatureListBits
    (signatures : List Surface.Signature) :
    Surface.checkerSignaturesFuel signatures ≤ signatureListBits signatures := by
  have folded : Surface.checkerSignaturesFuel signatures ≤
      signatures.foldr (fun signature rest => signatureBits signature + rest) 1 := by
    induction signatures with
    | nil => simp [Surface.checkerSignaturesFuel]
    | cons signature tail ih =>
        have headBound := checkerSignatureFuel_le_signatureBits signature
        have headPositive : 1 ≤ signatureBits signature := by
          unfold signatureBits
          omega
        have tailPositive : 1 ≤ tail.foldr
            (fun item rest => signatureBits item + rest) 1 := by
          induction tail with
          | nil => simp
          | cons head rest ih =>
              have headPositive : 1 ≤ signatureBits head := by
                unfold signatureBits
                omega
              simp only [List.foldr]
              omega
        simp only [Surface.checkerSignaturesFuel, List.foldr]
        omega
  unfold signatureListBits
  omega

theorem expressionBits_positive (expression : Surface.Expr) :
    0 < expressionBits expression := by
  cases expression <;> simp [expressionBits] <;> omega

inductive CheckerSimpleLeaf : Surface.Expr → Prop where
  | var (index : Nat) : CheckerSimpleLeaf (.var index)
  | bool (value : Bool) : CheckerSimpleLeaf (.bool value)
  | int (value : Int) : CheckerSimpleLeaf (.int value)
  | float (value : Float) : CheckerSimpleLeaf (.float value)
  | string (value : String) : CheckerSimpleLeaf (.string value)
  | character (value : Char) : CheckerSimpleLeaf (.character value)
  | unit : CheckerSimpleLeaf .unit

/-- The atomic expressions consume one checker step. The extra scale unit
charges the list walker even for empty string and unit payloads. -/
theorem checkerSimpleLeafExprFuel_le_scaled_expressionBits
    (globals : List Surface.Signature) (expression : Surface.Expr)
    (leaf : CheckerSimpleLeaf expression) :
    Surface.checkerExprFuel globals expression + 1 ≤
      expressionBits expression * expressionCheckerScale globals := by
  have bitsPositive := expressionBits_positive expression
  have scaleLower : 2 ≤ expressionCheckerScale globals := by
    simp [expressionCheckerScale]
  have productLower := Nat.mul_le_mul_left (expressionBits expression) scaleLower
  have twoBits : 2 ≤ expressionBits expression * 2 := by
    have := Nat.mul_le_mul_left 2 bitsPositive
    simp only [Nat.one_mul] at this
    omega
  cases leaf <;> simp [Surface.checkerExprFuel] <;>
    first | exact Nat.le_trans twoBits (by simpa [Nat.mul_comm] using productLower) | omega

theorem checkerNilExprFuel_le_scaled_expressionBits
    (globals : List Surface.Signature) (type : Surface.Ty) :
    Surface.checkerExprFuel globals (.nil type) + 1 ≤
      expressionBits (.nil type) * expressionCheckerScale globals := by
  have typeBound := checkerTypeFuel_le_typeBits type
  have scaleLower : 2 ≤ expressionCheckerScale globals := by
    simp [expressionCheckerScale]
  have bitsLower : 2 * (1 + typeBits type) ≤
      (1 + typeBits type) * expressionCheckerScale globals := by
    calc
      2 * (1 + typeBits type) = (1 + typeBits type) * 2 := Nat.mul_comm _ _
      _ ≤ (1 + typeBits type) * expressionCheckerScale globals :=
        Nat.mul_le_mul_left _ scaleLower
  have structural : Surface.checkerTypeFuel type + 2 ≤ 2 * (1 + typeBits type) := by
    omega
  have result := Nat.le_trans structural bitsLower
  simpa [Surface.checkerExprFuel, expressionBits, Nat.mul_comm] using result

theorem checkerNoneExprFuel_le_scaled_expressionBits
    (globals : List Surface.Signature) (type : Surface.Ty) :
    Surface.checkerExprFuel globals (.none type) + 1 ≤
      expressionBits (.none type) * expressionCheckerScale globals := by
  have typeBound := checkerTypeFuel_le_typeBits type
  have scaleLower : 2 ≤ expressionCheckerScale globals := by
    simp [expressionCheckerScale]
  have bitsLower : 2 * (1 + typeBits type) ≤
      (1 + typeBits type) * expressionCheckerScale globals := by
    calc
      2 * (1 + typeBits type) = (1 + typeBits type) * 2 := Nat.mul_comm _ _
      _ ≤ (1 + typeBits type) * expressionCheckerScale globals :=
        Nat.mul_le_mul_left _ scaleLower
  have structural : Surface.checkerTypeFuel type + 2 ≤ 2 * (1 + typeBits type) := by
    omega
  have result := Nat.le_trans structural bitsLower
  simpa [Surface.checkerExprFuel, expressionBits, Nat.mul_comm] using result

/-- A global lookup checks its type arguments and rescans the complete
signature table. Charging one signature-table fuel unit per encoded
expression bit is enough to cover both costs, including the list-walker
step. -/
theorem checkerGlobalExprFuel_le_scaled_expressionBits
    (globals : List Surface.Signature) (index : Nat) (arguments : List Surface.Ty) :
    Surface.checkerExprFuel globals (.global index arguments) + 1 ≤
      expressionBits (.global index arguments) * expressionCheckerScale globals := by
  have argumentsBound := checkerTypesFuel_le_typeListBits arguments
  have indexBitsPositive := naturalBits_positive index
  have bitsLower : 2 + typeListBits arguments ≤
      expressionBits (.global index arguments) := by
    simp [expressionBits]
    omega
  have bitsAtLeastOne : 1 ≤ expressionBits (.global index arguments) := by
    omega
  have tableBound : Surface.checkerSignaturesFuel globals ≤
      expressionBits (.global index arguments) * Surface.checkerSignaturesFuel globals := by
    simpa using Nat.mul_le_mul_right (Surface.checkerSignaturesFuel globals) bitsAtLeastOne
  have argumentsAndStep : Surface.checkerTypesFuel arguments + 2 ≤
      expressionBits (.global index arguments) := by
    omega
  simp only [Surface.checkerExprFuel, expressionCheckerScale]
  rw [show Surface.checkerSignaturesFuel globals + 2 =
      Surface.checkerSignaturesFuel globals + 1 + 1 by omega, Nat.mul_add,
      Nat.mul_add]
  omega

private theorem expressionListLength_le_fold (expressions : List Surface.Expr) :
    expressions.length ≤ expressions.foldr
      (fun expression rest => expressionBits expression + rest) 1 := by
  induction expressions with
  | nil => simp
  | cons head tail ih =>
      have headPositive := expressionBits_positive head
      simp only [List.length_cons, List.foldr]
      omega

theorem expressionListLength_le_bits (expressions : List Surface.Expr) :
    expressions.length ≤ expressionListBits expressions := by
  have structural := expressionListLength_le_fold expressions
  simp [expressionListBits, expressionListPayloadBits]
  omega

/-- The list walker is bounded by the encoded list size and the sum of the
per-expression checker bounds. The pointwise premise is where the repeated
global-signature scan for each expression is charged. -/
theorem checkerExprsFuel_le_scaled_expressionListContents
    (globals : List Surface.Signature) (expressions : List Surface.Expr)
    (eachExpression : ∀ expression, expression ∈ expressions →
      Surface.checkerExprFuel globals expression + 1 ≤
        expressionBits expression * expressionCheckerScale globals) :
    Surface.checkerExprsFuel globals expressions ≤
      expressionListPayloadBits expressions *
        expressionCheckerScale globals := by
  induction expressions with
  | nil =>
      have scalePositive : 0 < expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      simp [Surface.checkerExprsFuel, expressionListPayloadBits]
      simpa only [Nat.one_mul] using Nat.succ_le_of_lt scalePositive
  | cons head tail ih =>
      have headBound := eachExpression head (by simp)
      have tailBound : ∀ expression, expression ∈ tail →
          Surface.checkerExprFuel globals expression + 1 ≤
            expressionBits expression * expressionCheckerScale globals := by
        intro expression member
        exact eachExpression expression (by simp [member])
      have restBound := ih tailBound
      have restBound' : Surface.checkerExprsFuel globals tail ≤
          tail.foldr (fun expression rest => expressionBits expression + rest) 1 *
            expressionCheckerScale globals := by
        simpa [expressionListPayloadBits] using restBound
      simp only [Surface.checkerExprsFuel, expressionListPayloadBits, List.foldr]
      calc
        Surface.checkerExprFuel globals head +
            Surface.checkerExprsFuel globals tail + 1 ≤
            (Surface.checkerExprFuel globals head + 1) +
            Surface.checkerExprsFuel globals tail := by omega
        _ ≤ expressionBits head * expressionCheckerScale globals +
            tail.foldr (fun expression rest => expressionBits expression + rest) 1 *
              expressionCheckerScale globals := Nat.add_le_add headBound restBound'
        _ = (expressionBits head +
            tail.foldr (fun expression rest => expressionBits expression + rest) 1) *
              expressionCheckerScale globals := by rw [Nat.add_mul]

theorem checkerExprsFuel_le_scaled_expressionListBits
    (globals : List Surface.Signature) (expressions : List Surface.Expr)
    (eachExpression : ∀ expression, expression ∈ expressions →
      Surface.checkerExprFuel globals expression + 1 ≤
        expressionBits expression * expressionCheckerScale globals) :
    Surface.checkerExprsFuel globals expressions ≤
      expressionListBits expressions * expressionCheckerScale globals := by
  have contents := checkerExprsFuel_le_scaled_expressionListContents globals expressions
    eachExpression
  have payloadIncluded : expressions.foldr
      (fun expression rest => expressionBits expression + rest) 1 ≤
      naturalBits expressions.length + expressions.foldr
        (fun expression rest => expressionBits expression + rest) 1 := by
    omega
  have scaledIncluded := Nat.mul_le_mul_right (expressionCheckerScale globals) payloadIncluded
  exact Nat.le_trans contents (by simpa [expressionListBits] using scaledIncluded)

inductive CheckerLeafExpression : Surface.Expr → Prop where
  | simple (expression : Surface.Expr) (leaf : CheckerSimpleLeaf expression) :
      CheckerLeafExpression expression
  | global (index : Nat) (arguments : List Surface.Ty) :
      CheckerLeafExpression (.global index arguments)
  | nil (type : Surface.Ty) : CheckerLeafExpression (.nil type)
  | none (type : Surface.Ty) : CheckerLeafExpression (.none type)

theorem checkerLeafExpression_fuel_bound (globals : List Surface.Signature)
    (expression : Surface.Expr) (leaf : CheckerLeafExpression expression) :
    Surface.checkerExprFuel globals expression + 1 ≤
      expressionBits expression * expressionCheckerScale globals := by
  cases leaf with
  | simple expression simpleLeaf =>
      exact checkerSimpleLeafExprFuel_le_scaled_expressionBits globals expression simpleLeaf
  | global index arguments =>
      exact checkerGlobalExprFuel_le_scaled_expressionBits globals index arguments
  | nil type => exact checkerNilExprFuel_le_scaled_expressionBits globals type
  | none type => exact checkerNoneExprFuel_le_scaled_expressionBits globals type

inductive CheckerLeafExpressions : List Surface.Expr → Prop where
  | nil : CheckerLeafExpressions []
  | cons (head : Surface.Expr) (tail : List Surface.Expr) :
      CheckerLeafExpression head → CheckerLeafExpressions tail →
      CheckerLeafExpressions (head :: tail)

/-- Any list made only of checker leaf expressions receives the general
scaled list traversal bound without a separate pointwise fuel premise. -/
theorem checkerLeafExpressions_fuel_bound (globals : List Surface.Signature)
    (expressions : List Surface.Expr) (leaves : CheckerLeafExpressions expressions) :
    Surface.checkerExprsFuel globals expressions ≤
      expressionListBits expressions * expressionCheckerScale globals := by
  apply checkerExprsFuel_le_scaled_expressionListBits
  intro expression member
  induction leaves generalizing expression with
  | nil => simp at member
  | cons head tail headLeaf tailLeaves ih =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · cases same
        exact checkerLeafExpression_fuel_bound globals head headLeaf
      · exact ih expression member

theorem checkerLeafExpressions_fuel_plus_one_bound
    (globals : List Surface.Signature) (expressions : List Surface.Expr)
    (leaves : CheckerLeafExpressions expressions) :
    Surface.checkerExprsFuel globals expressions + 1 ≤
      expressionListBits expressions * expressionCheckerScale globals := by
  have eachExpression : ∀ expression, expression ∈ expressions →
      Surface.checkerExprFuel globals expression + 1 ≤
        expressionBits expression * expressionCheckerScale globals := by
    intro expression member
    induction leaves generalizing expression with
    | nil => simp at member
    | cons head tail headLeaf tailLeaves ih =>
        simp only [List.mem_cons] at member
        rcases member with same | member
        · cases same
          exact checkerLeafExpression_fuel_bound globals head headLeaf
        · exact ih expression member
  have contents := checkerExprsFuel_le_scaled_expressionListContents
    globals expressions eachExpression
  have lengthBitsPositive := naturalBits_positive expressions.length
  have scalePositive : 0 < expressionCheckerScale globals := by
    simp [expressionCheckerScale]
  have slack : 1 ≤ naturalBits expressions.length * expressionCheckerScale globals := by
    have product := Nat.mul_le_mul_left (naturalBits expressions.length)
      (show 1 ≤ expressionCheckerScale globals by omega)
    simpa only [Nat.mul_one] using Nat.le_trans (by omega) product
  unfold expressionListBits
  calc
    Surface.checkerExprsFuel globals expressions + 1 ≤
        expressionListPayloadBits expressions * expressionCheckerScale globals + 1 :=
      Nat.add_le_add_right contents 1
    _ ≤ expressionListPayloadBits expressions * expressionCheckerScale globals +
          naturalBits expressions.length * expressionCheckerScale globals := by omega
    _ = (naturalBits expressions.length + expressionListPayloadBits expressions) *
          expressionCheckerScale globals := by rw [Nat.add_mul]; omega

theorem checkerTypeFuel_le_scaled_typeBits (globals : List Surface.Signature)
    (type : Surface.Ty) :
    Surface.checkerTypeFuel type + 1 ≤ typeBits type * expressionCheckerScale globals := by
  have typeBound := checkerTypeFuel_le_typeBits type
  have typeBitsPositive : 0 < typeBits type := by
    cases type <;> simp [typeBits] <;> omega
  have scaleLower : 2 ≤ expressionCheckerScale globals := by
    simp [expressionCheckerScale]
  have structural : Surface.checkerTypeFuel type + 1 ≤ 2 * typeBits type := by
    omega
  calc
    Surface.checkerTypeFuel type + 1 ≤ 2 * typeBits type := structural
    _ = typeBits type * 2 := Nat.mul_comm _ _
    _ ≤ typeBits type * expressionCheckerScale globals :=
      Nat.mul_le_mul_left _ scaleLower

theorem checkerTypesFuel_le_scaled_typeListBits (globals : List Surface.Signature)
    (types : List Surface.Ty) :
    Surface.checkerTypesFuel types + 1 ≤ typeListBits types * expressionCheckerScale globals := by
  have typeBound := checkerTypesFuel_le_typeListBits types
  have bitsPositive : 0 < typeListBits types := by
    unfold typeListBits
    have lengthPositive := naturalBits_positive types.length
    omega
  have scaleLower : 2 ≤ expressionCheckerScale globals := by
    simp [expressionCheckerScale]
  have structural : Surface.checkerTypesFuel types + 1 ≤ 2 * typeListBits types := by
    omega
  calc
    Surface.checkerTypesFuel types + 1 ≤ 2 * typeListBits types := structural
    _ = typeListBits types * 2 := Nat.mul_comm _ _
    _ ≤ typeListBits types * expressionCheckerScale globals :=
      Nat.mul_le_mul_left _ scaleLower

inductive CheckerBinaryTreeExpression : Surface.Expr → Prop where
  | leaf (expression : Surface.Expr) (leaf : CheckerLeafExpression expression) :
      CheckerBinaryTreeExpression expression
  | add (left right : Surface.Expr) : CheckerBinaryTreeExpression left →
      CheckerBinaryTreeExpression right → CheckerBinaryTreeExpression (.add left right)
  | sub (left right : Surface.Expr) : CheckerBinaryTreeExpression left →
      CheckerBinaryTreeExpression right → CheckerBinaryTreeExpression (.sub left right)
  | mul (left right : Surface.Expr) : CheckerBinaryTreeExpression left →
      CheckerBinaryTreeExpression right → CheckerBinaryTreeExpression (.mul left right)
  | le (left right : Surface.Expr) : CheckerBinaryTreeExpression left →
      CheckerBinaryTreeExpression right → CheckerBinaryTreeExpression (.le left right)
  | intEq (left right : Surface.Expr) : CheckerBinaryTreeExpression left →
      CheckerBinaryTreeExpression right → CheckerBinaryTreeExpression (.intEq left right)
  | floatBin (op : Surface.FloatBinOp) (left right : Surface.Expr) :
      CheckerBinaryTreeExpression left → CheckerBinaryTreeExpression right →
      CheckerBinaryTreeExpression (.floatBin op left right)
  | some (type : Surface.Ty) (value : Surface.Expr) :
      CheckerBinaryTreeExpression value → CheckerBinaryTreeExpression (.some type value)
  | cons (type : Surface.Ty) (head tail : Surface.Expr) :
      CheckerBinaryTreeExpression head → CheckerBinaryTreeExpression tail →
      CheckerBinaryTreeExpression (.cons type head tail)
  | ite (condition yes no : Surface.Expr) :
      CheckerBinaryTreeExpression condition → CheckerBinaryTreeExpression yes →
      CheckerBinaryTreeExpression no → CheckerBinaryTreeExpression (.ite condition yes no)
  | lam (parameters : List Surface.Ty) (result : Surface.Ty) (body : Surface.Expr) :
      CheckerBinaryTreeExpression body →
      CheckerBinaryTreeExpression (.lam parameters result body)
  | appZero (function : Surface.Expr) : CheckerBinaryTreeExpression function →
      CheckerBinaryTreeExpression (.app function [])
  | letManyNil (types : List Surface.Ty) (body : Surface.Expr) :
      CheckerBinaryTreeExpression body →
      CheckerBinaryTreeExpression (.letMany types [] body)
  | letManyOne (types : List Surface.Ty) (initializer body : Surface.Expr) :
      CheckerBinaryTreeExpression initializer → CheckerBinaryTreeExpression body →
      CheckerBinaryTreeExpression (.letMany types [initializer] body)
  | letManyTwo (types : List Surface.Ty) (first second body : Surface.Expr) :
      CheckerBinaryTreeExpression first → CheckerBinaryTreeExpression second →
      CheckerBinaryTreeExpression body →
      CheckerBinaryTreeExpression (.letMany types [first, second] body)
  | letManyThree (types : List Surface.Ty)
      (first second third body : Surface.Expr) :
      CheckerBinaryTreeExpression first → CheckerBinaryTreeExpression second →
      CheckerBinaryTreeExpression third → CheckerBinaryTreeExpression body →
      CheckerBinaryTreeExpression (.letMany types [first, second, third] body)
  | letManyFour (types : List Surface.Ty)
      (first second third fourth body : Surface.Expr) :
      CheckerBinaryTreeExpression first → CheckerBinaryTreeExpression second →
      CheckerBinaryTreeExpression third → CheckerBinaryTreeExpression fourth →
      CheckerBinaryTreeExpression body →
      CheckerBinaryTreeExpression (.letMany types [first, second, third, fourth] body)
  | letManyFive (types : List Surface.Ty)
      (first second third fourth fifth body : Surface.Expr) :
      CheckerBinaryTreeExpression first → CheckerBinaryTreeExpression second →
      CheckerBinaryTreeExpression third → CheckerBinaryTreeExpression fourth →
      CheckerBinaryTreeExpression fifth → CheckerBinaryTreeExpression body →
      CheckerBinaryTreeExpression
        (.letMany types [first, second, third, fourth, fifth] body)
  | beginNil (first : Surface.Expr) : CheckerBinaryTreeExpression first →
      CheckerBinaryTreeExpression (.begin first [])
  | beginOne (first second : Surface.Expr) :
      CheckerBinaryTreeExpression first → CheckerBinaryTreeExpression second →
      CheckerBinaryTreeExpression (.begin first [second])
  | beginTwo (first second third : Surface.Expr) :
      CheckerBinaryTreeExpression first → CheckerBinaryTreeExpression second →
      CheckerBinaryTreeExpression third →
      CheckerBinaryTreeExpression (.begin first [second, third])
  | matchList (target empty full : Surface.Expr) :
      CheckerBinaryTreeExpression target → CheckerBinaryTreeExpression empty →
      CheckerBinaryTreeExpression full →
      CheckerBinaryTreeExpression (.matchList target empty full)
  | matchOption (target empty full : Surface.Expr) :
      CheckerBinaryTreeExpression target → CheckerBinaryTreeExpression empty →
      CheckerBinaryTreeExpression full →
      CheckerBinaryTreeExpression (.matchOption target empty full)

/-- Recursive arithmetic trees built from supported leaves have a structural
checker fuel bound. Each binary node's two child traversals pay for their own
step, leaving room for the parent's dispatch step. -/
theorem checkerBinaryTreeExpression_fuel_bound (globals : List Surface.Signature)
    (expression : Surface.Expr) (tree : CheckerBinaryTreeExpression expression) :
    Surface.checkerExprFuel globals expression + 1 ≤
      expressionBits expression * expressionCheckerScale globals := by
  induction tree with
  | leaf expression leaf => exact checkerLeafExpression_fuel_bound globals expression leaf
  | add left right leftTree rightTree leftIH rightIH =>
      have children := Nat.add_le_add leftIH rightIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits left + expressionBits right ≤
          1 + expressionBits left + expressionBits right by omega)
      rw [expressionBits_add]
      simp only [Surface.checkerExprFuel]
      calc
        _ = (Surface.checkerExprFuel globals left + 1) +
            (Surface.checkerExprFuel globals right + 1) := by omega
        _ ≤ expressionBits left * expressionCheckerScale globals +
            expressionBits right * expressionCheckerScale globals := children
        _ = (expressionBits left + expressionBits right) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
        _ ≤ (1 + expressionBits left + expressionBits right) *
            expressionCheckerScale globals := included
  | sub left right leftTree rightTree leftIH rightIH =>
      have children := Nat.add_le_add leftIH rightIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits left + expressionBits right ≤
          1 + expressionBits left + expressionBits right by omega)
      rw [expressionBits_sub]
      simp only [Surface.checkerExprFuel]
      calc
        _ = (Surface.checkerExprFuel globals left + 1) +
            (Surface.checkerExprFuel globals right + 1) := by omega
        _ ≤ expressionBits left * expressionCheckerScale globals +
            expressionBits right * expressionCheckerScale globals := children
        _ = (expressionBits left + expressionBits right) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
        _ ≤ (1 + expressionBits left + expressionBits right) *
            expressionCheckerScale globals := included
  | mul left right leftTree rightTree leftIH rightIH =>
      have children := Nat.add_le_add leftIH rightIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits left + expressionBits right ≤
          1 + expressionBits left + expressionBits right by omega)
      rw [expressionBits_mul]
      simp only [Surface.checkerExprFuel]
      calc
        _ = (Surface.checkerExprFuel globals left + 1) +
            (Surface.checkerExprFuel globals right + 1) := by omega
        _ ≤ expressionBits left * expressionCheckerScale globals +
            expressionBits right * expressionCheckerScale globals := children
        _ = (expressionBits left + expressionBits right) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
        _ ≤ (1 + expressionBits left + expressionBits right) *
            expressionCheckerScale globals := included
  | le left right leftTree rightTree leftIH rightIH =>
      have children := Nat.add_le_add leftIH rightIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits left + expressionBits right ≤
          1 + expressionBits left + expressionBits right by omega)
      rw [expressionBits_le]
      simp only [Surface.checkerExprFuel]
      calc
        _ = (Surface.checkerExprFuel globals left + 1) +
            (Surface.checkerExprFuel globals right + 1) := by omega
        _ ≤ expressionBits left * expressionCheckerScale globals +
            expressionBits right * expressionCheckerScale globals := children
        _ = (expressionBits left + expressionBits right) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
        _ ≤ (1 + expressionBits left + expressionBits right) *
            expressionCheckerScale globals := included
  | intEq left right leftTree rightTree leftIH rightIH =>
      have children := Nat.add_le_add leftIH rightIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits left + expressionBits right ≤
          1 + expressionBits left + expressionBits right by omega)
      rw [expressionBits_intEq]
      simp only [Surface.checkerExprFuel]
      calc
        _ = (Surface.checkerExprFuel globals left + 1) +
            (Surface.checkerExprFuel globals right + 1) := by omega
        _ ≤ expressionBits left * expressionCheckerScale globals +
            expressionBits right * expressionCheckerScale globals := children
        _ = (expressionBits left + expressionBits right) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
        _ ≤ (1 + expressionBits left + expressionBits right) *
            expressionCheckerScale globals := included
  | floatBin op left right leftTree rightTree leftIH rightIH =>
      have children := Nat.add_le_add leftIH rightIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits left + expressionBits right ≤
          1 + expressionBits left + expressionBits right by omega)
      rw [expressionBits_floatBin]
      simp only [Surface.checkerExprFuel]
      calc
        _ = (Surface.checkerExprFuel globals left + 1) +
            (Surface.checkerExprFuel globals right + 1) := by omega
        _ ≤ expressionBits left * expressionCheckerScale globals +
            expressionBits right * expressionCheckerScale globals := children
        _ = (expressionBits left + expressionBits right) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
        _ ≤ (1 + expressionBits left + expressionBits right) *
            expressionCheckerScale globals := included
  | some type value valueTree valueIH =>
      have parts := Nat.add_le_add
        (checkerTypeFuel_le_scaled_typeBits globals type) valueIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show typeBits type + expressionBits value ≤
          1 + typeBits type + expressionBits value by omega)
      rw [expressionBits_some]
      simp only [Surface.checkerExprFuel]
      calc
        _ = (Surface.checkerTypeFuel type + 1) +
            (Surface.checkerExprFuel globals value + 1) := by omega
        _ ≤ typeBits type * expressionCheckerScale globals +
            expressionBits value * expressionCheckerScale globals := parts
        _ = (typeBits type + expressionBits value) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
        _ ≤ (1 + typeBits type + expressionBits value) *
            expressionCheckerScale globals := included
  | cons type head tail headTree tailTree headIH tailIH =>
      have annotation := checkerTypeFuel_le_scaled_typeBits globals type
      have parts := Nat.add_le_add (Nat.add_le_add annotation headIH) tailIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show typeBits type + expressionBits head + expressionBits tail ≤
          1 + typeBits type + expressionBits head + expressionBits tail by omega)
      rw [expressionBits_cons]
      simp only [Surface.checkerExprFuel]
      calc
        _ ≤ (Surface.checkerTypeFuel type + 1) +
            (Surface.checkerExprFuel globals head + 1) +
            (Surface.checkerExprFuel globals tail + 1) := by omega
        _ ≤ typeBits type * expressionCheckerScale globals +
            expressionBits head * expressionCheckerScale globals +
            expressionBits tail * expressionCheckerScale globals := parts
        _ = (typeBits type + expressionBits head + expressionBits tail) *
            expressionCheckerScale globals := by rw [Nat.add_mul, Nat.add_mul]
        _ ≤ (1 + typeBits type + expressionBits head + expressionBits tail) *
            expressionCheckerScale globals := included
  | ite condition yes no conditionTree yesTree noTree conditionIH yesIH noIH =>
      have parts := Nat.add_le_add (Nat.add_le_add conditionIH yesIH) noIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits condition + expressionBits yes + expressionBits no ≤
          1 + expressionBits condition + expressionBits yes + expressionBits no by omega)
      rw [expressionBits_ite]
      simp only [Surface.checkerExprFuel]
      calc
        _ ≤ (Surface.checkerExprFuel globals condition + 1) +
            (Surface.checkerExprFuel globals yes + 1) +
            (Surface.checkerExprFuel globals no + 1) := by omega
        _ ≤ expressionBits condition * expressionCheckerScale globals +
            expressionBits yes * expressionCheckerScale globals +
            expressionBits no * expressionCheckerScale globals := parts
        _ = (expressionBits condition + expressionBits yes + expressionBits no) *
            expressionCheckerScale globals := by rw [Nat.add_mul, Nat.add_mul]
        _ ≤ (1 + expressionBits condition + expressionBits yes + expressionBits no) *
            expressionCheckerScale globals := included
  | lam parameters result body bodyTree bodyIH =>
      have parts := Nat.add_le_add
        (Nat.add_le_add
          (checkerTypesFuel_le_scaled_typeListBits globals parameters)
          (checkerTypeFuel_le_scaled_typeBits globals result)) bodyIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show typeListBits parameters + typeBits result + expressionBits body ≤
          1 + typeListBits parameters + typeBits result + expressionBits body by omega)
      rw [expressionBits_lam]
      simp only [Surface.checkerExprFuel]
      calc
        _ ≤ (Surface.checkerTypesFuel parameters + 1) +
            (Surface.checkerTypeFuel result + 1) +
            (Surface.checkerExprFuel globals body + 1) := by omega
        _ ≤ typeListBits parameters * expressionCheckerScale globals +
            typeBits result * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals := parts
        _ = (typeListBits parameters + typeBits result + expressionBits body) *
            expressionCheckerScale globals := by rw [Nat.add_mul, Nat.add_mul]
        _ ≤ (1 + typeListBits parameters + typeBits result + expressionBits body) *
            expressionCheckerScale globals := included
  | appZero function functionTree functionIH =>
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have twoScaled : 2 ≤ 2 * expressionCheckerScale globals := by omega
      rw [expressionBits_app_nil]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerExprFuel globals function + 1) + 2 := by omega
        _ ≤ expressionBits function * expressionCheckerScale globals +
            2 * expressionCheckerScale globals := Nat.add_le_add functionIH twoScaled
        _ = (2 + expressionBits function) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
            omega
  | letManyNil types body bodyTree bodyIH =>
      have parts := Nat.add_le_add
        (checkerTypesFuel_le_scaled_typeListBits globals types) bodyIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 1 ≤ 2 * expressionCheckerScale globals := by omega
      rw [expressionBits_letMany_nil]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerTypesFuel types + 1) +
            (Surface.checkerExprFuel globals body + 1) + 1 := by omega
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals + 1 :=
          Nat.add_le_add_right parts 1
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals +
            2 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (2 + typeListBits types + expressionBits body) *
            expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul]
          omega
  | letManyOne types initializer body initializerTree bodyTree initializerIH bodyIH =>
      have parts := Nat.add_le_add
        (Nat.add_le_add
          (checkerTypesFuel_le_scaled_typeListBits globals types) initializerIH) bodyIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 1 ≤ 3 * expressionCheckerScale globals := by omega
      rw [expressionBits_letMany_one]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerTypesFuel types + 1) +
            (Surface.checkerExprFuel globals initializer + 1) +
            (Surface.checkerExprFuel globals body + 1) + 1 := by omega
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits initializer * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals + 1 :=
          Nat.add_le_add_right parts 1
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits initializer * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals +
            3 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (3 + typeListBits types + expressionBits initializer + expressionBits body) *
            expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
          omega
  | letManyTwo types first second body firstTree secondTree bodyTree firstIH secondIH bodyIH =>
      have parts := Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (checkerTypesFuel_le_scaled_typeListBits globals types) firstIH) secondIH) bodyIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 1 ≤ 4 * expressionCheckerScale globals := by omega
      rw [expressionBits_letMany_two]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerTypesFuel types + 1) +
            (Surface.checkerExprFuel globals first + 1) +
            (Surface.checkerExprFuel globals second + 1) +
            (Surface.checkerExprFuel globals body + 1) + 1 := by omega
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals + 1 :=
          Nat.add_le_add_right parts 1
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals +
            4 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (4 + typeListBits types + expressionBits first + expressionBits second +
            expressionBits body) * expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
          omega
  | letManyThree types first second third body firstTree secondTree thirdTree bodyTree
      firstIH secondIH thirdIH bodyIH =>
      have parts := Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (checkerTypesFuel_le_scaled_typeListBits globals types) firstIH) secondIH)
          thirdIH) bodyIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 1 ≤ 5 * expressionCheckerScale globals := by omega
      rw [expressionBits_letMany_three]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerTypesFuel types + 1) +
            (Surface.checkerExprFuel globals first + 1) +
            (Surface.checkerExprFuel globals second + 1) +
            (Surface.checkerExprFuel globals third + 1) +
            (Surface.checkerExprFuel globals body + 1) + 1 := by omega
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals + 1 :=
          Nat.add_le_add_right parts 1
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals +
            5 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (5 + typeListBits types + expressionBits first + expressionBits second +
            expressionBits third + expressionBits body) * expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
          omega
  | letManyFour types first second third fourth body firstTree secondTree thirdTree
      fourthTree bodyTree firstIH secondIH thirdIH fourthIH bodyIH =>
      have parts := Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (checkerTypesFuel_le_scaled_typeListBits globals types) firstIH) secondIH)
              thirdIH) fourthIH) bodyIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 1 ≤ 6 * expressionCheckerScale globals := by omega
      rw [expressionBits_letMany_four]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerTypesFuel types + 1) +
            (Surface.checkerExprFuel globals first + 1) +
            (Surface.checkerExprFuel globals second + 1) +
            (Surface.checkerExprFuel globals third + 1) +
            (Surface.checkerExprFuel globals fourth + 1) +
            (Surface.checkerExprFuel globals body + 1) + 1 := by omega
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals +
            expressionBits fourth * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals + 1 :=
          Nat.add_le_add_right parts 1
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals +
            expressionBits fourth * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals +
            6 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (6 + typeListBits types + expressionBits first + expressionBits second +
            expressionBits third + expressionBits fourth + expressionBits body) *
            expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul]
          omega
  | letManyFive types first second third fourth fifth body firstTree secondTree thirdTree
      fourthTree fifthTree bodyTree firstIH secondIH thirdIH fourthIH fifthIH bodyIH =>
      have parts := Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (checkerTypesFuel_le_scaled_typeListBits globals types) firstIH) secondIH)
                thirdIH) fourthIH) fifthIH) bodyIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 1 ≤ 7 * expressionCheckerScale globals := by omega
      rw [expressionBits_letMany_five]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerTypesFuel types + 1) +
            (Surface.checkerExprFuel globals first + 1) +
            (Surface.checkerExprFuel globals second + 1) +
            (Surface.checkerExprFuel globals third + 1) +
            (Surface.checkerExprFuel globals fourth + 1) +
            (Surface.checkerExprFuel globals fifth + 1) +
            (Surface.checkerExprFuel globals body + 1) + 1 := by omega
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals +
            expressionBits fourth * expressionCheckerScale globals +
            expressionBits fifth * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals + 1 :=
          Nat.add_le_add_right parts 1
        _ ≤ typeListBits types * expressionCheckerScale globals +
            expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals +
            expressionBits fourth * expressionCheckerScale globals +
            expressionBits fifth * expressionCheckerScale globals +
            expressionBits body * expressionCheckerScale globals +
            7 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (7 + typeListBits types + expressionBits first + expressionBits second +
            expressionBits third + expressionBits fourth + expressionBits fifth +
            expressionBits body) * expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul, Nat.add_mul,
            Nat.add_mul, Nat.add_mul]
          omega
  | beginNil first firstTree firstIH =>
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have twoScaled : 2 ≤ 2 * expressionCheckerScale globals := by omega
      rw [expressionBits_begin_nil]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerExprFuel globals first + 1) + 2 := by omega
        _ ≤ expressionBits first * expressionCheckerScale globals +
            2 * expressionCheckerScale globals := Nat.add_le_add firstIH twoScaled
        _ = (2 + expressionBits first) * expressionCheckerScale globals := by
            rw [Nat.add_mul]
            omega
  | beginOne first second firstTree secondTree firstIH secondIH =>
      have parts := Nat.add_le_add firstIH secondIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 2 ≤ 3 * expressionCheckerScale globals := by omega
      rw [expressionBits_begin_one]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerExprFuel globals first + 1) +
            (Surface.checkerExprFuel globals second + 1) + 2 := by omega
        _ ≤ expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals + 2 :=
          Nat.add_le_add_right parts 2
        _ ≤ expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            3 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (3 + expressionBits first + expressionBits second) *
            expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul]
          omega
  | beginTwo first second third firstTree secondTree thirdTree firstIH secondIH thirdIH =>
      have parts := Nat.add_le_add (Nat.add_le_add firstIH secondIH) thirdIH
      have scaleLower : 2 ≤ expressionCheckerScale globals := by
        simp [expressionCheckerScale]
      have slack : 2 ≤ 4 * expressionCheckerScale globals := by omega
      rw [expressionBits_begin_two]
      simp only [Surface.checkerExprFuel, Surface.checkerExprsFuel]
      calc
        _ = (Surface.checkerExprFuel globals first + 1) +
            (Surface.checkerExprFuel globals second + 1) +
            (Surface.checkerExprFuel globals third + 1) + 2 := by omega
        _ ≤ expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals + 2 :=
          Nat.add_le_add_right parts 2
        _ ≤ expressionBits first * expressionCheckerScale globals +
            expressionBits second * expressionCheckerScale globals +
            expressionBits third * expressionCheckerScale globals +
            4 * expressionCheckerScale globals := Nat.add_le_add_left slack _
        _ = (4 + expressionBits first + expressionBits second + expressionBits third) *
            expressionCheckerScale globals := by
          rw [Nat.add_mul, Nat.add_mul, Nat.add_mul]
          omega
  | matchList target empty full targetTree emptyTree fullTree targetIH emptyIH fullIH =>
      have parts := Nat.add_le_add (Nat.add_le_add targetIH emptyIH) fullIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits target + expressionBits empty + expressionBits full ≤
          1 + expressionBits target + expressionBits empty + expressionBits full by omega)
      rw [expressionBits_matchList]
      simp only [Surface.checkerExprFuel]
      calc
        _ ≤ (Surface.checkerExprFuel globals target + 1) +
            (Surface.checkerExprFuel globals empty + 1) +
            (Surface.checkerExprFuel globals full + 1) := by omega
        _ ≤ expressionBits target * expressionCheckerScale globals +
            expressionBits empty * expressionCheckerScale globals +
            expressionBits full * expressionCheckerScale globals := parts
        _ = (expressionBits target + expressionBits empty + expressionBits full) *
            expressionCheckerScale globals := by rw [Nat.add_mul, Nat.add_mul]
        _ ≤ (1 + expressionBits target + expressionBits empty + expressionBits full) *
            expressionCheckerScale globals := included
  | matchOption target empty full targetTree emptyTree fullTree targetIH emptyIH fullIH =>
      have parts := Nat.add_le_add (Nat.add_le_add targetIH emptyIH) fullIH
      have included := Nat.mul_le_mul_right (expressionCheckerScale globals)
        (show expressionBits target + expressionBits empty + expressionBits full ≤
          1 + expressionBits target + expressionBits empty + expressionBits full by omega)
      rw [expressionBits_matchOption]
      simp only [Surface.checkerExprFuel]
      calc
        _ ≤ (Surface.checkerExprFuel globals target + 1) +
            (Surface.checkerExprFuel globals empty + 1) +
            (Surface.checkerExprFuel globals full + 1) := by omega
        _ ≤ expressionBits target * expressionCheckerScale globals +
            expressionBits empty * expressionCheckerScale globals +
            expressionBits full * expressionCheckerScale globals := parts
        _ = (expressionBits target + expressionBits empty + expressionBits full) *
            expressionCheckerScale globals := by rw [Nat.add_mul, Nat.add_mul]
        _ ≤ (1 + expressionBits target + expressionBits empty + expressionBits full) *
            expressionCheckerScale globals := included

inductive CheckerBinaryTreeExpressions : List Surface.Expr → Prop where
  | nil : CheckerBinaryTreeExpressions []
  | cons (head : Surface.Expr) (tail : List Surface.Expr) :
      CheckerBinaryTreeExpression head → CheckerBinaryTreeExpressions tail →
      CheckerBinaryTreeExpressions (head :: tail)

/-- Lists of supported recursively structured expressions also satisfy the
scaled checker bound, including each list dispatch step. -/
theorem checkerBinaryTreeExpressions_fuel_bound (globals : List Surface.Signature)
    (expressions : List Surface.Expr) (trees : CheckerBinaryTreeExpressions expressions) :
    Surface.checkerExprsFuel globals expressions ≤
      expressionListBits expressions * expressionCheckerScale globals := by
  apply checkerExprsFuel_le_scaled_expressionListBits
  intro expression member
  induction trees generalizing expression with
  | nil => simp at member
  | cons head tail headTree tailTrees ih =>
      simp only [List.mem_cons] at member
      rcases member with same | member
      · cases same
        exact checkerBinaryTreeExpression_fuel_bound globals head headTree
      · exact ih expression member

theorem checkerBinaryTreeExpressions_fuel_plus_one_bound
    (globals : List Surface.Signature) (expressions : List Surface.Expr)
    (trees : CheckerBinaryTreeExpressions expressions) :
    Surface.checkerExprsFuel globals expressions + 1 ≤
      expressionListBits expressions * expressionCheckerScale globals := by
  have eachExpression : ∀ expression, expression ∈ expressions →
      Surface.checkerExprFuel globals expression + 1 ≤
        expressionBits expression * expressionCheckerScale globals := by
    intro expression member
    induction trees generalizing expression with
    | nil => simp at member
    | cons head tail headTree tailTrees ih =>
        simp only [List.mem_cons] at member
        rcases member with same | member
        · cases same
          exact checkerBinaryTreeExpression_fuel_bound globals head headTree
        · exact ih expression member
  have contents := checkerExprsFuel_le_scaled_expressionListContents
    globals expressions eachExpression
  have lengthBitsPositive := naturalBits_positive expressions.length
  have scalePositive : 0 < expressionCheckerScale globals := by
    simp [expressionCheckerScale]
  have slack : 1 ≤ naturalBits expressions.length * expressionCheckerScale globals := by
    have product := Nat.mul_le_mul_left (naturalBits expressions.length)
      (show 1 ≤ expressionCheckerScale globals by omega)
    simpa only [Nat.mul_one] using Nat.le_trans (by omega) product
  unfold expressionListBits
  calc
    Surface.checkerExprsFuel globals expressions + 1 ≤
        expressionListPayloadBits expressions * expressionCheckerScale globals + 1 :=
      Nat.add_le_add_right contents 1
    _ ≤ expressionListPayloadBits expressions * expressionCheckerScale globals +
          naturalBits expressions.length * expressionCheckerScale globals := by omega
    _ = (naturalBits expressions.length + expressionListPayloadBits expressions) *
          expressionCheckerScale globals := by rw [Nat.add_mul]; omega

theorem signatureBits_positive (signature : Surface.Signature) :
    0 < signatureBits signature := by
  unfold signatureBits
  omega

private theorem signatureListLength_le_fold (signatures : List Surface.Signature) :
    signatures.length ≤ signatures.foldr
      (fun signature rest => signatureBits signature + rest) 1 := by
  induction signatures with
  | nil => simp
  | cons head tail ih =>
      have headPositive := signatureBits_positive head
      simp only [List.length_cons, List.foldr]
      omega

theorem signatureListLength_le_bits (signatures : List Surface.Signature) :
    signatures.length ≤ signatureListBits signatures := by
  have structural := signatureListLength_le_fold signatures
  simp only [signatureListBits]
  omega

noncomputable def typedProgramBits (signatures : List Surface.Signature)
    (bodies : List Surface.Expr) (entry : Nat) : Nat :=
  1 + signatureListBits signatures + expressionListBits bodies + naturalBits entry

def typedProgramTopLevelScanCost (signatures : List Surface.Signature)
    (bodies : List Surface.Expr) : Nat := signatures.length + bodies.length

theorem typedProgramTopLevelScanCost_le_bits (signatures : List Surface.Signature)
    (bodies : List Surface.Expr) (entry : Nat) :
    typedProgramTopLevelScanCost signatures bodies ≤ typedProgramBits signatures bodies entry := by
  have signaturesBound := signatureListLength_le_bits signatures
  have bodiesBound := expressionListLength_le_bits bodies
  simp only [typedProgramTopLevelScanCost, typedProgramBits]
  omega

/-- Composite input-size bound for validating the complete global signature
table and scanning the typed program's top-level signature/body rows. This
covers the signature WF fuel and row scan used by the verifier before the
recursive expression-checking cost is added. -/
theorem typedProgramSignatureValidationAndScanCost_le_bits
    (signatures : List Surface.Signature) (bodies : List Surface.Expr) (entry : Nat) :
    Surface.checkerSignaturesFuel signatures +
        typedProgramTopLevelScanCost signatures bodies ≤
      2 * typedProgramBits signatures bodies entry := by
  have signatureValidationBound := checkerSignaturesFuel_le_signatureListBits signatures
  have signatureScanBound := typedProgramTopLevelScanCost_le_bits signatures bodies entry
  have validationInput : Surface.checkerSignaturesFuel signatures ≤
      typedProgramBits signatures bodies entry := by
    calc
      Surface.checkerSignaturesFuel signatures ≤ signatureListBits signatures :=
        signatureValidationBound
      _ ≤ typedProgramBits signatures bodies entry := by
        simp [typedProgramBits]
        omega
  omega

noncomputable def rulesBits (rules : List (Nat × Tree)) : Nat :=
  naturalBits rules.length + rules.foldr
    (fun (origin, rule) rest => naturalBits origin + treeBits rule + rest) 1

noncomputable def certificateBits : Certificate → Nat
  | .refl tree => 1 + treeBits tree
  | .congList pre suffix child =>
      1 + treeListBits pre + treeListBits suffix + certificateBits child
  | .macroStep origin fuel fresh final rule input output =>
      1 + naturalBits origin + naturalBits fuel + naturalBits fresh + naturalBits final +
        treeBits rule + treeBits input + treeBits output
  | .trans first second => 1 + certificateBits first + certificateBits second

theorem certificateEndpoints_le_max (certificate : Certificate) :
    treeNodeCount (source certificate) ≤ certificateMaxEndpointNodes certificate ∧
      treeNodeCount (target certificate) ≤ certificateMaxEndpointNodes certificate := by
  induction certificate with
  | refl tree => simp [source, target, certificateMaxEndpointNodes]
  | congList pre suffix child _ih =>
      simp only [source, target, certificateMaxEndpointNodes]
      exact ⟨Nat.le_max_left _ _,
        Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)⟩
  | macroStep origin fuel fresh final rule input output =>
      simp only [source, target, certificateMaxEndpointNodes]
      exact ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  | trans first second ihFirst ihSecond =>
      simp only [source, target, certificateMaxEndpointNodes]
      exact ⟨Nat.le_trans ihFirst.1
          (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)),
        Nat.le_trans ihSecond.2
          (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))⟩

theorem certificateMaxEndpointNodes_le_bits (certificate : Certificate) :
    certificateMaxEndpointNodes certificate ≤ certificateBits certificate := by
  induction certificate with
  | refl tree =>
      simp only [certificateMaxEndpointNodes, certificateBits]
      have treeBound := treeNodeCount_le_treeBits tree
      omega
  | macroStep origin fuel fresh final rule input output =>
      simp only [certificateMaxEndpointNodes, certificateBits]
      have inputBound := treeNodeCount_le_treeBits input
      have outputBound := treeNodeCount_le_treeBits output
      omega
  | trans first second ihFirst ihSecond =>
      simp only [certificateMaxEndpointNodes, certificateBits]
      have firstBound := certificateEndpoints_le_max first
      omega
  | congList pre suffix child ih =>
      simp only [certificateMaxEndpointNodes, certificateBits]
      have childEndpoints := certificateEndpoints_le_max child
      have preBound := treeListNodeCount_le_treeListBits pre
      have suffixBound := treeListNodeCount_le_treeListBits suffix
      have sourceCount : treeListNodeCount (pre ++ source child :: suffix) =
          treeListNodeCount pre + (treeNodeCount (source child) + treeListNodeCount suffix) := by
        rw [treeListNodeCount_append]
        simp [treeListNodeCount, treeNodeCount]
      have targetCount : treeListNodeCount (pre ++ target child :: suffix) =
          treeListNodeCount pre + (treeNodeCount (target child) + treeListNodeCount suffix) := by
        rw [treeListNodeCount_append]
        simp [treeListNodeCount, treeNodeCount]
      have sourceBound : treeNodeCount (source (.congList pre suffix child)) ≤
          1 + treeListBits pre + certificateMaxEndpointNodes child + treeListBits suffix := by
        rw [source, treeNodeCount_list, sourceCount]
        omega
      have targetBound : treeNodeCount (target (.congList pre suffix child)) ≤
          1 + treeListBits pre + certificateMaxEndpointNodes child + treeListBits suffix := by
        rw [target, treeNodeCount_list, targetCount]
        omega
      omega

theorem certificateNodeCount_le_bits (certificate : Certificate) :
    certificateNodeCount certificate ≤ certificateBits certificate := by
  induction certificate with
  | refl tree => simp [certificateNodeCount, certificateBits] <;> omega
  | congList pre suffix child ih => simp [certificateNodeCount, certificateBits] at * <;> omega
  | macroStep origin fuel fresh final rule input output =>
      simp [certificateNodeCount, certificateBits] <;> omega
  | trans first second ihFirst ihSecond =>
      simp [certificateNodeCount, certificateBits] at * <;> omega

theorem checkFreshWithMatchCost_le_modeled_payload_polynomial
    (rules : List (Nat × Tree)) (certificate : Certificate) :
    (checkFreshWithMatchCost rules certificate).2 ≤
      certificateNodeCount certificate + certificateMacroParameterTotal certificate +
        certificateNodeCount certificate * (rules.length + 1) +
        certificateNodeCount certificate * certificateNodeCount certificate +
        certificateNodeCount certificate + certificateNodeCount certificate +
        certificateNodeCount certificate * certificateBits certificate := by
  have structuralBound := checkFreshWithMatchCost_le_endpoint_polynomial rules certificate
  have endpointBound := certificateMaxEndpointNodes_le_bits certificate
  have scaledBound := Nat.mul_le_mul_left (certificateNodeCount certificate) endpointBound
  omega

noncomputable def checkedExpansionBits (rules : List (Nat × Tree)) (certificate : Certificate) : Nat :=
  1 + rulesBits rules + certificateBits certificate

noncomputable def processDataBits (source : String) (rules : List (Nat × Tree))
    (certificate : Certificate) (signatures : List Surface.Signature)
    (bodies : List Surface.Expr) (entry : Nat) : Nat :=
  1 + byteStringBits source + checkedExpansionBits rules certificate +
    typedProgramBits signatures bodies entry

theorem certificateBits_positive (certificate : Certificate) :
    0 < certificateBits certificate := by
  cases certificate <;> simp only [certificateBits] <;> omega

theorem certificateNodeCount_le_processBits
    (source : String) (rules : List (Nat × Tree)) (certificate : Certificate)
    (signatures : List Surface.Signature) (bodies : List Surface.Expr) (entry : Nat) :
    certificateNodeCount certificate ≤
      processDataBits source rules certificate signatures bodies entry := by
  apply Nat.le_trans (certificateNodeCount_le_bits certificate)
  simp only [processDataBits, checkedExpansionBits]
  omega

private theorem treeNodeCount_positive (tree : Tree) : 0 < treeNodeCount tree := by
  cases tree <;> simp [treeNodeCount]

private theorem treeListNodeCount_ge_length (trees : List Tree) :
    trees.length ≤ treeListNodeCount trees := by
  induction trees with
  | nil => simp [treeListNodeCount]
  | cons head tail ih =>
      have headPositive := treeNodeCount_positive head
      change tail.length + 1 ≤ treeNodeCount head + treeListNodeCount tail
      omega

private theorem parameterShape_nodeCount (head : Atom) (parameters : List Tree)
    (macroName replacement template : Tree) :
    parameters.length ≤
      treeNodeCount (.list [.list (.atom head :: parameters), macroName, replacement, template]) := by
  have parametersBound := treeListNodeCount_ge_length parameters
  simp [treeNodeCount, treeListNodeCount] at parametersBound ⊢
  omega

private theorem matchRuleParameterCount_le_treeNodeCount (rule : Tree) :
    matchRuleParameterCount rule ≤ treeNodeCount rule := by
  by_cases shape : ∃ (head : Atom) (parameters : List Tree)
      (macroName replacement template : Tree),
      rule = .list [.list (.atom head :: parameters), macroName, replacement, template]
  · obtain ⟨head, parameters, macroName, replacement, template, rfl⟩ := shape
    simpa [matchRuleParameterCount] using
      parameterShape_nodeCount head parameters macroName replacement template
  · unfold matchRuleParameterCount
    split <;> simp_all [treeNodeCount]

private theorem macroParameterTotal_le_bits (certificate : Certificate) :
    certificateMacroParameterTotal certificate ≤ certificateBits certificate := by
  induction certificate with
  | refl tree => simp [certificateMacroParameterTotal, certificateBits]
  | congList pre suffix child ih =>
      simp only [certificateMacroParameterTotal, certificateBits]
      omega
  | macroStep origin fuel fresh final rule input output =>
      simp only [certificateMacroParameterTotal, certificateBits]
      have parameters := matchRuleParameterCount_le_treeNodeCount rule
      have payload := treeNodeCount_le_treeBits rule
      omega
  | trans first second ihFirst ihSecond =>
      simp only [certificateMacroParameterTotal, certificateBits]
      omega

theorem macroParameterTotal_le_processBits
    (source : String) (rules : List (Nat × Tree)) (certificate : Certificate)
    (signatures : List Surface.Signature) (bodies : List Surface.Expr) (entry : Nat) :
    certificateMacroParameterTotal certificate ≤
      processDataBits source rules certificate signatures bodies entry := by
  apply Nat.le_trans (macroParameterTotal_le_bits certificate)
  simp only [processDataBits, checkedExpansionBits]
  omega

private theorem rulesFoldBits_ge_length (rules : List (Nat × Tree)) :
    rules.length ≤ rules.foldr
      (fun (rule : Nat × Tree) rest => naturalBits rule.1 + treeBits rule.2 + rest) 1 := by
  induction rules with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.foldr]
      have identityBits : 1 ≤ naturalBits head.1 := by simp [naturalBits]
      have ruleBits : 1 ≤ treeBits head.2 := by
        have lower := treeNodeCount_positive head.2
        exact Nat.le_trans (by omega) (treeNodeCount_le_treeBits head.2)
      omega

/-- Every rule contributes at least one serialized unit, so the number of
rules cannot exceed the encoded rule-list size. -/
theorem rules_length_le_bits (rules : List (Nat × Tree)) :
    rules.length ≤ rulesBits rules := by
  have folded := rulesFoldBits_ge_length rules
  simp only [rulesBits]
  omega

theorem rules_length_le_processBits
    (source : String) (rules : List (Nat × Tree)) (certificate : Certificate)
    (signatures : List Surface.Signature) (bodies : List Surface.Expr) (entry : Nat) :
    rules.length ≤ processDataBits source rules certificate signatures bodies entry := by
  apply Nat.le_trans (rules_length_le_bits rules)
  simp only [processDataBits, checkedExpansionBits]
  omega

/-- The current composite checker-cost model is quadratic in the complete
process bit-size. This bound covers the measured certificate traversal,
fresh-interval comparisons, rule membership, and shallow macro matching. -/
theorem checkFreshWithMatchCost_le_processBits_quadratic
    (source : String) (rules : List (Nat × Tree)) (certificate : Certificate)
    (signatures : List Surface.Signature) (bodies : List Surface.Expr) (entry : Nat) :
    (checkFreshWithMatchCost rules certificate).2 ≤
      8 * processDataBits source rules certificate signatures bodies entry ^ 2 := by
  let inputBits := processDataBits source rules certificate signatures bodies entry
  have positive : 0 < inputBits := by
    dsimp [inputBits, processDataBits, checkedExpansionBits]
    omega
  have nodes : certificateNodeCount certificate ≤ inputBits :=
    Nat.le_trans (certificateNodeCount_le_bits certificate) (by
      dsimp [inputBits, processDataBits, checkedExpansionBits]
      omega)
  have parameters : certificateMacroParameterTotal certificate ≤ inputBits :=
    Nat.le_trans (macroParameterTotal_le_bits certificate) (by
      dsimp [inputBits, processDataBits, checkedExpansionBits]
      omega)
  have ruleCount : rules.length ≤ inputBits :=
    Nat.le_trans (rules_length_le_bits rules) (by
      dsimp [inputBits, processDataBits, checkedExpansionBits]
      omega)
  have certPayload : certificateBits certificate ≤ inputBits := by
    dsimp [inputBits, processDataBits, checkedExpansionBits]
    omega
  have cross : certificateNodeCount certificate * (rules.length + 1) ≤
      inputBits * inputBits + inputBits := by
    calc
      certificateNodeCount certificate * (rules.length + 1) ≤
          inputBits * (rules.length + 1) := Nat.mul_le_mul_right _ nodes
      _ ≤ inputBits * (inputBits + 1) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add ruleCount (by omega))
      _ = inputBits * inputBits + inputBits := by simp [Nat.mul_add]
  have square : certificateNodeCount certificate * certificateNodeCount certificate ≤
      inputBits * inputBits := Nat.mul_le_mul nodes nodes
  have payload : certificateNodeCount certificate * certificateBits certificate ≤
      inputBits * inputBits := Nat.mul_le_mul nodes certPayload
  have model := checkFreshWithMatchCost_le_modeled_payload_polynomial rules certificate
  have costBound' : (checkFreshWithMatchCost rules certificate).2 ≤
      5 * inputBits + 3 * (inputBits * inputBits) := by omega
  have costBound : (checkFreshWithMatchCost rules certificate).2 ≤
      5 * inputBits + 3 * inputBits * inputBits := by
    simpa [Nat.mul_assoc] using costBound'
  have inputSquare : inputBits ≤ inputBits * inputBits := by
    have lower := Nat.mul_le_mul_left inputBits (show 1 ≤ inputBits by omega)
    simpa using lower
  have finalBound' : 5 * inputBits + 3 * (inputBits * inputBits) ≤
      8 * (inputBits * inputBits) := by omega
  have finalBound : 5 * inputBits + 3 * inputBits * inputBits ≤
      8 * inputBits * inputBits := by
    simpa [Nat.mul_assoc] using finalBound'
  have combined := Nat.le_trans costBound finalBound
  simpa [inputBits, Nat.pow_succ, Nat.mul_assoc] using combined

end NLisp.CertificateSize
