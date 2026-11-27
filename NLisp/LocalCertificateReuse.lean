import NLisp.TypedExpansion

/-! # Local typing-certificate reuse under copying

This module makes the typed-substitution boundary explicit. The source
certificate is represented by intrinsically typed syntax; copying a hole is
modeled by a typed substitution, which may use the same replacement at any
number of occurrences. This proves the abstract typed layer only. It does not
yet show that the C copy routines implement this substitution or that their
fresh binder tokens are disjoint across copies.
-/

namespace NLisp.LocalCertificateReuse

open NLisp.TypedExpansion

/-- A local certificate pairs the source syntax with its context and result
type. Because `Expr` is indexed by both, an ill-typed source certificate
cannot be constructed. -/
structure LocalCertificate (context : List Ty) where
  result : Ty
  expression : Expr context result

/-- The checker-facing erased term carried by a local certificate. -/
def LocalCertificate.term (certificate : LocalCertificate context) : Term :=
  certificate.expression.erase

/-- Reuse a local certificate through a type-preserving substitution. A
substitution can duplicate source syntax: multiple variable occurrences may
map to the same replacement expression. The result keeps the certificate's
result type while changing its context to the substitution target. -/
def LocalCertificate.transport (certificate : LocalCertificate context)
    (substitution : Sub context target) : LocalCertificate target :=
  ⟨certificate.result, certificate.expression.subst substitution⟩

/-- The transported certificate remains acceptable to the independent
extrinsic typing relation after erasure. -/
theorem LocalCertificate.transport_sound (certificate : LocalCertificate context)
    (substitution : Sub context target) :
    HasType target (certificate.transport substitution).term certificate.result := by
  exact Expr.subst_hasType certificate.expression substitution

/-- Instantiating a one-hole typed template is a concrete copying case. The
hole may occur zero, one, or many times in the template; all occurrences are
replaced by the same typed argument, and the resulting erased syntax retains
the template result type. -/
theorem repeated_hole_copy_sound (body : Expr [argumentTy] result)
    (argument : Expr context argumentTy) :
    HasType context (body.subst (singleHoleSub argument)).erase result := by
  exact Expr.singleHoleSubstitution_hasType body argument

/-- The same result packaged as a reusable local certificate. -/
def repeated_hole_copy_certificate (body : Expr [argumentTy] result)
    (argument : Expr context argumentTy) : LocalCertificate context :=
  ⟨result, body.subst (singleHoleSub argument)⟩

theorem repeated_hole_copy_certificate_sound (body : Expr [argumentTy] result)
    (argument : Expr context argumentTy) :
    HasType context (repeated_hole_copy_certificate body argument).term result := by
  exact repeated_hole_copy_sound body argument

end NLisp.LocalCertificateReuse
