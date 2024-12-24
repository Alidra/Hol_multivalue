Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7673122_term_abbrevs.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNIV_spec.
Require Import thm1855_spec.
Require Import thm7_spec.
Lemma lem7673046 {A B : Type'} (y : B) : term0 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem7673047 {A B : Type'} (y : B) : (term0 A B y) = (term1 A B y).
Proof. exact (eq_refl (term0 A B y)). Qed.
Lemma lem7673048 {A B : Type'} (y : B) : term1 A B y.
Proof. exact (EQ_MP (@lem7673047 A B y) (@lem7673046 A B y)). Qed.
Lemma lem7673049 {A B : Type'} (y : B) (s : A -> Prop) : term2 A B y s.
Proof. exact (@lem7673048 A B y s). Qed.
Lemma lem7673050 {A B : Type'} (y : B) (s : A -> Prop) : (term2 A B y s) = (term3 A B y s).
Proof. exact (eq_refl (term2 A B y s)). Qed.
Lemma lem7673051 {A B : Type'} (y : B) (s : A -> Prop) : term3 A B y s.
Proof. exact (EQ_MP (@lem7673050 A B y s) (@lem7673049 A B y s)). Qed.
Lemma lem7673052 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term4 A B y s f.
Proof. exact (@lem7673051 A B y s f). Qed.
Lemma lem7673053 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term4 A B y s f) = ((term5 A B y f s) = (term6 A B y f s)).
Proof. exact (eq_refl (term4 A B y s f)). Qed.
Lemma lem7673055 {A : Type'} (x : A) : term7 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem7673056 {A : Type'} (x : A) : (term7 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term7 A x)). Qed.
Lemma lem7673057 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem7673056 A x) (@lem7673055 A x)). Qed.
Lemma lem7673058 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem7673060 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem7673061 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (eq_refl (term8 A s)). Qed.
Lemma lem7673062 {A : Type'} (s : A -> Prop) : term9 A s.
Proof. exact (EQ_MP (@lem7673061 A s) (@lem7673060 A s)). Qed.
Lemma lem7673063 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (@lem7673062 A s t). Qed.
Lemma lem7673064 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term10 A s t) = ((s = t) = (term11 A s t)).
Proof. exact (eq_refl (term10 A s t)). Qed.
Lemma lem7673069 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term11 A s t).
Proof. exact (EQ_MP (@lem7673064 A s t) (@lem7673063 A s t)). Qed.
Lemma lem7673070 {A B : Type'} (s : type31 A B) (t : type31 A B) : (s = t) = (term12 A B s t).
Proof. exact (@lem7673069 (finite_diff A B) s t). Qed.
Lemma lem7673071 {A B : Type'} : ((@UNIV (finite_diff A B)) = (term13 A B)) = (term14 A B).
Proof. exact (@lem7673070 A B (@UNIV (finite_diff A B)) (term13 A B)). Qed.
Lemma lem7673081 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem7673058 A x) (@lem7673057 A x)). Qed.
Lemma lem7673082 {A B : Type'} (x : finite_diff A B) : (@IN (finite_diff A B) x (@UNIV (finite_diff A B))) = True.
Proof. exact (@lem7673081 (finite_diff A B) x). Qed.
Lemma lem7673083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7673084 {A B : Type'} (x : finite_diff A B) : (term15 A B x) = (@eq Prop True).
Proof. exact (MK_COMB (@lem7673083) (@lem7673082 A B x)). Qed.
Lemma lem7673086 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term5 A B y f s) = (term6 A B y f s).
Proof. exact (EQ_MP (@lem7673053 A B y f s) (@lem7673052 A B y s f)). Qed.
Lemma lem7673087 {A B : Type'} (y : finite_diff A B) (f : type1556 A B) (s : nat -> Prop) : (term16 A B y f s) = (term17 A B y f s).
Proof. exact (@lem7673086 nat (finite_diff A B) y f s). Qed.
Lemma lem7673088 {A B : Type'} (x : finite_diff A B) : (term18 A B x) = (term19 A B x).
Proof. exact (@lem7673087 A B x (@mk_finite_diff A B) (term20 A B)). Qed.
Lemma lem7673099 {A B : Type'} (x : finite_diff A B) : ((@IN (finite_diff A B) x (@UNIV (finite_diff A B))) = (term18 A B x)) = (True = (term19 A B x)).
Proof. exact (MK_COMB (@lem7673084 A B x) (@lem7673088 A B x)). Qed.
Lemma lem7673101 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem7673102 {A B : Type'} (x : finite_diff A B) : (True = (term19 A B x)) = (term19 A B x).
Proof. exact (@lem7673101 (term19 A B x)). Qed.
Lemma lem7673113 {A B : Type'} (x : finite_diff A B) : ((@IN (finite_diff A B) x (@UNIV (finite_diff A B))) = (term18 A B x)) = (term19 A B x).
Proof. exact (TRANS (@lem7673099 A B x) (@lem7673102 A B x)). Qed.
Lemma lem7673114 {A B : Type'} : (term21 A B) = (term22 A B).
Proof. exact (fun_ext (fun x : finite_diff A B => @lem7673113 A B x)). Qed.
Lemma lem7673115 {A B : Type'} : (@all (finite_diff A B)) = (@all (finite_diff A B)).
Proof. exact (eq_refl (@all (finite_diff A B))). Qed.
Lemma lem7673116 {A B : Type'} : (term14 A B) = (term23 A B).
Proof. exact (MK_COMB (@lem7673115 A B) (@lem7673114 A B)). Qed.
Lemma lem7673121 {A B : Type'} : ((@UNIV (finite_diff A B)) = (term13 A B)) = (term23 A B).
Proof. exact (TRANS (@lem7673071 A B) (@lem7673116 A B)). Qed.
Lemma lem7673122 {A B : Type'} : (term23 A B) = ((@UNIV (finite_diff A B)) = (term13 A B)).
Proof. exact (SYM (@lem7673121 A B)). Qed.
