Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUP_SING_term_abbrevs.
Require Import FINITE_EMPTY_spec.
Require Import SUP_INSERT_FINITE_spec.
Require Import thm0_spec.
Require Import thm15249_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem5178188 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem5178190 (x : real) : term0 x.
Proof. exact (@lem5178187 x). Qed.
Lemma lem5178191 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem5178192 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem5178191 x) (@lem5178190 x)). Qed.
Lemma lem5178193 (x : real) (s : real -> Prop) : term2 x s.
Proof. exact (@lem5178192 x s). Qed.
Lemma lem5178194 (x : real) (s : real -> Prop) : (term2 x s) = (term3 x s).
Proof. exact (eq_refl (term2 x s)). Qed.
Lemma lem5178195 (x : real) (s : real -> Prop) : term3 x s.
Proof. exact (EQ_MP (@lem5178194 x s) (@lem5178193 x s)). Qed.
Lemma lem5178196 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5178197 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term4 x s) = (term5 x s).
Proof. exact (@lem5178195 x s (@lem5178196 s h1)). Qed.
Lemma lem5178210 (x : real) (s : real -> Prop) : term3 x s.
Proof. exact (fun h0 : @FINITE real s => @lem5178197 x s h0). Qed.
Lemma lem5178211 (a : real) : term6 a.
Proof. exact (@lem5178210 a (@EMPTY real)). Qed.
Lemma lem5178213 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem5178188 _92140) (@lem3596285 _92140)). Qed.
Lemma lem5178214 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5178213 real). Qed.
Lemma lem5178215 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5178214)). Qed.
Lemma lem5178216 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5178215) (@lem0)). Qed.
Lemma lem5178217 (a : real) : (term7 a) = (term8 a).
Proof. exact (@lem5178211 a (@lem5178216)). Qed.
Lemma lem5178219 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term9 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem5178220 (x : real -> Prop) (z : real) (y : real) : (term10 x y z) = y.
Proof. exact (@lem5178219 real (real -> Prop) x z y). Qed.
Lemma lem5178221 (a : real) : (term8 a) = a.
Proof. exact (@lem5178220 (@EMPTY real) (term11 a) a). Qed.
Lemma lem5178222 (a : real) : (term7 a) = a.
Proof. exact (TRANS (@lem5178217 a) (@lem5178221 a)). Qed.
Lemma lem5178223 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5178224 (a : real) : (term12 a) = (@eq real a).
Proof. exact (MK_COMB (@lem5178223) (@lem5178222 a)). Qed.
Lemma lem5178225 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5178226 (a : real) : ((term7 a) = a) = (a = a).
Proof. exact (MK_COMB (@lem5178224 a) (@lem5178225 a)). Qed.
Lemma lem5178228 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5178229 (x : real) : (x = x) = True.
Proof. exact (@lem5178228 real x). Qed.
Lemma lem5178230 (a : real) : (a = a) = True.
Proof. exact (@lem5178229 a). Qed.
Lemma lem5178231 (a : real) : ((term7 a) = a) = True.
Proof. exact (TRANS (@lem5178226 a) (@lem5178230 a)). Qed.
Lemma lem5178232 : term13 = term14.
Proof. exact (fun_ext (fun a : real => @lem5178231 a)). Qed.
Lemma lem5178233 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5178234 : term15 = term16.
Proof. exact (MK_COMB (@lem5178233) (@lem5178232)). Qed.
Lemma lem5178236 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5178237 (t : Prop) : (term18 t) = t.
Proof. exact (@lem5178236 real t). Qed.
Lemma lem5178238 : term16 = True.
Proof. exact (@lem5178237 True). Qed.
Lemma lem5178239 : term15 = True.
Proof. exact (TRANS (@lem5178234) (@lem5178238)). Qed.
Lemma lem5178240 : True = term15.
Proof. exact (SYM (@lem5178239)). Qed.
Lemma lem5178241 : term15.
Proof. exact (EQ_MP (@lem5178240) (@lem0)). Qed.
