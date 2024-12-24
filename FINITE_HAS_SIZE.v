Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_HAS_SIZE_term_abbrevs.
Require Import HAS_SIZE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3884188 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem3884189 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem3884190 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem3884189 _100044 s) (@lem3884188 _100044 s)). Qed.
Lemma lem3884191 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem3884190 _100044 s n). Qed.
Lemma lem3884192 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem3884201 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem3884192 _100044 s n) (@lem3884191 _100044 s n)). Qed.
Lemma lem3884202 {_100437 : Type'} (s : _100437 -> Prop) (n : nat) : (@HAS_SIZE _100437 s n) = (term3 _100437 s n).
Proof. exact (@lem3884201 _100437 s n). Qed.
Lemma lem3884203 {_100437 : Type'} (s : _100437 -> Prop) : (term4 _100437 s) = (term5 _100437 s).
Proof. exact (@lem3884202 _100437 s (@CARD _100437 s)). Qed.
Lemma lem3884207 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3884208 (x : nat) : (x = x) = True.
Proof. exact (@lem3884207 nat x). Qed.
Lemma lem3884209 {_100437 : Type'} (s : _100437 -> Prop) : ((@CARD _100437 s) = (@CARD _100437 s)) = True.
Proof. exact (@lem3884208 (@CARD _100437 s)). Qed.
Lemma lem3884210 {_100437 : Type'} (s : _100437 -> Prop) : (term6 _100437 s) = (term6 _100437 s).
Proof. exact (eq_refl (term6 _100437 s)). Qed.
Lemma lem3884211 {_100437 : Type'} (s : _100437 -> Prop) : (term5 _100437 s) = (term7 _100437 s).
Proof. exact (MK_COMB (@lem3884210 _100437 s) (@lem3884209 _100437 s)). Qed.
Lemma lem3884213 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3884214 {_100437 : Type'} (s : _100437 -> Prop) : (term7 _100437 s) = (@FINITE _100437 s).
Proof. exact (@lem3884213 (@FINITE _100437 s)). Qed.
Lemma lem3884215 {_100437 : Type'} (s : _100437 -> Prop) : (term5 _100437 s) = (@FINITE _100437 s).
Proof. exact (TRANS (@lem3884211 _100437 s) (@lem3884214 _100437 s)). Qed.
Lemma lem3884216 {_100437 : Type'} (s : _100437 -> Prop) : (term4 _100437 s) = (@FINITE _100437 s).
Proof. exact (TRANS (@lem3884203 _100437 s) (@lem3884215 _100437 s)). Qed.
Lemma lem3884217 {_100437 : Type'} (s : _100437 -> Prop) : (term8 _100437 s) = (term8 _100437 s).
Proof. exact (eq_refl (term8 _100437 s)). Qed.
Lemma lem3884218 {_100437 : Type'} (s : _100437 -> Prop) : ((@FINITE _100437 s) = (term4 _100437 s)) = ((@FINITE _100437 s) = (@FINITE _100437 s)).
Proof. exact (MK_COMB (@lem3884217 _100437 s) (@lem3884216 _100437 s)). Qed.
Lemma lem3884220 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3884221 (x : Prop) : (x = x) = True.
Proof. exact (@lem3884220 Prop x). Qed.
Lemma lem3884222 {_100437 : Type'} (s : _100437 -> Prop) : ((@FINITE _100437 s) = (@FINITE _100437 s)) = True.
Proof. exact (@lem3884221 (@FINITE _100437 s)). Qed.
Lemma lem3884223 {_100437 : Type'} (s : _100437 -> Prop) : ((@FINITE _100437 s) = (term4 _100437 s)) = True.
Proof. exact (TRANS (@lem3884218 _100437 s) (@lem3884222 _100437 s)). Qed.
Lemma lem3884224 {_100437 : Type'} : (term9 _100437) = (term10 _100437).
Proof. exact (fun_ext (fun s : _100437 -> Prop => @lem3884223 _100437 s)). Qed.
Lemma lem3884225 {_100437 : Type'} : (@all (_100437 -> Prop)) = (@all (_100437 -> Prop)).
Proof. exact (eq_refl (@all (_100437 -> Prop))). Qed.
Lemma lem3884226 {_100437 : Type'} : (term11 _100437) = (term12 _100437).
Proof. exact (MK_COMB (@lem3884225 _100437) (@lem3884224 _100437)). Qed.
Lemma lem3884228 {A : Type'} (t : Prop) : (term13 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3884229 {_100437 : Type'} (t : Prop) : (term14 _100437 t) = t.
Proof. exact (@lem3884228 (_100437 -> Prop) t). Qed.
Lemma lem3884230 {_100437 : Type'} : (term12 _100437) = True.
Proof. exact (@lem3884229 _100437 True). Qed.
Lemma lem3884231 {_100437 : Type'} : (term11 _100437) = True.
Proof. exact (TRANS (@lem3884226 _100437) (@lem3884230 _100437)). Qed.
Lemma lem3884232 {_100437 : Type'} : True = (term11 _100437).
Proof. exact (SYM (@lem3884231 _100437)). Qed.
Lemma lem3884233 {_100437 : Type'} : term11 _100437.
Proof. exact (EQ_MP (@lem3884232 _100437) (@lem0)). Qed.
