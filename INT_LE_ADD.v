Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_ADD_term_abbrevs.
Require Import REAL_LE_ADD_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302173 (x : int) : term0 x.
Proof. exact (@lem1373458 (real_of_int x)). Qed.
Lemma lem2302174 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2302175 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2302174 x) (@lem2302173 x)). Qed.
Lemma lem2302176 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2302175 x (real_of_int y)). Qed.
Lemma lem2302177 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2302178 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2302177 x y) (@lem2302176 x y)). Qed.
Lemma lem2302180 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302181 : term5 = term6.
Proof. exact (@lem2302180 (NUMERAL 0)). Qed.
Lemma lem2302182 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302183 : term7 = term8.
Proof. exact (MK_COMB (@lem2302182) (@lem2302181)). Qed.
Lemma lem2302184 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2302185 (x : int) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem2302183) (@lem2302184 x)). Qed.
Lemma lem2302187 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302188 (x : int) : (term10 x) = (term12 x).
Proof. exact (@lem2302187 term13 x). Qed.
Lemma lem2302189 (x : int) : (term9 x) = (term12 x).
Proof. exact (TRANS (@lem2302185 x) (@lem2302188 x)). Qed.
Lemma lem2302190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302191 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2302190) (@lem2302189 x)). Qed.
Lemma lem2302193 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302194 : term5 = term6.
Proof. exact (@lem2302193 (NUMERAL 0)). Qed.
Lemma lem2302195 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302196 : term7 = term8.
Proof. exact (MK_COMB (@lem2302195) (@lem2302194)). Qed.
Lemma lem2302197 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2302198 (y : int) : (term9 y) = (term10 y).
Proof. exact (MK_COMB (@lem2302196) (@lem2302197 y)). Qed.
Lemma lem2302200 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302201 (y : int) : (term10 y) = (term12 y).
Proof. exact (@lem2302200 term13 y). Qed.
Lemma lem2302202 (y : int) : (term9 y) = (term12 y).
Proof. exact (TRANS (@lem2302198 y) (@lem2302201 y)). Qed.
Lemma lem2302203 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem2302191 x) (@lem2302202 y)). Qed.
Lemma lem2302204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302205 (x : int) (y : int) : (term18 x y) = (term19 x y).
Proof. exact (MK_COMB (@lem2302204) (@lem2302203 x y)). Qed.
Lemma lem2302207 (n : nat) : (real_of_num n) = (term4 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2302208 : term5 = term6.
Proof. exact (@lem2302207 (NUMERAL 0)). Qed.
Lemma lem2302209 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302210 : term7 = term8.
Proof. exact (MK_COMB (@lem2302209) (@lem2302208)). Qed.
Lemma lem2302212 (x : int) (y : int) : (term20 x y) = (term21 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302213 (x : int) (y : int) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem2302210) (@lem2302212 x y)). Qed.
Lemma lem2302215 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302216 (x : int) (y : int) : (term23 x y) = (term24 x y).
Proof. exact (@lem2302215 term13 (int_add x y)). Qed.
Lemma lem2302217 (x : int) (y : int) : (term22 x y) = (term24 x y).
Proof. exact (TRANS (@lem2302213 x y) (@lem2302216 x y)). Qed.
Lemma lem2302218 (x : int) (y : int) : (term3 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem2302205 x y) (@lem2302217 x y)). Qed.
Lemma lem2302219 (x : int) (y : int) : term25 x y.
Proof. exact (EQ_MP (@lem2302218 x y) (@lem2302178 x y)). Qed.
Lemma lem2302220 (x : int) : term26 x.
Proof. exact (fun y : int => @lem2302219 x y). Qed.
Lemma lem2302221 : term27.
Proof. exact (fun x : int => @lem2302220 x). Qed.
