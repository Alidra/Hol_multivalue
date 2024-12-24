Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_ADD2_term_abbrevs.
Require Import REAL_LE_ADD2_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2302222 (w : int) : term0 w.
Proof. exact (@lem1502113 (real_of_int w)). Qed.
Lemma lem2302223 (w : int) : (term0 w) = (term1 w).
Proof. exact (eq_refl (term0 w)). Qed.
Lemma lem2302224 (w : int) : term1 w.
Proof. exact (EQ_MP (@lem2302223 w) (@lem2302222 w)). Qed.
Lemma lem2302225 (w : int) (x : int) : term2 w x.
Proof. exact (@lem2302224 w (real_of_int x)). Qed.
Lemma lem2302226 (w : int) (x : int) : (term2 w x) = (term3 w x).
Proof. exact (eq_refl (term2 w x)). Qed.
Lemma lem2302227 (w : int) (x : int) : term3 w x.
Proof. exact (EQ_MP (@lem2302226 w x) (@lem2302225 w x)). Qed.
Lemma lem2302228 (w : int) (x : int) (y : int) : term4 w x y.
Proof. exact (@lem2302227 w x (real_of_int y)). Qed.
Lemma lem2302229 (w : int) (y : int) (x : int) : (term4 w x y) = (term5 w y x).
Proof. exact (eq_refl (term4 w x y)). Qed.
Lemma lem2302230 (w : int) (y : int) (x : int) : term5 w y x.
Proof. exact (EQ_MP (@lem2302229 w y x) (@lem2302228 w x y)). Qed.
Lemma lem2302231 (w : int) (y : int) (x : int) (z : int) : term6 w y x z.
Proof. exact (@lem2302230 w y x (real_of_int z)). Qed.
Lemma lem2302232 (w : int) (y : int) (x : int) (z : int) : (term6 w y x z) = (term7 w y x z).
Proof. exact (eq_refl (term6 w y x z)). Qed.
Lemma lem2302233 (w : int) (y : int) (x : int) (z : int) : term7 w y x z.
Proof. exact (EQ_MP (@lem2302232 w y x z) (@lem2302231 w y x z)). Qed.
Lemma lem2302235 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302236 (w : int) (x : int) : (term8 w x) = (int_le w x).
Proof. exact (@lem2302235 w x). Qed.
Lemma lem2302237 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2302238 (w : int) (x : int) : (term9 w x) = (term10 w x).
Proof. exact (MK_COMB (@lem2302237) (@lem2302236 w x)). Qed.
Lemma lem2302240 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302241 (y : int) (z : int) : (term8 y z) = (int_le y z).
Proof. exact (@lem2302240 y z). Qed.
Lemma lem2302242 (w : int) (x : int) (y : int) (z : int) : (term11 w x y z) = (term12 w x y z).
Proof. exact (MK_COMB (@lem2302238 w x) (@lem2302241 y z)). Qed.
Lemma lem2302243 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2302244 (w : int) (x : int) (y : int) (z : int) : (term13 w x y z) = (term14 w x y z).
Proof. exact (MK_COMB (@lem2302243) (@lem2302242 w x y z)). Qed.
Lemma lem2302246 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302247 (w : int) (y : int) : (term15 w y) = (term16 w y).
Proof. exact (@lem2302246 w y). Qed.
Lemma lem2302248 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2302249 (w : int) (y : int) : (term17 w y) = (term18 w y).
Proof. exact (MK_COMB (@lem2302248) (@lem2302247 w y)). Qed.
Lemma lem2302251 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2302252 (x : int) (z : int) : (term15 x z) = (term16 x z).
Proof. exact (@lem2302251 x z). Qed.
Lemma lem2302253 (w : int) (y : int) (x : int) (z : int) : (term19 w y x z) = (term20 w y x z).
Proof. exact (MK_COMB (@lem2302249 w y) (@lem2302252 x z)). Qed.
Lemma lem2302255 (x : int) (y : int) : (term8 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2302256 (w : int) (y : int) (x : int) (z : int) : (term20 w y x z) = (term21 w y x z).
Proof. exact (@lem2302255 (int_add w y) (int_add x z)). Qed.
Lemma lem2302257 (w : int) (y : int) (x : int) (z : int) : (term19 w y x z) = (term21 w y x z).
Proof. exact (TRANS (@lem2302253 w y x z) (@lem2302256 w y x z)). Qed.
Lemma lem2302258 (w : int) (y : int) (x : int) (z : int) : (term7 w y x z) = (term22 w y x z).
Proof. exact (MK_COMB (@lem2302244 w x y z) (@lem2302257 w y x z)). Qed.
Lemma lem2302259 (w : int) (y : int) (x : int) (z : int) : term22 w y x z.
Proof. exact (EQ_MP (@lem2302258 w y x z) (@lem2302233 w y x z)). Qed.
Lemma lem2302260 (w : int) (y : int) (x : int) : term23 w y x.
Proof. exact (fun z : int => @lem2302259 w y x z). Qed.
Lemma lem2302261 (w : int) (x : int) : term24 w x.
Proof. exact (fun y : int => @lem2302260 w y x). Qed.
Lemma lem2302262 (w : int) : term25 w.
Proof. exact (fun x : int => @lem2302261 w x). Qed.
Lemma lem2302263 : term26.
Proof. exact (fun w : int => @lem2302262 w). Qed.
