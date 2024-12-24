Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_DIV_LMUL_term_abbrevs.
Require Import REAL_DIV_RMUL_spec.
Require Import thm0_spec.
Require Import thm1338712_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1593154 (x : real) : term0 x.
Proof. exact (@lem1593153 x). Qed.
Lemma lem1593155 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1593156 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1593155 x) (@lem1593154 x)). Qed.
Lemma lem1593157 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1593156 x y). Qed.
Lemma lem1593158 (y : real) (x : real) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1593159 (y : real) (x : real) : term3 y x.
Proof. exact (EQ_MP (@lem1593158 y x) (@lem1593157 x y)). Qed.
Lemma lem1593160 (y : real) (x : real) : (term3 y x) = ((term3 y x) = True).
Proof. exact (@lem7 (term3 y x)). Qed.
Lemma lem1593162 (x : real) : term4 x.
Proof. exact (@lem1338712 x). Qed.
Lemma lem1593163 (x : real) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1593164 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1593163 x) (@lem1593162 x)). Qed.
Lemma lem1593165 (x : real) (y : real) : term6 x y.
Proof. exact (@lem1593164 x y). Qed.
Lemma lem1593166 (y : real) (x : real) : (term6 x y) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1593183 (y : real) (x : real) : (real_mul x y) = (real_mul y x).
Proof. exact (EQ_MP (@lem1593166 y x) (@lem1593165 x y)). Qed.
Lemma lem1593184 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (@lem1593183 (real_div x y) y). Qed.
Lemma lem1593185 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1593186 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (MK_COMB (@lem1593185) (@lem1593184 x y)). Qed.
Lemma lem1593187 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1593188 (y : real) (x : real) : ((term7 x y) = x) = ((term8 x y) = x).
Proof. exact (MK_COMB (@lem1593186 x y) (@lem1593187 x)). Qed.
Lemma lem1593189 (y : real) : (term11 y) = (term11 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1593190 (y : real) (x : real) : (term12 y x) = (term3 y x).
Proof. exact (MK_COMB (@lem1593189 y) (@lem1593188 y x)). Qed.
Lemma lem1593191 (x : real) : (term13 x) = (term14 x).
Proof. exact (fun_ext (fun y : real => @lem1593190 y x)). Qed.
Lemma lem1593192 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593193 (x : real) : (term15 x) = (term1 x).
Proof. exact (MK_COMB (@lem1593192) (@lem1593191 x)). Qed.
Lemma lem1593194 : term16 = term17.
Proof. exact (fun_ext (fun x : real => @lem1593193 x)). Qed.
Lemma lem1593195 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593196 : term18 = term19.
Proof. exact (MK_COMB (@lem1593195) (@lem1593194)). Qed.
Lemma lem1593197 : term19 = term18.
Proof. exact (SYM (@lem1593196)). Qed.
Lemma lem1593207 (y : real) (x : real) : (term3 y x) = True.
Proof. exact (EQ_MP (@lem1593160 y x) (@lem1593159 y x)). Qed.
Lemma lem1593208 (x : real) : (term14 x) = term20.
Proof. exact (fun_ext (fun y : real => @lem1593207 y x)). Qed.
Lemma lem1593209 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593210 (x : real) : (term1 x) = term21.
Proof. exact (MK_COMB (@lem1593209) (@lem1593208 x)). Qed.
Lemma lem1593212 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1593213 (t : Prop) : (term23 t) = t.
Proof. exact (@lem1593212 real t). Qed.
Lemma lem1593214 : term21 = True.
Proof. exact (@lem1593213 True). Qed.
Lemma lem1593215 (x : real) : (term1 x) = True.
Proof. exact (TRANS (@lem1593210 x) (@lem1593214)). Qed.
Lemma lem1593216 : term17 = term20.
Proof. exact (fun_ext (fun x : real => @lem1593215 x)). Qed.
Lemma lem1593217 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1593218 : term19 = term21.
Proof. exact (MK_COMB (@lem1593217) (@lem1593216)). Qed.
Lemma lem1593220 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1593221 (t : Prop) : (term23 t) = t.
Proof. exact (@lem1593220 real t). Qed.
Lemma lem1593222 : term21 = True.
Proof. exact (@lem1593221 True). Qed.
Lemma lem1593223 : term19 = True.
Proof. exact (TRANS (@lem1593218) (@lem1593222)). Qed.
Lemma lem1593224 : True = term19.
Proof. exact (SYM (@lem1593223)). Qed.
Lemma lem1593225 : term19.
Proof. exact (EQ_MP (@lem1593224) (@lem0)). Qed.
Lemma lem1593226 : term18.
Proof. exact (EQ_MP (@lem1593197) (@lem1593225)). Qed.
