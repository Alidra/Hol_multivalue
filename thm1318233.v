Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1318233_term_abbrevs.
Require Import NADD_EQ_REFL_spec.
Require Import NADD_EQ_TRANS_spec.
Require Import NADD_INV_WELLDEF_spec.
Require Import thm1317744_spec.
Require Import thm32_spec.
Require Import thm9127_spec.
Lemma lem1318149 : hreal_inv = term0.
Proof. exact (@hreal_inv_def). Qed.
Lemma lem1318150 (x : hreal) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1318151 (x : hreal) : (hreal_inv x) = (term1 x).
Proof. exact (MK_COMB (@lem1318149) (@lem1318150 x)). Qed.
Lemma lem1318152 (x : hreal) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1318153 (x : hreal) : (term3 x) = (term3 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1318154 (x : hreal) : ((hreal_inv x) = (term1 x)) = ((hreal_inv x) = (term2 x)).
Proof. exact (MK_COMB (@lem1318153 x) (@lem1318152 x)). Qed.
Lemma lem1318155 (x : hreal) : (hreal_inv x) = (term2 x).
Proof. exact (EQ_MP (@lem1318154 x) (@lem1318151 x)). Qed.
Lemma lem1318156 (x : nadd) : (term4 x) = ((term5 x) = (nadd_eq x)).
Proof. exact (@lem1317744 (nadd_eq x)). Qed.
Lemma lem1318157 (x : nadd) : (nadd_eq x) = (nadd_eq x).
Proof. exact (eq_refl (nadd_eq x)). Qed.
Lemma lem1318158 (x : nadd) : term4 x.
Proof. exact (ex_intro (term6 x) x (@lem1318157 x)). Qed.
Lemma lem1318159 (x : nadd) : (term5 x) = (nadd_eq x).
Proof. exact (EQ_MP (@lem1318156 x) (@lem1318158 x)). Qed.
Lemma lem1318160 (x : nadd) : (term7 x) = (term8 x).
Proof. exact (@lem1318155 (term9 x)). Qed.
Lemma lem1318161 (x : nadd) : (term5 x) = (nadd_eq x).
Proof. exact (@lem1318159 x). Qed.
Lemma lem1318162 (x : nadd) : (term10 x) = (term10 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1318163 (x : nadd) : (term11 x) = (term12 x).
Proof. exact (MK_COMB (@lem1318162 x) (@lem1318161 x)). Qed.
Lemma lem1318164 (x : nadd) : (term12 x) = ((term7 x) = (term13 x)).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1318165 (x : nadd) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1318166 (x : nadd) : ((term11 x) = (term12 x)) = ((term11 x) = ((term7 x) = (term13 x))).
Proof. exact (MK_COMB (@lem1318165 x) (@lem1318164 x)). Qed.
Lemma lem1318167 (x : nadd) : (term11 x) = ((term7 x) = (term8 x)).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1318168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1318169 (x : nadd) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1318168) (@lem1318167 x)). Qed.
Lemma lem1318170 (x : nadd) : ((term7 x) = (term13 x)) = ((term7 x) = (term13 x)).
Proof. exact (eq_refl ((term7 x) = (term13 x))). Qed.
Lemma lem1318171 (x : nadd) : ((term11 x) = ((term7 x) = (term13 x))) = (((term7 x) = (term8 x)) = ((term7 x) = (term13 x))).
Proof. exact (MK_COMB (@lem1318169 x) (@lem1318170 x)). Qed.
Lemma lem1318172 (x : nadd) : ((term11 x) = (term12 x)) = (((term7 x) = (term8 x)) = ((term7 x) = (term13 x))).
Proof. exact (TRANS (@lem1318166 x) (@lem1318171 x)). Qed.
Lemma lem1318173 (x : nadd) : ((term7 x) = (term8 x)) = ((term7 x) = (term13 x)).
Proof. exact (EQ_MP (@lem1318172 x) (@lem1318163 x)). Qed.
Lemma lem1318174 (x : nadd) : (term7 x) = (term13 x).
Proof. exact (EQ_MP (@lem1318173 x) (@lem1318160 x)). Qed.
Lemma lem1318175 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : term16 u x x'.
Proof. exact (h1). Qed.
Lemma lem1318176 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : nadd_eq x x'.
Proof. exact (proj2 (@lem1318175 u x x' h1)). Qed.
Lemma lem1318177 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : term17 x' u.
Proof. exact (proj1 (@lem1318175 u x x' h1)). Qed.
Lemma lem1318178 (x : nadd) : term18 x.
Proof. exact (@lem1317729 x). Qed.
Lemma lem1318179 (x : nadd) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1318180 (x : nadd) : term19 x.
Proof. exact (EQ_MP (@lem1318179 x) (@lem1318178 x)). Qed.
Lemma lem1318181 (x : nadd) (y : nadd) : term20 x y.
Proof. exact (@lem1318180 x y). Qed.
Lemma lem1318182 (x : nadd) (y : nadd) : (term20 x y) = (term21 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1318185 (x : nadd) (y : nadd) : term21 x y.
Proof. exact (EQ_MP (@lem1318182 x y) (@lem1318181 x y)). Qed.
Lemma lem1318186 (x : nadd) (x' : nadd) : term21 x x'.
Proof. exact (@lem1318185 x x'). Qed.
Lemma lem1318187 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : term22 x x'.
Proof. exact (@lem1318186 x x' (@lem1318176 u x x' h1)). Qed.
Lemma lem1318188 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : term23 x x' u.
Proof. exact (conj (@lem1318187 u x x' h1) (@lem1318177 u x x' h1)). Qed.
Lemma lem1318189 (x : nadd) : term24 x.
Proof. exact (@lem1268295 x). Qed.
Lemma lem1318190 (x : nadd) : (term24 x) = (term25 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1318191 (x : nadd) : term25 x.
Proof. exact (EQ_MP (@lem1318190 x) (@lem1318189 x)). Qed.
Lemma lem1318192 (x : nadd) (y : nadd) : term26 x y.
Proof. exact (@lem1318191 x y). Qed.
Lemma lem1318193 (y : nadd) (x : nadd) : (term26 x y) = (term27 y x).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1318194 (y : nadd) (x : nadd) : term27 y x.
Proof. exact (EQ_MP (@lem1318193 y x) (@lem1318192 x y)). Qed.
Lemma lem1318195 (y : nadd) (x : nadd) (z : nadd) : term28 y x z.
Proof. exact (@lem1318194 y x z). Qed.
Lemma lem1318196 (y : nadd) (x : nadd) (z : nadd) : (term28 y x z) = (term29 y x z).
Proof. exact (eq_refl (term28 y x z)). Qed.
Lemma lem1318199 (y : nadd) (x : nadd) (z : nadd) : term29 y x z.
Proof. exact (EQ_MP (@lem1318196 y x z) (@lem1318195 y x z)). Qed.
Lemma lem1318200 (x' : nadd) (x : nadd) (u : nadd) : term30 x' x u.
Proof. exact (@lem1318199 (nadd_inv x') (nadd_inv x) u). Qed.
Lemma lem1318201 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : term17 x u.
Proof. exact (@lem1318200 x' x u (@lem1318188 u x x' h1)). Qed.
Lemma lem1318202 (u : nadd) (x : nadd) (h1 : term31 u x) : term31 u x.
Proof. exact (h1). Qed.
Lemma lem1318203 (u : nadd) (x : nadd) (h1 : term31 u x) : term17 x u.
Proof. exact (ex_elim (@lem1318202 u x h1) (fun x' : nadd => fun h0 : term32 u x x' => @lem1318201 u x x' h0)). Qed.
Lemma lem1318204 (x : nadd) (u : nadd) (h1 : term17 x u) : term17 x u.
Proof. exact (h1). Qed.
Lemma lem1318205 (x : nadd) : term33 x.
Proof. exact (@lem1267990 x). Qed.
Lemma lem1318206 (x : nadd) : (term33 x) = (nadd_eq x x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem1318207 (x : nadd) : nadd_eq x x.
Proof. exact (EQ_MP (@lem1318206 x) (@lem1318205 x)). Qed.
Lemma lem1318208 (x : nadd) (u : nadd) (h1 : term17 x u) : term34 u x.
Proof. exact (conj (@lem1318204 x u h1) (@lem1318207 x)). Qed.
Lemma lem1318209 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : term16 u x x'.
Proof. exact (h1). Qed.
Lemma lem1318210 (u : nadd) (x : nadd) (x' : nadd) (h1 : term16 u x x') : term31 u x.
Proof. exact (ex_intro (term32 u x) x' (@lem1318209 u x x' h1)). Qed.
Lemma lem1318213 (x' : nadd) (u : nadd) (x : nadd) : term35 x' u x.
Proof. exact (fun h0 : term16 u x x' => @lem1318210 u x x' h0). Qed.
Lemma lem1318214 (u : nadd) (x : nadd) : term36 u x.
Proof. exact (@lem1318213 x u x). Qed.
Lemma lem1318215 (x : nadd) (u : nadd) (h1 : term17 x u) : term31 u x.
Proof. exact (@lem1318214 u x (@lem1318208 x u h1)). Qed.
Lemma lem1318216 (u : nadd) (x : nadd) : term37 u x.
Proof. exact (fun h0 : term17 x u => @lem1318215 x u h0). Qed.
Lemma lem1318217 (x : nadd) (u : nadd) : term38 x u.
Proof. exact (fun h0 : term31 u x => @lem1318203 u x h0). Qed.
Lemma lem1318218 (u : nadd) (x : nadd) : term39 u x.
Proof. exact (conj (@lem1318217 x u) (@lem1318216 u x)). Qed.
Lemma lem1318219 (x : nadd) (u : nadd) : (term39 u x) = ((term31 u x) = (term17 x u)).
Proof. exact (@lem32 (term31 u x) (term17 x u)). Qed.
Lemma lem1318220 (x : nadd) (u : nadd) : (term31 u x) = (term17 x u).
Proof. exact (EQ_MP (@lem1318219 x u) (@lem1318218 u x)). Qed.
Lemma lem1318221 (x : nadd) : (term40 x) = (term41 x).
Proof. exact (fun_ext (fun u : nadd => @lem1318220 x u)). Qed.
Lemma lem1318222 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1318223 (x : nadd) : (term13 x) = (term42 x).
Proof. exact (MK_COMB (@lem1318222) (@lem1318221 x)). Qed.
Lemma lem1318224 (x : nadd) : (term7 x) = (term42 x).
Proof. exact (TRANS (@lem1318174 x) (@lem1318223 x)). Qed.
Lemma lem1318225 (t : nadd -> Prop) : (term43 t) = t.
Proof. exact (@lem9127 nadd Prop t). Qed.
Lemma lem1318228 (x : nadd) : (term41 x) = (term44 x).
Proof. exact (@lem1318225 (term44 x)). Qed.
Lemma lem1318229 : mk_hreal = mk_hreal.
Proof. exact (eq_refl mk_hreal). Qed.
Lemma lem1318230 (x : nadd) : (term42 x) = (term45 x).
Proof. exact (MK_COMB (@lem1318229) (@lem1318228 x)). Qed.
Lemma lem1318231 (x : nadd) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1318232 (x : nadd) : ((term7 x) = (term42 x)) = ((term7 x) = (term45 x)).
Proof. exact (MK_COMB (@lem1318231 x) (@lem1318230 x)). Qed.
Lemma lem1318233 (x : nadd) : (term7 x) = (term45 x).
Proof. exact (EQ_MP (@lem1318232 x) (@lem1318224 x)). Qed.
