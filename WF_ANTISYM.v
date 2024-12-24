Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_ANTISYM_term_abbrevs.
Require Import WF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem367122 {A : Type'} (lt2 : type1402 A) : term0 A lt2.
Proof. exact (@lem303045 A lt2). Qed.
Lemma lem367123 {A : Type'} (lt2 : type1402 A) : (term0 A lt2) = ((@WF A lt2) = (term1 A lt2)).
Proof. exact (eq_refl (term0 A lt2)). Qed.
Lemma lem367125 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : @WF A lt2.
Proof. exact (h1). Qed.
Lemma lem367126 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term2 A lt2 y x) : term2 A lt2 y x.
Proof. exact (h1). Qed.
Lemma lem367127 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (h1). Qed.
Lemma lem367128 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367130 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (EQ_MP (@lem367123 A lt2) (@lem367122 A lt2)). Qed.
Lemma lem367131 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term1 A lt2).
Proof. exact (@lem367130 A lt2). Qed.
Lemma lem367132 {A : Type'} (lt2 : type1402 A) (h1 : @WF A lt2) : term1 A lt2.
Proof. exact (EQ_MP (@lem367131 A lt2) (@lem367125 A lt2 h1)). Qed.
Lemma lem367133 {A : Type'} (lt2 : type1402 A) (h1 : term1 A lt2) : term1 A lt2.
Proof. exact (h1). Qed.
Lemma lem367134 {A : Type'} (x : A) (y : A) (lt2 : type1402 A) (h1 : term1 A lt2) : term3 A lt2 x y.
Proof. exact (@lem367133 A lt2 h1 (term4 A x y)). Qed.
Lemma lem367135 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term3 A lt2 x y) = (term5 A lt2 x y).
Proof. exact (eq_refl (term3 A lt2 x y)). Qed.
Lemma lem367136 {A : Type'} (x : A) (y : A) (lt2 : type1402 A) (h1 : term1 A lt2) : term5 A lt2 x y.
Proof. exact (EQ_MP (@lem367135 A lt2 x y) (@lem367134 A x y lt2 h1)). Qed.
Lemma lem367138 (p : Prop) : p = (term6 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem367139 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term7 A lt2 x y) = (term8 A lt2 x y).
Proof. exact (@lem367138 (term7 A lt2 x y)). Qed.
Lemma lem367140 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term8 A lt2 x y) = (term7 A lt2 x y).
Proof. exact (SYM (@lem367139 A lt2 x y)). Qed.
Lemma lem367141 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term9 A lt2 x y) : term9 A lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367144 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term10 A lt2 x y) : term10 A lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367145 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : term11 A lt2 x y.
Proof. exact (fun h0 : term10 A lt2 x y => @lem367144 A lt2 x y h0). Qed.
Lemma lem367146 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term11 A lt2 x y) : term11 A lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367147 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term10 A lt2 x y) : term10 A lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367148 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term11 A lt2 x y) (h2 : term10 A lt2 x y) : term10 A lt2 x y.
Proof. exact (@lem367146 A lt2 x y h1 (@lem367147 A lt2 x y h2)). Qed.
Lemma lem367149 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term10 A lt2 x y) : term12 A lt2 x y.
Proof. exact (fun h0 : term11 A lt2 x y => @lem367148 A lt2 x y h0 h1). Qed.
Lemma lem367150 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term11 A lt2 x y) : term11 A lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367151 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term11 A lt2 x y) (h2 : term10 A lt2 x y) : term10 A lt2 x y.
Proof. exact (@lem367149 A lt2 x y h2 (@lem367150 A lt2 x y h1)). Qed.
Lemma lem367152 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term11 A lt2 x y) : term11 A lt2 x y.
Proof. exact (fun h0 : term10 A lt2 x y => @lem367151 A lt2 x y h1 h0). Qed.
Lemma lem367153 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : term13 A lt2 x y.
Proof. exact (fun h0 : term11 A lt2 x y => @lem367152 A lt2 x y h0). Qed.
Lemma lem367156 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : term11 A lt2 x y.
Proof. exact (@lem367153 A lt2 x y (@lem367145 A lt2 x y)). Qed.
Lemma lem367157 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : term11 A lt2 x y.
Proof. exact (@lem367156 A lt2 x y). Qed.
Lemma lem367175 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem367176 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term8 A lt2 x y) = (term14 A lt2 x y).
Proof. exact (@lem367175 (term9 A lt2 x y)). Qed.
Lemma lem367178 (t : Prop) : (term15 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem367179 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term14 A lt2 x y) = (term7 A lt2 x y).
Proof. exact (@lem367178 (term7 A lt2 x y)). Qed.
Lemma lem367181 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem367182 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term7 A lt2 x y) = (term16 A lt2 x y).
Proof. exact (@lem367181 (term5 A lt2 x y)). Qed.
Lemma lem367183 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term14 A lt2 x y) = (term16 A lt2 x y).
Proof. exact (TRANS (@lem367179 A lt2 x y) (@lem367182 A lt2 x y)). Qed.
Lemma lem367184 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term8 A lt2 x y) = (term16 A lt2 x y).
Proof. exact (TRANS (@lem367176 A lt2 x y) (@lem367183 A lt2 x y)). Qed.
Lemma lem367233 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term17 A lt2 y x) = (term17 A lt2 y x).
Proof. exact (eq_refl (term17 A lt2 y x)). Qed.
Lemma lem367234 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term18 A lt2 x y) = (term19 A lt2 x y).
Proof. exact (MK_COMB (@lem367233 A lt2 y x) (@lem367184 A lt2 x y)). Qed.
Lemma lem367237 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term17 A lt2 x y) = (term17 A lt2 x y).
Proof. exact (eq_refl (term17 A lt2 x y)). Qed.
Lemma lem367238 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term10 A lt2 x y) = (term20 A lt2 x y).
Proof. exact (MK_COMB (@lem367237 A lt2 x y) (@lem367234 A lt2 x y)). Qed.
Lemma lem367241 {A : Type'} (x : A) (y : A) : (term21 A x y) = (term22 A x y).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem367238 A lt2 x y)). Qed.
Lemma lem367242 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem367243 {A : Type'} (x : A) (y : A) : (term23 A x y) = (term24 A x y).
Proof. exact (MK_COMB (@lem367242 A) (@lem367241 A x y)). Qed.
Lemma lem367248 {A : Type'} (y : A) : (term25 A y) = (term26 A y).
Proof. exact (fun_ext (fun x : A => @lem367243 A x y)). Qed.
Lemma lem367249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367250 {A : Type'} (y : A) : (term27 A y) = (term28 A y).
Proof. exact (MK_COMB (@lem367249 A) (@lem367248 A y)). Qed.
Lemma lem367255 {A : Type'} : (term29 A) = (term30 A).
Proof. exact (fun_ext (fun y : A => @lem367250 A y)). Qed.
Lemma lem367256 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367257 {A : Type'} : (term31 A) = (term32 A).
Proof. exact (MK_COMB (@lem367256 A) (@lem367255 A)). Qed.
Lemma lem367262 {A : Type'} (x : A) (x' : A) (y : A) : (term33 A x y x') = (term34 A x x' y).
Proof. exact (eq_refl (term33 A x y x')). Qed.
Lemma lem367263 {A : Type'} (x : A) (y : A) : (term35 A x y) = (term4 A x y).
Proof. exact (fun_ext (fun x' : A => @lem367262 A x x' y)). Qed.
Lemma lem367264 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem367265 {A : Type'} (x : A) (y : A) : (term36 A x y) = (term37 A x y).
Proof. exact (MK_COMB (@lem367264 A) (@lem367263 A x y)). Qed.
Lemma lem367266 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem367267 {A : Type'} (x : A) (y : A) : (term38 A x y) = (term39 A x y).
Proof. exact (MK_COMB (@lem367266) (@lem367265 A x y)). Qed.
Lemma lem367268 {A : Type'} (x : A) (x' : A) (y : A) : (term33 A x y x') = (term34 A x x' y).
Proof. exact (eq_refl (term33 A x y x')). Qed.
Lemma lem367269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem367270 {A : Type'} (x : A) (x' : A) (y : A) : (term40 A x y x') = (term41 A x x' y).
Proof. exact (MK_COMB (@lem367269) (@lem367268 A x x' y)). Qed.
Lemma lem367271 {A : Type'} (x : A) (y' : A) (y : A) : (term33 A x y y') = (term34 A x y' y).
Proof. exact (eq_refl (term33 A x y y')). Qed.
Lemma lem367272 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem367273 {A : Type'} (x : A) (y' : A) (y : A) : (term42 A x y y') = (term43 A x y' y).
Proof. exact (MK_COMB (@lem367272) (@lem367271 A x y' y)). Qed.
Lemma lem367274 {A : Type'} (lt2 : type1402 A) (y' : A) (x' : A) : (term17 A lt2 y' x') = (term17 A lt2 y' x').
Proof. exact (eq_refl (term17 A lt2 y' x')). Qed.
Lemma lem367275 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y' : A) (y : A) : (term44 A lt2 x' x y y') = (term45 A lt2 x' x y' y).
Proof. exact (MK_COMB (@lem367274 A lt2 y' x') (@lem367273 A x y' y)). Qed.
Lemma lem367276 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term46 A lt2 x' x y) = (term47 A lt2 x' x y).
Proof. exact (fun_ext (fun y' : A => @lem367275 A lt2 x' x y' y)). Qed.
Lemma lem367277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367278 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term48 A lt2 x' x y) = (term49 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367277 A) (@lem367276 A lt2 x' x y)). Qed.
Lemma lem367279 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term50 A lt2 x' x y) = (term51 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367270 A x x' y) (@lem367278 A lt2 x' x y)). Qed.
Lemma lem367280 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term52 A lt2 x y) = (term53 A lt2 x y).
Proof. exact (fun_ext (fun x' : A => @lem367279 A lt2 x' x y)). Qed.
Lemma lem367281 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem367282 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term54 A lt2 x y) = (term55 A lt2 x y).
Proof. exact (MK_COMB (@lem367281 A) (@lem367280 A lt2 x y)). Qed.
Lemma lem367283 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term5 A lt2 x y) = (term56 A lt2 x y).
Proof. exact (MK_COMB (@lem367267 A x y) (@lem367282 A lt2 x y)). Qed.
Lemma lem367284 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem367285 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term16 A lt2 x y) = (term57 A lt2 x y).
Proof. exact (MK_COMB (@lem367284) (@lem367283 A lt2 x y)). Qed.
Lemma lem367286 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term17 A lt2 y x) = (term17 A lt2 y x).
Proof. exact (eq_refl (term17 A lt2 y x)). Qed.
Lemma lem367287 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term19 A lt2 x y) = (term58 A lt2 x y).
Proof. exact (MK_COMB (@lem367286 A lt2 y x) (@lem367285 A lt2 x y)). Qed.
Lemma lem367288 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term17 A lt2 x y) = (term17 A lt2 x y).
Proof. exact (eq_refl (term17 A lt2 x y)). Qed.
Lemma lem367289 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term20 A lt2 x y) = (term59 A lt2 x y).
Proof. exact (MK_COMB (@lem367288 A lt2 x y) (@lem367287 A lt2 x y)). Qed.
Lemma lem367290 {A : Type'} (x : A) (y : A) : (term22 A x y) = (term60 A x y).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem367289 A lt2 x y)). Qed.
Lemma lem367291 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem367292 {A : Type'} (x : A) (y : A) : (term24 A x y) = (term61 A x y).
Proof. exact (MK_COMB (@lem367291 A) (@lem367290 A x y)). Qed.
Lemma lem367293 {A : Type'} (y : A) : (term26 A y) = (term62 A y).
Proof. exact (fun_ext (fun x : A => @lem367292 A x y)). Qed.
Lemma lem367294 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367295 {A : Type'} (y : A) : (term28 A y) = (term63 A y).
Proof. exact (MK_COMB (@lem367294 A) (@lem367293 A y)). Qed.
Lemma lem367296 {A : Type'} : (term30 A) = (term64 A).
Proof. exact (fun_ext (fun y : A => @lem367295 A y)). Qed.
Lemma lem367297 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367298 {A : Type'} : (term32 A) = (term65 A).
Proof. exact (MK_COMB (@lem367297 A) (@lem367296 A)). Qed.
Lemma lem367301 {A : Type'} : (term31 A) = (term65 A).
Proof. exact (TRANS (@lem367257 A) (@lem367298 A)). Qed.
Lemma lem367312 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y' : A) (y : A) : (term45 A lt2 x' x y' y) = (term45 A lt2 x' x y' y).
Proof. exact (eq_refl (term45 A lt2 x' x y' y)). Qed.
Lemma lem367313 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term47 A lt2 x' x y) = (term47 A lt2 x' x y).
Proof. exact (fun_ext (fun y' : A => @lem367312 A lt2 x' x y' y)). Qed.
Lemma lem367314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367315 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term49 A lt2 x' x y) = (term49 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367314 A) (@lem367313 A lt2 x' x y)). Qed.
Lemma lem367322 {A : Type'} (x : A) (x' : A) (y : A) : (term41 A x x' y) = (term41 A x x' y).
Proof. exact (eq_refl (term41 A x x' y)). Qed.
Lemma lem367323 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term51 A lt2 x' x y) = (term51 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367322 A x x' y) (@lem367315 A lt2 x' x y)). Qed.
Lemma lem367324 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term53 A lt2 x y) = (term53 A lt2 x y).
Proof. exact (fun_ext (fun x' : A => @lem367323 A lt2 x' x y)). Qed.
Lemma lem367325 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem367326 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term55 A lt2 x y) = (term55 A lt2 x y).
Proof. exact (MK_COMB (@lem367325 A) (@lem367324 A lt2 x y)). Qed.
Lemma lem367331 {A : Type'} (x : A) (x' : A) (y : A) : (term34 A x x' y) = (term34 A x x' y).
Proof. exact (eq_refl (term34 A x x' y)). Qed.
Lemma lem367332 {A : Type'} (x : A) (y : A) : (term4 A x y) = (term4 A x y).
Proof. exact (fun_ext (fun x' : A => @lem367331 A x x' y)). Qed.
Lemma lem367333 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem367334 {A : Type'} (x : A) (y : A) : (term37 A x y) = (term37 A x y).
Proof. exact (MK_COMB (@lem367333 A) (@lem367332 A x y)). Qed.
Lemma lem367335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem367336 {A : Type'} (x : A) (y : A) : (term39 A x y) = (term39 A x y).
Proof. exact (MK_COMB (@lem367335) (@lem367334 A x y)). Qed.
Lemma lem367337 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term56 A lt2 x y) = (term56 A lt2 x y).
Proof. exact (MK_COMB (@lem367336 A x y) (@lem367326 A lt2 x y)). Qed.
Lemma lem367338 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem367339 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term57 A lt2 x y) = (term57 A lt2 x y).
Proof. exact (MK_COMB (@lem367338) (@lem367337 A lt2 x y)). Qed.
Lemma lem367342 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term17 A lt2 y x) = (term17 A lt2 y x).
Proof. exact (eq_refl (term17 A lt2 y x)). Qed.
Lemma lem367343 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term58 A lt2 x y) = (term58 A lt2 x y).
Proof. exact (MK_COMB (@lem367342 A lt2 y x) (@lem367339 A lt2 x y)). Qed.
Lemma lem367346 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term17 A lt2 x y) = (term17 A lt2 x y).
Proof. exact (eq_refl (term17 A lt2 x y)). Qed.
Lemma lem367347 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term59 A lt2 x y) = (term59 A lt2 x y).
Proof. exact (MK_COMB (@lem367346 A lt2 x y) (@lem367343 A lt2 x y)). Qed.
Lemma lem367348 {A : Type'} (x : A) (y : A) : (term60 A x y) = (term60 A x y).
Proof. exact (fun_ext (fun lt2 : type1402 A => @lem367347 A lt2 x y)). Qed.
Lemma lem367349 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem367350 {A : Type'} (x : A) (y : A) : (term61 A x y) = (term61 A x y).
Proof. exact (MK_COMB (@lem367349 A) (@lem367348 A x y)). Qed.
Lemma lem367351 {A : Type'} (y : A) : (term62 A y) = (term62 A y).
Proof. exact (fun_ext (fun x : A => @lem367350 A x y)). Qed.
Lemma lem367352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367353 {A : Type'} (y : A) : (term63 A y) = (term63 A y).
Proof. exact (MK_COMB (@lem367352 A) (@lem367351 A y)). Qed.
Lemma lem367354 {A : Type'} : (term64 A) = (term64 A).
Proof. exact (fun_ext (fun y : A => @lem367353 A y)). Qed.
Lemma lem367355 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367356 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (MK_COMB (@lem367355 A) (@lem367354 A)). Qed.
Lemma lem367411 {A : Type'} : (term31 A) = (term65 A).
Proof. exact (TRANS (@lem367301 A) (@lem367356 A)). Qed.
Lemma lem367412 {A : Type'} : (term65 A) = (term31 A).
Proof. exact (SYM (@lem367411 A)). Qed.
Lemma lem367415 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term56 A lt2 x y) : term56 A lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367421 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367427 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (h1). Qed.
Lemma lem367434 {A : Type'} (x : A) (x' : A) (y : A) : (term43 A x x' y) = (term66 A x x' y).
Proof. exact (@lem17160 (x' = x) (x' = y)). Qed.
Lemma lem367435 {A : Type'} (P : A -> Prop) : (term67 A P) = (term68 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem367436 {A : Type'} (x : A) (y : A) : (term69 A x y) = (term70 A x y).
Proof. exact (@lem367435 A (term4 A x y)). Qed.
Lemma lem367437 {A : Type'} (x : A) (x' : A) (y : A) : (term33 A x y x') = (term34 A x x' y).
Proof. exact (eq_refl (term33 A x y x')). Qed.
Lemma lem367438 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem367439 {A : Type'} (x : A) (x' : A) (y : A) : (term42 A x y x') = (term43 A x x' y).
Proof. exact (MK_COMB (@lem367438) (@lem367437 A x x' y)). Qed.
Lemma lem367440 {A : Type'} (x : A) (x' : A) (y : A) : (term42 A x y x') = (term66 A x x' y).
Proof. exact (TRANS (@lem367439 A x x' y) (@lem367434 A x x' y)). Qed.
Lemma lem367441 {A : Type'} (x : A) (y : A) : (term71 A x y) = (term72 A x y).
Proof. exact (fun_ext (fun x' : A => @lem367440 A x x' y)). Qed.
Lemma lem367442 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367443 {A : Type'} (x : A) (y : A) : (term70 A x y) = (term73 A x y).
Proof. exact (MK_COMB (@lem367442 A) (@lem367441 A x y)). Qed.
Lemma lem367444 {A : Type'} (x : A) (y : A) : (term69 A x y) = (term73 A x y).
Proof. exact (TRANS (@lem367436 A x y) (@lem367443 A x y)). Qed.
Lemma lem367457 {A : Type'} (x : A) (y' : A) (y : A) : (term43 A x y' y) = (term66 A x y' y).
Proof. exact (@lem17160 (y' = x) (y' = y)). Qed.
Lemma lem367459 {A : Type'} (lt2 : type1402 A) (y' : A) (x' : A) : (term74 A lt2 y' x') = (term74 A lt2 y' x').
Proof. exact (eq_refl (term74 A lt2 y' x')). Qed.
Lemma lem367460 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y' : A) (y : A) : (term75 A lt2 x' x y' y) = (term76 A lt2 x' x y' y).
Proof. exact (MK_COMB (@lem367459 A lt2 y' x') (@lem367457 A x y' y)). Qed.
Lemma lem367461 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y' : A) (y : A) : (term45 A lt2 x' x y' y) = (term75 A lt2 x' x y' y).
Proof. exact (@lem17265 (lt2 y' x') (term43 A x y' y)). Qed.
Lemma lem367462 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y' : A) (y : A) : (term45 A lt2 x' x y' y) = (term76 A lt2 x' x y' y).
Proof. exact (TRANS (@lem367461 A lt2 x' x y' y) (@lem367460 A lt2 x' x y' y)). Qed.
Lemma lem367463 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term47 A lt2 x' x y) = (term77 A lt2 x' x y).
Proof. exact (fun_ext (fun y' : A => @lem367462 A lt2 x' x y' y)). Qed.
Lemma lem367464 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367465 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term49 A lt2 x' x y) = (term78 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367464 A) (@lem367463 A lt2 x' x y)). Qed.
Lemma lem367467 {A : Type'} (x : A) (x' : A) (y : A) : (term41 A x x' y) = (term41 A x x' y).
Proof. exact (eq_refl (term41 A x x' y)). Qed.
Lemma lem367468 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term51 A lt2 x' x y) = (term79 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367467 A x x' y) (@lem367465 A lt2 x' x y)). Qed.
Lemma lem367469 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term53 A lt2 x y) = (term80 A lt2 x y).
Proof. exact (fun_ext (fun x' : A => @lem367468 A lt2 x' x y)). Qed.
Lemma lem367470 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem367471 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term55 A lt2 x y) = (term81 A lt2 x y).
Proof. exact (MK_COMB (@lem367470 A) (@lem367469 A lt2 x y)). Qed.
Lemma lem367472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem367473 {A : Type'} (x : A) (y : A) : (term82 A x y) = (term83 A x y).
Proof. exact (MK_COMB (@lem367472) (@lem367444 A x y)). Qed.
Lemma lem367474 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term84 A lt2 x y) = (term85 A lt2 x y).
Proof. exact (MK_COMB (@lem367473 A x y) (@lem367471 A lt2 x y)). Qed.
Lemma lem367475 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term56 A lt2 x y) = (term84 A lt2 x y).
Proof. exact (@lem17265 (term37 A x y) (term55 A lt2 x y)). Qed.
Lemma lem367476 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term56 A lt2 x y) = (term85 A lt2 x y).
Proof. exact (TRANS (@lem367475 A lt2 x y) (@lem367474 A lt2 x y)). Qed.
Lemma lem367478 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem367479 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (@lem367478 A P Q). Qed.
Lemma lem367480 {A : Type'} (x : A) (y : A) : (term88 A x y) = (term89 A x y).
Proof. exact (@lem367479 A (term90 A x) (term90 A y)). Qed.
Lemma lem367481 {A : Type'} (x' : A) (x : A) : (term91 A x x') = (term92 A x' x).
Proof. exact (eq_refl (term91 A x x')). Qed.
Lemma lem367482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem367483 {A : Type'} (x' : A) (x : A) : (term93 A x x') = (term94 A x' x).
Proof. exact (MK_COMB (@lem367482) (@lem367481 A x' x)). Qed.
Lemma lem367484 {A : Type'} (x' : A) (y : A) : (term91 A y x') = (term92 A x' y).
Proof. exact (eq_refl (term91 A y x')). Qed.
Lemma lem367485 {A : Type'} (x : A) (x' : A) (y : A) : (term95 A x y x') = (term66 A x x' y).
Proof. exact (MK_COMB (@lem367483 A x' x) (@lem367484 A x' y)). Qed.
Lemma lem367486 {A : Type'} (x : A) (y : A) : (term96 A x y) = (term72 A x y).
Proof. exact (fun_ext (fun x' : A => @lem367485 A x x' y)). Qed.
Lemma lem367487 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367488 {A : Type'} (x : A) (y : A) : (term88 A x y) = (term73 A x y).
Proof. exact (MK_COMB (@lem367487 A) (@lem367486 A x y)). Qed.
Lemma lem367489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem367490 {A : Type'} (x : A) (y : A) : (term97 A x y) = (term98 A x y).
Proof. exact (MK_COMB (@lem367489) (@lem367488 A x y)). Qed.
Lemma lem367491 {A : Type'} (x' : A) (x : A) : (term91 A x x') = (term92 A x' x).
Proof. exact (eq_refl (term91 A x x')). Qed.
Lemma lem367492 {A : Type'} (x : A) : (term99 A x) = (term90 A x).
Proof. exact (fun_ext (fun x' : A => @lem367491 A x' x)). Qed.
Lemma lem367493 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367494 {A : Type'} (x : A) : (term100 A x) = (term101 A x).
Proof. exact (MK_COMB (@lem367493 A) (@lem367492 A x)). Qed.
Lemma lem367495 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem367496 {A : Type'} (x : A) : (term102 A x) = (term103 A x).
Proof. exact (MK_COMB (@lem367495) (@lem367494 A x)). Qed.
Lemma lem367497 {A : Type'} (x' : A) (y : A) : (term91 A y x') = (term92 A x' y).
Proof. exact (eq_refl (term91 A y x')). Qed.
Lemma lem367498 {A : Type'} (y : A) : (term99 A y) = (term90 A y).
Proof. exact (fun_ext (fun x' : A => @lem367497 A x' y)). Qed.
Lemma lem367499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367500 {A : Type'} (y : A) : (term100 A y) = (term101 A y).
Proof. exact (MK_COMB (@lem367499 A) (@lem367498 A y)). Qed.
Lemma lem367501 {A : Type'} (x : A) (y : A) : (term89 A x y) = (term104 A x y).
Proof. exact (MK_COMB (@lem367496 A x) (@lem367500 A y)). Qed.
Lemma lem367502 {A : Type'} (x : A) (y : A) : ((term88 A x y) = (term89 A x y)) = ((term73 A x y) = (term104 A x y)).
Proof. exact (MK_COMB (@lem367490 A x y) (@lem367501 A x y)). Qed.
Lemma lem367503 {A : Type'} (x : A) (y : A) : (term73 A x y) = (term104 A x y).
Proof. exact (EQ_MP (@lem367502 A x y) (@lem367480 A x y)). Qed.
Lemma lem367512 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem367513 {A : Type'} (x : A) (y : A) : (term83 A x y) = (term105 A x y).
Proof. exact (MK_COMB (@lem367512) (@lem367503 A x y)). Qed.
Lemma lem367610 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term81 A lt2 x y) = (term81 A lt2 x y).
Proof. exact (eq_refl (term81 A lt2 x y)). Qed.
Lemma lem367611 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term85 A lt2 x y) = (term106 A lt2 x y).
Proof. exact (MK_COMB (@lem367513 A x y) (@lem367610 A lt2 x y)). Qed.
Lemma lem367613 {A : Type'} (P : Prop) (Q : A -> Prop) : (term107 A P Q) = (term108 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem367614 {A : Type'} (P : Prop) (Q : A -> Prop) : (term107 A P Q) = (term108 A P Q).
Proof. exact (@lem367613 A P Q). Qed.
Lemma lem367615 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term109 A lt2 x y) = (term110 A lt2 x y).
Proof. exact (@lem367614 A (term104 A x y) (term80 A lt2 x y)). Qed.
Lemma lem367616 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term111 A lt2 x y x') = (term79 A lt2 x' x y).
Proof. exact (eq_refl (term111 A lt2 x y x')). Qed.
Lemma lem367617 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term112 A lt2 x y) = (term80 A lt2 x y).
Proof. exact (fun_ext (fun x' : A => @lem367616 A lt2 x' x y)). Qed.
Lemma lem367618 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem367619 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term113 A lt2 x y) = (term81 A lt2 x y).
Proof. exact (MK_COMB (@lem367618 A) (@lem367617 A lt2 x y)). Qed.
Lemma lem367620 {A : Type'} (x : A) (y : A) : (term105 A x y) = (term105 A x y).
Proof. exact (eq_refl (term105 A x y)). Qed.
Lemma lem367621 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term109 A lt2 x y) = (term106 A lt2 x y).
Proof. exact (MK_COMB (@lem367620 A x y) (@lem367619 A lt2 x y)). Qed.
Lemma lem367622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem367623 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term114 A lt2 x y) = (term115 A lt2 x y).
Proof. exact (MK_COMB (@lem367622) (@lem367621 A lt2 x y)). Qed.
Lemma lem367624 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term111 A lt2 x y x') = (term79 A lt2 x' x y).
Proof. exact (eq_refl (term111 A lt2 x y x')). Qed.
Lemma lem367625 {A : Type'} (x : A) (y : A) : (term105 A x y) = (term105 A x y).
Proof. exact (eq_refl (term105 A x y)). Qed.
Lemma lem367626 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term116 A lt2 x y x') = (term117 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367625 A x y) (@lem367624 A lt2 x' x y)). Qed.
Lemma lem367627 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term118 A lt2 x y) = (term119 A lt2 x y).
Proof. exact (fun_ext (fun x' : A => @lem367626 A lt2 x' x y)). Qed.
Lemma lem367628 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem367629 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term110 A lt2 x y) = (term120 A lt2 x y).
Proof. exact (MK_COMB (@lem367628 A) (@lem367627 A lt2 x y)). Qed.
Lemma lem367630 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : ((term109 A lt2 x y) = (term110 A lt2 x y)) = ((term106 A lt2 x y) = (term120 A lt2 x y)).
Proof. exact (MK_COMB (@lem367623 A lt2 x y) (@lem367629 A lt2 x y)). Qed.
Lemma lem367631 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term106 A lt2 x y) = (term120 A lt2 x y).
Proof. exact (EQ_MP (@lem367630 A lt2 x y) (@lem367615 A lt2 x y)). Qed.
Lemma lem367632 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term85 A lt2 x y) = (term120 A lt2 x y).
Proof. exact (TRANS (@lem367611 A lt2 x y) (@lem367631 A lt2 x y)). Qed.
Lemma lem367633 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term56 A lt2 x y) = (term120 A lt2 x y).
Proof. exact (TRANS (@lem367476 A lt2 x y) (@lem367632 A lt2 x y)). Qed.
Lemma lem367634 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : term56 A lt2 x y) : term120 A lt2 x y.
Proof. exact (EQ_MP (@lem367633 A lt2 x y) (@lem367415 A lt2 x y h1)). Qed.
Lemma lem367635 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term117 A lt2 x' x y) : term117 A lt2 x' x y.
Proof. exact (h1). Qed.
Lemma lem367641 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367647 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (h1). Qed.
Lemma lem367674 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y' : A) (y : A) : (term76 A lt2 x' x y' y) = (term76 A lt2 x' x y' y).
Proof. exact (eq_refl (term76 A lt2 x' x y' y)). Qed.
Lemma lem367675 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term77 A lt2 x' x y) = (term77 A lt2 x' x y).
Proof. exact (fun_ext (fun y' : A => @lem367674 A lt2 x' x y' y)). Qed.
Lemma lem367676 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367677 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term78 A lt2 x' x y) = (term78 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367676 A) (@lem367675 A lt2 x' x y)). Qed.
Lemma lem367692 {A : Type'} (x : A) (x' : A) (y : A) : (term41 A x x' y) = (term41 A x x' y).
Proof. exact (eq_refl (term41 A x x' y)). Qed.
Lemma lem367693 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term79 A lt2 x' x y) = (term79 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367692 A x x' y) (@lem367677 A lt2 x' x y)). Qed.
Lemma lem367700 {A : Type'} (x' : A) (y : A) : (term92 A x' y) = (term92 A x' y).
Proof. exact (eq_refl (term92 A x' y)). Qed.
Lemma lem367701 {A : Type'} (y : A) : (term90 A y) = (term90 A y).
Proof. exact (fun_ext (fun x' : A => @lem367700 A x' y)). Qed.
Lemma lem367702 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367703 {A : Type'} (y : A) : (term101 A y) = (term101 A y).
Proof. exact (MK_COMB (@lem367702 A) (@lem367701 A y)). Qed.
Lemma lem367710 {A : Type'} (x' : A) (x : A) : (term92 A x' x) = (term92 A x' x).
Proof. exact (eq_refl (term92 A x' x)). Qed.
Lemma lem367711 {A : Type'} (x : A) : (term90 A x) = (term90 A x).
Proof. exact (fun_ext (fun x' : A => @lem367710 A x' x)). Qed.
Lemma lem367712 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367713 {A : Type'} (x : A) : (term101 A x) = (term101 A x).
Proof. exact (MK_COMB (@lem367712 A) (@lem367711 A x)). Qed.
Lemma lem367714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem367715 {A : Type'} (x : A) : (term103 A x) = (term103 A x).
Proof. exact (MK_COMB (@lem367714) (@lem367713 A x)). Qed.
Lemma lem367716 {A : Type'} (x : A) (y : A) : (term104 A x y) = (term104 A x y).
Proof. exact (MK_COMB (@lem367715 A x) (@lem367703 A y)). Qed.
Lemma lem367717 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem367718 {A : Type'} (x : A) (y : A) : (term105 A x y) = (term105 A x y).
Proof. exact (MK_COMB (@lem367717) (@lem367716 A x y)). Qed.
Lemma lem367719 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) : (term117 A lt2 x' x y) = (term117 A lt2 x' x y).
Proof. exact (MK_COMB (@lem367718 A x y) (@lem367693 A lt2 x' x y)). Qed.
Lemma lem367720 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term117 A lt2 x' x y) : term117 A lt2 x' x y.
Proof. exact (EQ_MP (@lem367719 A lt2 x' x y) (@lem367635 A lt2 x' x y h1)). Qed.
Lemma lem367721 {A : Type'} (x : A) (y : A) (h1 : term104 A x y) : term104 A x y.
Proof. exact (h1). Qed.
Lemma lem367722 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term79 A lt2 x' x y.
Proof. exact (h1). Qed.
Lemma lem367723 {A : Type'} (x : A) (y : A) (h1 : term104 A x y) : term101 A y.
Proof. exact (proj2 (@lem367721 A x y h1)). Qed.
Lemma lem367725 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term78 A lt2 x' x y.
Proof. exact (proj2 (@lem367722 A lt2 x' x y h1)). Qed.
Lemma lem367726 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term34 A x x' y.
Proof. exact (proj1 (@lem367722 A lt2 x' x y h1)). Qed.
Lemma lem367745 {A : Type'} (x' : A) (y : A) : (term92 A x' y) = (term92 A x' y).
Proof. exact (eq_refl (term92 A x' y)). Qed.
Lemma lem367746 {A : Type'} (y : A) : (term90 A y) = (term90 A y).
Proof. exact (fun_ext (fun x' : A => @lem367745 A x' y)). Qed.
Lemma lem367747 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367749 {A : Type'} (y : A) : (term101 A y) = (term101 A y).
Proof. exact (MK_COMB (@lem367747 A) (@lem367746 A y)). Qed.
Lemma lem367750 {A : Type'} (x : A) (y : A) (h1 : term104 A x y) : term101 A y.
Proof. exact (EQ_MP (@lem367749 A y) (@lem367723 A x y h1)). Qed.
Lemma lem367758 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (h1). Qed.
Lemma lem367776 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (y' : A) (y : A) : (term76 A lt2 x' x y' y) = (term121 A x lt2 x' y' y).
Proof. exact (@lem19490 (term92 A y' x) (term122 A lt2 y' x') (term92 A y' y)). Qed.
Lemma lem367777 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (y : A) : (term77 A lt2 x' x y) = (term123 A x lt2 x' y).
Proof. exact (fun_ext (fun y' : A => @lem367776 A x lt2 x' y' y)). Qed.
Lemma lem367778 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367780 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (y : A) : (term78 A lt2 x' x y) = (term124 A x lt2 x' y).
Proof. exact (MK_COMB (@lem367778 A) (@lem367777 A x lt2 x' y)). Qed.
Lemma lem367781 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term124 A x lt2 x' y.
Proof. exact (EQ_MP (@lem367780 A x lt2 x' y) (@lem367725 A lt2 x' x y h1)). Qed.
Lemma lem367785 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem367789 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367811 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (y' : A) (y : A) : (term76 A lt2 x' x y' y) = (term121 A x lt2 x' y' y).
Proof. exact (@lem19490 (term92 A y' x) (term122 A lt2 y' x') (term92 A y' y)). Qed.
Lemma lem367812 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (y : A) : (term77 A lt2 x' x y) = (term123 A x lt2 x' y).
Proof. exact (fun_ext (fun y' : A => @lem367811 A x lt2 x' y' y)). Qed.
Lemma lem367813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem367815 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (y : A) : (term78 A lt2 x' x y) = (term124 A x lt2 x' y).
Proof. exact (MK_COMB (@lem367813 A) (@lem367812 A x lt2 x' y)). Qed.
Lemma lem367816 {A : Type'} (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term124 A x lt2 x' y.
Proof. exact (EQ_MP (@lem367815 A x lt2 x' y) (@lem367725 A lt2 x' x y h1)). Qed.
Lemma lem367820 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem367824 {A : Type'} (_7954 : A) (x : A) (y : A) (h1 : term104 A x y) : term91 A y _7954.
Proof. exact (@lem367750 A x y h1 _7954). Qed.
Lemma lem367825 {A : Type'} (_7954 : A) (y : A) : (term91 A y _7954) = (term92 A _7954 y).
Proof. exact (eq_refl (term91 A y _7954)). Qed.
Lemma lem367827 {A : Type'} (_7955 : A) (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term125 A x lt2 x' y _7955.
Proof. exact (@lem367781 A lt2 x' x y h1 _7955). Qed.
Lemma lem367828 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (_7955 : A) (y : A) : (term125 A x lt2 x' y _7955) = (term121 A x lt2 x' _7955 y).
Proof. exact (eq_refl (term125 A x lt2 x' y _7955)). Qed.
Lemma lem367829 {A : Type'} (_7955 : A) (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term121 A x lt2 x' _7955 y.
Proof. exact (EQ_MP (@lem367828 A x lt2 x' _7955 y) (@lem367827 A _7955 lt2 x' x y h1)). Qed.
Lemma lem367830 {A : Type'} (_7956 : A) (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term125 A x lt2 x' y _7956.
Proof. exact (@lem367816 A lt2 x' x y h1 _7956). Qed.
Lemma lem367831 {A : Type'} (x : A) (lt2 : type1402 A) (x' : A) (_7956 : A) (y : A) : (term125 A x lt2 x' y _7956) = (term121 A x lt2 x' _7956 y).
Proof. exact (eq_refl (term125 A x lt2 x' y _7956)). Qed.
Lemma lem367832 {A : Type'} (_7956 : A) (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term121 A x lt2 x' _7956 y.
Proof. exact (EQ_MP (@lem367831 A x lt2 x' _7956 y) (@lem367830 A _7956 lt2 x' x y h1)). Qed.
Lemma lem367844 {A : Type'} (_7954 : A) (x : A) (y : A) (h1 : term104 A x y) : term92 A _7954 y.
Proof. exact (EQ_MP (@lem367825 A _7954 y) (@lem367824 A _7954 x y h1)). Qed.
Lemma lem367848 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (h1). Qed.
Lemma lem367850 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem367862 {A : Type'} (_7955 : A) (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term126 A lt2 x' _7955 y.
Proof. exact (proj2 (@lem367829 A _7955 lt2 x' x y h1)). Qed.
Lemma lem367864 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367868 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem367874 {A : Type'} (_7956 : A) (lt2 : type1402 A) (x' : A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) : term126 A lt2 x' _7956 x.
Proof. exact (proj1 (@lem367832 A _7956 lt2 x' x y h1)). Qed.
Lemma lem367922 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (h1). Qed.
Lemma lem367936 {A : Type'} (lt2 : type1402 A) (_7955 : A) (y : A) : (term127 A lt2 _7955 y) = (term127 A lt2 _7955 y).
Proof. exact (eq_refl (term127 A lt2 _7955 y)). Qed.
Lemma lem367937 {A : Type'} (lt2 : type1402 A) (_7955 : A) (y : A) (x' : A) (x : A) (h1 : x' = x) : (term128 A lt2 _7955 y x') = (term128 A lt2 _7955 y x).
Proof. exact (MK_COMB (@lem367936 A lt2 _7955 y) (@lem367850 A x' x h1)). Qed.
Lemma lem367938 {A : Type'} (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : (term128 A lt2 _7955 y x) = (term126 A lt2 x _7955 y).
Proof. exact (eq_refl (term128 A lt2 _7955 y x)). Qed.
Lemma lem367939 {A : Type'} (lt2 : type1402 A) (_7955 : A) (y : A) (x' : A) : (term129 A lt2 _7955 y x') = (term129 A lt2 _7955 y x').
Proof. exact (eq_refl (term129 A lt2 _7955 y x')). Qed.
Lemma lem367940 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : ((term128 A lt2 _7955 y x') = (term128 A lt2 _7955 y x)) = ((term128 A lt2 _7955 y x') = (term126 A lt2 x _7955 y)).
Proof. exact (MK_COMB (@lem367939 A lt2 _7955 y x') (@lem367938 A lt2 x _7955 y)). Qed.
Lemma lem367941 {A : Type'} (lt2 : type1402 A) (x' : A) (_7955 : A) (y : A) : (term128 A lt2 _7955 y x') = (term126 A lt2 x' _7955 y).
Proof. exact (eq_refl (term128 A lt2 _7955 y x')). Qed.
Lemma lem367942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem367943 {A : Type'} (lt2 : type1402 A) (x' : A) (_7955 : A) (y : A) : (term129 A lt2 _7955 y x') = (term130 A lt2 x' _7955 y).
Proof. exact (MK_COMB (@lem367942) (@lem367941 A lt2 x' _7955 y)). Qed.
Lemma lem367944 {A : Type'} (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : (term126 A lt2 x _7955 y) = (term126 A lt2 x _7955 y).
Proof. exact (eq_refl (term126 A lt2 x _7955 y)). Qed.
Lemma lem367945 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : ((term128 A lt2 _7955 y x') = (term126 A lt2 x _7955 y)) = ((term126 A lt2 x' _7955 y) = (term126 A lt2 x _7955 y)).
Proof. exact (MK_COMB (@lem367943 A lt2 x' _7955 y) (@lem367944 A lt2 x _7955 y)). Qed.
Lemma lem367946 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : ((term128 A lt2 _7955 y x') = (term128 A lt2 _7955 y x)) = ((term126 A lt2 x' _7955 y) = (term126 A lt2 x _7955 y)).
Proof. exact (TRANS (@lem367940 A x' lt2 x _7955 y) (@lem367945 A x' lt2 x _7955 y)). Qed.
Lemma lem367947 {A : Type'} (lt2 : type1402 A) (_7955 : A) (y : A) (x' : A) (x : A) (h1 : x' = x) : (term126 A lt2 x' _7955 y) = (term126 A lt2 x _7955 y).
Proof. exact (EQ_MP (@lem367946 A x' lt2 x _7955 y) (@lem367937 A lt2 _7955 y x' x h1)). Qed.
Lemma lem367948 {A : Type'} (_7955 : A) (lt2 : type1402 A) (y : A) (x' : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) : term126 A lt2 x _7955 y.
Proof. exact (EQ_MP (@lem367947 A lt2 _7955 y x' x h2) (@lem367862 A _7955 lt2 x' x y h1)). Qed.
Lemma lem367976 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (h1). Qed.
Lemma lem367991 {A : Type'} (lt2 : type1402 A) (_7956 : A) (x : A) : (term127 A lt2 _7956 x) = (term127 A lt2 _7956 x).
Proof. exact (eq_refl (term127 A lt2 _7956 x)). Qed.
Lemma lem367992 {A : Type'} (lt2 : type1402 A) (_7956 : A) (x : A) (x' : A) (y : A) (h1 : x' = y) : (term128 A lt2 _7956 x x') = (term128 A lt2 _7956 x y).
Proof. exact (MK_COMB (@lem367991 A lt2 _7956 x) (@lem367868 A x' y h1)). Qed.
Lemma lem367993 {A : Type'} (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : (term128 A lt2 _7956 x y) = (term126 A lt2 y _7956 x).
Proof. exact (eq_refl (term128 A lt2 _7956 x y)). Qed.
Lemma lem367994 {A : Type'} (lt2 : type1402 A) (_7956 : A) (x : A) (x' : A) : (term129 A lt2 _7956 x x') = (term129 A lt2 _7956 x x').
Proof. exact (eq_refl (term129 A lt2 _7956 x x')). Qed.
Lemma lem367995 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : ((term128 A lt2 _7956 x x') = (term128 A lt2 _7956 x y)) = ((term128 A lt2 _7956 x x') = (term126 A lt2 y _7956 x)).
Proof. exact (MK_COMB (@lem367994 A lt2 _7956 x x') (@lem367993 A lt2 y _7956 x)). Qed.
Lemma lem367996 {A : Type'} (lt2 : type1402 A) (x' : A) (_7956 : A) (x : A) : (term128 A lt2 _7956 x x') = (term126 A lt2 x' _7956 x).
Proof. exact (eq_refl (term128 A lt2 _7956 x x')). Qed.
Lemma lem367997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem367998 {A : Type'} (lt2 : type1402 A) (x' : A) (_7956 : A) (x : A) : (term129 A lt2 _7956 x x') = (term130 A lt2 x' _7956 x).
Proof. exact (MK_COMB (@lem367997) (@lem367996 A lt2 x' _7956 x)). Qed.
Lemma lem367999 {A : Type'} (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : (term126 A lt2 y _7956 x) = (term126 A lt2 y _7956 x).
Proof. exact (eq_refl (term126 A lt2 y _7956 x)). Qed.
Lemma lem368000 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : ((term128 A lt2 _7956 x x') = (term126 A lt2 y _7956 x)) = ((term126 A lt2 x' _7956 x) = (term126 A lt2 y _7956 x)).
Proof. exact (MK_COMB (@lem367998 A lt2 x' _7956 x) (@lem367999 A lt2 y _7956 x)). Qed.
Lemma lem368001 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : ((term128 A lt2 _7956 x x') = (term128 A lt2 _7956 x y)) = ((term126 A lt2 x' _7956 x) = (term126 A lt2 y _7956 x)).
Proof. exact (TRANS (@lem367995 A x' lt2 y _7956 x) (@lem368000 A x' lt2 y _7956 x)). Qed.
Lemma lem368002 {A : Type'} (lt2 : type1402 A) (_7956 : A) (x : A) (x' : A) (y : A) (h1 : x' = y) : (term126 A lt2 x' _7956 x) = (term126 A lt2 y _7956 x).
Proof. exact (EQ_MP (@lem368001 A x' lt2 y _7956 x) (@lem367992 A lt2 _7956 x x' y h1)). Qed.
Lemma lem368003 {A : Type'} (_7956 : A) (lt2 : type1402 A) (x : A) (x' : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) : term126 A lt2 y _7956 x.
Proof. exact (EQ_MP (@lem368002 A lt2 _7956 x x' y h2) (@lem367874 A _7956 lt2 x' x y h1)). Qed.
Lemma lem368039 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem368040 {A : Type'} (x : A) : x = x.
Proof. exact (@lem368039 A x). Qed.
Lemma lem368041 {A : Type'} (y : A) : y = y.
Proof. exact (@lem368040 A y). Qed.
Lemma lem368042 {A : Type'} (y : A) : term131 A y.
Proof. exact (fun h0 : term132 A y => @lem368041 A y). Qed.
Lemma lem368044 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368045 {A : Type'} (y : A) : (term131 A y) = (y = y).
Proof. exact (@lem368044 (y = y)). Qed.
Lemma lem368046 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem368045 A y) (@lem368042 A y)). Qed.
Lemma lem368049 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem368051 {A : Type'} (_7954 : A) (y : A) : (term92 A _7954 y) = (term134 A _7954 y).
Proof. exact (@lem368049 (_7954 = y)). Qed.
Lemma lem368054 {A : Type'} (_7954 : A) (x : A) (y : A) (h1 : term104 A x y) : term134 A _7954 y.
Proof. exact (EQ_MP (@lem368051 A _7954 y) (@lem367844 A _7954 x y h1)). Qed.
Lemma lem368055 {A : Type'} (_7954 : A) (x : A) (y : A) (h1 : term104 A x y) : term134 A _7954 y.
Proof. exact (@lem368054 A _7954 x y h1). Qed.
Lemma lem368056 {A : Type'} (x : A) (y : A) (h1 : term104 A x y) : term135 A y.
Proof. exact (@lem368055 A y x y h1). Qed.
Lemma lem368059 {A : Type'} (x : A) (y : A) (h1 : term104 A x y) : False.
Proof. exact (@lem368056 A x y h1 (@lem368046 A y)). Qed.
Lemma lem368060 {A : Type'} (x : A) (y : A) (h1 : term104 A x y) : term136.
Proof. exact (fun h0 : ~ False => @lem368059 A x y h1). Qed.
Lemma lem368062 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368063 : term136 = False.
Proof. exact (@lem368062 False). Qed.
Lemma lem368064 {A : Type'} (x : A) (y : A) (h1 : term104 A x y) : False.
Proof. exact (EQ_MP (@lem368063) (@lem368060 A x y h1)). Qed.
Lemma lem368087 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (h1). Qed.
Lemma lem368088 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : term137 A lt2 y x.
Proof. exact (fun h0 : term122 A lt2 y x => @lem368087 A lt2 y x h1). Qed.
Lemma lem368090 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368091 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term137 A lt2 y x) = (lt2 y x).
Proof. exact (@lem368090 (lt2 y x)). Qed.
Lemma lem368092 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : lt2 y x.
Proof. exact (EQ_MP (@lem368091 A lt2 y x) (@lem368088 A lt2 y x h1)). Qed.
Lemma lem368094 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem368095 {A : Type'} (x : A) : x = x.
Proof. exact (@lem368094 A x). Qed.
Lemma lem368096 {A : Type'} (y : A) : y = y.
Proof. exact (@lem368095 A y). Qed.
Lemma lem368097 {A : Type'} (y : A) : term131 A y.
Proof. exact (fun h0 : term132 A y => @lem368096 A y). Qed.
Lemma lem368099 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368100 {A : Type'} (y : A) : (term131 A y) = (y = y).
Proof. exact (@lem368099 (y = y)). Qed.
Lemma lem368101 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem368100 A y) (@lem368097 A y)). Qed.
Lemma lem368103 (a : Prop) (b : Prop) : (term138 a b) = (term139 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem368104 {A : Type'} (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : (term126 A lt2 x _7955 y) = (term140 A lt2 x _7955 y).
Proof. exact (@lem368103 (lt2 _7955 x) (_7955 = y)). Qed.
Lemma lem368106 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem368107 {A : Type'} (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : (term140 A lt2 x _7955 y) = (term141 A lt2 x _7955 y).
Proof. exact (@lem368106 (term142 A lt2 x _7955 y)). Qed.
Lemma lem368108 {A : Type'} (lt2 : type1402 A) (x : A) (_7955 : A) (y : A) : (term126 A lt2 x _7955 y) = (term141 A lt2 x _7955 y).
Proof. exact (TRANS (@lem368104 A lt2 x _7955 y) (@lem368107 A lt2 x _7955 y)). Qed.
Lemma lem368110 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 y x) : term143 A lt2 x y.
Proof. exact (conj (@lem368092 A lt2 y x h1) (@lem368101 A y)). Qed.
Lemma lem368112 {A : Type'} (_7955 : A) (lt2 : type1402 A) (y : A) (x' : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) : term141 A lt2 x _7955 y.
Proof. exact (EQ_MP (@lem368108 A lt2 x _7955 y) (@lem367948 A _7955 lt2 y x' x h1 h2)). Qed.
Lemma lem368113 {A : Type'} (_7955 : A) (lt2 : type1402 A) (y : A) (x' : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) : term141 A lt2 x _7955 y.
Proof. exact (@lem368112 A _7955 lt2 y x' x h1 h2). Qed.
Lemma lem368114 {A : Type'} (lt2 : type1402 A) (y : A) (x' : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) : term144 A lt2 x y.
Proof. exact (@lem368113 A y lt2 y x' x h1 h2). Qed.
Lemma lem368117 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (@lem368114 A lt2 y x' x h1 h2 (@lem368110 A lt2 y x h3)). Qed.
Lemma lem368118 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : term136.
Proof. exact (fun h0 : ~ False => @lem368117 A x' lt2 y x h1 h2 h3). Qed.
Lemma lem368120 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368121 : term136 = False.
Proof. exact (@lem368120 False). Qed.
Lemma lem368122 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368121) (@lem368118 A x' lt2 y x h1 h2 h3)). Qed.
Lemma lem368145 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (h1). Qed.
Lemma lem368146 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : term137 A lt2 x y.
Proof. exact (fun h0 : term122 A lt2 x y => @lem368145 A lt2 x y h1). Qed.
Lemma lem368148 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368149 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term137 A lt2 x y) = (lt2 x y).
Proof. exact (@lem368148 (lt2 x y)). Qed.
Lemma lem368150 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : lt2 x y.
Proof. exact (EQ_MP (@lem368149 A lt2 x y) (@lem368146 A lt2 x y h1)). Qed.
Lemma lem368152 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem368153 {A : Type'} (x : A) : x = x.
Proof. exact (@lem368152 A x). Qed.
Lemma lem368154 {A : Type'} (x : A) : term131 A x.
Proof. exact (fun h0 : term132 A x => @lem368153 A x). Qed.
Lemma lem368156 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368157 {A : Type'} (x : A) : (term131 A x) = (x = x).
Proof. exact (@lem368156 (x = x)). Qed.
Lemma lem368158 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem368157 A x) (@lem368154 A x)). Qed.
Lemma lem368160 (a : Prop) (b : Prop) : (term138 a b) = (term139 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem368161 {A : Type'} (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : (term126 A lt2 y _7956 x) = (term140 A lt2 y _7956 x).
Proof. exact (@lem368160 (lt2 _7956 y) (_7956 = x)). Qed.
Lemma lem368163 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem368164 {A : Type'} (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : (term140 A lt2 y _7956 x) = (term141 A lt2 y _7956 x).
Proof. exact (@lem368163 (term142 A lt2 y _7956 x)). Qed.
Lemma lem368165 {A : Type'} (lt2 : type1402 A) (y : A) (_7956 : A) (x : A) : (term126 A lt2 y _7956 x) = (term141 A lt2 y _7956 x).
Proof. exact (TRANS (@lem368161 A lt2 y _7956 x) (@lem368164 A lt2 y _7956 x)). Qed.
Lemma lem368167 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : term143 A lt2 y x.
Proof. exact (conj (@lem368150 A lt2 x y h1) (@lem368158 A x)). Qed.
Lemma lem368169 {A : Type'} (_7956 : A) (lt2 : type1402 A) (x : A) (x' : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) : term141 A lt2 y _7956 x.
Proof. exact (EQ_MP (@lem368165 A lt2 y _7956 x) (@lem368003 A _7956 lt2 x x' y h1 h2)). Qed.
Lemma lem368170 {A : Type'} (_7956 : A) (lt2 : type1402 A) (x : A) (x' : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) : term141 A lt2 y _7956 x.
Proof. exact (@lem368169 A _7956 lt2 x x' y h1 h2). Qed.
Lemma lem368171 {A : Type'} (lt2 : type1402 A) (x : A) (x' : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) : term144 A lt2 y x.
Proof. exact (@lem368170 A x lt2 x x' y h1 h2). Qed.
Lemma lem368174 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (@lem368171 A lt2 x x' y h1 h2 (@lem368167 A lt2 x y h3)). Qed.
Lemma lem368175 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : term136.
Proof. exact (fun h0 : ~ False => @lem368174 A x' lt2 x y h1 h2 h3). Qed.
Lemma lem368177 (p : Prop) : (term133 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem368178 : term136 = False.
Proof. exact (@lem368177 False). Qed.
Lemma lem368179 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368178) (@lem368175 A x' lt2 x y h1 h2 h3)). Qed.
Lemma lem368180 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : lt2 x y => @lem368179 A x' lt2 x y h1 h2 h3) (fun h4 : False => @lem367976 A lt2 x y h3)). Qed.
Lemma lem368182 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368180 A x' lt2 x y h1 h2 h3) (@lem367976 A lt2 x y h3)). Qed.
Lemma lem368183 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368122 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367922 A lt2 y x h3)). Qed.
Lemma lem368185 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368183 A x' lt2 y x h1 h2 h3) (@lem367922 A lt2 y x h3)). Qed.
Lemma lem368186 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem368182 A x' lt2 x y h1 h2 h3) (fun h4 : False => @lem367868 A x' y h2)). Qed.
Lemma lem368187 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368186 A x' lt2 x y h1 h2 h3) (@lem367868 A x' y h2)). Qed.
Lemma lem368188 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : lt2 x y => @lem368187 A x' lt2 x y h1 h2 h3) (fun h4 : False => @lem367864 A lt2 x y h3)). Qed.
Lemma lem368189 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368188 A x' lt2 x y h1 h2 h3) (@lem367864 A lt2 x y h3)). Qed.
Lemma lem368190 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem368185 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367850 A x' x h2)). Qed.
Lemma lem368191 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368190 A x' lt2 y x h1 h2 h3) (@lem367850 A x' x h2)). Qed.
Lemma lem368192 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368191 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367848 A lt2 y x h3)). Qed.
Lemma lem368193 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368192 A x' lt2 y x h1 h2 h3) (@lem367848 A lt2 y x h3)). Qed.
Lemma lem368194 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem368189 A x' lt2 x y h1 h2 h3) (fun h4 : False => @lem367820 A x' y h2)). Qed.
Lemma lem368195 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368194 A x' lt2 x y h1 h2 h3) (@lem367820 A x' y h2)). Qed.
Lemma lem368196 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : lt2 x y => @lem368195 A x' lt2 x y h1 h2 h3) (fun h4 : False => @lem367789 A lt2 x y h3)). Qed.
Lemma lem368197 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368196 A x' lt2 x y h1 h2 h3) (@lem367789 A lt2 x y h3)). Qed.
Lemma lem368198 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem368193 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367785 A x' x h2)). Qed.
Lemma lem368199 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368198 A x' lt2 y x h1 h2 h3) (@lem367785 A x' x h2)). Qed.
Lemma lem368200 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368199 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367758 A lt2 y x h3)). Qed.
Lemma lem368201 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368200 A x' lt2 y x h1 h2 h3) (@lem367758 A lt2 y x h3)). Qed.
Lemma lem368202 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : (x' = y) = False.
Proof. exact (prop_ext (fun h4 : x' = y => @lem368197 A x' lt2 x y h1 h2 h3) (fun h4 : False => @lem367820 A x' y h2)). Qed.
Lemma lem368203 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368202 A x' lt2 x y h1 h2 h3) (@lem367820 A x' y h2)). Qed.
Lemma lem368204 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : lt2 x y => @lem368203 A x' lt2 x y h1 h2 h3) (fun h4 : False => @lem367789 A lt2 x y h3)). Qed.
Lemma lem368205 {A : Type'} (x' : A) (lt2 : type1402 A) (x : A) (y : A) (h1 : term79 A lt2 x' x y) (h2 : x' = y) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368204 A x' lt2 x y h1 h2 h3) (@lem367789 A lt2 x y h3)). Qed.
Lemma lem368206 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem368201 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367785 A x' x h2)). Qed.
Lemma lem368207 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368206 A x' lt2 y x h1 h2 h3) (@lem367785 A x' x h2)). Qed.
Lemma lem368208 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368207 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367758 A lt2 y x h3)). Qed.
Lemma lem368209 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : x' = x) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368208 A x' lt2 y x h1 h2 h3) (@lem367758 A lt2 y x h3)). Qed.
Lemma lem368210 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term79 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (or_elim (@lem367726 A lt2 x' x y h1) (fun h0 : x' = x => @lem368209 A x' lt2 y x h1 h0 h3) (fun h0 : x' = y => @lem368205 A x' lt2 x y h1 h0 h2)). Qed.
Lemma lem368211 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term117 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (or_elim (@lem367720 A lt2 x' x y h1) (fun h0 : term104 A x y => @lem368064 A x y h0) (fun h0 : term79 A lt2 x' x y => @lem368210 A x' lt2 y x h0 h2 h3)). Qed.
Lemma lem368212 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term117 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : (term117 A lt2 x' x y) = False.
Proof. exact (prop_ext (fun h4 : term117 A lt2 x' x y => @lem368211 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367720 A lt2 x' x y h1)). Qed.
Lemma lem368213 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term117 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368212 A x' lt2 y x h1 h2 h3) (@lem367720 A lt2 x' x y h1)). Qed.
Lemma lem368214 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term117 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368213 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367647 A lt2 y x h3)). Qed.
Lemma lem368215 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term117 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368214 A x' lt2 y x h1 h2 h3) (@lem367647 A lt2 y x h3)). Qed.
Lemma lem368216 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term117 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : lt2 x y => @lem368215 A x' lt2 y x h1 h2 h3) (fun h4 : False => @lem367641 A lt2 x y h2)). Qed.
Lemma lem368217 {A : Type'} (x' : A) (lt2 : type1402 A) (y : A) (x : A) (h1 : term117 A lt2 x' x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368216 A x' lt2 y x h1 h2 h3) (@lem367641 A lt2 x y h2)). Qed.
Lemma lem368218 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term56 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (ex_elim (@lem367634 A lt2 x y h1) (fun x' : A => fun h0 : term119 A lt2 x y x' => @lem368217 A x' lt2 y x h0 h2 h3)). Qed.
Lemma lem368219 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term56 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368218 A lt2 y x h1 h2 h3) (fun h4 : False => @lem367427 A lt2 y x h3)). Qed.
Lemma lem368220 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term56 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368219 A lt2 y x h1 h2 h3) (@lem367427 A lt2 y x h3)). Qed.
Lemma lem368221 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term56 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : lt2 x y => @lem368220 A lt2 y x h1 h2 h3) (fun h4 : False => @lem367421 A lt2 x y h2)). Qed.
Lemma lem368222 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term56 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368221 A lt2 y x h1 h2 h3) (@lem367421 A lt2 x y h2)). Qed.
Lemma lem368223 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 x y) (h2 : lt2 y x) : term145 A lt2 x y.
Proof. exact (fun h0 : term56 A lt2 x y => @lem368222 A lt2 y x h0 h1 h2). Qed.
Lemma lem368224 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term145 A lt2 x y) = (term57 A lt2 x y).
Proof. exact (@lem69 (term56 A lt2 x y)). Qed.
Lemma lem368225 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 x y) (h2 : lt2 y x) : term57 A lt2 x y.
Proof. exact (EQ_MP (@lem368224 A lt2 x y) (@lem368223 A lt2 y x h1 h2)). Qed.
Lemma lem368226 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : term58 A lt2 x y.
Proof. exact (fun h0 : lt2 y x => @lem368225 A lt2 y x h1 h0). Qed.
Lemma lem368227 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : term59 A lt2 x y.
Proof. exact (fun h0 : lt2 x y => @lem368226 A lt2 x y h0). Qed.
Lemma lem368232 {A : Type'} (x : A) (y : A) : term61 A x y.
Proof. exact (fun lt2 : type1402 A => @lem368227 A lt2 x y). Qed.
Lemma lem368237 {A : Type'} (y : A) : term63 A y.
Proof. exact (fun x : A => @lem368232 A x y). Qed.
Lemma lem368242 {A : Type'} : term65 A.
Proof. exact (fun y : A => @lem368237 A y). Qed.
Lemma lem368243 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem367412 A) (@lem368242 A)). Qed.
Lemma lem368244 {A : Type'} (y : A) : term146 A y.
Proof. exact (@lem368243 A y). Qed.
Lemma lem368245 {A : Type'} (y : A) : (term146 A y) = (term27 A y).
Proof. exact (eq_refl (term146 A y)). Qed.
Lemma lem368246 {A : Type'} (y : A) : term27 A y.
Proof. exact (EQ_MP (@lem368245 A y) (@lem368244 A y)). Qed.
Lemma lem368247 {A : Type'} (y : A) (x : A) : term147 A y x.
Proof. exact (@lem368246 A y x). Qed.
Lemma lem368248 {A : Type'} (x : A) (y : A) : (term147 A y x) = (term23 A x y).
Proof. exact (eq_refl (term147 A y x)). Qed.
Lemma lem368249 {A : Type'} (x : A) (y : A) : term23 A x y.
Proof. exact (EQ_MP (@lem368248 A x y) (@lem368247 A y x)). Qed.
Lemma lem368250 {A : Type'} (x : A) (y : A) (lt2 : type1402 A) : term148 A x y lt2.
Proof. exact (@lem368249 A x y lt2). Qed.
Lemma lem368251 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : (term148 A x y lt2) = (term10 A lt2 x y).
Proof. exact (eq_refl (term148 A x y lt2)). Qed.
Lemma lem368252 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : term10 A lt2 x y.
Proof. exact (EQ_MP (@lem368251 A lt2 x y) (@lem368250 A x y lt2)). Qed.
Lemma lem368254 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) : term10 A lt2 x y.
Proof. exact (@lem367157 A lt2 x y (@lem368252 A lt2 x y)). Qed.
Lemma lem368255 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : lt2 x y) : term18 A lt2 x y.
Proof. exact (@lem368254 A lt2 x y (@lem367128 A lt2 x y h1)). Qed.
Lemma lem368256 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 x y) (h2 : lt2 y x) : term8 A lt2 x y.
Proof. exact (@lem368255 A lt2 x y h1 (@lem367127 A lt2 y x h2)). Qed.
Lemma lem368257 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term9 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (@lem368256 A lt2 y x h2 h3 (@lem367141 A lt2 x y h1)). Qed.
Lemma lem368258 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term9 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : (term9 A lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : term9 A lt2 x y => @lem368257 A lt2 y x h1 h2 h3) (fun h4 : False => @lem367141 A lt2 x y h1)). Qed.
Lemma lem368259 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term9 A lt2 x y) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368258 A lt2 y x h1 h2 h3) (@lem367141 A lt2 x y h1)). Qed.
Lemma lem368260 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 x y) (h2 : lt2 y x) : term8 A lt2 x y.
Proof. exact (fun h0 : term9 A lt2 x y => @lem368259 A lt2 y x h0 h1 h2). Qed.
Lemma lem368261 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 x y) (h2 : lt2 y x) : term7 A lt2 x y.
Proof. exact (EQ_MP (@lem367140 A lt2 x y) (@lem368260 A lt2 y x h1 h2)). Qed.
Lemma lem368262 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term1 A lt2) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (@lem368261 A lt2 y x h2 h3 (@lem367136 A x y lt2 h1)). Qed.
Lemma lem368263 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : lt2 x y) (h2 : lt2 y x) : term149 A lt2.
Proof. exact (fun h0 : term1 A lt2 => @lem368262 A lt2 y x h0 h1 h2). Qed.
Lemma lem368264 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : @WF A lt2) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (@lem368263 A lt2 y x h2 h3 (@lem367132 A lt2 h1)). Qed.
Lemma lem368265 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term2 A lt2 y x) : lt2 y x.
Proof. exact (proj2 (@lem367126 A lt2 y x h1)). Qed.
Lemma lem368266 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : term2 A lt2 y x) : lt2 x y.
Proof. exact (proj1 (@lem367126 A lt2 y x h1)). Qed.
Lemma lem368267 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : @WF A lt2) (h2 : lt2 x y) (h3 : lt2 y x) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368264 A lt2 y x h1 h2 h3) (fun h4 : False => @lem367127 A lt2 y x h3)). Qed.
Lemma lem368268 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : @WF A lt2) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368267 A lt2 y x h1 h2 h3) (@lem367127 A lt2 y x h3)). Qed.
Lemma lem368269 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : @WF A lt2) (h2 : lt2 x y) (h3 : lt2 y x) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h4 : lt2 x y => @lem368268 A lt2 y x h1 h2 h3) (fun h4 : False => @lem367128 A lt2 x y h2)). Qed.
Lemma lem368270 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : @WF A lt2) (h2 : lt2 x y) (h3 : lt2 y x) : False.
Proof. exact (EQ_MP (@lem368269 A lt2 y x h1 h2 h3) (@lem367128 A lt2 x y h2)). Qed.
Lemma lem368271 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : @WF A lt2) (h2 : term2 A lt2 y x) (h3 : lt2 x y) : (lt2 y x) = False.
Proof. exact (prop_ext (fun h4 : lt2 y x => @lem368270 A lt2 y x h1 h3 h4) (fun h4 : False => @lem368265 A lt2 y x h2)). Qed.
Lemma lem368272 {A : Type'} (lt2 : type1402 A) (x : A) (y : A) (h1 : @WF A lt2) (h2 : term2 A lt2 y x) (h3 : lt2 x y) : False.
Proof. exact (EQ_MP (@lem368271 A lt2 x y h1 h2 h3) (@lem368265 A lt2 y x h2)). Qed.
Lemma lem368273 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : @WF A lt2) (h2 : term2 A lt2 y x) : (lt2 x y) = False.
Proof. exact (prop_ext (fun h3 : lt2 x y => @lem368272 A lt2 x y h1 h2 h3) (fun h3 : False => @lem368266 A lt2 y x h2)). Qed.
Lemma lem368274 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) (h1 : @WF A lt2) (h2 : term2 A lt2 y x) : False.
Proof. exact (EQ_MP (@lem368273 A lt2 y x h1 h2) (@lem368266 A lt2 y x h2)). Qed.
Lemma lem368275 {A : Type'} (y : A) (x : A) (lt2 : type1402 A) (h1 : @WF A lt2) : term150 A lt2 y x.
Proof. exact (fun h0 : term2 A lt2 y x => @lem368274 A lt2 y x h1 h0). Qed.
Lemma lem368276 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : (term150 A lt2 y x) = (term151 A lt2 y x).
Proof. exact (@lem69 (term2 A lt2 y x)). Qed.
Lemma lem368277 {A : Type'} (y : A) (x : A) (lt2 : type1402 A) (h1 : @WF A lt2) : term151 A lt2 y x.
Proof. exact (EQ_MP (@lem368276 A lt2 y x) (@lem368275 A y x lt2 h1)). Qed.
Lemma lem368278 {A : Type'} (y : A) (x : A) (lt2 : type1402 A) (h1 : @WF A lt2) : (@WF A lt2) = (term151 A lt2 y x).
Proof. exact (prop_ext (fun h2 : @WF A lt2 => @lem368277 A y x lt2 h1) (fun h2 : term151 A lt2 y x => @lem367125 A lt2 h1)). Qed.
Lemma lem368279 {A : Type'} (y : A) (x : A) (lt2 : type1402 A) (h1 : @WF A lt2) : term151 A lt2 y x.
Proof. exact (EQ_MP (@lem368278 A y x lt2 h1) (@lem367125 A lt2 h1)). Qed.
Lemma lem368280 {A : Type'} (lt2 : type1402 A) (y : A) (x : A) : term152 A lt2 y x.
Proof. exact (fun h0 : @WF A lt2 => @lem368279 A y x lt2 h0). Qed.
Lemma lem368285 {A : Type'} (lt2 : type1402 A) (x : A) : term153 A lt2 x.
Proof. exact (fun y : A => @lem368280 A lt2 y x). Qed.
Lemma lem368290 {A : Type'} (lt2 : type1402 A) : term154 A lt2.
Proof. exact (fun x : A => @lem368285 A lt2 x). Qed.
Lemma lem368295 {A : Type'} : term155 A.
Proof. exact (fun lt2 : type1402 A => @lem368290 A lt2). Qed.
