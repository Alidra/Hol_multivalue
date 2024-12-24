Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ABSORPTION_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3275040 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3275041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3275040 A s t). Qed.
Lemma lem3275042 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = s) = (term1 A x s).
Proof. exact (@lem3275041 A (@INSERT A x s) s). Qed.
Lemma lem3275051 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term2 A x s).
Proof. exact (eq_refl (term2 A x s)). Qed.
Lemma lem3275052 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = ((@INSERT A x s) = s)) = ((@IN A x s) = (term1 A x s)).
Proof. exact (MK_COMB (@lem3275051 A x s) (@lem3275042 A x s)). Qed.
Lemma lem3275057 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3275052 A x s)). Qed.
Lemma lem3275058 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3275059 {A : Type'} (x : A) : (term5 A x) = (term6 A x).
Proof. exact (MK_COMB (@lem3275058 A) (@lem3275057 A x)). Qed.
Lemma lem3275064 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (fun_ext (fun x : A => @lem3275059 A x)). Qed.
Lemma lem3275065 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275066 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (MK_COMB (@lem3275065 A) (@lem3275064 A)). Qed.
Lemma lem3275071 {A : Type'} : (term10 A) = (term9 A).
Proof. exact (SYM (@lem3275066 A)). Qed.
Lemma lem3275083 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3275084 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3275083 A P x). Qed.
Lemma lem3275085 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3275084 A s x). Qed.
Lemma lem3275086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3275087 {A : Type'} (s : A -> Prop) (x : A) : (term2 A x s) = (term11 A s x).
Proof. exact (MK_COMB (@lem3275086) (@lem3275085 A s x)). Qed.
Lemma lem3275095 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term12 A x y s) = (term13 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3275096 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term12 A x y s) = (term13 A y x s).
Proof. exact (@lem3275095 A y x s). Qed.
Lemma lem3275097 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term12 A x' x s) = (term13 A x x' s).
Proof. exact (@lem3275096 A x x' s). Qed.
Lemma lem3275103 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3275104 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3275103 A P x). Qed.
Lemma lem3275105 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3275104 A s x'). Qed.
Lemma lem3275106 {A : Type'} (x' : A) (x : A) : (term14 A x' x) = (term14 A x' x).
Proof. exact (eq_refl (term14 A x' x)). Qed.
Lemma lem3275107 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term13 A x x' s) = (term15 A x s x').
Proof. exact (MK_COMB (@lem3275106 A x' x) (@lem3275105 A s x')). Qed.
Lemma lem3275110 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term12 A x' x s) = (term15 A x s x').
Proof. exact (TRANS (@lem3275097 A x x' s) (@lem3275107 A x s x')). Qed.
Lemma lem3275111 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3275112 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term16 A x' x s) = (term17 A x s x').
Proof. exact (MK_COMB (@lem3275111) (@lem3275110 A x s x')). Qed.
Lemma lem3275114 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3275115 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3275114 A P x). Qed.
Lemma lem3275116 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3275115 A s x'). Qed.
Lemma lem3275117 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term12 A x' x s) = (@IN A x' s)) = ((term15 A x s x') = (s x')).
Proof. exact (MK_COMB (@lem3275112 A x s x') (@lem3275116 A s x')). Qed.
Lemma lem3275120 {A : Type'} (x : A) (s : A -> Prop) : (term18 A x s) = (term19 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275117 A x s x')). Qed.
Lemma lem3275121 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275122 {A : Type'} (x : A) (s : A -> Prop) : (term1 A x s) = (term20 A x s).
Proof. exact (MK_COMB (@lem3275121 A) (@lem3275120 A x s)). Qed.
Lemma lem3275127 {A : Type'} (x : A) (s : A -> Prop) : ((@IN A x s) = (term1 A x s)) = ((s x) = (term20 A x s)).
Proof. exact (MK_COMB (@lem3275087 A s x) (@lem3275122 A x s)). Qed.
Lemma lem3275130 {A : Type'} (x : A) : (term4 A x) = (term21 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3275127 A x s)). Qed.
Lemma lem3275131 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3275132 {A : Type'} (x : A) : (term6 A x) = (term22 A x).
Proof. exact (MK_COMB (@lem3275131 A) (@lem3275130 A x)). Qed.
Lemma lem3275137 {A : Type'} : (term8 A) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3275132 A x)). Qed.
Lemma lem3275138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275139 {A : Type'} : (term10 A) = (term24 A).
Proof. exact (MK_COMB (@lem3275138 A) (@lem3275137 A)). Qed.
Lemma lem3275144 {A : Type'} : (term24 A) = (term10 A).
Proof. exact (SYM (@lem3275139 A)). Qed.
Lemma lem3275146 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3275147 {A : Type'} : (term24 A) = (term26 A).
Proof. exact (@lem3275146 (term24 A)). Qed.
Lemma lem3275148 {A : Type'} : (term26 A) = (term24 A).
Proof. exact (SYM (@lem3275147 A)). Qed.
Lemma lem3275149 {A : Type'} (h1 : term27 A) : term27 A.
Proof. exact (h1). Qed.
Lemma lem3275152 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3275153 {A : Type'} : term28 A.
Proof. exact (fun h0 : term26 A => @lem3275152 A h0). Qed.
Lemma lem3275154 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3275155 {A : Type'} (h1 : term26 A) : term26 A.
Proof. exact (h1). Qed.
Lemma lem3275156 {A : Type'} (h1 : term26 A) (h2 : term28 A) : term26 A.
Proof. exact (@lem3275154 A h2 (@lem3275155 A h1)). Qed.
Lemma lem3275157 {A : Type'} (h1 : term26 A) : term29 A.
Proof. exact (fun h0 : term28 A => @lem3275156 A h1 h0). Qed.
Lemma lem3275158 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3275159 {A : Type'} (h1 : term26 A) (h2 : term28 A) : term26 A.
Proof. exact (@lem3275157 A h1 (@lem3275158 A h2)). Qed.
Lemma lem3275160 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (fun h0 : term26 A => @lem3275159 A h0 h1). Qed.
Lemma lem3275161 {A : Type'} : term30 A.
Proof. exact (fun h0 : term28 A => @lem3275160 A h0). Qed.
Lemma lem3275164 {A : Type'} : term28 A.
Proof. exact (@lem3275161 A (@lem3275153 A)). Qed.
Lemma lem3275165 {A : Type'} : term28 A.
Proof. exact (@lem3275164 A). Qed.
Lemma lem3275167 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3275168 {A : Type'} : (term26 A) = (term31 A).
Proof. exact (@lem3275167 (term27 A)). Qed.
Lemma lem3275170 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3275171 {A : Type'} : (term31 A) = (term24 A).
Proof. exact (@lem3275170 (term24 A)). Qed.
Lemma lem3275190 {A : Type'} : (term26 A) = (term24 A).
Proof. exact (TRANS (@lem3275168 A) (@lem3275171 A)). Qed.
Lemma lem3275199 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term15 A x s x') = (s x')) = ((term15 A x s x') = (s x')).
Proof. exact (eq_refl ((term15 A x s x') = (s x'))). Qed.
Lemma lem3275200 {A : Type'} (x : A) (s : A -> Prop) : (term19 A x s) = (term19 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275199 A x s x')). Qed.
Lemma lem3275201 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275202 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term20 A x s).
Proof. exact (MK_COMB (@lem3275201 A) (@lem3275200 A x s)). Qed.
Lemma lem3275205 {A : Type'} (s : A -> Prop) (x : A) : (term11 A s x) = (term11 A s x).
Proof. exact (eq_refl (term11 A s x)). Qed.
Lemma lem3275206 {A : Type'} (x : A) (s : A -> Prop) : ((s x) = (term20 A x s)) = ((s x) = (term20 A x s)).
Proof. exact (MK_COMB (@lem3275205 A s x) (@lem3275202 A x s)). Qed.
Lemma lem3275207 {A : Type'} (x : A) : (term21 A x) = (term21 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3275206 A x s)). Qed.
Lemma lem3275208 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3275209 {A : Type'} (x : A) : (term22 A x) = (term22 A x).
Proof. exact (MK_COMB (@lem3275208 A) (@lem3275207 A x)). Qed.
Lemma lem3275210 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (fun_ext (fun x : A => @lem3275209 A x)). Qed.
Lemma lem3275211 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275212 {A : Type'} : (term24 A) = (term24 A).
Proof. exact (MK_COMB (@lem3275211 A) (@lem3275210 A)). Qed.
Lemma lem3275235 {A : Type'} : (term26 A) = (term24 A).
Proof. exact (TRANS (@lem3275190 A) (@lem3275212 A)). Qed.
Lemma lem3275236 {A : Type'} : (term24 A) = (term26 A).
Proof. exact (SYM (@lem3275235 A)). Qed.
Lemma lem3275238 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3275239 {A : Type'} (x : A) (s : A -> Prop) : ((s x) = (term20 A x s)) = (term33 A x s).
Proof. exact (@lem3275238 ((s x) = (term20 A x s))). Qed.
Lemma lem3275240 {A : Type'} (x : A) (s : A -> Prop) : (term33 A x s) = ((s x) = (term20 A x s)).
Proof. exact (SYM (@lem3275239 A x s)). Qed.
Lemma lem3275241 {A : Type'} (x : A) (s : A -> Prop) (h1 : term34 A x s) : term34 A x s.
Proof. exact (h1). Qed.
Lemma lem3275252 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term35 A x s x') = (term36 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3275256 {A : Type'} (s : A -> Prop) (x' : A) : (term37 A s x') = (term37 A s x').
Proof. exact (eq_refl (term37 A s x')). Qed.
Lemma lem3275257 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (s x').
Proof. exact (eq_refl (s x')). Qed.
Lemma lem3275258 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3275259 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term38 A x s x') = (term39 A x s x').
Proof. exact (MK_COMB (@lem3275258) (@lem3275252 A x s x')). Qed.
Lemma lem3275260 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term40 A x s x') = (term41 A x s x').
Proof. exact (MK_COMB (@lem3275259 A x s x') (@lem3275256 A s x')). Qed.
Lemma lem3275265 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term42 A x s x') = (term42 A x s x').
Proof. exact (eq_refl (term42 A x s x')). Qed.
Lemma lem3275266 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term43 A x s x') = (term44 A x s x').
Proof. exact (MK_COMB (@lem3275265 A x s x') (@lem3275260 A x s x')). Qed.
Lemma lem3275267 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term45 A x s x') = (term43 A x s x').
Proof. exact (@lem17930 (term15 A x s x') (s x')). Qed.
Lemma lem3275268 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term45 A x s x') = (term44 A x s x').
Proof. exact (TRANS (@lem3275267 A x s x') (@lem3275266 A x s x')). Qed.
Lemma lem3275269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3275270 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term38 A x s x') = (term39 A x s x').
Proof. exact (MK_COMB (@lem3275269) (@lem3275252 A x s x')). Qed.
Lemma lem3275271 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term46 A x s x') = (term47 A x s x').
Proof. exact (MK_COMB (@lem3275270 A x s x') (@lem3275257 A s x')). Qed.
Lemma lem3275276 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term48 A x s x') = (term48 A x s x').
Proof. exact (eq_refl (term48 A x s x')). Qed.
Lemma lem3275277 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term49 A x s x') = (term50 A x s x').
Proof. exact (MK_COMB (@lem3275276 A x s x') (@lem3275271 A x s x')). Qed.
Lemma lem3275278 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term15 A x s x') = (s x')) = (term49 A x s x').
Proof. exact (@lem17784 (term15 A x s x') (s x')). Qed.
Lemma lem3275279 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term15 A x s x') = (s x')) = (term50 A x s x').
Proof. exact (TRANS (@lem3275278 A x s x') (@lem3275277 A x s x')). Qed.
Lemma lem3275280 {A : Type'} (P : A -> Prop) : (term51 A P) = (term52 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3275281 {A : Type'} (x : A) (s : A -> Prop) : (term53 A x s) = (term54 A x s).
Proof. exact (@lem3275280 A (term19 A x s)). Qed.
Lemma lem3275282 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term55 A x s x') = ((term15 A x s x') = (s x')).
Proof. exact (eq_refl (term55 A x s x')). Qed.
Lemma lem3275283 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3275284 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term56 A x s x') = (term45 A x s x').
Proof. exact (MK_COMB (@lem3275283) (@lem3275282 A x s x')). Qed.
Lemma lem3275285 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term56 A x s x') = (term44 A x s x').
Proof. exact (TRANS (@lem3275284 A x s x') (@lem3275268 A x s x')). Qed.
Lemma lem3275286 {A : Type'} (x : A) (s : A -> Prop) : (term57 A x s) = (term58 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275285 A x s x')). Qed.
Lemma lem3275287 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3275288 {A : Type'} (x : A) (s : A -> Prop) : (term54 A x s) = (term59 A x s).
Proof. exact (MK_COMB (@lem3275287 A) (@lem3275286 A x s)). Qed.
Lemma lem3275289 {A : Type'} (x : A) (s : A -> Prop) : (term53 A x s) = (term59 A x s).
Proof. exact (TRANS (@lem3275281 A x s) (@lem3275288 A x s)). Qed.
Lemma lem3275290 {A : Type'} (x : A) (s : A -> Prop) : (term19 A x s) = (term60 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275279 A x s x')). Qed.
Lemma lem3275291 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275292 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term61 A x s).
Proof. exact (MK_COMB (@lem3275291 A) (@lem3275290 A x s)). Qed.
Lemma lem3275294 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term62 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3275295 {A : Type'} (x : A) (s : A -> Prop) : (term63 A x s) = (term64 A x s).
Proof. exact (MK_COMB (@lem3275294 A s x) (@lem3275292 A x s)). Qed.
Lemma lem3275297 {A : Type'} (s : A -> Prop) (x : A) : (term65 A s x) = (term65 A s x).
Proof. exact (eq_refl (term65 A s x)). Qed.
Lemma lem3275298 {A : Type'} (x : A) (s : A -> Prop) : (term66 A x s) = (term67 A x s).
Proof. exact (MK_COMB (@lem3275297 A s x) (@lem3275289 A x s)). Qed.
Lemma lem3275299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3275300 {A : Type'} (x : A) (s : A -> Prop) : (term68 A x s) = (term69 A x s).
Proof. exact (MK_COMB (@lem3275299) (@lem3275298 A x s)). Qed.
Lemma lem3275301 {A : Type'} (x : A) (s : A -> Prop) : (term70 A x s) = (term71 A x s).
Proof. exact (MK_COMB (@lem3275300 A x s) (@lem3275295 A x s)). Qed.
Lemma lem3275302 {A : Type'} (x : A) (s : A -> Prop) : (term34 A x s) = (term70 A x s).
Proof. exact (@lem17646 (s x) (term20 A x s)). Qed.
Lemma lem3275303 {A : Type'} (x : A) (s : A -> Prop) : (term34 A x s) = (term71 A x s).
Proof. exact (TRANS (@lem3275302 A x s) (@lem3275301 A x s)). Qed.
Lemma lem3275353 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3275354 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (@lem3275353 A P Q). Qed.
Lemma lem3275355 {A : Type'} (x : A) (s : A -> Prop) : (term74 A x s) = (term75 A x s).
Proof. exact (@lem3275354 A (term76 A x s) (term77 A x s)). Qed.
Lemma lem3275356 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term78 A x s x') = (term79 A x s x').
Proof. exact (eq_refl (term78 A x s x')). Qed.
Lemma lem3275357 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3275358 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term80 A x s x') = (term48 A x s x').
Proof. exact (MK_COMB (@lem3275357) (@lem3275356 A x s x')). Qed.
Lemma lem3275359 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term81 A x s x') = (term47 A x s x').
Proof. exact (eq_refl (term81 A x s x')). Qed.
Lemma lem3275360 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term82 A x s x') = (term50 A x s x').
Proof. exact (MK_COMB (@lem3275358 A x s x') (@lem3275359 A x s x')). Qed.
Lemma lem3275361 {A : Type'} (x : A) (s : A -> Prop) : (term83 A x s) = (term60 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275360 A x s x')). Qed.
Lemma lem3275362 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275363 {A : Type'} (x : A) (s : A -> Prop) : (term74 A x s) = (term61 A x s).
Proof. exact (MK_COMB (@lem3275362 A) (@lem3275361 A x s)). Qed.
Lemma lem3275364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3275365 {A : Type'} (x : A) (s : A -> Prop) : (term84 A x s) = (term85 A x s).
Proof. exact (MK_COMB (@lem3275364) (@lem3275363 A x s)). Qed.
Lemma lem3275366 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term78 A x s x') = (term79 A x s x').
Proof. exact (eq_refl (term78 A x s x')). Qed.
Lemma lem3275367 {A : Type'} (x : A) (s : A -> Prop) : (term86 A x s) = (term76 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275366 A x s x')). Qed.
Lemma lem3275368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275369 {A : Type'} (x : A) (s : A -> Prop) : (term87 A x s) = (term88 A x s).
Proof. exact (MK_COMB (@lem3275368 A) (@lem3275367 A x s)). Qed.
Lemma lem3275370 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3275371 {A : Type'} (x : A) (s : A -> Prop) : (term89 A x s) = (term90 A x s).
Proof. exact (MK_COMB (@lem3275370) (@lem3275369 A x s)). Qed.
Lemma lem3275372 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term81 A x s x') = (term47 A x s x').
Proof. exact (eq_refl (term81 A x s x')). Qed.
Lemma lem3275373 {A : Type'} (x : A) (s : A -> Prop) : (term91 A x s) = (term77 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275372 A x s x')). Qed.
Lemma lem3275374 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275375 {A : Type'} (x : A) (s : A -> Prop) : (term92 A x s) = (term93 A x s).
Proof. exact (MK_COMB (@lem3275374 A) (@lem3275373 A x s)). Qed.
Lemma lem3275376 {A : Type'} (x : A) (s : A -> Prop) : (term75 A x s) = (term94 A x s).
Proof. exact (MK_COMB (@lem3275371 A x s) (@lem3275375 A x s)). Qed.
Lemma lem3275377 {A : Type'} (x : A) (s : A -> Prop) : ((term74 A x s) = (term75 A x s)) = ((term61 A x s) = (term94 A x s)).
Proof. exact (MK_COMB (@lem3275365 A x s) (@lem3275376 A x s)). Qed.
Lemma lem3275378 {A : Type'} (x : A) (s : A -> Prop) : (term61 A x s) = (term94 A x s).
Proof. exact (EQ_MP (@lem3275377 A x s) (@lem3275355 A x s)). Qed.
Lemma lem3275459 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term62 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3275460 {A : Type'} (x : A) (s : A -> Prop) : (term64 A x s) = (term95 A x s).
Proof. exact (MK_COMB (@lem3275459 A s x) (@lem3275378 A x s)). Qed.
Lemma lem3275461 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (term69 A x s).
Proof. exact (eq_refl (term69 A x s)). Qed.
Lemma lem3275462 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term96 A x s).
Proof. exact (MK_COMB (@lem3275461 A x s) (@lem3275460 A x s)). Qed.
Lemma lem3275464 {A : Type'} (P : Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3275465 {A : Type'} (P : Prop) (Q : A -> Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (@lem3275464 A P Q). Qed.
Lemma lem3275466 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term100 A x s).
Proof. exact (@lem3275465 A (s x) (term58 A x s)). Qed.
Lemma lem3275467 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term101 A x s x') = (term44 A x s x').
Proof. exact (eq_refl (term101 A x s x')). Qed.
Lemma lem3275468 {A : Type'} (x : A) (s : A -> Prop) : (term102 A x s) = (term58 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275467 A x s x')). Qed.
Lemma lem3275469 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3275470 {A : Type'} (x : A) (s : A -> Prop) : (term103 A x s) = (term59 A x s).
Proof. exact (MK_COMB (@lem3275469 A) (@lem3275468 A x s)). Qed.
Lemma lem3275471 {A : Type'} (s : A -> Prop) (x : A) : (term65 A s x) = (term65 A s x).
Proof. exact (eq_refl (term65 A s x)). Qed.
Lemma lem3275472 {A : Type'} (x : A) (s : A -> Prop) : (term99 A x s) = (term67 A x s).
Proof. exact (MK_COMB (@lem3275471 A s x) (@lem3275470 A x s)). Qed.
Lemma lem3275473 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3275474 {A : Type'} (x : A) (s : A -> Prop) : (term104 A x s) = (term105 A x s).
Proof. exact (MK_COMB (@lem3275473) (@lem3275472 A x s)). Qed.
Lemma lem3275475 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term101 A x s x') = (term44 A x s x').
Proof. exact (eq_refl (term101 A x s x')). Qed.
Lemma lem3275476 {A : Type'} (s : A -> Prop) (x : A) : (term65 A s x) = (term65 A s x).
Proof. exact (eq_refl (term65 A s x)). Qed.
Lemma lem3275477 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term106 A x s x') = (term107 A x s x').
Proof. exact (MK_COMB (@lem3275476 A s x) (@lem3275475 A x s x')). Qed.
Lemma lem3275478 {A : Type'} (x : A) (s : A -> Prop) : (term108 A x s) = (term109 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275477 A x s x')). Qed.
Lemma lem3275479 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3275480 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (term110 A x s).
Proof. exact (MK_COMB (@lem3275479 A) (@lem3275478 A x s)). Qed.
Lemma lem3275481 {A : Type'} (x : A) (s : A -> Prop) : ((term99 A x s) = (term100 A x s)) = ((term67 A x s) = (term110 A x s)).
Proof. exact (MK_COMB (@lem3275474 A x s) (@lem3275480 A x s)). Qed.
Lemma lem3275482 {A : Type'} (x : A) (s : A -> Prop) : (term67 A x s) = (term110 A x s).
Proof. exact (EQ_MP (@lem3275481 A x s) (@lem3275466 A x s)). Qed.
Lemma lem3275483 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3275484 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (term111 A x s).
Proof. exact (MK_COMB (@lem3275483) (@lem3275482 A x s)). Qed.
Lemma lem3275485 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term95 A x s).
Proof. exact (eq_refl (term95 A x s)). Qed.
Lemma lem3275486 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = (term112 A x s).
Proof. exact (MK_COMB (@lem3275484 A x s) (@lem3275485 A x s)). Qed.
Lemma lem3275488 {A : Type'} (P : A -> Prop) (Q : Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3275489 {A : Type'} (P : A -> Prop) (Q : Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (@lem3275488 A P Q). Qed.
Lemma lem3275490 {A : Type'} (x : A) (s : A -> Prop) : (term115 A x s) = (term116 A x s).
Proof. exact (@lem3275489 A (term109 A x s) (term95 A x s)). Qed.
Lemma lem3275491 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term117 A x s x') = (term107 A x s x').
Proof. exact (eq_refl (term117 A x s x')). Qed.
Lemma lem3275492 {A : Type'} (x : A) (s : A -> Prop) : (term118 A x s) = (term109 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275491 A x s x')). Qed.
Lemma lem3275493 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3275494 {A : Type'} (x : A) (s : A -> Prop) : (term119 A x s) = (term110 A x s).
Proof. exact (MK_COMB (@lem3275493 A) (@lem3275492 A x s)). Qed.
Lemma lem3275495 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3275496 {A : Type'} (x : A) (s : A -> Prop) : (term120 A x s) = (term111 A x s).
Proof. exact (MK_COMB (@lem3275495) (@lem3275494 A x s)). Qed.
Lemma lem3275497 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term95 A x s).
Proof. exact (eq_refl (term95 A x s)). Qed.
Lemma lem3275498 {A : Type'} (x : A) (s : A -> Prop) : (term115 A x s) = (term112 A x s).
Proof. exact (MK_COMB (@lem3275496 A x s) (@lem3275497 A x s)). Qed.
Lemma lem3275499 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3275500 {A : Type'} (x : A) (s : A -> Prop) : (term121 A x s) = (term122 A x s).
Proof. exact (MK_COMB (@lem3275499) (@lem3275498 A x s)). Qed.
Lemma lem3275501 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term117 A x s x') = (term107 A x s x').
Proof. exact (eq_refl (term117 A x s x')). Qed.
Lemma lem3275502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3275503 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term123 A x s x') = (term124 A x s x').
Proof. exact (MK_COMB (@lem3275502) (@lem3275501 A x s x')). Qed.
Lemma lem3275504 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term95 A x s).
Proof. exact (eq_refl (term95 A x s)). Qed.
Lemma lem3275505 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term125 A x' x s) = (term126 A x' x s).
Proof. exact (MK_COMB (@lem3275503 A x s x') (@lem3275504 A x s)). Qed.
Lemma lem3275506 {A : Type'} (x : A) (s : A -> Prop) : (term127 A x s) = (term128 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275505 A x' x s)). Qed.
Lemma lem3275507 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3275508 {A : Type'} (x : A) (s : A -> Prop) : (term116 A x s) = (term129 A x s).
Proof. exact (MK_COMB (@lem3275507 A) (@lem3275506 A x s)). Qed.
Lemma lem3275509 {A : Type'} (x : A) (s : A -> Prop) : ((term115 A x s) = (term116 A x s)) = ((term112 A x s) = (term129 A x s)).
Proof. exact (MK_COMB (@lem3275500 A x s) (@lem3275508 A x s)). Qed.
Lemma lem3275510 {A : Type'} (x : A) (s : A -> Prop) : (term112 A x s) = (term129 A x s).
Proof. exact (EQ_MP (@lem3275509 A x s) (@lem3275490 A x s)). Qed.
Lemma lem3275511 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = (term129 A x s).
Proof. exact (TRANS (@lem3275486 A x s) (@lem3275510 A x s)). Qed.
Lemma lem3275512 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term129 A x s).
Proof. exact (TRANS (@lem3275462 A x s) (@lem3275511 A x s)). Qed.
Lemma lem3275513 {A : Type'} (x : A) (s : A -> Prop) : (term34 A x s) = (term129 A x s).
Proof. exact (TRANS (@lem3275303 A x s) (@lem3275512 A x s)). Qed.
Lemma lem3275514 {A : Type'} (x : A) (s : A -> Prop) (h1 : term34 A x s) : term129 A x s.
Proof. exact (EQ_MP (@lem3275513 A x s) (@lem3275241 A x s h1)). Qed.
Lemma lem3275515 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term126 A x' x s) : term126 A x' x s.
Proof. exact (h1). Qed.
Lemma lem3275536 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term47 A x s x') = (term47 A x s x').
Proof. exact (eq_refl (term47 A x s x')). Qed.
Lemma lem3275537 {A : Type'} (x : A) (s : A -> Prop) : (term77 A x s) = (term77 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275536 A x s x')). Qed.
Lemma lem3275538 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275539 {A : Type'} (x : A) (s : A -> Prop) : (term93 A x s) = (term93 A x s).
Proof. exact (MK_COMB (@lem3275538 A) (@lem3275537 A x s)). Qed.
Lemma lem3275558 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term79 A x s x') = (term79 A x s x').
Proof. exact (eq_refl (term79 A x s x')). Qed.
Lemma lem3275559 {A : Type'} (x : A) (s : A -> Prop) : (term76 A x s) = (term76 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275558 A x s x')). Qed.
Lemma lem3275560 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275561 {A : Type'} (x : A) (s : A -> Prop) : (term88 A x s) = (term88 A x s).
Proof. exact (MK_COMB (@lem3275560 A) (@lem3275559 A x s)). Qed.
Lemma lem3275562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3275563 {A : Type'} (x : A) (s : A -> Prop) : (term90 A x s) = (term90 A x s).
Proof. exact (MK_COMB (@lem3275562) (@lem3275561 A x s)). Qed.
Lemma lem3275564 {A : Type'} (x : A) (s : A -> Prop) : (term94 A x s) = (term94 A x s).
Proof. exact (MK_COMB (@lem3275563 A x s) (@lem3275539 A x s)). Qed.
Lemma lem3275571 {A : Type'} (s : A -> Prop) (x : A) : (term62 A s x) = (term62 A s x).
Proof. exact (eq_refl (term62 A s x)). Qed.
Lemma lem3275572 {A : Type'} (x : A) (s : A -> Prop) : (term95 A x s) = (term95 A x s).
Proof. exact (MK_COMB (@lem3275571 A s x) (@lem3275564 A x s)). Qed.
Lemma lem3275623 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term124 A x s x') = (term124 A x s x').
Proof. exact (eq_refl (term124 A x s x')). Qed.
Lemma lem3275624 {A : Type'} (x' : A) (x : A) (s : A -> Prop) : (term126 A x' x s) = (term126 A x' x s).
Proof. exact (MK_COMB (@lem3275623 A x s x') (@lem3275572 A x s)). Qed.
Lemma lem3275625 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term126 A x' x s) : term126 A x' x s.
Proof. exact (EQ_MP (@lem3275624 A x' x s) (@lem3275515 A x' x s h1)). Qed.
Lemma lem3275626 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : term107 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3275627 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term95 A x s.
Proof. exact (h1). Qed.
Lemma lem3275628 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : term44 A x s x'.
Proof. exact (proj2 (@lem3275626 A x s x' h1)). Qed.
Lemma lem3275630 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : term41 A x s x'.
Proof. exact (proj2 (@lem3275628 A x s x' h1)). Qed.
Lemma lem3275631 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : term130 A x s x'.
Proof. exact (proj1 (@lem3275628 A x s x' h1)). Qed.
Lemma lem3275632 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term36 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3275636 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term15 A x s x') : term15 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3275640 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term15 A x s x') : term15 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3275644 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term94 A x s.
Proof. exact (proj2 (@lem3275627 A x s h1)). Qed.
Lemma lem3275646 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term93 A x s.
Proof. exact (proj2 (@lem3275644 A x s h1)). Qed.
Lemma lem3275663 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3275679 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275695 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275703 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3275707 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3275715 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3275719 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275727 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3275731 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275772 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term47 A x s x') = (term131 A x s x').
Proof. exact (@lem19699 (term132 A x' x) (term37 A s x') (s x')). Qed.
Lemma lem3275773 {A : Type'} (x : A) (s : A -> Prop) : (term77 A x s) = (term133 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3275772 A x s x')). Qed.
Lemma lem3275774 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3275776 {A : Type'} (x : A) (s : A -> Prop) : (term93 A x s) = (term134 A x s).
Proof. exact (MK_COMB (@lem3275774 A) (@lem3275773 A x s)). Qed.
Lemma lem3275777 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term134 A x s.
Proof. exact (EQ_MP (@lem3275776 A x s) (@lem3275646 A x s h1)). Qed.
Lemma lem3275781 {A : Type'} (_33481 : A) (x : A) (s : A -> Prop) (h1 : term95 A x s) : term135 A x s _33481.
Proof. exact (@lem3275777 A x s h1 _33481). Qed.
Lemma lem3275782 {A : Type'} (x : A) (s : A -> Prop) (_33481 : A) : (term135 A x s _33481) = (term131 A x s _33481).
Proof. exact (eq_refl (term135 A x s _33481)). Qed.
Lemma lem3275783 {A : Type'} (_33481 : A) (x : A) (s : A -> Prop) (h1 : term95 A x s) : term131 A x s _33481.
Proof. exact (EQ_MP (@lem3275782 A x s _33481) (@lem3275781 A _33481 x s h1)). Qed.
Lemma lem3275791 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term37 A s x'.
Proof. exact (proj2 (@lem3275632 A x s x' h1)). Qed.
Lemma lem3275793 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3275799 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term37 A s x'.
Proof. exact (proj2 (@lem3275632 A x s x' h1)). Qed.
Lemma lem3275801 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275807 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term37 A s x'.
Proof. exact (proj2 (@lem3275632 A x s x' h1)). Qed.
Lemma lem3275809 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275813 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3275815 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3275819 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3275821 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275825 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term37 A s x'.
Proof. exact (h1). Qed.
Lemma lem3275827 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3275829 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term37 A s x.
Proof. exact (proj1 (@lem3275627 A x s h1)). Qed.
Lemma lem3275847 {A : Type'} (_33481 : A) (x : A) (s : A -> Prop) (h1 : term95 A x s) : term136 A x s _33481.
Proof. exact (proj1 (@lem3275783 A _33481 x s h1)). Qed.
Lemma lem3275895 {A : Type'} (s : A -> Prop) : (term137 A s) = (term137 A s).
Proof. exact (eq_refl (term137 A s)). Qed.
Lemma lem3275896 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term138 A s x') = (term138 A s x).
Proof. exact (MK_COMB (@lem3275895 A s) (@lem3275793 A x' x h1)). Qed.
Lemma lem3275897 {A : Type'} (s : A -> Prop) (x : A) : (term138 A s x) = (term37 A s x).
Proof. exact (eq_refl (term138 A s x)). Qed.
Lemma lem3275898 {A : Type'} (s : A -> Prop) (x' : A) : (term139 A s x') = (term139 A s x').
Proof. exact (eq_refl (term139 A s x')). Qed.
Lemma lem3275899 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term138 A s x') = (term138 A s x)) = ((term138 A s x') = (term37 A s x)).
Proof. exact (MK_COMB (@lem3275898 A s x') (@lem3275897 A s x)). Qed.
Lemma lem3275900 {A : Type'} (s : A -> Prop) (x' : A) : (term138 A s x') = (term37 A s x').
Proof. exact (eq_refl (term138 A s x')). Qed.
Lemma lem3275901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3275902 {A : Type'} (s : A -> Prop) (x' : A) : (term139 A s x') = (term140 A s x').
Proof. exact (MK_COMB (@lem3275901) (@lem3275900 A s x')). Qed.
Lemma lem3275903 {A : Type'} (s : A -> Prop) (x : A) : (term37 A s x) = (term37 A s x).
Proof. exact (eq_refl (term37 A s x)). Qed.
Lemma lem3275904 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term138 A s x') = (term37 A s x)) = ((term37 A s x') = (term37 A s x)).
Proof. exact (MK_COMB (@lem3275902 A s x') (@lem3275903 A s x)). Qed.
Lemma lem3275905 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term138 A s x') = (term138 A s x)) = ((term37 A s x') = (term37 A s x)).
Proof. exact (TRANS (@lem3275899 A x' s x) (@lem3275904 A x' s x)). Qed.
Lemma lem3275906 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term37 A s x') = (term37 A s x).
Proof. exact (EQ_MP (@lem3275905 A x' s x) (@lem3275896 A s x' x h1)). Qed.
Lemma lem3275907 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : x' = x) : term37 A s x.
Proof. exact (EQ_MP (@lem3275906 A s x' x h2) (@lem3275791 A x s x' h1)). Qed.
Lemma lem3275936 {A : Type'} (s : A -> Prop) : (term137 A s) = (term137 A s).
Proof. exact (eq_refl (term137 A s)). Qed.
Lemma lem3275937 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term138 A s x') = (term138 A s x).
Proof. exact (MK_COMB (@lem3275936 A s) (@lem3275815 A x' x h1)). Qed.
Lemma lem3275938 {A : Type'} (s : A -> Prop) (x : A) : (term138 A s x) = (term37 A s x).
Proof. exact (eq_refl (term138 A s x)). Qed.
Lemma lem3275939 {A : Type'} (s : A -> Prop) (x' : A) : (term139 A s x') = (term139 A s x').
Proof. exact (eq_refl (term139 A s x')). Qed.
Lemma lem3275940 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term138 A s x') = (term138 A s x)) = ((term138 A s x') = (term37 A s x)).
Proof. exact (MK_COMB (@lem3275939 A s x') (@lem3275938 A s x)). Qed.
Lemma lem3275941 {A : Type'} (s : A -> Prop) (x' : A) : (term138 A s x') = (term37 A s x').
Proof. exact (eq_refl (term138 A s x')). Qed.
Lemma lem3275942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3275943 {A : Type'} (s : A -> Prop) (x' : A) : (term139 A s x') = (term140 A s x').
Proof. exact (MK_COMB (@lem3275942) (@lem3275941 A s x')). Qed.
Lemma lem3275944 {A : Type'} (s : A -> Prop) (x : A) : (term37 A s x) = (term37 A s x).
Proof. exact (eq_refl (term37 A s x)). Qed.
Lemma lem3275945 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term138 A s x') = (term37 A s x)) = ((term37 A s x') = (term37 A s x)).
Proof. exact (MK_COMB (@lem3275943 A s x') (@lem3275944 A s x)). Qed.
Lemma lem3275946 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term138 A s x') = (term138 A s x)) = ((term37 A s x') = (term37 A s x)).
Proof. exact (TRANS (@lem3275940 A x' s x) (@lem3275945 A x' s x)). Qed.
Lemma lem3275947 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term37 A s x') = (term37 A s x).
Proof. exact (EQ_MP (@lem3275946 A x' s x) (@lem3275937 A s x' x h1)). Qed.
Lemma lem3275948 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : x' = x) : term37 A s x.
Proof. exact (EQ_MP (@lem3275947 A s x' x h2) (@lem3275813 A s x' h1)). Qed.
Lemma lem3275964 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : s x.
Proof. exact (proj1 (@lem3275626 A x s x' h1)). Qed.
Lemma lem3275965 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : term141 A s x.
Proof. exact (fun h0 : term37 A s x => @lem3275964 A x s x' h1). Qed.
Lemma lem3275967 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3275968 {A : Type'} (s : A -> Prop) (x : A) : (term141 A s x) = (s x).
Proof. exact (@lem3275967 (s x)). Qed.
Lemma lem3275969 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : s x.
Proof. exact (EQ_MP (@lem3275968 A s x) (@lem3275965 A x s x' h1)). Qed.
Lemma lem3275972 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3275974 {A : Type'} (s : A -> Prop) (x : A) : (term37 A s x) = (term143 A s x).
Proof. exact (@lem3275972 (s x)). Qed.
Lemma lem3275977 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : x' = x) : term143 A s x.
Proof. exact (EQ_MP (@lem3275974 A s x) (@lem3275907 A s x' x h1 h2)). Qed.
Lemma lem3275980 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3275977 A s x' x h1 h3 (@lem3275969 A x s x' h2)). Qed.
Lemma lem3275981 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : term144.
Proof. exact (fun h0 : ~ False => @lem3275980 A s x' x h1 h2 h3). Qed.
Lemma lem3275983 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3275984 : term144 = False.
Proof. exact (@lem3275983 False). Qed.
Lemma lem3276001 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276002 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term141 A s x'.
Proof. exact (fun h0 : term37 A s x' => @lem3276001 A s x' h1). Qed.
Lemma lem3276004 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276005 {A : Type'} (s : A -> Prop) (x' : A) : (term141 A s x') = (s x').
Proof. exact (@lem3276004 (s x')). Qed.
Lemma lem3276006 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3276005 A s x') (@lem3276002 A s x' h1)). Qed.
Lemma lem3276009 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3276011 {A : Type'} (s : A -> Prop) (x' : A) : (term37 A s x') = (term143 A s x').
Proof. exact (@lem3276009 (s x')). Qed.
Lemma lem3276014 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term143 A s x'.
Proof. exact (EQ_MP (@lem3276011 A s x') (@lem3275799 A x s x' h1)). Qed.
Lemma lem3276017 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (@lem3276014 A x s x' h2 (@lem3276006 A s x' h1)). Qed.
Lemma lem3276018 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : term144.
Proof. exact (fun h0 : ~ False => @lem3276017 A x s x' h1 h2). Qed.
Lemma lem3276020 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276021 : term144 = False.
Proof. exact (@lem3276020 False). Qed.
Lemma lem3276022 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276021) (@lem3276018 A x s x' h1 h2)). Qed.
Lemma lem3276038 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276039 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term141 A s x'.
Proof. exact (fun h0 : term37 A s x' => @lem3276038 A s x' h1). Qed.
Lemma lem3276041 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276042 {A : Type'} (s : A -> Prop) (x' : A) : (term141 A s x') = (s x').
Proof. exact (@lem3276041 (s x')). Qed.
Lemma lem3276043 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3276042 A s x') (@lem3276039 A s x' h1)). Qed.
Lemma lem3276046 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3276048 {A : Type'} (s : A -> Prop) (x' : A) : (term37 A s x') = (term143 A s x').
Proof. exact (@lem3276046 (s x')). Qed.
Lemma lem3276051 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') : term143 A s x'.
Proof. exact (EQ_MP (@lem3276048 A s x') (@lem3275807 A x s x' h1)). Qed.
Lemma lem3276054 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (@lem3276051 A x s x' h2 (@lem3276043 A s x' h1)). Qed.
Lemma lem3276055 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : term144.
Proof. exact (fun h0 : ~ False => @lem3276054 A x s x' h1 h2). Qed.
Lemma lem3276057 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276058 : term144 = False.
Proof. exact (@lem3276057 False). Qed.
Lemma lem3276059 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276058) (@lem3276055 A x s x' h1 h2)). Qed.
Lemma lem3276061 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : s x.
Proof. exact (proj1 (@lem3275626 A x s x' h1)). Qed.
Lemma lem3276062 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : term141 A s x.
Proof. exact (fun h0 : term37 A s x => @lem3276061 A x s x' h1). Qed.
Lemma lem3276064 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276065 {A : Type'} (s : A -> Prop) (x : A) : (term141 A s x) = (s x).
Proof. exact (@lem3276064 (s x)). Qed.
Lemma lem3276066 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : s x.
Proof. exact (EQ_MP (@lem3276065 A s x) (@lem3276062 A x s x' h1)). Qed.
Lemma lem3276069 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3276071 {A : Type'} (s : A -> Prop) (x : A) : (term37 A s x) = (term143 A s x).
Proof. exact (@lem3276069 (s x)). Qed.
Lemma lem3276074 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : x' = x) : term143 A s x.
Proof. exact (EQ_MP (@lem3276071 A s x) (@lem3275948 A s x' x h1 h2)). Qed.
Lemma lem3276077 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (@lem3276074 A s x' x h1 h3 (@lem3276066 A x s x' h2)). Qed.
Lemma lem3276078 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : term144.
Proof. exact (fun h0 : ~ False => @lem3276077 A s x' x h1 h2 h3). Qed.
Lemma lem3276080 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276081 : term144 = False.
Proof. exact (@lem3276080 False). Qed.
Lemma lem3276084 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276085 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term141 A s x'.
Proof. exact (fun h0 : term37 A s x' => @lem3276084 A s x' h1). Qed.
Lemma lem3276087 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276088 {A : Type'} (s : A -> Prop) (x' : A) : (term141 A s x') = (s x').
Proof. exact (@lem3276087 (s x')). Qed.
Lemma lem3276089 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3276088 A s x') (@lem3276085 A s x' h1)). Qed.
Lemma lem3276092 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3276094 {A : Type'} (s : A -> Prop) (x' : A) : (term37 A s x') = (term143 A s x').
Proof. exact (@lem3276092 (s x')). Qed.
Lemma lem3276097 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term143 A s x'.
Proof. exact (EQ_MP (@lem3276094 A s x') (@lem3275819 A s x' h1)). Qed.
Lemma lem3276100 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (@lem3276097 A s x' h1 (@lem3276089 A s x' h2)). Qed.
Lemma lem3276101 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : term144.
Proof. exact (fun h0 : ~ False => @lem3276100 A s x' h1 h2). Qed.
Lemma lem3276103 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276104 : term144 = False.
Proof. exact (@lem3276103 False). Qed.
Lemma lem3276105 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276104) (@lem3276101 A s x' h1 h2)). Qed.
Lemma lem3276107 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3276108 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term141 A s x'.
Proof. exact (fun h0 : term37 A s x' => @lem3276107 A s x' h1). Qed.
Lemma lem3276110 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276111 {A : Type'} (s : A -> Prop) (x' : A) : (term141 A s x') = (s x').
Proof. exact (@lem3276110 (s x')). Qed.
Lemma lem3276112 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3276111 A s x') (@lem3276108 A s x' h1)). Qed.
Lemma lem3276115 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3276117 {A : Type'} (s : A -> Prop) (x' : A) : (term37 A s x') = (term143 A s x').
Proof. exact (@lem3276115 (s x')). Qed.
Lemma lem3276120 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') : term143 A s x'.
Proof. exact (EQ_MP (@lem3276117 A s x') (@lem3275825 A s x' h1)). Qed.
Lemma lem3276123 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (@lem3276120 A s x' h1 (@lem3276112 A s x' h2)). Qed.
Lemma lem3276124 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : term144.
Proof. exact (fun h0 : ~ False => @lem3276123 A s x' h1 h2). Qed.
Lemma lem3276126 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276127 : term144 = False.
Proof. exact (@lem3276126 False). Qed.
Lemma lem3276128 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276127) (@lem3276124 A s x' h1 h2)). Qed.
Lemma lem3276144 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3276145 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3276144 A x). Qed.
Lemma lem3276146 {A : Type'} (x : A) : term145 A x.
Proof. exact (fun h0 : term146 A x => @lem3276145 A x). Qed.
Lemma lem3276148 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276149 {A : Type'} (x : A) : (term145 A x) = (x = x).
Proof. exact (@lem3276148 (x = x)). Qed.
Lemma lem3276150 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3276149 A x) (@lem3276146 A x)). Qed.
Lemma lem3276156 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3276157 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : (term136 A x s _33481) = (term147 A s _33481 x).
Proof. exact (@lem3276156 (s _33481) (term132 A _33481 x)). Qed.
Lemma lem3276165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3276166 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : (term148 A x s _33481) = (term149 A s _33481 x).
Proof. exact (MK_COMB (@lem3276165) (@lem3276157 A s _33481 x)). Qed.
Lemma lem3276174 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : (term147 A s _33481 x) = (term147 A s _33481 x).
Proof. exact (eq_refl (term147 A s _33481 x)). Qed.
Lemma lem3276175 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : ((term136 A x s _33481) = (term147 A s _33481 x)) = ((term147 A s _33481 x) = (term147 A s _33481 x)).
Proof. exact (MK_COMB (@lem3276166 A s _33481 x) (@lem3276174 A s _33481 x)). Qed.
Lemma lem3276177 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3276178 (x : Prop) : (x = x) = True.
Proof. exact (@lem3276177 Prop x). Qed.
Lemma lem3276179 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : ((term147 A s _33481 x) = (term147 A s _33481 x)) = True.
Proof. exact (@lem3276178 (term147 A s _33481 x)). Qed.
Lemma lem3276180 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : ((term136 A x s _33481) = (term147 A s _33481 x)) = True.
Proof. exact (TRANS (@lem3276175 A s _33481 x) (@lem3276179 A s _33481 x)). Qed.
Lemma lem3276181 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : True = ((term136 A x s _33481) = (term147 A s _33481 x)).
Proof. exact (SYM (@lem3276180 A s _33481 x)). Qed.
Lemma lem3276182 {A : Type'} (s : A -> Prop) (_33481 : A) (x : A) : (term136 A x s _33481) = (term147 A s _33481 x).
Proof. exact (EQ_MP (@lem3276181 A s _33481 x) (@lem0)). Qed.
Lemma lem3276183 {A : Type'} (_33481 : A) (x : A) (s : A -> Prop) (h1 : term95 A x s) : term147 A s _33481 x.
Proof. exact (EQ_MP (@lem3276182 A s _33481 x) (@lem3275847 A _33481 x s h1)). Qed.
Lemma lem3276185 (b : Prop) (a : Prop) : (a \/ b) = (term150 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3276186 {A : Type'} (x : A) (s : A -> Prop) (_33481 : A) : (term147 A s _33481 x) = (term151 A x s _33481).
Proof. exact (@lem3276185 (term132 A _33481 x) (s _33481)). Qed.
Lemma lem3276188 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3276189 {A : Type'} (_33481 : A) (x : A) : (term152 A _33481 x) = (_33481 = x).
Proof. exact (@lem3276188 (_33481 = x)). Qed.
Lemma lem3276190 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3276191 {A : Type'} (_33481 : A) (x : A) : (term153 A _33481 x) = (term154 A _33481 x).
Proof. exact (MK_COMB (@lem3276190) (@lem3276189 A _33481 x)). Qed.
Lemma lem3276192 {A : Type'} (s : A -> Prop) (_33481 : A) : (s _33481) = (s _33481).
Proof. exact (eq_refl (s _33481)). Qed.
Lemma lem3276193 {A : Type'} (x : A) (s : A -> Prop) (_33481 : A) : (term151 A x s _33481) = (term155 A x s _33481).
Proof. exact (MK_COMB (@lem3276191 A _33481 x) (@lem3276192 A s _33481)). Qed.
Lemma lem3276194 {A : Type'} (x : A) (s : A -> Prop) (_33481 : A) : (term147 A s _33481 x) = (term155 A x s _33481).
Proof. exact (TRANS (@lem3276186 A x s _33481) (@lem3276193 A x s _33481)). Qed.
Lemma lem3276197 {A : Type'} (_33481 : A) (x : A) (s : A -> Prop) (h1 : term95 A x s) : term155 A x s _33481.
Proof. exact (EQ_MP (@lem3276194 A x s _33481) (@lem3276183 A _33481 x s h1)). Qed.
Lemma lem3276198 {A : Type'} (_33481 : A) (x : A) (s : A -> Prop) (h1 : term95 A x s) : term155 A x s _33481.
Proof. exact (@lem3276197 A _33481 x s h1). Qed.
Lemma lem3276199 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term156 A s x.
Proof. exact (@lem3276198 A x x s h1). Qed.
Lemma lem3276202 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : s x.
Proof. exact (@lem3276199 A x s h1 (@lem3276150 A x)). Qed.
Lemma lem3276203 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term141 A s x.
Proof. exact (fun h0 : term37 A s x => @lem3276202 A x s h1). Qed.
Lemma lem3276205 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276206 {A : Type'} (s : A -> Prop) (x : A) : (term141 A s x) = (s x).
Proof. exact (@lem3276205 (s x)). Qed.
Lemma lem3276207 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : s x.
Proof. exact (EQ_MP (@lem3276206 A s x) (@lem3276203 A x s h1)). Qed.
Lemma lem3276210 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3276212 {A : Type'} (s : A -> Prop) (x : A) : (term37 A s x) = (term143 A s x).
Proof. exact (@lem3276210 (s x)). Qed.
Lemma lem3276215 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term143 A s x.
Proof. exact (EQ_MP (@lem3276212 A s x) (@lem3275829 A x s h1)). Qed.
Lemma lem3276218 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : False.
Proof. exact (@lem3276215 A x s h1 (@lem3276207 A x s h1)). Qed.
Lemma lem3276219 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : term144.
Proof. exact (fun h0 : ~ False => @lem3276218 A x s h1). Qed.
Lemma lem3276221 (p : Prop) : (term142 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3276222 : term144 = False.
Proof. exact (@lem3276221 False). Qed.
Lemma lem3276223 {A : Type'} (x : A) (s : A -> Prop) (h1 : term95 A x s) : False.
Proof. exact (EQ_MP (@lem3276222) (@lem3276219 A x s h1)). Qed.
Lemma lem3276224 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276081) (@lem3276078 A s x' x h1 h2 h3)). Qed.
Lemma lem3276225 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3275984) (@lem3275981 A s x' x h1 h2 h3)). Qed.
Lemma lem3276226 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276128 A s x' h1 h2) (fun h3 : False => @lem3275827 A s x' h2)). Qed.
Lemma lem3276227 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276226 A s x' h1 h2) (@lem3275827 A s x' h2)). Qed.
Lemma lem3276228 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3276227 A s x' h1 h2) (fun h3 : False => @lem3275825 A s x' h1)). Qed.
Lemma lem3276229 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276228 A s x' h1 h2) (@lem3275825 A s x' h1)). Qed.
Lemma lem3276230 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276105 A s x' h1 h2) (fun h3 : False => @lem3275821 A s x' h2)). Qed.
Lemma lem3276231 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276230 A s x' h1 h2) (@lem3275821 A s x' h2)). Qed.
Lemma lem3276232 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3276231 A s x' h1 h2) (fun h3 : False => @lem3275819 A s x' h1)). Qed.
Lemma lem3276233 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276232 A s x' h1 h2) (@lem3275819 A s x' h1)). Qed.
Lemma lem3276234 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3276224 A s x' x h1 h2 h3) (fun h4 : False => @lem3275815 A x' x h3)). Qed.
Lemma lem3276235 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276234 A s x' x h1 h2 h3) (@lem3275815 A x' x h3)). Qed.
Lemma lem3276236 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h4 : term37 A s x' => @lem3276235 A s x' x h1 h2 h3) (fun h4 : False => @lem3275813 A s x' h1)). Qed.
Lemma lem3276237 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276236 A s x' x h1 h2 h3) (@lem3275813 A s x' h1)). Qed.
Lemma lem3276238 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276059 A x s x' h1 h2) (fun h3 : False => @lem3275809 A s x' h1)). Qed.
Lemma lem3276239 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276238 A x s x' h1 h2) (@lem3275809 A s x' h1)). Qed.
Lemma lem3276240 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276022 A x s x' h1 h2) (fun h3 : False => @lem3275801 A s x' h1)). Qed.
Lemma lem3276241 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276240 A x s x' h1 h2) (@lem3275801 A s x' h1)). Qed.
Lemma lem3276242 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3276225 A s x' x h1 h2 h3) (fun h4 : False => @lem3275793 A x' x h3)). Qed.
Lemma lem3276243 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276242 A s x' x h1 h2 h3) (@lem3275793 A x' x h3)). Qed.
Lemma lem3276244 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276229 A s x' h1 h2) (fun h3 : False => @lem3275731 A s x' h2)). Qed.
Lemma lem3276245 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276244 A s x' h1 h2) (@lem3275731 A s x' h2)). Qed.
Lemma lem3276246 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3276245 A s x' h1 h2) (fun h3 : False => @lem3275727 A s x' h1)). Qed.
Lemma lem3276247 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276246 A s x' h1 h2) (@lem3275727 A s x' h1)). Qed.
Lemma lem3276248 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276233 A s x' h1 h2) (fun h3 : False => @lem3275719 A s x' h2)). Qed.
Lemma lem3276249 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276248 A s x' h1 h2) (@lem3275719 A s x' h2)). Qed.
Lemma lem3276250 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3276249 A s x' h1 h2) (fun h3 : False => @lem3275715 A s x' h1)). Qed.
Lemma lem3276251 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276250 A s x' h1 h2) (@lem3275715 A s x' h1)). Qed.
Lemma lem3276252 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3276237 A s x' x h1 h2 h3) (fun h4 : False => @lem3275707 A x' x h3)). Qed.
Lemma lem3276253 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276252 A s x' x h1 h2 h3) (@lem3275707 A x' x h3)). Qed.
Lemma lem3276254 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h4 : term37 A s x' => @lem3276253 A s x' x h1 h2 h3) (fun h4 : False => @lem3275703 A s x' h1)). Qed.
Lemma lem3276255 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276254 A s x' x h1 h2 h3) (@lem3275703 A s x' h1)). Qed.
Lemma lem3276256 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276239 A x s x' h1 h2) (fun h3 : False => @lem3275695 A s x' h1)). Qed.
Lemma lem3276257 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276256 A x s x' h1 h2) (@lem3275695 A s x' h1)). Qed.
Lemma lem3276258 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276241 A x s x' h1 h2) (fun h3 : False => @lem3275679 A s x' h1)). Qed.
Lemma lem3276259 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276258 A x s x' h1 h2) (@lem3275679 A s x' h1)). Qed.
Lemma lem3276260 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3276243 A s x' x h1 h2 h3) (fun h4 : False => @lem3275663 A x' x h3)). Qed.
Lemma lem3276261 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276260 A s x' x h1 h2 h3) (@lem3275663 A x' x h3)). Qed.
Lemma lem3276262 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276247 A s x' h1 h2) (fun h3 : False => @lem3275731 A s x' h2)). Qed.
Lemma lem3276263 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276262 A s x' h1 h2) (@lem3275731 A s x' h2)). Qed.
Lemma lem3276264 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3276263 A s x' h1 h2) (fun h3 : False => @lem3275727 A s x' h1)). Qed.
Lemma lem3276265 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276264 A s x' h1 h2) (@lem3275727 A s x' h1)). Qed.
Lemma lem3276266 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276251 A s x' h1 h2) (fun h3 : False => @lem3275719 A s x' h2)). Qed.
Lemma lem3276267 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276266 A s x' h1 h2) (@lem3275719 A s x' h2)). Qed.
Lemma lem3276268 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : (term37 A s x') = False.
Proof. exact (prop_ext (fun h3 : term37 A s x' => @lem3276267 A s x' h1 h2) (fun h3 : False => @lem3275715 A s x' h1)). Qed.
Lemma lem3276269 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3276268 A s x' h1 h2) (@lem3275715 A s x' h1)). Qed.
Lemma lem3276270 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3276255 A s x' x h1 h2 h3) (fun h4 : False => @lem3275707 A x' x h3)). Qed.
Lemma lem3276271 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276270 A s x' x h1 h2 h3) (@lem3275707 A x' x h3)). Qed.
Lemma lem3276272 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : (term37 A s x') = False.
Proof. exact (prop_ext (fun h4 : term37 A s x' => @lem3276271 A s x' x h1 h2 h3) (fun h4 : False => @lem3275703 A s x' h1)). Qed.
Lemma lem3276273 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276272 A s x' x h1 h2 h3) (@lem3275703 A s x' h1)). Qed.
Lemma lem3276274 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276257 A x s x' h1 h2) (fun h3 : False => @lem3275695 A s x' h1)). Qed.
Lemma lem3276275 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276274 A x s x' h1 h2) (@lem3275695 A s x' h1)). Qed.
Lemma lem3276276 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3276259 A x s x' h1 h2) (fun h3 : False => @lem3275679 A s x' h1)). Qed.
Lemma lem3276277 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term36 A x s x') : False.
Proof. exact (EQ_MP (@lem3276276 A x s x' h1 h2) (@lem3275679 A s x' h1)). Qed.
Lemma lem3276278 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3276261 A s x' x h1 h2 h3) (fun h4 : False => @lem3275663 A x' x h3)). Qed.
Lemma lem3276279 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3276278 A s x' x h1 h2 h3) (@lem3275663 A x' x h3)). Qed.
Lemma lem3276280 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : term107 A x s x') (h3 : term15 A x s x') : False.
Proof. exact (or_elim (@lem3275640 A x s x' h3) (fun h0 : x' = x => @lem3276273 A s x' x h1 h2 h0) (fun h0 : s x' => @lem3276269 A s x' h1 h0)). Qed.
Lemma lem3276281 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term37 A s x') (h2 : term107 A x s x') : False.
Proof. exact (or_elim (@lem3275631 A x s x' h2) (fun h0 : term15 A x s x' => @lem3276280 A x s x' h1 h2 h0) (fun h0 : s x' => @lem3276265 A s x' h1 h0)). Qed.
Lemma lem3276282 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') (h2 : term107 A x s x') (h3 : term15 A x s x') : False.
Proof. exact (or_elim (@lem3275636 A x s x' h3) (fun h0 : x' = x => @lem3276279 A s x' x h1 h2 h0) (fun h0 : s x' => @lem3276277 A x s x' h0 h1)). Qed.
Lemma lem3276283 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term36 A x s x') (h2 : term107 A x s x') : False.
Proof. exact (or_elim (@lem3275631 A x s x' h2) (fun h0 : term15 A x s x' => @lem3276282 A x s x' h1 h2 h0) (fun h0 : s x' => @lem3276275 A x s x' h0 h1)). Qed.
Lemma lem3276284 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term107 A x s x') : False.
Proof. exact (or_elim (@lem3275630 A x s x' h1) (fun h0 : term36 A x s x' => @lem3276283 A x s x' h0 h1) (fun h0 : term37 A s x' => @lem3276281 A x s x' h0 h1)). Qed.
Lemma lem3276285 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term126 A x' x s) : False.
Proof. exact (or_elim (@lem3275625 A x' x s h1) (fun h0 : term107 A x s x' => @lem3276284 A x s x' h0) (fun h0 : term95 A x s => @lem3276223 A x s h0)). Qed.
Lemma lem3276286 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term126 A x' x s) : (term126 A x' x s) = False.
Proof. exact (prop_ext (fun h2 : term126 A x' x s => @lem3276285 A x' x s h1) (fun h2 : False => @lem3275625 A x' x s h1)). Qed.
Lemma lem3276287 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (h1 : term126 A x' x s) : False.
Proof. exact (EQ_MP (@lem3276286 A x' x s h1) (@lem3275625 A x' x s h1)). Qed.
Lemma lem3276288 {A : Type'} (x : A) (s : A -> Prop) (h1 : term34 A x s) : False.
Proof. exact (ex_elim (@lem3275514 A x s h1) (fun x' : A => fun h0 : term128 A x s x' => @lem3276287 A x' x s h0)). Qed.
Lemma lem3276289 {A : Type'} (x : A) (s : A -> Prop) (h1 : term34 A x s) : (term34 A x s) = False.
Proof. exact (prop_ext (fun h2 : term34 A x s => @lem3276288 A x s h1) (fun h2 : False => @lem3275241 A x s h1)). Qed.
Lemma lem3276290 {A : Type'} (x : A) (s : A -> Prop) (h1 : term34 A x s) : False.
Proof. exact (EQ_MP (@lem3276289 A x s h1) (@lem3275241 A x s h1)). Qed.
Lemma lem3276291 {A : Type'} (x : A) (s : A -> Prop) : term33 A x s.
Proof. exact (fun h0 : term34 A x s => @lem3276290 A x s h0). Qed.
Lemma lem3276292 {A : Type'} (x : A) (s : A -> Prop) : (s x) = (term20 A x s).
Proof. exact (EQ_MP (@lem3275240 A x s) (@lem3276291 A x s)). Qed.
Lemma lem3276297 {A : Type'} (x : A) : term22 A x.
Proof. exact (fun s : A -> Prop => @lem3276292 A x s). Qed.
Lemma lem3276302 {A : Type'} : term24 A.
Proof. exact (fun x : A => @lem3276297 A x). Qed.
Lemma lem3276303 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem3275236 A) (@lem3276302 A)). Qed.
Lemma lem3276305 {A : Type'} : term26 A.
Proof. exact (@lem3275165 A (@lem3276303 A)). Qed.
Lemma lem3276306 {A : Type'} (h1 : term27 A) : False.
Proof. exact (@lem3276305 A (@lem3275149 A h1)). Qed.
Lemma lem3276307 {A : Type'} (h1 : term27 A) : (term27 A) = False.
Proof. exact (prop_ext (fun h2 : term27 A => @lem3276306 A h1) (fun h2 : False => @lem3275149 A h1)). Qed.
Lemma lem3276308 {A : Type'} (h1 : term27 A) : False.
Proof. exact (EQ_MP (@lem3276307 A h1) (@lem3275149 A h1)). Qed.
Lemma lem3276309 {A : Type'} : term26 A.
Proof. exact (fun h0 : term27 A => @lem3276308 A h0). Qed.
Lemma lem3276310 {A : Type'} : term24 A.
Proof. exact (EQ_MP (@lem3275148 A) (@lem3276309 A)). Qed.
Lemma lem3276311 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3275144 A) (@lem3276310 A)). Qed.
Lemma lem3276312 {A : Type'} : term9 A.
Proof. exact (EQ_MP (@lem3275071 A) (@lem3276311 A)). Qed.
