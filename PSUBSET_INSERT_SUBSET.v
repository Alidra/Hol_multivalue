Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PSUBSET_INSERT_SUBSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3313048 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3313049 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term0 A s t).
Proof. exact (@lem3313048 A s t). Qed.
Lemma lem3313053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3313054 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3313053 A s t). Qed.
Lemma lem3313061 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313062 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (MK_COMB (@lem3313061) (@lem3313054 A s t)). Qed.
Lemma lem3313066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3313067 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term4 A s t).
Proof. exact (@lem3313066 A s t). Qed.
Lemma lem3313076 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313077 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term5 A s t) = (term6 A s t).
Proof. exact (MK_COMB (@lem3313076) (@lem3313067 A s t)). Qed.
Lemma lem3313078 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term7 A s t).
Proof. exact (MK_COMB (@lem3313062 A s t) (@lem3313077 A s t)). Qed.
Lemma lem3313081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term7 A s t).
Proof. exact (TRANS (@lem3313049 A s t) (@lem3313078 A s t)). Qed.
Lemma lem3313082 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3313083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term8 A s t) = (term9 A s t).
Proof. exact (MK_COMB (@lem3313082) (@lem3313081 A s t)). Qed.
Lemma lem3313091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3313092 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term1 A s t).
Proof. exact (@lem3313091 A s t). Qed.
Lemma lem3313093 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term10 A x s t) = (term11 A x s t).
Proof. exact (@lem3313092 A (@INSERT A x s) t). Qed.
Lemma lem3313100 {A : Type'} (x : A) (s : A -> Prop) : (term12 A x s) = (term12 A x s).
Proof. exact (eq_refl (term12 A x s)). Qed.
Lemma lem3313101 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term13 A x s t) = (term14 A x s t).
Proof. exact (MK_COMB (@lem3313100 A x s) (@lem3313093 A x s t)). Qed.
Lemma lem3313104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term15 A s t) = (term16 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313101 A x s t)). Qed.
Lemma lem3313105 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3313106 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term17 A s t) = (term18 A s t).
Proof. exact (MK_COMB (@lem3313105 A) (@lem3313104 A s t)). Qed.
Lemma lem3313111 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((@PSUBSET A s t) = (term17 A s t)) = ((term7 A s t) = (term18 A s t)).
Proof. exact (MK_COMB (@lem3313083 A s t) (@lem3313106 A s t)). Qed.
Lemma lem3313116 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3313111 A s t)). Qed.
Lemma lem3313117 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3313118 {A : Type'} (s : A -> Prop) : (term21 A s) = (term22 A s).
Proof. exact (MK_COMB (@lem3313117 A) (@lem3313116 A s)). Qed.
Lemma lem3313123 {A : Type'} : (term23 A) = (term24 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3313118 A s)). Qed.
Lemma lem3313124 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3313125 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (MK_COMB (@lem3313124 A) (@lem3313123 A)). Qed.
Lemma lem3313130 {A : Type'} : (term26 A) = (term25 A).
Proof. exact (SYM (@lem3313125 A)). Qed.
Lemma lem3313150 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3313151 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3313150 A P x). Qed.
Lemma lem3313152 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3313151 A s x). Qed.
Lemma lem3313153 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3313154 {A : Type'} (s : A -> Prop) (x : A) : (term27 A x s) = (term28 A s x).
Proof. exact (MK_COMB (@lem3313153) (@lem3313152 A s x)). Qed.
Lemma lem3313156 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3313157 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3313156 A P x). Qed.
Lemma lem3313158 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3313157 A t x). Qed.
Lemma lem3313159 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term29 A s x t) = (term30 A s t x).
Proof. exact (MK_COMB (@lem3313154 A s x) (@lem3313158 A t x)). Qed.
Lemma lem3313162 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term31 A s t) = (term32 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313159 A s t x)). Qed.
Lemma lem3313163 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313164 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term33 A s t).
Proof. exact (MK_COMB (@lem3313163 A) (@lem3313162 A s t)). Qed.
Lemma lem3313169 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313170 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term3 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3313169) (@lem3313164 A s t)). Qed.
Lemma lem3313178 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3313179 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3313178 A P x). Qed.
Lemma lem3313180 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3313179 A s x). Qed.
Lemma lem3313181 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3313182 {A : Type'} (s : A -> Prop) (x : A) : (term35 A x s) = (term36 A s x).
Proof. exact (MK_COMB (@lem3313181) (@lem3313180 A s x)). Qed.
Lemma lem3313184 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3313185 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3313184 A P x). Qed.
Lemma lem3313186 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3313185 A t x). Qed.
Lemma lem3313187 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3313182 A s x) (@lem3313186 A t x)). Qed.
Lemma lem3313190 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term37 A s t) = (term38 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313187 A s t x)). Qed.
Lemma lem3313191 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313192 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term4 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem3313191 A) (@lem3313190 A s t)). Qed.
Lemma lem3313197 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313198 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term6 A s t) = (term40 A s t).
Proof. exact (MK_COMB (@lem3313197) (@lem3313192 A s t)). Qed.
Lemma lem3313199 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3313170 A s t) (@lem3313198 A s t)). Qed.
Lemma lem3313202 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3313203 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3313202) (@lem3313199 A s t)). Qed.
Lemma lem3313211 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3313212 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3313211 A P x). Qed.
Lemma lem3313213 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3313212 A s x). Qed.
Lemma lem3313214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313215 {A : Type'} (s : A -> Prop) (x : A) : (term43 A x s) = (term44 A s x).
Proof. exact (MK_COMB (@lem3313214) (@lem3313213 A s x)). Qed.
Lemma lem3313216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313217 {A : Type'} (s : A -> Prop) (x : A) : (term12 A x s) = (term45 A s x).
Proof. exact (MK_COMB (@lem3313216) (@lem3313215 A s x)). Qed.
Lemma lem3313225 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term46 A x y s) = (term47 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3313226 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term46 A x y s) = (term47 A y x s).
Proof. exact (@lem3313225 A y x s). Qed.
Lemma lem3313227 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term46 A x' x s) = (term47 A x x' s).
Proof. exact (@lem3313226 A x x' s). Qed.
Lemma lem3313233 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3313234 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3313233 A P x). Qed.
Lemma lem3313235 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3313234 A s x'). Qed.
Lemma lem3313236 {A : Type'} (x' : A) (x : A) : (term48 A x' x) = (term48 A x' x).
Proof. exact (eq_refl (term48 A x' x)). Qed.
Lemma lem3313237 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term47 A x x' s) = (term49 A x s x').
Proof. exact (MK_COMB (@lem3313236 A x' x) (@lem3313235 A s x')). Qed.
Lemma lem3313240 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term46 A x' x s) = (term49 A x s x').
Proof. exact (TRANS (@lem3313227 A x x' s) (@lem3313237 A x s x')). Qed.
Lemma lem3313241 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3313242 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term50 A x' x s) = (term51 A x s x').
Proof. exact (MK_COMB (@lem3313241) (@lem3313240 A x s x')). Qed.
Lemma lem3313244 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3313245 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3313244 A P x). Qed.
Lemma lem3313246 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3313245 A t x'). Qed.
Lemma lem3313247 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term52 A x s x' t) = (term53 A x s t x').
Proof. exact (MK_COMB (@lem3313242 A x s x') (@lem3313246 A t x')). Qed.
Lemma lem3313250 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term54 A x s t) = (term55 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3313247 A x s t x')). Qed.
Lemma lem3313251 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313252 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term11 A x s t) = (term56 A x s t).
Proof. exact (MK_COMB (@lem3313251 A) (@lem3313250 A x s t)). Qed.
Lemma lem3313257 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term14 A x s t) = (term57 A x s t).
Proof. exact (MK_COMB (@lem3313217 A s x) (@lem3313252 A x s t)). Qed.
Lemma lem3313260 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = (term58 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313257 A x s t)). Qed.
Lemma lem3313261 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3313262 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = (term59 A s t).
Proof. exact (MK_COMB (@lem3313261 A) (@lem3313260 A s t)). Qed.
Lemma lem3313267 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term7 A s t) = (term18 A s t)) = ((term41 A s t) = (term59 A s t)).
Proof. exact (MK_COMB (@lem3313203 A s t) (@lem3313262 A s t)). Qed.
Lemma lem3313270 {A : Type'} (s : A -> Prop) : (term20 A s) = (term60 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3313267 A s t)). Qed.
Lemma lem3313271 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3313272 {A : Type'} (s : A -> Prop) : (term22 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3313271 A) (@lem3313270 A s)). Qed.
Lemma lem3313277 {A : Type'} : (term24 A) = (term62 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3313272 A s)). Qed.
Lemma lem3313278 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3313279 {A : Type'} : (term26 A) = (term63 A).
Proof. exact (MK_COMB (@lem3313278 A) (@lem3313277 A)). Qed.
Lemma lem3313284 {A : Type'} : (term63 A) = (term26 A).
Proof. exact (SYM (@lem3313279 A)). Qed.
Lemma lem3313286 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3313287 {A : Type'} : (term63 A) = (term65 A).
Proof. exact (@lem3313286 (term63 A)). Qed.
Lemma lem3313288 {A : Type'} : (term65 A) = (term63 A).
Proof. exact (SYM (@lem3313287 A)). Qed.
Lemma lem3313289 {A : Type'} (h1 : term66 A) : term66 A.
Proof. exact (h1). Qed.
Lemma lem3313292 {A : Type'} (h1 : term65 A) : term65 A.
Proof. exact (h1). Qed.
Lemma lem3313293 {A : Type'} : term67 A.
Proof. exact (fun h0 : term65 A => @lem3313292 A h0). Qed.
Lemma lem3313294 {A : Type'} (h1 : term67 A) : term67 A.
Proof. exact (h1). Qed.
Lemma lem3313295 {A : Type'} (h1 : term65 A) : term65 A.
Proof. exact (h1). Qed.
Lemma lem3313296 {A : Type'} (h1 : term65 A) (h2 : term67 A) : term65 A.
Proof. exact (@lem3313294 A h2 (@lem3313295 A h1)). Qed.
Lemma lem3313297 {A : Type'} (h1 : term65 A) : term68 A.
Proof. exact (fun h0 : term67 A => @lem3313296 A h1 h0). Qed.
Lemma lem3313298 {A : Type'} (h1 : term67 A) : term67 A.
Proof. exact (h1). Qed.
Lemma lem3313299 {A : Type'} (h1 : term65 A) (h2 : term67 A) : term65 A.
Proof. exact (@lem3313297 A h1 (@lem3313298 A h2)). Qed.
Lemma lem3313300 {A : Type'} (h1 : term67 A) : term67 A.
Proof. exact (fun h0 : term65 A => @lem3313299 A h0 h1). Qed.
Lemma lem3313301 {A : Type'} : term69 A.
Proof. exact (fun h0 : term67 A => @lem3313300 A h0). Qed.
Lemma lem3313304 {A : Type'} : term67 A.
Proof. exact (@lem3313301 A (@lem3313293 A)). Qed.
Lemma lem3313305 {A : Type'} : term67 A.
Proof. exact (@lem3313304 A). Qed.
Lemma lem3313307 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3313308 {A : Type'} : (term65 A) = (term70 A).
Proof. exact (@lem3313307 (term66 A)). Qed.
Lemma lem3313310 (t : Prop) : (term71 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3313311 {A : Type'} : (term70 A) = (term63 A).
Proof. exact (@lem3313310 (term63 A)). Qed.
Lemma lem3313394 {A : Type'} : (term65 A) = (term63 A).
Proof. exact (TRANS (@lem3313308 A) (@lem3313311 A)). Qed.
Lemma lem3313403 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term53 A x s t x') = (term53 A x s t x').
Proof. exact (eq_refl (term53 A x s t x')). Qed.
Lemma lem3313404 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term55 A x s t) = (term55 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3313403 A x s t x')). Qed.
Lemma lem3313405 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313406 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term56 A x s t).
Proof. exact (MK_COMB (@lem3313405 A) (@lem3313404 A x s t)). Qed.
Lemma lem3313411 {A : Type'} (s : A -> Prop) (x : A) : (term45 A s x) = (term45 A s x).
Proof. exact (eq_refl (term45 A s x)). Qed.
Lemma lem3313412 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term57 A x s t) = (term57 A x s t).
Proof. exact (MK_COMB (@lem3313411 A s x) (@lem3313406 A x s t)). Qed.
Lemma lem3313413 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313412 A x s t)). Qed.
Lemma lem3313414 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3313415 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term59 A s t).
Proof. exact (MK_COMB (@lem3313414 A) (@lem3313413 A s t)). Qed.
Lemma lem3313420 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem3313421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term38 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313420 A s t x)). Qed.
Lemma lem3313422 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313423 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term39 A s t).
Proof. exact (MK_COMB (@lem3313422 A) (@lem3313421 A s t)). Qed.
Lemma lem3313424 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313425 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term40 A s t).
Proof. exact (MK_COMB (@lem3313424) (@lem3313423 A s t)). Qed.
Lemma lem3313430 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term30 A s t x) = (term30 A s t x).
Proof. exact (eq_refl (term30 A s t x)). Qed.
Lemma lem3313431 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term32 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313430 A s t x)). Qed.
Lemma lem3313432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313433 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term33 A s t).
Proof. exact (MK_COMB (@lem3313432 A) (@lem3313431 A s t)). Qed.
Lemma lem3313434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313435 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term34 A s t).
Proof. exact (MK_COMB (@lem3313434) (@lem3313433 A s t)). Qed.
Lemma lem3313436 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3313435 A s t) (@lem3313425 A s t)). Qed.
Lemma lem3313437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3313438 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term42 A s t) = (term42 A s t).
Proof. exact (MK_COMB (@lem3313437) (@lem3313436 A s t)). Qed.
Lemma lem3313439 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term41 A s t) = (term59 A s t)) = ((term41 A s t) = (term59 A s t)).
Proof. exact (MK_COMB (@lem3313438 A s t) (@lem3313415 A s t)). Qed.
Lemma lem3313440 {A : Type'} (s : A -> Prop) : (term60 A s) = (term60 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3313439 A s t)). Qed.
Lemma lem3313441 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3313442 {A : Type'} (s : A -> Prop) : (term61 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3313441 A) (@lem3313440 A s)). Qed.
Lemma lem3313443 {A : Type'} : (term62 A) = (term62 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3313442 A s)). Qed.
Lemma lem3313444 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3313445 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (MK_COMB (@lem3313444 A) (@lem3313443 A)). Qed.
Lemma lem3313494 {A : Type'} : (term65 A) = (term63 A).
Proof. exact (TRANS (@lem3313394 A) (@lem3313445 A)). Qed.
Lemma lem3313495 {A : Type'} : (term63 A) = (term65 A).
Proof. exact (SYM (@lem3313494 A)). Qed.
Lemma lem3313497 (p : Prop) : p = (term64 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3313498 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term41 A s t) = (term59 A s t)) = (term72 A s t).
Proof. exact (@lem3313497 ((term41 A s t) = (term59 A s t))). Qed.
Lemma lem3313499 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term72 A s t) = ((term41 A s t) = (term59 A s t)).
Proof. exact (SYM (@lem3313498 A s t)). Qed.
Lemma lem3313500 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term73 A s t) : term73 A s t.
Proof. exact (h1). Qed.
Lemma lem3313509 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term74 A s t x) = (term75 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3313514 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term30 A s t x) = (term76 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3313515 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3313516 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term80 A s t).
Proof. exact (@lem3313515 A (term32 A s t)). Qed.
Lemma lem3313517 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term81 A s t x) = (term30 A s t x).
Proof. exact (eq_refl (term81 A s t x)). Qed.
Lemma lem3313518 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313519 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term82 A s t x) = (term74 A s t x).
Proof. exact (MK_COMB (@lem3313518) (@lem3313517 A s t x)). Qed.
Lemma lem3313520 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term82 A s t x) = (term75 A s t x).
Proof. exact (TRANS (@lem3313519 A s t x) (@lem3313509 A s t x)). Qed.
Lemma lem3313521 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313520 A s t x)). Qed.
Lemma lem3313522 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3313523 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3313522 A) (@lem3313521 A s t)). Qed.
Lemma lem3313524 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = (term85 A s t).
Proof. exact (TRANS (@lem3313516 A s t) (@lem3313523 A s t)). Qed.
Lemma lem3313525 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term32 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313514 A s t x)). Qed.
Lemma lem3313526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313527 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term33 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3313526 A) (@lem3313525 A s t)). Qed.
Lemma lem3313542 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term88 A s t x) = (term89 A s t x).
Proof. exact (@lem17930 (s x) (t x)). Qed.
Lemma lem3313553 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = (term90 A s t x).
Proof. exact (@lem17784 (s x) (t x)). Qed.
Lemma lem3313554 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3313555 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term91 A s t).
Proof. exact (@lem3313554 A (term38 A s t)). Qed.
Lemma lem3313556 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term92 A s t x) = ((s x) = (t x)).
Proof. exact (eq_refl (term92 A s t x)). Qed.
Lemma lem3313557 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313558 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term93 A s t x) = (term88 A s t x).
Proof. exact (MK_COMB (@lem3313557) (@lem3313556 A s t x)). Qed.
Lemma lem3313559 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term93 A s t x) = (term89 A s t x).
Proof. exact (TRANS (@lem3313558 A s t x) (@lem3313542 A s t x)). Qed.
Lemma lem3313560 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term95 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313559 A s t x)). Qed.
Lemma lem3313561 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3313562 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term96 A s t).
Proof. exact (MK_COMB (@lem3313561 A) (@lem3313560 A s t)). Qed.
Lemma lem3313563 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term96 A s t).
Proof. exact (TRANS (@lem3313555 A s t) (@lem3313562 A s t)). Qed.
Lemma lem3313564 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term38 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313553 A s t x)). Qed.
Lemma lem3313565 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313566 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3313565 A) (@lem3313564 A s t)). Qed.
Lemma lem3313567 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term39 A s t).
Proof. exact (@lem16933 (term39 A s t)). Qed.
Lemma lem3313568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term99 A s t) = (term98 A s t).
Proof. exact (TRANS (@lem3313567 A s t) (@lem3313566 A s t)). Qed.
Lemma lem3313569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3313570 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term100 A s t) = (term101 A s t).
Proof. exact (MK_COMB (@lem3313569) (@lem3313524 A s t)). Qed.
Lemma lem3313571 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term103 A s t).
Proof. exact (MK_COMB (@lem3313570 A s t) (@lem3313568 A s t)). Qed.
Lemma lem3313572 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term104 A s t) = (term102 A s t).
Proof. exact (@lem17045 (term33 A s t) (term40 A s t)). Qed.
Lemma lem3313573 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term104 A s t) = (term103 A s t).
Proof. exact (TRANS (@lem3313572 A s t) (@lem3313571 A s t)). Qed.
Lemma lem3313574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313575 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term34 A s t) = (term105 A s t).
Proof. exact (MK_COMB (@lem3313574) (@lem3313527 A s t)). Qed.
Lemma lem3313576 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3313575 A s t) (@lem3313563 A s t)). Qed.
Lemma lem3313580 {A : Type'} (s : A -> Prop) (x : A) : (term107 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3313589 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term108 A x s x') = (term109 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3313594 {A : Type'} (t : A -> Prop) (x' : A) : (t x') = (t x').
Proof. exact (eq_refl (t x')). Qed.
Lemma lem3313599 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term110 A x s t x') = (term111 A x s t x').
Proof. exact (@lem17362 (term49 A x s x') (t x')). Qed.
Lemma lem3313600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3313601 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term112 A x s x') = (term113 A x s x').
Proof. exact (MK_COMB (@lem3313600) (@lem3313589 A x s x')). Qed.
Lemma lem3313602 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term114 A x s t x') = (term115 A x s t x').
Proof. exact (MK_COMB (@lem3313601 A x s x') (@lem3313594 A t x')). Qed.
Lemma lem3313603 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term53 A x s t x') = (term114 A x s t x').
Proof. exact (@lem17265 (term49 A x s x') (t x')). Qed.
Lemma lem3313604 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term53 A x s t x') = (term115 A x s t x').
Proof. exact (TRANS (@lem3313603 A x s t x') (@lem3313602 A x s t x')). Qed.
Lemma lem3313605 {A : Type'} (P : A -> Prop) : (term77 A P) = (term78 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3313606 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term116 A x s t) = (term117 A x s t).
Proof. exact (@lem3313605 A (term55 A x s t)). Qed.
Lemma lem3313607 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term118 A x s t x') = (term53 A x s t x').
Proof. exact (eq_refl (term118 A x s t x')). Qed.
Lemma lem3313608 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313609 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term119 A x s t x') = (term110 A x s t x').
Proof. exact (MK_COMB (@lem3313608) (@lem3313607 A x s t x')). Qed.
Lemma lem3313610 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term119 A x s t x') = (term111 A x s t x').
Proof. exact (TRANS (@lem3313609 A x s t x') (@lem3313599 A x s t x')). Qed.
Lemma lem3313611 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term120 A x s t) = (term121 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3313610 A x s t x')). Qed.
Lemma lem3313612 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3313613 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term117 A x s t) = (term122 A x s t).
Proof. exact (MK_COMB (@lem3313612 A) (@lem3313611 A x s t)). Qed.
Lemma lem3313614 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term116 A x s t) = (term122 A x s t).
Proof. exact (TRANS (@lem3313606 A x s t) (@lem3313613 A x s t)). Qed.
Lemma lem3313615 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term55 A x s t) = (term123 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3313604 A x s t x')). Qed.
Lemma lem3313616 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313617 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term56 A x s t) = (term124 A x s t).
Proof. exact (MK_COMB (@lem3313616 A) (@lem3313615 A x s t)). Qed.
Lemma lem3313618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3313619 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term126 A s x).
Proof. exact (MK_COMB (@lem3313618) (@lem3313580 A s x)). Qed.
Lemma lem3313620 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term127 A x s t) = (term128 A x s t).
Proof. exact (MK_COMB (@lem3313619 A s x) (@lem3313614 A x s t)). Qed.
Lemma lem3313621 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term129 A x s t) = (term127 A x s t).
Proof. exact (@lem17045 (term44 A s x) (term56 A x s t)). Qed.
Lemma lem3313622 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term129 A x s t) = (term128 A x s t).
Proof. exact (TRANS (@lem3313621 A x s t) (@lem3313620 A x s t)). Qed.
Lemma lem3313624 {A : Type'} (s : A -> Prop) (x : A) : (term45 A s x) = (term45 A s x).
Proof. exact (eq_refl (term45 A s x)). Qed.
Lemma lem3313625 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term57 A x s t) = (term130 A x s t).
Proof. exact (MK_COMB (@lem3313624 A s x) (@lem3313617 A x s t)). Qed.
Lemma lem3313626 {A : Type'} (P : A -> Prop) : (term131 A P) = (term132 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3313627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term133 A s t) = (term134 A s t).
Proof. exact (@lem3313626 A (term58 A s t)). Qed.
Lemma lem3313628 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term135 A s t x) = (term57 A x s t).
Proof. exact (eq_refl (term135 A s t x)). Qed.
Lemma lem3313629 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3313630 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term136 A s t x) = (term129 A x s t).
Proof. exact (MK_COMB (@lem3313629) (@lem3313628 A x s t)). Qed.
Lemma lem3313631 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term136 A s t x) = (term128 A x s t).
Proof. exact (TRANS (@lem3313630 A x s t) (@lem3313622 A x s t)). Qed.
Lemma lem3313632 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term137 A s t) = (term138 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313631 A x s t)). Qed.
Lemma lem3313633 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313634 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term134 A s t) = (term139 A s t).
Proof. exact (MK_COMB (@lem3313633 A) (@lem3313632 A s t)). Qed.
Lemma lem3313635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term133 A s t) = (term139 A s t).
Proof. exact (TRANS (@lem3313627 A s t) (@lem3313634 A s t)). Qed.
Lemma lem3313636 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term140 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313625 A x s t)). Qed.
Lemma lem3313637 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3313638 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term141 A s t).
Proof. exact (MK_COMB (@lem3313637 A) (@lem3313636 A s t)). Qed.
Lemma lem3313639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313640 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term142 A s t) = (term143 A s t).
Proof. exact (MK_COMB (@lem3313639) (@lem3313573 A s t)). Qed.
Lemma lem3313641 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term144 A s t) = (term145 A s t).
Proof. exact (MK_COMB (@lem3313640 A s t) (@lem3313638 A s t)). Qed.
Lemma lem3313642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313643 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term146 A s t) = (term147 A s t).
Proof. exact (MK_COMB (@lem3313642) (@lem3313576 A s t)). Qed.
Lemma lem3313644 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term148 A s t) = (term149 A s t).
Proof. exact (MK_COMB (@lem3313643 A s t) (@lem3313635 A s t)). Qed.
Lemma lem3313645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3313646 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term151 A s t).
Proof. exact (MK_COMB (@lem3313645) (@lem3313644 A s t)). Qed.
Lemma lem3313647 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term152 A s t) = (term153 A s t).
Proof. exact (MK_COMB (@lem3313646 A s t) (@lem3313641 A s t)). Qed.
Lemma lem3313648 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term152 A s t).
Proof. exact (@lem17646 (term41 A s t) (term59 A s t)). Qed.
Lemma lem3313649 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term153 A s t).
Proof. exact (TRANS (@lem3313648 A s t) (@lem3313647 A s t)). Qed.
Lemma lem3313835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3313836 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (@lem3313835 A P Q). Qed.
Lemma lem3313837 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term156 A s t) = (term157 A s t).
Proof. exact (@lem3313836 A (term158 A s t) (term86 A s t)). Qed.
Lemma lem3313838 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term159 A s t x) = (term160 A s t x).
Proof. exact (eq_refl (term159 A s t x)). Qed.
Lemma lem3313839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term161 A s t x) = (term162 A s t x).
Proof. exact (MK_COMB (@lem3313839) (@lem3313838 A s t x)). Qed.
Lemma lem3313841 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term163 A s t x) = (term76 A s t x).
Proof. exact (eq_refl (term163 A s t x)). Qed.
Lemma lem3313842 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term164 A s t x) = (term90 A s t x).
Proof. exact (MK_COMB (@lem3313840 A s t x) (@lem3313841 A s t x)). Qed.
Lemma lem3313843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term165 A s t) = (term97 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313842 A s t x)). Qed.
Lemma lem3313844 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313845 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term156 A s t) = (term98 A s t).
Proof. exact (MK_COMB (@lem3313844 A) (@lem3313843 A s t)). Qed.
Lemma lem3313846 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3313847 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term166 A s t) = (term167 A s t).
Proof. exact (MK_COMB (@lem3313846) (@lem3313845 A s t)). Qed.
Lemma lem3313848 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term159 A s t x) = (term160 A s t x).
Proof. exact (eq_refl (term159 A s t x)). Qed.
Lemma lem3313849 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term168 A s t) = (term158 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313848 A s t x)). Qed.
Lemma lem3313850 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313851 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term169 A s t) = (term170 A s t).
Proof. exact (MK_COMB (@lem3313850 A) (@lem3313849 A s t)). Qed.
Lemma lem3313852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313853 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term171 A s t) = (term172 A s t).
Proof. exact (MK_COMB (@lem3313852) (@lem3313851 A s t)). Qed.
Lemma lem3313854 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term163 A s t x) = (term76 A s t x).
Proof. exact (eq_refl (term163 A s t x)). Qed.
Lemma lem3313855 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term173 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3313854 A s t x)). Qed.
Lemma lem3313856 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3313857 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term174 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3313856 A) (@lem3313855 A s t)). Qed.
Lemma lem3313858 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term157 A s t) = (term175 A s t).
Proof. exact (MK_COMB (@lem3313853 A s t) (@lem3313857 A s t)). Qed.
Lemma lem3313859 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term156 A s t) = (term157 A s t)) = ((term98 A s t) = (term175 A s t)).
Proof. exact (MK_COMB (@lem3313847 A s t) (@lem3313858 A s t)). Qed.
Lemma lem3313860 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term98 A s t) = (term175 A s t).
Proof. exact (EQ_MP (@lem3313859 A s t) (@lem3313837 A s t)). Qed.
Lemma lem3313921 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term101 A s t).
Proof. exact (eq_refl (term101 A s t)). Qed.
Lemma lem3313922 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term103 A s t) = (term176 A s t).
Proof. exact (MK_COMB (@lem3313921 A s t) (@lem3313860 A s t)). Qed.
Lemma lem3313923 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3313924 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term143 A s t) = (term177 A s t).
Proof. exact (MK_COMB (@lem3313923) (@lem3313922 A s t)). Qed.
Lemma lem3314005 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term141 A s t) = (term141 A s t).
Proof. exact (eq_refl (term141 A s t)). Qed.
Lemma lem3314006 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term145 A s t) = (term178 A s t).
Proof. exact (MK_COMB (@lem3313924 A s t) (@lem3314005 A s t)). Qed.
Lemma lem3314007 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term151 A s t).
Proof. exact (eq_refl (term151 A s t)). Qed.
Lemma lem3314008 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term153 A s t) = (term179 A s t).
Proof. exact (MK_COMB (@lem3314007 A s t) (@lem3314006 A s t)). Qed.
Lemma lem3314010 {A : Type'} (P : Prop) (Q : A -> Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3314011 {A : Type'} (P : Prop) (Q : A -> Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (@lem3314010 A P Q). Qed.
Lemma lem3314012 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term182 A s t) = (term183 A s t).
Proof. exact (@lem3314011 A (term87 A s t) (term95 A s t)). Qed.
Lemma lem3314013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term184 A s t x) = (term89 A s t x).
Proof. exact (eq_refl (term184 A s t x)). Qed.
Lemma lem3314014 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term185 A s t) = (term95 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314013 A s t x)). Qed.
Lemma lem3314015 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314016 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term186 A s t) = (term96 A s t).
Proof. exact (MK_COMB (@lem3314015 A) (@lem3314014 A s t)). Qed.
Lemma lem3314017 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term105 A s t).
Proof. exact (eq_refl (term105 A s t)). Qed.
Lemma lem3314018 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term182 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3314017 A s t) (@lem3314016 A s t)). Qed.
Lemma lem3314019 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314020 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term187 A s t) = (term188 A s t).
Proof. exact (MK_COMB (@lem3314019) (@lem3314018 A s t)). Qed.
Lemma lem3314021 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term184 A s t x) = (term89 A s t x).
Proof. exact (eq_refl (term184 A s t x)). Qed.
Lemma lem3314022 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term105 A s t).
Proof. exact (eq_refl (term105 A s t)). Qed.
Lemma lem3314023 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term189 A s t x) = (term190 A s t x).
Proof. exact (MK_COMB (@lem3314022 A s t) (@lem3314021 A s t x)). Qed.
Lemma lem3314024 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term191 A s t) = (term192 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314023 A s t x)). Qed.
Lemma lem3314025 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314026 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term183 A s t) = (term193 A s t).
Proof. exact (MK_COMB (@lem3314025 A) (@lem3314024 A s t)). Qed.
Lemma lem3314027 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term182 A s t) = (term183 A s t)) = ((term106 A s t) = (term193 A s t)).
Proof. exact (MK_COMB (@lem3314020 A s t) (@lem3314026 A s t)). Qed.
Lemma lem3314028 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term193 A s t).
Proof. exact (EQ_MP (@lem3314027 A s t) (@lem3314012 A s t)). Qed.
Lemma lem3314029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314030 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term194 A s t).
Proof. exact (MK_COMB (@lem3314029) (@lem3314028 A s t)). Qed.
Lemma lem3314032 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3314033 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (@lem3314032 A P Q). Qed.
Lemma lem3314034 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term197 A x s t) = (term198 A x s t).
Proof. exact (@lem3314033 A (s x) (term121 A x s t)). Qed.
Lemma lem3314035 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term199 A x s t x') = (term111 A x s t x').
Proof. exact (eq_refl (term199 A x s t x')). Qed.
Lemma lem3314036 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term200 A x s t) = (term121 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3314035 A x s t x')). Qed.
Lemma lem3314037 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314038 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term201 A x s t) = (term122 A x s t).
Proof. exact (MK_COMB (@lem3314037 A) (@lem3314036 A x s t)). Qed.
Lemma lem3314039 {A : Type'} (s : A -> Prop) (x : A) : (term126 A s x) = (term126 A s x).
Proof. exact (eq_refl (term126 A s x)). Qed.
Lemma lem3314040 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term197 A x s t) = (term128 A x s t).
Proof. exact (MK_COMB (@lem3314039 A s x) (@lem3314038 A x s t)). Qed.
Lemma lem3314041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314042 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term202 A x s t) = (term203 A x s t).
Proof. exact (MK_COMB (@lem3314041) (@lem3314040 A x s t)). Qed.
Lemma lem3314043 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term199 A x s t x') = (term111 A x s t x').
Proof. exact (eq_refl (term199 A x s t x')). Qed.
Lemma lem3314044 {A : Type'} (s : A -> Prop) (x : A) : (term126 A s x) = (term126 A s x).
Proof. exact (eq_refl (term126 A s x)). Qed.
Lemma lem3314045 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term204 A x s t x') = (term205 A x s t x').
Proof. exact (MK_COMB (@lem3314044 A s x) (@lem3314043 A x s t x')). Qed.
Lemma lem3314046 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term206 A x s t) = (term207 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3314045 A x s t x')). Qed.
Lemma lem3314047 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314048 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term198 A x s t) = (term208 A x s t).
Proof. exact (MK_COMB (@lem3314047 A) (@lem3314046 A x s t)). Qed.
Lemma lem3314049 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term197 A x s t) = (term198 A x s t)) = ((term128 A x s t) = (term208 A x s t)).
Proof. exact (MK_COMB (@lem3314042 A x s t) (@lem3314048 A x s t)). Qed.
Lemma lem3314050 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term128 A x s t) = (term208 A x s t).
Proof. exact (EQ_MP (@lem3314049 A x s t) (@lem3314034 A x s t)). Qed.
Lemma lem3314051 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term209 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314050 A x s t)). Qed.
Lemma lem3314052 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term210 A s t).
Proof. exact (MK_COMB (@lem3314052 A) (@lem3314051 A s t)). Qed.
Lemma lem3314055 {A B : Type'} (P : type1413 A B) : (term211 A B P) = (term212 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3314056 {A : Type'} (P : type1402 A) : (term213 A P) = (term214 A P).
Proof. exact (@lem3314055 A A P). Qed.
Lemma lem3314057 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term215 A s t) = (term216 A s t).
Proof. exact (@lem3314056 A (term217 A s t)). Qed.
Lemma lem3314058 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term218 A s t x) = (term207 A x s t).
Proof. exact (eq_refl (term218 A s t x)). Qed.
Lemma lem3314059 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3314060 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term219 A s t x x') = (term220 A x s t x').
Proof. exact (MK_COMB (@lem3314058 A x s t) (@lem3314059 A x')). Qed.
Lemma lem3314061 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term220 A x s t x') = (term205 A x s t x').
Proof. exact (eq_refl (term220 A x s t x')). Qed.
Lemma lem3314062 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term219 A s t x x') = (term205 A x s t x').
Proof. exact (TRANS (@lem3314060 A x s t x') (@lem3314061 A x s t x')). Qed.
Lemma lem3314063 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term221 A s t x) = (term207 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3314062 A x s t x')). Qed.
Lemma lem3314064 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314065 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term222 A s t x) = (term208 A x s t).
Proof. exact (MK_COMB (@lem3314064 A) (@lem3314063 A x s t)). Qed.
Lemma lem3314066 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term223 A s t) = (term209 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314065 A x s t)). Qed.
Lemma lem3314067 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314068 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term215 A s t) = (term210 A s t).
Proof. exact (MK_COMB (@lem3314067 A) (@lem3314066 A s t)). Qed.
Lemma lem3314069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314070 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term224 A s t) = (term225 A s t).
Proof. exact (MK_COMB (@lem3314069) (@lem3314068 A s t)). Qed.
Lemma lem3314071 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term218 A s t x) = (term207 A x s t).
Proof. exact (eq_refl (term218 A s t x)). Qed.
Lemma lem3314072 {A : Type'} (x' : A -> A) (x : A) : (x' x) = (x' x).
Proof. exact (eq_refl (x' x)). Qed.
Lemma lem3314073 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (x : A) : (term226 A s t x' x) = (term227 A s t x' x).
Proof. exact (MK_COMB (@lem3314071 A x s t) (@lem3314072 A x' x)). Qed.
Lemma lem3314074 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (x : A) : (term227 A s t x' x) = (term228 A s t x' x).
Proof. exact (eq_refl (term227 A s t x' x)). Qed.
Lemma lem3314075 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (x : A) : (term226 A s t x' x) = (term228 A s t x' x).
Proof. exact (TRANS (@lem3314073 A s t x' x) (@lem3314074 A s t x' x)). Qed.
Lemma lem3314076 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term229 A s t x') = (term230 A s t x').
Proof. exact (fun_ext (fun x : A => @lem3314075 A s t x' x)). Qed.
Lemma lem3314077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314078 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term231 A s t x') = (term232 A s t x').
Proof. exact (MK_COMB (@lem3314077 A) (@lem3314076 A s t x')). Qed.
Lemma lem3314079 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term233 A s t) = (term234 A s t).
Proof. exact (fun_ext (fun x' : A -> A => @lem3314078 A s t x')). Qed.
Lemma lem3314080 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3314081 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term216 A s t) = (term235 A s t).
Proof. exact (MK_COMB (@lem3314080 A) (@lem3314079 A s t)). Qed.
Lemma lem3314082 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term215 A s t) = (term216 A s t)) = ((term210 A s t) = (term235 A s t)).
Proof. exact (MK_COMB (@lem3314070 A s t) (@lem3314081 A s t)). Qed.
Lemma lem3314083 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term210 A s t) = (term235 A s t).
Proof. exact (EQ_MP (@lem3314082 A s t) (@lem3314057 A s t)). Qed.
Lemma lem3314084 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term139 A s t) = (term235 A s t).
Proof. exact (TRANS (@lem3314053 A s t) (@lem3314083 A s t)). Qed.
Lemma lem3314085 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term149 A s t) = (term236 A s t).
Proof. exact (MK_COMB (@lem3314030 A s t) (@lem3314084 A s t)). Qed.
Lemma lem3314087 {A : Type'} (P : A -> Prop) (Q : Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3314088 {A : Type'} (P : A -> Prop) (Q : Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem3314087 A P Q). Qed.
Lemma lem3314089 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term240 A s t).
Proof. exact (@lem3314088 A (term192 A s t) (term235 A s t)). Qed.
Lemma lem3314090 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term241 A s t x) = (term190 A s t x).
Proof. exact (eq_refl (term241 A s t x)). Qed.
Lemma lem3314091 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term242 A s t) = (term192 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314090 A s t x)). Qed.
Lemma lem3314092 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314093 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term243 A s t) = (term193 A s t).
Proof. exact (MK_COMB (@lem3314092 A) (@lem3314091 A s t)). Qed.
Lemma lem3314094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314095 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term244 A s t) = (term194 A s t).
Proof. exact (MK_COMB (@lem3314094) (@lem3314093 A s t)). Qed.
Lemma lem3314096 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term235 A s t) = (term235 A s t).
Proof. exact (eq_refl (term235 A s t)). Qed.
Lemma lem3314097 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term239 A s t) = (term236 A s t).
Proof. exact (MK_COMB (@lem3314095 A s t) (@lem3314096 A s t)). Qed.
Lemma lem3314098 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314099 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term245 A s t) = (term246 A s t).
Proof. exact (MK_COMB (@lem3314098) (@lem3314097 A s t)). Qed.
Lemma lem3314100 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term241 A s t x) = (term190 A s t x).
Proof. exact (eq_refl (term241 A s t x)). Qed.
Lemma lem3314101 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314102 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term247 A s t x) = (term248 A s t x).
Proof. exact (MK_COMB (@lem3314101) (@lem3314100 A s t x)). Qed.
Lemma lem3314103 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term235 A s t) = (term235 A s t).
Proof. exact (eq_refl (term235 A s t)). Qed.
Lemma lem3314104 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term249 A x s t) = (term250 A x s t).
Proof. exact (MK_COMB (@lem3314102 A s t x) (@lem3314103 A s t)). Qed.
Lemma lem3314105 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term251 A s t) = (term252 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314104 A x s t)). Qed.
Lemma lem3314106 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314107 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term240 A s t) = (term253 A s t).
Proof. exact (MK_COMB (@lem3314106 A) (@lem3314105 A s t)). Qed.
Lemma lem3314108 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term239 A s t) = (term240 A s t)) = ((term236 A s t) = (term253 A s t)).
Proof. exact (MK_COMB (@lem3314099 A s t) (@lem3314107 A s t)). Qed.
Lemma lem3314109 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term236 A s t) = (term253 A s t).
Proof. exact (EQ_MP (@lem3314108 A s t) (@lem3314089 A s t)). Qed.
Lemma lem3314111 {A : Type'} (P : Prop) (Q : A -> Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3314112 {A : Type'} (P : Prop) (Q : type488 A) : (term254 A P Q) = (term255 A P Q).
Proof. exact (@lem3314111 (A -> A) P Q). Qed.
Lemma lem3314113 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term256 A x s t) = (term257 A x s t).
Proof. exact (@lem3314112 A (term190 A s t x) (term234 A s t)). Qed.
Lemma lem3314114 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term258 A s t x') = (term232 A s t x').
Proof. exact (eq_refl (term258 A s t x')). Qed.
Lemma lem3314115 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term259 A s t) = (term234 A s t).
Proof. exact (fun_ext (fun x' : A -> A => @lem3314114 A s t x')). Qed.
Lemma lem3314116 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3314117 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term260 A s t) = (term235 A s t).
Proof. exact (MK_COMB (@lem3314116 A) (@lem3314115 A s t)). Qed.
Lemma lem3314118 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term248 A s t x) = (term248 A s t x).
Proof. exact (eq_refl (term248 A s t x)). Qed.
Lemma lem3314119 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term256 A x s t) = (term250 A x s t).
Proof. exact (MK_COMB (@lem3314118 A s t x) (@lem3314117 A s t)). Qed.
Lemma lem3314120 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314121 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term261 A x s t) = (term262 A x s t).
Proof. exact (MK_COMB (@lem3314120) (@lem3314119 A x s t)). Qed.
Lemma lem3314122 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term258 A s t x') = (term232 A s t x').
Proof. exact (eq_refl (term258 A s t x')). Qed.
Lemma lem3314123 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term248 A s t x) = (term248 A s t x).
Proof. exact (eq_refl (term248 A s t x)). Qed.
Lemma lem3314124 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term263 A x s t x') = (term264 A x s t x').
Proof. exact (MK_COMB (@lem3314123 A s t x) (@lem3314122 A s t x')). Qed.
Lemma lem3314125 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term265 A x s t) = (term266 A x s t).
Proof. exact (fun_ext (fun x' : A -> A => @lem3314124 A x s t x')). Qed.
Lemma lem3314126 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3314127 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term257 A x s t) = (term267 A x s t).
Proof. exact (MK_COMB (@lem3314126 A) (@lem3314125 A x s t)). Qed.
Lemma lem3314128 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term256 A x s t) = (term257 A x s t)) = ((term250 A x s t) = (term267 A x s t)).
Proof. exact (MK_COMB (@lem3314121 A x s t) (@lem3314127 A x s t)). Qed.
Lemma lem3314129 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term250 A x s t) = (term267 A x s t).
Proof. exact (EQ_MP (@lem3314128 A x s t) (@lem3314113 A x s t)). Qed.
Lemma lem3314130 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term252 A s t) = (term268 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314129 A x s t)). Qed.
Lemma lem3314131 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term253 A s t) = (term269 A s t).
Proof. exact (MK_COMB (@lem3314131 A) (@lem3314130 A s t)). Qed.
Lemma lem3314133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term236 A s t) = (term269 A s t).
Proof. exact (TRANS (@lem3314109 A s t) (@lem3314132 A s t)). Qed.
Lemma lem3314134 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term149 A s t) = (term269 A s t).
Proof. exact (TRANS (@lem3314085 A s t) (@lem3314133 A s t)). Qed.
Lemma lem3314135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314136 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term270 A s t).
Proof. exact (MK_COMB (@lem3314135) (@lem3314134 A s t)). Qed.
Lemma lem3314138 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3314139 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (@lem3314138 A P Q). Qed.
Lemma lem3314140 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term273 A s t) = (term274 A s t).
Proof. exact (@lem3314139 A (term84 A s t) (term175 A s t)). Qed.
Lemma lem3314141 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term275 A s t x) = (term75 A s t x).
Proof. exact (eq_refl (term275 A s t x)). Qed.
Lemma lem3314142 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term276 A s t) = (term84 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314141 A s t x)). Qed.
Lemma lem3314143 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314144 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term277 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3314143 A) (@lem3314142 A s t)). Qed.
Lemma lem3314145 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314146 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term278 A s t) = (term101 A s t).
Proof. exact (MK_COMB (@lem3314145) (@lem3314144 A s t)). Qed.
Lemma lem3314147 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term175 A s t) = (term175 A s t).
Proof. exact (eq_refl (term175 A s t)). Qed.
Lemma lem3314148 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term273 A s t) = (term176 A s t).
Proof. exact (MK_COMB (@lem3314146 A s t) (@lem3314147 A s t)). Qed.
Lemma lem3314149 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314150 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term279 A s t) = (term280 A s t).
Proof. exact (MK_COMB (@lem3314149) (@lem3314148 A s t)). Qed.
Lemma lem3314151 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term275 A s t x) = (term75 A s t x).
Proof. exact (eq_refl (term275 A s t x)). Qed.
Lemma lem3314152 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314153 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term281 A s t x) = (term282 A s t x).
Proof. exact (MK_COMB (@lem3314152) (@lem3314151 A s t x)). Qed.
Lemma lem3314154 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term175 A s t) = (term175 A s t).
Proof. exact (eq_refl (term175 A s t)). Qed.
Lemma lem3314155 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term283 A x s t) = (term284 A x s t).
Proof. exact (MK_COMB (@lem3314153 A s t x) (@lem3314154 A s t)). Qed.
Lemma lem3314156 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term285 A s t) = (term286 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314155 A x s t)). Qed.
Lemma lem3314157 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314158 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term274 A s t) = (term287 A s t).
Proof. exact (MK_COMB (@lem3314157 A) (@lem3314156 A s t)). Qed.
Lemma lem3314159 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term273 A s t) = (term274 A s t)) = ((term176 A s t) = (term287 A s t)).
Proof. exact (MK_COMB (@lem3314150 A s t) (@lem3314158 A s t)). Qed.
Lemma lem3314160 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term176 A s t) = (term287 A s t).
Proof. exact (EQ_MP (@lem3314159 A s t) (@lem3314140 A s t)). Qed.
Lemma lem3314161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314162 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term177 A s t) = (term288 A s t).
Proof. exact (MK_COMB (@lem3314161) (@lem3314160 A s t)). Qed.
Lemma lem3314163 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term141 A s t) = (term141 A s t).
Proof. exact (eq_refl (term141 A s t)). Qed.
Lemma lem3314164 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A s t) = (term289 A s t).
Proof. exact (MK_COMB (@lem3314162 A s t) (@lem3314163 A s t)). Qed.
Lemma lem3314166 {A : Type'} (P : A -> Prop) (Q : Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3314167 {A : Type'} (P : A -> Prop) (Q : Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (@lem3314166 A P Q). Qed.
Lemma lem3314168 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term290 A s t) = (term291 A s t).
Proof. exact (@lem3314167 A (term286 A s t) (term141 A s t)). Qed.
Lemma lem3314169 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term292 A s t x) = (term284 A x s t).
Proof. exact (eq_refl (term292 A s t x)). Qed.
Lemma lem3314170 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term293 A s t) = (term286 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314169 A x s t)). Qed.
Lemma lem3314171 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314172 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term294 A s t) = (term287 A s t).
Proof. exact (MK_COMB (@lem3314171 A) (@lem3314170 A s t)). Qed.
Lemma lem3314173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term295 A s t) = (term288 A s t).
Proof. exact (MK_COMB (@lem3314173) (@lem3314172 A s t)). Qed.
Lemma lem3314175 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term141 A s t) = (term141 A s t).
Proof. exact (eq_refl (term141 A s t)). Qed.
Lemma lem3314176 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term290 A s t) = (term289 A s t).
Proof. exact (MK_COMB (@lem3314174 A s t) (@lem3314175 A s t)). Qed.
Lemma lem3314177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314178 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term296 A s t) = (term297 A s t).
Proof. exact (MK_COMB (@lem3314177) (@lem3314176 A s t)). Qed.
Lemma lem3314179 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term292 A s t x) = (term284 A x s t).
Proof. exact (eq_refl (term292 A s t x)). Qed.
Lemma lem3314180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314181 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term298 A s t x) = (term299 A x s t).
Proof. exact (MK_COMB (@lem3314180) (@lem3314179 A x s t)). Qed.
Lemma lem3314182 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term141 A s t) = (term141 A s t).
Proof. exact (eq_refl (term141 A s t)). Qed.
Lemma lem3314183 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term300 A x s t) = (term301 A x s t).
Proof. exact (MK_COMB (@lem3314181 A x s t) (@lem3314182 A s t)). Qed.
Lemma lem3314184 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term302 A s t) = (term303 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314183 A x s t)). Qed.
Lemma lem3314185 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314186 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term291 A s t) = (term304 A s t).
Proof. exact (MK_COMB (@lem3314185 A) (@lem3314184 A s t)). Qed.
Lemma lem3314187 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term290 A s t) = (term291 A s t)) = ((term289 A s t) = (term304 A s t)).
Proof. exact (MK_COMB (@lem3314178 A s t) (@lem3314186 A s t)). Qed.
Lemma lem3314188 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term289 A s t) = (term304 A s t).
Proof. exact (EQ_MP (@lem3314187 A s t) (@lem3314168 A s t)). Qed.
Lemma lem3314190 {A : Type'} (P : Prop) (Q : A -> Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3314191 {A : Type'} (P : Prop) (Q : A -> Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (@lem3314190 A P Q). Qed.
Lemma lem3314192 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term305 A x s t) = (term306 A x s t).
Proof. exact (@lem3314191 A (term284 A x s t) (term140 A s t)). Qed.
Lemma lem3314193 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term307 A s t x) = (term130 A x s t).
Proof. exact (eq_refl (term307 A s t x)). Qed.
Lemma lem3314194 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term308 A s t) = (term140 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314193 A x s t)). Qed.
Lemma lem3314195 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314196 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term309 A s t) = (term141 A s t).
Proof. exact (MK_COMB (@lem3314195 A) (@lem3314194 A s t)). Qed.
Lemma lem3314197 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term299 A x s t) = (term299 A x s t).
Proof. exact (eq_refl (term299 A x s t)). Qed.
Lemma lem3314198 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term305 A x s t) = (term301 A x s t).
Proof. exact (MK_COMB (@lem3314197 A x s t) (@lem3314196 A s t)). Qed.
Lemma lem3314199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314200 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term310 A x s t) = (term311 A x s t).
Proof. exact (MK_COMB (@lem3314199) (@lem3314198 A x s t)). Qed.
Lemma lem3314201 {A : Type'} (x' : A) (s : A -> Prop) (t : A -> Prop) : (term307 A s t x') = (term130 A x' s t).
Proof. exact (eq_refl (term307 A s t x')). Qed.
Lemma lem3314202 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term299 A x s t) = (term299 A x s t).
Proof. exact (eq_refl (term299 A x s t)). Qed.
Lemma lem3314203 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term312 A x s t x') = (term313 A x x' s t).
Proof. exact (MK_COMB (@lem3314202 A x s t) (@lem3314201 A x' s t)). Qed.
Lemma lem3314204 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term314 A x s t) = (term315 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3314203 A x x' s t)). Qed.
Lemma lem3314205 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314206 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term306 A x s t) = (term316 A x s t).
Proof. exact (MK_COMB (@lem3314205 A) (@lem3314204 A x s t)). Qed.
Lemma lem3314207 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term305 A x s t) = (term306 A x s t)) = ((term301 A x s t) = (term316 A x s t)).
Proof. exact (MK_COMB (@lem3314200 A x s t) (@lem3314206 A x s t)). Qed.
Lemma lem3314208 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term301 A x s t) = (term316 A x s t).
Proof. exact (EQ_MP (@lem3314207 A x s t) (@lem3314192 A x s t)). Qed.
Lemma lem3314209 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term303 A s t) = (term317 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314208 A x s t)). Qed.
Lemma lem3314210 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314211 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term304 A s t) = (term318 A s t).
Proof. exact (MK_COMB (@lem3314210 A) (@lem3314209 A s t)). Qed.
Lemma lem3314212 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term289 A s t) = (term318 A s t).
Proof. exact (TRANS (@lem3314188 A s t) (@lem3314211 A s t)). Qed.
Lemma lem3314213 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term178 A s t) = (term318 A s t).
Proof. exact (TRANS (@lem3314164 A s t) (@lem3314212 A s t)). Qed.
Lemma lem3314214 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term179 A s t) = (term319 A s t).
Proof. exact (MK_COMB (@lem3314136 A s t) (@lem3314213 A s t)). Qed.
Lemma lem3314216 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3314217 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term320 A P Q) = (term321 A P Q).
Proof. exact (@lem3314216 A P Q). Qed.
Lemma lem3314218 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term322 A s t) = (term323 A s t).
Proof. exact (@lem3314217 A (term268 A s t) (term317 A s t)). Qed.
Lemma lem3314219 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term324 A s t x) = (term267 A x s t).
Proof. exact (eq_refl (term324 A s t x)). Qed.
Lemma lem3314220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term325 A s t) = (term268 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314219 A x s t)). Qed.
Lemma lem3314221 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314222 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term326 A s t) = (term269 A s t).
Proof. exact (MK_COMB (@lem3314221 A) (@lem3314220 A s t)). Qed.
Lemma lem3314223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314224 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term327 A s t) = (term270 A s t).
Proof. exact (MK_COMB (@lem3314223) (@lem3314222 A s t)). Qed.
Lemma lem3314225 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term328 A s t x) = (term316 A x s t).
Proof. exact (eq_refl (term328 A s t x)). Qed.
Lemma lem3314226 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term329 A s t) = (term317 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314225 A x s t)). Qed.
Lemma lem3314227 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314228 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term330 A s t) = (term318 A s t).
Proof. exact (MK_COMB (@lem3314227 A) (@lem3314226 A s t)). Qed.
Lemma lem3314229 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term322 A s t) = (term319 A s t).
Proof. exact (MK_COMB (@lem3314224 A s t) (@lem3314228 A s t)). Qed.
Lemma lem3314230 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314231 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term331 A s t) = (term332 A s t).
Proof. exact (MK_COMB (@lem3314230) (@lem3314229 A s t)). Qed.
Lemma lem3314232 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term324 A s t x) = (term267 A x s t).
Proof. exact (eq_refl (term324 A s t x)). Qed.
Lemma lem3314233 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314234 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term333 A s t x) = (term334 A x s t).
Proof. exact (MK_COMB (@lem3314233) (@lem3314232 A x s t)). Qed.
Lemma lem3314235 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term328 A s t x) = (term316 A x s t).
Proof. exact (eq_refl (term328 A s t x)). Qed.
Lemma lem3314236 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term335 A s t x) = (term336 A x s t).
Proof. exact (MK_COMB (@lem3314234 A x s t) (@lem3314235 A x s t)). Qed.
Lemma lem3314237 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term337 A s t) = (term338 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314236 A x s t)). Qed.
Lemma lem3314238 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314239 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term323 A s t) = (term339 A s t).
Proof. exact (MK_COMB (@lem3314238 A) (@lem3314237 A s t)). Qed.
Lemma lem3314240 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term322 A s t) = (term323 A s t)) = ((term319 A s t) = (term339 A s t)).
Proof. exact (MK_COMB (@lem3314231 A s t) (@lem3314239 A s t)). Qed.
Lemma lem3314241 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term319 A s t) = (term339 A s t).
Proof. exact (EQ_MP (@lem3314240 A s t) (@lem3314218 A s t)). Qed.
Lemma lem3314245 {A : Type'} (P : A -> Prop) (Q : Prop) : (term271 A P Q) = (term272 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3314246 {A : Type'} (P : type488 A) (Q : Prop) : (term340 A P Q) = (term341 A P Q).
Proof. exact (@lem3314245 (A -> A) P Q). Qed.
Lemma lem3314247 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term342 A x s t) = (term343 A x s t).
Proof. exact (@lem3314246 A (term266 A x s t) (term316 A x s t)). Qed.
Lemma lem3314248 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term344 A x s t x') = (term264 A x s t x').
Proof. exact (eq_refl (term344 A x s t x')). Qed.
Lemma lem3314249 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term345 A x s t) = (term266 A x s t).
Proof. exact (fun_ext (fun x' : A -> A => @lem3314248 A x s t x')). Qed.
Lemma lem3314250 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3314251 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term346 A x s t) = (term267 A x s t).
Proof. exact (MK_COMB (@lem3314250 A) (@lem3314249 A x s t)). Qed.
Lemma lem3314252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314253 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term347 A x s t) = (term334 A x s t).
Proof. exact (MK_COMB (@lem3314252) (@lem3314251 A x s t)). Qed.
Lemma lem3314254 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term316 A x s t) = (term316 A x s t).
Proof. exact (eq_refl (term316 A x s t)). Qed.
Lemma lem3314255 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term342 A x s t) = (term336 A x s t).
Proof. exact (MK_COMB (@lem3314253 A x s t) (@lem3314254 A x s t)). Qed.
Lemma lem3314256 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314257 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term348 A x s t) = (term349 A x s t).
Proof. exact (MK_COMB (@lem3314256) (@lem3314255 A x s t)). Qed.
Lemma lem3314258 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term344 A x s t x') = (term264 A x s t x').
Proof. exact (eq_refl (term344 A x s t x')). Qed.
Lemma lem3314259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314260 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term350 A x s t x') = (term351 A x s t x').
Proof. exact (MK_COMB (@lem3314259) (@lem3314258 A x s t x')). Qed.
Lemma lem3314261 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term316 A x s t) = (term316 A x s t).
Proof. exact (eq_refl (term316 A x s t)). Qed.
Lemma lem3314262 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term352 A x' x s t) = (term353 A x' x s t).
Proof. exact (MK_COMB (@lem3314260 A x s t x') (@lem3314261 A x s t)). Qed.
Lemma lem3314263 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term354 A x s t) = (term355 A x s t).
Proof. exact (fun_ext (fun x' : A -> A => @lem3314262 A x' x s t)). Qed.
Lemma lem3314264 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3314265 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term343 A x s t) = (term356 A x s t).
Proof. exact (MK_COMB (@lem3314264 A) (@lem3314263 A x s t)). Qed.
Lemma lem3314266 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term342 A x s t) = (term343 A x s t)) = ((term336 A x s t) = (term356 A x s t)).
Proof. exact (MK_COMB (@lem3314257 A x s t) (@lem3314265 A x s t)). Qed.
Lemma lem3314267 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term336 A x s t) = (term356 A x s t).
Proof. exact (EQ_MP (@lem3314266 A x s t) (@lem3314247 A x s t)). Qed.
Lemma lem3314269 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3314270 {A : Type'} (P : Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (@lem3314269 A P Q). Qed.
Lemma lem3314271 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term357 A x' x s t) = (term358 A x' x s t).
Proof. exact (@lem3314270 A (term264 A x s t x') (term315 A x s t)). Qed.
Lemma lem3314272 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term359 A x s t x') = (term313 A x x' s t).
Proof. exact (eq_refl (term359 A x s t x')). Qed.
Lemma lem3314273 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term360 A x s t) = (term315 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3314272 A x x' s t)). Qed.
Lemma lem3314274 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314275 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term361 A x s t) = (term316 A x s t).
Proof. exact (MK_COMB (@lem3314274 A) (@lem3314273 A x s t)). Qed.
Lemma lem3314276 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term351 A x s t x') = (term351 A x s t x').
Proof. exact (eq_refl (term351 A x s t x')). Qed.
Lemma lem3314277 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term357 A x' x s t) = (term353 A x' x s t).
Proof. exact (MK_COMB (@lem3314276 A x s t x') (@lem3314275 A x s t)). Qed.
Lemma lem3314278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3314279 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term362 A x' x s t) = (term363 A x' x s t).
Proof. exact (MK_COMB (@lem3314278) (@lem3314277 A x' x s t)). Qed.
Lemma lem3314280 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term359 A x s t x') = (term313 A x x' s t).
Proof. exact (eq_refl (term359 A x s t x')). Qed.
Lemma lem3314281 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term351 A x s t x') = (term351 A x s t x').
Proof. exact (eq_refl (term351 A x s t x')). Qed.
Lemma lem3314282 {A : Type'} (x' : A -> A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term364 A x' x s t x'') = (term365 A x' x x'' s t).
Proof. exact (MK_COMB (@lem3314281 A x s t x') (@lem3314280 A x x'' s t)). Qed.
Lemma lem3314283 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term366 A x' x s t) = (term367 A x' x s t).
Proof. exact (fun_ext (fun x'' : A => @lem3314282 A x' x x'' s t)). Qed.
Lemma lem3314284 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314285 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term358 A x' x s t) = (term368 A x' x s t).
Proof. exact (MK_COMB (@lem3314284 A) (@lem3314283 A x' x s t)). Qed.
Lemma lem3314286 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : ((term357 A x' x s t) = (term358 A x' x s t)) = ((term353 A x' x s t) = (term368 A x' x s t)).
Proof. exact (MK_COMB (@lem3314279 A x' x s t) (@lem3314285 A x' x s t)). Qed.
Lemma lem3314287 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term353 A x' x s t) = (term368 A x' x s t).
Proof. exact (EQ_MP (@lem3314286 A x' x s t) (@lem3314271 A x' x s t)). Qed.
Lemma lem3314288 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term355 A x s t) = (term369 A x s t).
Proof. exact (fun_ext (fun x' : A -> A => @lem3314287 A x' x s t)). Qed.
Lemma lem3314289 {A : Type'} : (@ex (A -> A)) = (@ex (A -> A)).
Proof. exact (eq_refl (@ex (A -> A))). Qed.
Lemma lem3314290 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term356 A x s t) = (term370 A x s t).
Proof. exact (MK_COMB (@lem3314289 A) (@lem3314288 A x s t)). Qed.
Lemma lem3314291 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term336 A x s t) = (term370 A x s t).
Proof. exact (TRANS (@lem3314267 A x s t) (@lem3314290 A x s t)). Qed.
Lemma lem3314292 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term338 A s t) = (term371 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314291 A x s t)). Qed.
Lemma lem3314293 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3314294 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term339 A s t) = (term372 A s t).
Proof. exact (MK_COMB (@lem3314293 A) (@lem3314292 A s t)). Qed.
Lemma lem3314295 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term319 A s t) = (term372 A s t).
Proof. exact (TRANS (@lem3314241 A s t) (@lem3314294 A s t)). Qed.
Lemma lem3314296 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term179 A s t) = (term372 A s t).
Proof. exact (TRANS (@lem3314214 A s t) (@lem3314295 A s t)). Qed.
Lemma lem3314297 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term153 A s t) = (term372 A s t).
Proof. exact (TRANS (@lem3314008 A s t) (@lem3314296 A s t)). Qed.
Lemma lem3314298 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term372 A s t).
Proof. exact (TRANS (@lem3313649 A s t) (@lem3314297 A s t)). Qed.
Lemma lem3314299 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term73 A s t) : term372 A s t.
Proof. exact (EQ_MP (@lem3314298 A s t) (@lem3313500 A s t h1)). Qed.
Lemma lem3314300 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term370 A x s t) : term370 A x s t.
Proof. exact (h1). Qed.
Lemma lem3314301 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term368 A x' x s t) : term368 A x' x s t.
Proof. exact (h1). Qed.
Lemma lem3314302 {A : Type'} (x' : A -> A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term365 A x' x x'' s t) : term365 A x' x x'' s t.
Proof. exact (h1). Qed.
Lemma lem3314323 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) (x''' : A) : (term115 A x'' s t x''') = (term115 A x'' s t x''').
Proof. exact (eq_refl (term115 A x'' s t x''')). Qed.
Lemma lem3314324 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term123 A x'' s t) = (term123 A x'' s t).
Proof. exact (fun_ext (fun x''' : A => @lem3314323 A x'' s t x''')). Qed.
Lemma lem3314325 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314326 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term124 A x'' s t) = (term124 A x'' s t).
Proof. exact (MK_COMB (@lem3314325 A) (@lem3314324 A x'' s t)). Qed.
Lemma lem3314333 {A : Type'} (s : A -> Prop) (x'' : A) : (term45 A s x'') = (term45 A s x'').
Proof. exact (eq_refl (term45 A s x'')). Qed.
Lemma lem3314334 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term130 A x'' s t) = (term130 A x'' s t).
Proof. exact (MK_COMB (@lem3314333 A s x'') (@lem3314326 A x'' s t)). Qed.
Lemma lem3314345 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term76 A s t x).
Proof. exact (eq_refl (term76 A s t x)). Qed.
Lemma lem3314346 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314345 A s t x)). Qed.
Lemma lem3314347 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314348 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3314347 A) (@lem3314346 A s t)). Qed.
Lemma lem3314359 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term160 A s t x) = (term160 A s t x).
Proof. exact (eq_refl (term160 A s t x)). Qed.
Lemma lem3314360 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term158 A s t) = (term158 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314359 A s t x)). Qed.
Lemma lem3314361 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314362 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term170 A s t) = (term170 A s t).
Proof. exact (MK_COMB (@lem3314361 A) (@lem3314360 A s t)). Qed.
Lemma lem3314363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314364 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term172 A s t) = (term172 A s t).
Proof. exact (MK_COMB (@lem3314363) (@lem3314362 A s t)). Qed.
Lemma lem3314365 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term175 A s t) = (term175 A s t).
Proof. exact (MK_COMB (@lem3314364 A s t) (@lem3314348 A s t)). Qed.
Lemma lem3314378 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term282 A s t x) = (term282 A s t x).
Proof. exact (eq_refl (term282 A s t x)). Qed.
Lemma lem3314379 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term284 A x s t) = (term284 A x s t).
Proof. exact (MK_COMB (@lem3314378 A s t x) (@lem3314365 A s t)). Qed.
Lemma lem3314380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314381 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term299 A x s t) = (term299 A x s t).
Proof. exact (MK_COMB (@lem3314380) (@lem3314379 A x s t)). Qed.
Lemma lem3314382 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term313 A x x'' s t) = (term313 A x x'' s t).
Proof. exact (MK_COMB (@lem3314381 A x s t) (@lem3314334 A x'' s t)). Qed.
Lemma lem3314413 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (x : A) : (term228 A s t x' x) = (term228 A s t x' x).
Proof. exact (eq_refl (term228 A s t x' x)). Qed.
Lemma lem3314414 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term230 A s t x') = (term230 A s t x').
Proof. exact (fun_ext (fun x : A => @lem3314413 A s t x' x)). Qed.
Lemma lem3314415 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314416 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term232 A s t x') = (term232 A s t x').
Proof. exact (MK_COMB (@lem3314415 A) (@lem3314414 A s t x')). Qed.
Lemma lem3314441 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term89 A s t x) = (term89 A s t x).
Proof. exact (eq_refl (term89 A s t x)). Qed.
Lemma lem3314452 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term76 A s t x).
Proof. exact (eq_refl (term76 A s t x)). Qed.
Lemma lem3314453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314452 A s t x)). Qed.
Lemma lem3314454 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314455 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3314454 A) (@lem3314453 A s t)). Qed.
Lemma lem3314456 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314457 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term105 A s t).
Proof. exact (MK_COMB (@lem3314456) (@lem3314455 A s t)). Qed.
Lemma lem3314458 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term190 A s t x) = (term190 A s t x).
Proof. exact (MK_COMB (@lem3314457 A s t) (@lem3314441 A s t x)). Qed.
Lemma lem3314459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3314460 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term248 A s t x) = (term248 A s t x).
Proof. exact (MK_COMB (@lem3314459) (@lem3314458 A s t x)). Qed.
Lemma lem3314461 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term264 A x s t x') = (term264 A x s t x').
Proof. exact (MK_COMB (@lem3314460 A s t x) (@lem3314416 A s t x')). Qed.
Lemma lem3314462 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3314463 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term351 A x s t x') = (term351 A x s t x').
Proof. exact (MK_COMB (@lem3314462) (@lem3314461 A x s t x')). Qed.
Lemma lem3314464 {A : Type'} (x' : A -> A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term365 A x' x x'' s t) = (term365 A x' x x'' s t).
Proof. exact (MK_COMB (@lem3314463 A x s t x') (@lem3314382 A x x'' s t)). Qed.
Lemma lem3314465 {A : Type'} (x' : A -> A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term365 A x' x x'' s t) : term365 A x' x x'' s t.
Proof. exact (EQ_MP (@lem3314464 A x' x x'' s t) (@lem3314302 A x' x x'' s t h1)). Qed.
Lemma lem3314466 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term264 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3314467 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term313 A x x'' s t.
Proof. exact (h1). Qed.
Lemma lem3314468 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term232 A s t x'.
Proof. exact (proj2 (@lem3314466 A x s t x' h1)). Qed.
Lemma lem3314469 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term190 A s t x.
Proof. exact (proj1 (@lem3314466 A x s t x' h1)). Qed.
Lemma lem3314470 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term89 A s t x.
Proof. exact (proj2 (@lem3314469 A x s t x' h1)). Qed.
Lemma lem3314471 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term87 A s t.
Proof. exact (proj1 (@lem3314469 A x s t x' h1)). Qed.
Lemma lem3314472 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term373 A s t x.
Proof. exact (proj2 (@lem3314470 A x s t x' h1)). Qed.
Lemma lem3314473 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term374 A s t x.
Proof. exact (proj1 (@lem3314470 A x s t x' h1)). Qed.
Lemma lem3314480 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term130 A x'' s t.
Proof. exact (proj2 (@lem3314467 A x x'' s t h1)). Qed.
Lemma lem3314481 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term284 A x s t.
Proof. exact (proj1 (@lem3314467 A x x'' s t h1)). Qed.
Lemma lem3314482 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term124 A x'' s t.
Proof. exact (proj2 (@lem3314480 A x x'' s t h1)). Qed.
Lemma lem3314484 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term75 A s t x) : term75 A s t x.
Proof. exact (h1). Qed.
Lemma lem3314485 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term175 A s t.
Proof. exact (h1). Qed.
Lemma lem3314489 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term170 A s t.
Proof. exact (proj1 (@lem3314485 A s t h1)). Qed.
Lemma lem3314535 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term44 A s x.
Proof. exact (h1). Qed.
Lemma lem3314539 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3314563 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (x : A) : (term228 A s t x' x) = (term375 A s t x' x).
Proof. exact (@lem19490 (term376 A s x' x) (s x) (term377 A t x' x)). Qed.
Lemma lem3314564 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term230 A s t x') = (term378 A s t x').
Proof. exact (fun_ext (fun x : A => @lem3314563 A s t x' x)). Qed.
Lemma lem3314565 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314567 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) : (term232 A s t x') = (term379 A s t x').
Proof. exact (MK_COMB (@lem3314565 A) (@lem3314564 A s t x')). Qed.
Lemma lem3314568 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term379 A s t x'.
Proof. exact (EQ_MP (@lem3314567 A s t x') (@lem3314468 A x s t x' h1)). Qed.
Lemma lem3314576 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term76 A s t x).
Proof. exact (eq_refl (term76 A s t x)). Qed.
Lemma lem3314577 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314576 A s t x)). Qed.
Lemma lem3314578 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314580 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3314578 A) (@lem3314577 A s t)). Qed.
Lemma lem3314581 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term87 A s t.
Proof. exact (EQ_MP (@lem3314580 A s t) (@lem3314471 A x s t x' h1)). Qed.
Lemma lem3314585 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term44 A s x.
Proof. exact (h1). Qed.
Lemma lem3314589 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3314626 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term76 A s t x) = (term76 A s t x).
Proof. exact (eq_refl (term76 A s t x)). Qed.
Lemma lem3314627 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term86 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314626 A s t x)). Qed.
Lemma lem3314628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314630 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3314628 A) (@lem3314627 A s t)). Qed.
Lemma lem3314631 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term87 A s t.
Proof. exact (EQ_MP (@lem3314630 A s t) (@lem3314471 A x s t x' h1)). Qed.
Lemma lem3314635 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) : term44 A t x.
Proof. exact (h1). Qed.
Lemma lem3314639 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3314685 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) : term44 A t x.
Proof. exact (h1). Qed.
Lemma lem3314689 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3314711 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) (x''' : A) : (term115 A x'' s t x''') = (term380 A x'' s t x''').
Proof. exact (@lem19699 (term381 A x''' x'') (term44 A s x''') (t x''')). Qed.
Lemma lem3314712 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term123 A x'' s t) = (term382 A x'' s t).
Proof. exact (fun_ext (fun x''' : A => @lem3314711 A x'' s t x''')). Qed.
Lemma lem3314713 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314715 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term124 A x'' s t) = (term383 A x'' s t).
Proof. exact (MK_COMB (@lem3314713 A) (@lem3314712 A x'' s t)). Qed.
Lemma lem3314716 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term383 A x'' s t.
Proof. exact (EQ_MP (@lem3314715 A x'' s t) (@lem3314482 A x x'' s t h1)). Qed.
Lemma lem3314746 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) (x''' : A) : (term115 A x'' s t x''') = (term380 A x'' s t x''').
Proof. exact (@lem19699 (term381 A x''' x'') (term44 A s x''') (t x''')). Qed.
Lemma lem3314747 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term123 A x'' s t) = (term382 A x'' s t).
Proof. exact (fun_ext (fun x''' : A => @lem3314746 A x'' s t x''')). Qed.
Lemma lem3314748 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314750 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) : (term124 A x'' s t) = (term383 A x'' s t).
Proof. exact (MK_COMB (@lem3314748 A) (@lem3314747 A x'' s t)). Qed.
Lemma lem3314751 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term383 A x'' s t.
Proof. exact (EQ_MP (@lem3314750 A x'' s t) (@lem3314482 A x x'' s t h1)). Qed.
Lemma lem3314759 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term160 A s t x) = (term160 A s t x).
Proof. exact (eq_refl (term160 A s t x)). Qed.
Lemma lem3314760 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term158 A s t) = (term158 A s t).
Proof. exact (fun_ext (fun x : A => @lem3314759 A s t x)). Qed.
Lemma lem3314761 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3314763 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term170 A s t) = (term170 A s t).
Proof. exact (MK_COMB (@lem3314761 A) (@lem3314760 A s t)). Qed.
Lemma lem3314764 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term170 A s t.
Proof. exact (EQ_MP (@lem3314763 A s t) (@lem3314489 A s t h1)). Qed.
Lemma lem3314784 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term384 A s t x' _34186.
Proof. exact (@lem3314568 A x s t x' h1 _34186). Qed.
Lemma lem3314785 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (_34186 : A) : (term384 A s t x' _34186) = (term375 A s t x' _34186).
Proof. exact (eq_refl (term384 A s t x' _34186)). Qed.
Lemma lem3314786 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term375 A s t x' _34186.
Proof. exact (EQ_MP (@lem3314785 A s t x' _34186) (@lem3314784 A _34186 x s t x' h1)). Qed.
Lemma lem3314787 {A : Type'} (_34187 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term163 A s t _34187.
Proof. exact (@lem3314581 A x s t x' h1 _34187). Qed.
Lemma lem3314788 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34187 : A) : (term163 A s t _34187) = (term76 A s t _34187).
Proof. exact (eq_refl (term163 A s t _34187)). Qed.
Lemma lem3314793 {A : Type'} (_34189 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term163 A s t _34189.
Proof. exact (@lem3314631 A x s t x' h1 _34189). Qed.
Lemma lem3314794 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34189 : A) : (term163 A s t _34189) = (term76 A s t _34189).
Proof. exact (eq_refl (term163 A s t _34189)). Qed.
Lemma lem3314802 {A : Type'} (_34192 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term385 A x'' s t _34192.
Proof. exact (@lem3314716 A x x'' s t h1 _34192). Qed.
Lemma lem3314803 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) (_34192 : A) : (term385 A x'' s t _34192) = (term380 A x'' s t _34192).
Proof. exact (eq_refl (term385 A x'' s t _34192)). Qed.
Lemma lem3314804 {A : Type'} (_34192 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term380 A x'' s t _34192.
Proof. exact (EQ_MP (@lem3314803 A x'' s t _34192) (@lem3314802 A _34192 x x'' s t h1)). Qed.
Lemma lem3314805 {A : Type'} (_34193 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term385 A x'' s t _34193.
Proof. exact (@lem3314751 A x x'' s t h1 _34193). Qed.
Lemma lem3314806 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) (_34193 : A) : (term385 A x'' s t _34193) = (term380 A x'' s t _34193).
Proof. exact (eq_refl (term385 A x'' s t _34193)). Qed.
Lemma lem3314807 {A : Type'} (_34193 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term380 A x'' s t _34193.
Proof. exact (EQ_MP (@lem3314806 A x'' s t _34193) (@lem3314805 A _34193 x x'' s t h1)). Qed.
Lemma lem3314808 {A : Type'} (_34194 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term159 A s t _34194.
Proof. exact (@lem3314764 A s t h1 _34194). Qed.
Lemma lem3314809 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34194 : A) : (term159 A s t _34194) = (term160 A s t _34194).
Proof. exact (eq_refl (term159 A s t _34194)). Qed.
Lemma lem3314833 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term44 A s x.
Proof. exact (h1). Qed.
Lemma lem3314835 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3314857 {A : Type'} (_34187 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term76 A s t _34187.
Proof. exact (EQ_MP (@lem3314788 A s t _34187) (@lem3314787 A _34187 x s t x' h1)). Qed.
Lemma lem3314859 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term44 A s x.
Proof. exact (h1). Qed.
Lemma lem3314861 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3314871 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term386 A s x' _34186.
Proof. exact (proj1 (@lem3314786 A _34186 x s t x' h1)). Qed.
Lemma lem3314877 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term387 A s t x' _34186.
Proof. exact (proj2 (@lem3314786 A _34186 x s t x' h1)). Qed.
Lemma lem3314883 {A : Type'} (_34189 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term76 A s t _34189.
Proof. exact (EQ_MP (@lem3314794 A s t _34189) (@lem3314793 A _34189 x s t x' h1)). Qed.
Lemma lem3314885 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) : term44 A t x.
Proof. exact (h1). Qed.
Lemma lem3314887 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3314911 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) : term44 A t x.
Proof. exact (h1). Qed.
Lemma lem3314913 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3314935 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term75 A s t x) : term44 A t x.
Proof. exact (proj2 (@lem3314484 A s t x h1)). Qed.
Lemma lem3314947 {A : Type'} (_34192 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term76 A s t _34192.
Proof. exact (proj2 (@lem3314804 A _34192 x x'' s t h1)). Qed.
Lemma lem3314949 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term44 A s x''.
Proof. exact (proj1 (@lem3314480 A x x'' s t h1)). Qed.
Lemma lem3314955 {A : Type'} (_34194 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term160 A s t _34194.
Proof. exact (EQ_MP (@lem3314809 A s t _34194) (@lem3314808 A _34194 s t h1)). Qed.
Lemma lem3314967 {A : Type'} (_34193 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term388 A x'' t _34193.
Proof. exact (proj1 (@lem3314807 A _34193 x x'' s t h1)). Qed.
Lemma lem3315009 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3315010 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term389 A s x.
Proof. exact (fun h0 : term44 A s x => @lem3315009 A s x h1). Qed.
Lemma lem3315012 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315013 {A : Type'} (s : A -> Prop) (x : A) : (term389 A s x) = (s x).
Proof. exact (@lem3315012 (s x)). Qed.
Lemma lem3315014 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3315013 A s x) (@lem3315010 A s x h1)). Qed.
Lemma lem3315017 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3315019 {A : Type'} (s : A -> Prop) (x : A) : (term44 A s x) = (term391 A s x).
Proof. exact (@lem3315017 (s x)). Qed.
Lemma lem3315022 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term391 A s x.
Proof. exact (EQ_MP (@lem3315019 A s x) (@lem3314833 A s x h1)). Qed.
Lemma lem3315025 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (@lem3315022 A s x h1 (@lem3315014 A s x h2)). Qed.
Lemma lem3315026 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : term392.
Proof. exact (fun h0 : ~ False => @lem3315025 A s x h1 h2). Qed.
Lemma lem3315028 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315029 : term392 = False.
Proof. exact (@lem3315028 False). Qed.
Lemma lem3315030 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3315029) (@lem3315026 A s x h1 h2)). Qed.
Lemma lem3315043 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3315044 {A : Type'} (_34204 : A) (_34205 : A) (h1 : _34204 = _34205) : _34204 = _34205.
Proof. exact (h1). Qed.
Lemma lem3315045 {A : Type'} (t : A -> Prop) (_34204 : A) (_34205 : A) (h1 : _34204 = _34205) : (t _34204) = (t _34205).
Proof. exact (MK_COMB (@lem3315043 A t) (@lem3315044 A _34204 _34205 h1)). Qed.
Lemma lem3315047 (b : Prop) (a : Prop) : term393 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3315048 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : term394 A _34205 t _34204.
Proof. exact (@lem3315047 (t _34205) (t _34204)). Qed.
Lemma lem3315049 {A : Type'} (t : A -> Prop) (_34204 : A) (_34205 : A) (h1 : _34204 = _34205) : term395 A _34205 t _34204.
Proof. exact (@lem3315048 A _34205 t _34204 (@lem3315045 A t _34204 _34205 h1)). Qed.
Lemma lem3315050 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : term396 A _34205 t _34204.
Proof. exact (fun h0 : _34204 = _34205 => @lem3315049 A t _34204 _34205 h0). Qed.
Lemma lem3315052 (a : Prop) (b : Prop) : (a -> b) = (term397 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3315053 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : (term396 A _34205 t _34204) = (term398 A _34205 t _34204).
Proof. exact (@lem3315052 (_34204 = _34205) (term395 A _34205 t _34204)). Qed.
Lemma lem3315054 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : term398 A _34205 t _34204.
Proof. exact (EQ_MP (@lem3315053 A _34205 t _34204) (@lem3315050 A _34205 t _34204)). Qed.
Lemma lem3315064 {A : Type'} (x : A) (y : A) (z : A) : term399 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem3315067 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term44 A s x.
Proof. exact (h1). Qed.
Lemma lem3315068 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term400 A s x.
Proof. exact (fun h0 : s x => @lem3315067 A s x h1). Qed.
Lemma lem3315070 (p : Prop) : (term401 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3315071 {A : Type'} (s : A -> Prop) (x : A) : (term400 A s x) = (term44 A s x).
Proof. exact (@lem3315070 (s x)). Qed.
Lemma lem3315072 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term44 A s x.
Proof. exact (EQ_MP (@lem3315071 A s x) (@lem3315068 A s x h1)). Qed.
Lemma lem3315074 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3315075 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3315074 A x). Qed.
Lemma lem3315076 {A : Type'} (x' : A -> A) (x : A) : (x' x) = (x' x).
Proof. exact (@lem3315075 A (x' x)). Qed.
Lemma lem3315077 {A : Type'} (x' : A -> A) (x : A) : term402 A x' x.
Proof. exact (fun h0 : term403 A x' x => @lem3315076 A x' x). Qed.
Lemma lem3315079 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315080 {A : Type'} (x' : A -> A) (x : A) : (term402 A x' x) = ((x' x) = (x' x)).
Proof. exact (@lem3315079 ((x' x) = (x' x))). Qed.
Lemma lem3315081 {A : Type'} (x' : A -> A) (x : A) : (x' x) = (x' x).
Proof. exact (EQ_MP (@lem3315080 A x' x) (@lem3315077 A x' x)). Qed.
Lemma lem3315084 {A : Type'} (t : A -> Prop) (x' : A -> A) (x : A) (h1 : term377 A t x' x) : term377 A t x' x.
Proof. exact (h1). Qed.
Lemma lem3315085 {A : Type'} (t : A -> Prop) (x' : A -> A) (x : A) (h1 : term377 A t x' x) : term404 A t x' x.
Proof. exact (fun h0 : term405 A t x' x => @lem3315084 A t x' x h1). Qed.
Lemma lem3315087 (p : Prop) : (term401 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3315088 {A : Type'} (t : A -> Prop) (x' : A -> A) (x : A) : (term404 A t x' x) = (term377 A t x' x).
Proof. exact (@lem3315087 (term405 A t x' x)). Qed.
Lemma lem3315089 {A : Type'} (t : A -> Prop) (x' : A -> A) (x : A) (h1 : term377 A t x' x) : term377 A t x' x.
Proof. exact (EQ_MP (@lem3315088 A t x' x) (@lem3315085 A t x' x h1)). Qed.
Lemma lem3315091 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3315092 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term389 A t x.
Proof. exact (fun h0 : term44 A t x => @lem3315091 A t x h1). Qed.
Lemma lem3315094 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315095 {A : Type'} (t : A -> Prop) (x : A) : (term389 A t x) = (t x).
Proof. exact (@lem3315094 (t x)). Qed.
Lemma lem3315096 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3315095 A t x) (@lem3315092 A t x h1)). Qed.
Lemma lem3315098 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315099 {A : Type'} (t : A -> Prop) (_34204 : A) (_34205 : A) : (term398 A _34205 t _34204) = (term407 A t _34204 _34205).
Proof. exact (@lem3315098 (term395 A _34205 t _34204) (term381 A _34204 _34205)). Qed.
Lemma lem3315101 (a : Prop) (b : Prop) : (term408 a b) = (term409 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3315102 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : (term410 A _34205 t _34204) = (term411 A _34205 t _34204).
Proof. exact (@lem3315101 (t _34205) (term44 A t _34204)). Qed.
Lemma lem3315104 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315105 {A : Type'} (t : A -> Prop) (_34204 : A) : (term107 A t _34204) = (t _34204).
Proof. exact (@lem3315104 (t _34204)). Qed.
Lemma lem3315106 {A : Type'} (t : A -> Prop) (_34205 : A) : (term45 A t _34205) = (term45 A t _34205).
Proof. exact (eq_refl (term45 A t _34205)). Qed.
Lemma lem3315107 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : (term411 A _34205 t _34204) = (term412 A _34205 t _34204).
Proof. exact (MK_COMB (@lem3315106 A t _34205) (@lem3315105 A t _34204)). Qed.
Lemma lem3315108 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : (term410 A _34205 t _34204) = (term412 A _34205 t _34204).
Proof. exact (TRANS (@lem3315102 A _34205 t _34204) (@lem3315107 A _34205 t _34204)). Qed.
Lemma lem3315109 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315110 {A : Type'} (_34205 : A) (t : A -> Prop) (_34204 : A) : (term413 A _34205 t _34204) = (term414 A _34205 t _34204).
Proof. exact (MK_COMB (@lem3315109) (@lem3315108 A _34205 t _34204)). Qed.
Lemma lem3315111 {A : Type'} (_34204 : A) (_34205 : A) : (term381 A _34204 _34205) = (term381 A _34204 _34205).
Proof. exact (eq_refl (term381 A _34204 _34205)). Qed.
Lemma lem3315112 {A : Type'} (t : A -> Prop) (_34204 : A) (_34205 : A) : (term407 A t _34204 _34205) = (term415 A t _34204 _34205).
Proof. exact (MK_COMB (@lem3315110 A _34205 t _34204) (@lem3315111 A _34204 _34205)). Qed.
Lemma lem3315113 {A : Type'} (t : A -> Prop) (_34204 : A) (_34205 : A) : (term398 A _34205 t _34204) = (term415 A t _34204 _34205).
Proof. exact (TRANS (@lem3315099 A t _34204 _34205) (@lem3315112 A t _34204 _34205)). Qed.
Lemma lem3315115 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term416 A x' t x.
Proof. exact (conj (@lem3315089 A t x' x h1) (@lem3315096 A t x h2)). Qed.
Lemma lem3315117 {A : Type'} (t : A -> Prop) (_34204 : A) (_34205 : A) : term415 A t _34204 _34205.
Proof. exact (EQ_MP (@lem3315113 A t _34204 _34205) (@lem3315054 A _34205 t _34204)). Qed.
Lemma lem3315118 {A : Type'} (t : A -> Prop) (_34204 : A) (_34205 : A) : term415 A t _34204 _34205.
Proof. exact (@lem3315117 A t _34204 _34205). Qed.
Lemma lem3315119 {A : Type'} (t : A -> Prop) (x' : A -> A) (x : A) : term417 A t x' x.
Proof. exact (@lem3315118 A t x (x' x)). Qed.
Lemma lem3315122 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term418 A x' x.
Proof. exact (@lem3315119 A t x' x (@lem3315115 A x' t x h1 h2)). Qed.
Lemma lem3315123 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term419 A x' x.
Proof. exact (fun h0 : x = (x' x) => @lem3315122 A x' t x h1 h2). Qed.
Lemma lem3315125 (p : Prop) : (term401 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3315126 {A : Type'} (x' : A -> A) (x : A) : (term419 A x' x) = (term418 A x' x).
Proof. exact (@lem3315125 (x = (x' x))). Qed.
Lemma lem3315127 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term418 A x' x.
Proof. exact (EQ_MP (@lem3315126 A x' x) (@lem3315123 A x' t x h1 h2)). Qed.
Lemma lem3315129 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315130 {A : Type'} (z : A) (x : A) (y : A) : (term399 A x y z) = (term420 A z x y).
Proof. exact (@lem3315129 (term421 A x y z) (term381 A x y)). Qed.
Lemma lem3315132 (a : Prop) (b : Prop) : (term408 a b) = (term409 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3315133 {A : Type'} (x : A) (y : A) (z : A) : (term422 A x y z) = (term423 A x y z).
Proof. exact (@lem3315132 (term381 A x z) (y = z)). Qed.
Lemma lem3315135 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315136 {A : Type'} (x : A) (z : A) : (term424 A x z) = (x = z).
Proof. exact (@lem3315135 (x = z)). Qed.
Lemma lem3315137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3315138 {A : Type'} (x : A) (z : A) : (term425 A x z) = (term426 A x z).
Proof. exact (MK_COMB (@lem3315137) (@lem3315136 A x z)). Qed.
Lemma lem3315139 {A : Type'} (y : A) (z : A) : (term381 A y z) = (term381 A y z).
Proof. exact (eq_refl (term381 A y z)). Qed.
Lemma lem3315140 {A : Type'} (x : A) (y : A) (z : A) : (term423 A x y z) = (term427 A x y z).
Proof. exact (MK_COMB (@lem3315138 A x z) (@lem3315139 A y z)). Qed.
Lemma lem3315141 {A : Type'} (x : A) (y : A) (z : A) : (term422 A x y z) = (term427 A x y z).
Proof. exact (TRANS (@lem3315133 A x y z) (@lem3315140 A x y z)). Qed.
Lemma lem3315142 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315143 {A : Type'} (x : A) (y : A) (z : A) : (term428 A x y z) = (term429 A x y z).
Proof. exact (MK_COMB (@lem3315142) (@lem3315141 A x y z)). Qed.
Lemma lem3315144 {A : Type'} (x : A) (y : A) : (term381 A x y) = (term381 A x y).
Proof. exact (eq_refl (term381 A x y)). Qed.
Lemma lem3315145 {A : Type'} (z : A) (x : A) (y : A) : (term420 A z x y) = (term430 A z x y).
Proof. exact (MK_COMB (@lem3315143 A x y z) (@lem3315144 A x y)). Qed.
Lemma lem3315146 {A : Type'} (z : A) (x : A) (y : A) : (term399 A x y z) = (term430 A z x y).
Proof. exact (TRANS (@lem3315130 A z x y) (@lem3315145 A z x y)). Qed.
Lemma lem3315148 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term431 A x' x.
Proof. exact (conj (@lem3315081 A x' x) (@lem3315127 A x' t x h1 h2)). Qed.
Lemma lem3315150 {A : Type'} (z : A) (x : A) (y : A) : term430 A z x y.
Proof. exact (EQ_MP (@lem3315146 A z x y) (@lem3315064 A x y z)). Qed.
Lemma lem3315151 {A : Type'} (z : A) (x : A) (y : A) : term430 A z x y.
Proof. exact (@lem3315150 A z x y). Qed.
Lemma lem3315152 {A : Type'} (x' : A -> A) (x : A) : term432 A x' x.
Proof. exact (@lem3315151 A (x' x) (x' x) x). Qed.
Lemma lem3315155 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term433 A x' x.
Proof. exact (@lem3315152 A x' x (@lem3315148 A x' t x h1 h2)). Qed.
Lemma lem3315156 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term434 A x' x.
Proof. exact (fun h0 : (x' x) = x => @lem3315155 A x' t x h1 h2). Qed.
Lemma lem3315158 (p : Prop) : (term401 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3315159 {A : Type'} (x' : A -> A) (x : A) : (term434 A x' x) = (term433 A x' x).
Proof. exact (@lem3315158 ((x' x) = x)). Qed.
Lemma lem3315160 {A : Type'} (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term377 A t x' x) (h2 : t x) : term433 A x' x.
Proof. exact (EQ_MP (@lem3315159 A x' x) (@lem3315156 A x' t x h1 h2)). Qed.
Lemma lem3315176 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3315177 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term376 A s x' _34186) = (term435 A s x' _34186).
Proof. exact (@lem3315176 (term405 A s x' _34186) ((x' _34186) = _34186)). Qed.
Lemma lem3315185 {A : Type'} (s : A -> Prop) (_34186 : A) : (term126 A s _34186) = (term126 A s _34186).
Proof. exact (eq_refl (term126 A s _34186)). Qed.
Lemma lem3315186 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term386 A s x' _34186) = (term436 A s x' _34186).
Proof. exact (MK_COMB (@lem3315185 A s _34186) (@lem3315177 A s x' _34186)). Qed.
Lemma lem3315197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3315198 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term437 A s x' _34186) = (term438 A s x' _34186).
Proof. exact (MK_COMB (@lem3315197) (@lem3315186 A s x' _34186)). Qed.
Lemma lem3315202 (q : Prop) (p : Prop) (r : Prop) : (term439 p q r) = (term439 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3315203 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term440 A s x' _34186) = (term436 A s x' _34186).
Proof. exact (@lem3315202 (s _34186) (term405 A s x' _34186) ((x' _34186) = _34186)). Qed.
Lemma lem3315221 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : ((term386 A s x' _34186) = (term440 A s x' _34186)) = ((term436 A s x' _34186) = (term436 A s x' _34186)).
Proof. exact (MK_COMB (@lem3315198 A s x' _34186) (@lem3315203 A s x' _34186)). Qed.
Lemma lem3315223 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3315224 (x : Prop) : (x = x) = True.
Proof. exact (@lem3315223 Prop x). Qed.
Lemma lem3315225 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : ((term436 A s x' _34186) = (term436 A s x' _34186)) = True.
Proof. exact (@lem3315224 (term436 A s x' _34186)). Qed.
Lemma lem3315226 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : ((term386 A s x' _34186) = (term440 A s x' _34186)) = True.
Proof. exact (TRANS (@lem3315221 A s x' _34186) (@lem3315225 A s x' _34186)). Qed.
Lemma lem3315227 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : True = ((term386 A s x' _34186) = (term440 A s x' _34186)).
Proof. exact (SYM (@lem3315226 A s x' _34186)). Qed.
Lemma lem3315228 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term386 A s x' _34186) = (term440 A s x' _34186).
Proof. exact (EQ_MP (@lem3315227 A s x' _34186) (@lem0)). Qed.
Lemma lem3315229 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term440 A s x' _34186.
Proof. exact (EQ_MP (@lem3315228 A s x' _34186) (@lem3314871 A _34186 x s t x' h1)). Qed.
Lemma lem3315231 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315232 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term440 A s x' _34186) = (term441 A s x' _34186).
Proof. exact (@lem3315231 (term442 A s x' _34186) (term405 A s x' _34186)). Qed.
Lemma lem3315234 (a : Prop) (b : Prop) : (term408 a b) = (term409 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3315235 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term443 A s x' _34186) = (term444 A s x' _34186).
Proof. exact (@lem3315234 (s _34186) ((x' _34186) = _34186)). Qed.
Lemma lem3315236 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315237 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term445 A s x' _34186) = (term446 A s x' _34186).
Proof. exact (MK_COMB (@lem3315236) (@lem3315235 A s x' _34186)). Qed.
Lemma lem3315238 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term405 A s x' _34186) = (term405 A s x' _34186).
Proof. exact (eq_refl (term405 A s x' _34186)). Qed.
Lemma lem3315239 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term441 A s x' _34186) = (term447 A s x' _34186).
Proof. exact (MK_COMB (@lem3315237 A s x' _34186) (@lem3315238 A s x' _34186)). Qed.
Lemma lem3315240 {A : Type'} (s : A -> Prop) (x' : A -> A) (_34186 : A) : (term440 A s x' _34186) = (term447 A s x' _34186).
Proof. exact (TRANS (@lem3315232 A s x' _34186) (@lem3315239 A s x' _34186)). Qed.
Lemma lem3315242 {A : Type'} (s : A -> Prop) (x' : A -> A) (t : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : term377 A t x' x) (h3 : t x) : term444 A s x' x.
Proof. exact (conj (@lem3315072 A s x h1) (@lem3315160 A x' t x h2 h3)). Qed.
Lemma lem3315244 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term447 A s x' _34186.
Proof. exact (EQ_MP (@lem3315240 A s x' _34186) (@lem3315229 A _34186 x s t x' h1)). Qed.
Lemma lem3315245 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term447 A s x' _34186.
Proof. exact (@lem3315244 A _34186 x s t x' h1). Qed.
Lemma lem3315246 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term447 A s x' x.
Proof. exact (@lem3315245 A x x s t x' h1). Qed.
Lemma lem3315249 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : term377 A t x' x) (h3 : t x) (h4 : term264 A x s t x') : term405 A s x' x.
Proof. exact (@lem3315246 A x s t x' h4 (@lem3315242 A s x' t x h1 h2 h3)). Qed.
Lemma lem3315250 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : term377 A t x' x) (h3 : t x) (h4 : term264 A x s t x') : term448 A s x' x.
Proof. exact (fun h0 : term377 A s x' x => @lem3315249 A x s t x' h1 h2 h3 h4). Qed.
Lemma lem3315252 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315253 {A : Type'} (s : A -> Prop) (x' : A -> A) (x : A) : (term448 A s x' x) = (term405 A s x' x).
Proof. exact (@lem3315252 (term405 A s x' x)). Qed.
Lemma lem3315254 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : term377 A t x' x) (h3 : t x) (h4 : term264 A x s t x') : term405 A s x' x.
Proof. exact (EQ_MP (@lem3315253 A s x' x) (@lem3315250 A x s t x' h1 h2 h3 h4)). Qed.
Lemma lem3315260 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3315261 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : (term76 A s t _34187) = (term160 A t s _34187).
Proof. exact (@lem3315260 (t _34187) (term44 A s _34187)). Qed.
Lemma lem3315267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3315268 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : (term449 A s t _34187) = (term450 A t s _34187).
Proof. exact (MK_COMB (@lem3315267) (@lem3315261 A t s _34187)). Qed.
Lemma lem3315274 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : (term160 A t s _34187) = (term160 A t s _34187).
Proof. exact (eq_refl (term160 A t s _34187)). Qed.
Lemma lem3315275 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : ((term76 A s t _34187) = (term160 A t s _34187)) = ((term160 A t s _34187) = (term160 A t s _34187)).
Proof. exact (MK_COMB (@lem3315268 A t s _34187) (@lem3315274 A t s _34187)). Qed.
Lemma lem3315277 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3315278 (x : Prop) : (x = x) = True.
Proof. exact (@lem3315277 Prop x). Qed.
Lemma lem3315279 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : ((term160 A t s _34187) = (term160 A t s _34187)) = True.
Proof. exact (@lem3315278 (term160 A t s _34187)). Qed.
Lemma lem3315280 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : ((term76 A s t _34187) = (term160 A t s _34187)) = True.
Proof. exact (TRANS (@lem3315275 A t s _34187) (@lem3315279 A t s _34187)). Qed.
Lemma lem3315281 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : True = ((term76 A s t _34187) = (term160 A t s _34187)).
Proof. exact (SYM (@lem3315280 A t s _34187)). Qed.
Lemma lem3315282 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34187 : A) : (term76 A s t _34187) = (term160 A t s _34187).
Proof. exact (EQ_MP (@lem3315281 A t s _34187) (@lem0)). Qed.
Lemma lem3315283 {A : Type'} (_34187 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term160 A t s _34187.
Proof. exact (EQ_MP (@lem3315282 A t s _34187) (@lem3314857 A _34187 x s t x' h1)). Qed.
Lemma lem3315285 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315286 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34187 : A) : (term160 A t s _34187) = (term451 A s t _34187).
Proof. exact (@lem3315285 (term44 A s _34187) (t _34187)). Qed.
Lemma lem3315288 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315289 {A : Type'} (s : A -> Prop) (_34187 : A) : (term107 A s _34187) = (s _34187).
Proof. exact (@lem3315288 (s _34187)). Qed.
Lemma lem3315290 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315291 {A : Type'} (s : A -> Prop) (_34187 : A) : (term452 A s _34187) = (term28 A s _34187).
Proof. exact (MK_COMB (@lem3315290) (@lem3315289 A s _34187)). Qed.
Lemma lem3315292 {A : Type'} (t : A -> Prop) (_34187 : A) : (t _34187) = (t _34187).
Proof. exact (eq_refl (t _34187)). Qed.
Lemma lem3315293 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34187 : A) : (term451 A s t _34187) = (term30 A s t _34187).
Proof. exact (MK_COMB (@lem3315291 A s _34187) (@lem3315292 A t _34187)). Qed.
Lemma lem3315294 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34187 : A) : (term160 A t s _34187) = (term30 A s t _34187).
Proof. exact (TRANS (@lem3315286 A s t _34187) (@lem3315293 A s t _34187)). Qed.
Lemma lem3315297 {A : Type'} (_34187 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term30 A s t _34187.
Proof. exact (EQ_MP (@lem3315294 A s t _34187) (@lem3315283 A _34187 x s t x' h1)). Qed.
Lemma lem3315298 {A : Type'} (_34187 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term30 A s t _34187.
Proof. exact (@lem3315297 A _34187 x s t x' h1). Qed.
Lemma lem3315299 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term453 A s t x' x.
Proof. exact (@lem3315298 A (x' x) x s t x' h1). Qed.
Lemma lem3315302 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : term377 A t x' x) (h3 : t x) (h4 : term264 A x s t x') : term405 A t x' x.
Proof. exact (@lem3315299 A x s t x' h4 (@lem3315254 A x s t x' h1 h2 h3 h4)). Qed.
Lemma lem3315303 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : term448 A t x' x.
Proof. exact (fun h0 : term377 A t x' x => @lem3315302 A x s t x' h1 h0 h2 h3). Qed.
Lemma lem3315305 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315306 {A : Type'} (t : A -> Prop) (x' : A -> A) (x : A) : (term448 A t x' x) = (term405 A t x' x).
Proof. exact (@lem3315305 (term405 A t x' x)). Qed.
Lemma lem3315307 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : term405 A t x' x.
Proof. exact (EQ_MP (@lem3315306 A t x' x) (@lem3315303 A x s t x' h1 h2 h3)). Qed.
Lemma lem3315309 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315310 {A : Type'} (t : A -> Prop) (x' : A -> A) (s : A -> Prop) (_34186 : A) : (term387 A s t x' _34186) = (term454 A t x' s _34186).
Proof. exact (@lem3315309 (term377 A t x' _34186) (s _34186)). Qed.
Lemma lem3315312 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315313 {A : Type'} (t : A -> Prop) (x' : A -> A) (_34186 : A) : (term455 A t x' _34186) = (term405 A t x' _34186).
Proof. exact (@lem3315312 (term405 A t x' _34186)). Qed.
Lemma lem3315314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315315 {A : Type'} (t : A -> Prop) (x' : A -> A) (_34186 : A) : (term456 A t x' _34186) = (term457 A t x' _34186).
Proof. exact (MK_COMB (@lem3315314) (@lem3315313 A t x' _34186)). Qed.
Lemma lem3315316 {A : Type'} (s : A -> Prop) (_34186 : A) : (s _34186) = (s _34186).
Proof. exact (eq_refl (s _34186)). Qed.
Lemma lem3315317 {A : Type'} (t : A -> Prop) (x' : A -> A) (s : A -> Prop) (_34186 : A) : (term454 A t x' s _34186) = (term458 A t x' s _34186).
Proof. exact (MK_COMB (@lem3315315 A t x' _34186) (@lem3315316 A s _34186)). Qed.
Lemma lem3315318 {A : Type'} (t : A -> Prop) (x' : A -> A) (s : A -> Prop) (_34186 : A) : (term387 A s t x' _34186) = (term458 A t x' s _34186).
Proof. exact (TRANS (@lem3315310 A t x' s _34186) (@lem3315317 A t x' s _34186)). Qed.
Lemma lem3315321 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term458 A t x' s _34186.
Proof. exact (EQ_MP (@lem3315318 A t x' s _34186) (@lem3314877 A _34186 x s t x' h1)). Qed.
Lemma lem3315322 {A : Type'} (_34186 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term458 A t x' s _34186.
Proof. exact (@lem3315321 A _34186 x s t x' h1). Qed.
Lemma lem3315323 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term458 A t x' s x.
Proof. exact (@lem3315322 A x x s t x' h1). Qed.
Lemma lem3315326 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : s x.
Proof. exact (@lem3315323 A x s t x' h3 (@lem3315307 A x s t x' h1 h2 h3)). Qed.
Lemma lem3315327 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : t x) (h2 : term264 A x s t x') : term389 A s x.
Proof. exact (fun h0 : term44 A s x => @lem3315326 A x s t x' h0 h1 h2). Qed.
Lemma lem3315329 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315330 {A : Type'} (s : A -> Prop) (x : A) : (term389 A s x) = (s x).
Proof. exact (@lem3315329 (s x)). Qed.
Lemma lem3315331 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : t x) (h2 : term264 A x s t x') : s x.
Proof. exact (EQ_MP (@lem3315330 A s x) (@lem3315327 A x s t x' h1 h2)). Qed.
Lemma lem3315334 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3315336 {A : Type'} (s : A -> Prop) (x : A) : (term44 A s x) = (term391 A s x).
Proof. exact (@lem3315334 (s x)). Qed.
Lemma lem3315339 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) : term391 A s x.
Proof. exact (EQ_MP (@lem3315336 A s x) (@lem3314859 A s x h1)). Qed.
Lemma lem3315342 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (@lem3315339 A s x h1 (@lem3315331 A x s t x' h2 h3)). Qed.
Lemma lem3315343 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : term392.
Proof. exact (fun h0 : ~ False => @lem3315342 A x s t x' h1 h2 h3). Qed.
Lemma lem3315345 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315346 : term392 = False.
Proof. exact (@lem3315345 False). Qed.
Lemma lem3315347 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315346) (@lem3315343 A x s t x' h1 h2 h3)). Qed.
Lemma lem3315383 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3315384 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term389 A s x.
Proof. exact (fun h0 : term44 A s x => @lem3315383 A s x h1). Qed.
Lemma lem3315386 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315387 {A : Type'} (s : A -> Prop) (x : A) : (term389 A s x) = (s x).
Proof. exact (@lem3315386 (s x)). Qed.
Lemma lem3315388 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3315387 A s x) (@lem3315384 A s x h1)). Qed.
Lemma lem3315394 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3315395 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : (term76 A s t _34189) = (term160 A t s _34189).
Proof. exact (@lem3315394 (t _34189) (term44 A s _34189)). Qed.
Lemma lem3315401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3315402 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : (term449 A s t _34189) = (term450 A t s _34189).
Proof. exact (MK_COMB (@lem3315401) (@lem3315395 A t s _34189)). Qed.
Lemma lem3315408 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : (term160 A t s _34189) = (term160 A t s _34189).
Proof. exact (eq_refl (term160 A t s _34189)). Qed.
Lemma lem3315409 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : ((term76 A s t _34189) = (term160 A t s _34189)) = ((term160 A t s _34189) = (term160 A t s _34189)).
Proof. exact (MK_COMB (@lem3315402 A t s _34189) (@lem3315408 A t s _34189)). Qed.
Lemma lem3315411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3315412 (x : Prop) : (x = x) = True.
Proof. exact (@lem3315411 Prop x). Qed.
Lemma lem3315413 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : ((term160 A t s _34189) = (term160 A t s _34189)) = True.
Proof. exact (@lem3315412 (term160 A t s _34189)). Qed.
Lemma lem3315414 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : ((term76 A s t _34189) = (term160 A t s _34189)) = True.
Proof. exact (TRANS (@lem3315409 A t s _34189) (@lem3315413 A t s _34189)). Qed.
Lemma lem3315415 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : True = ((term76 A s t _34189) = (term160 A t s _34189)).
Proof. exact (SYM (@lem3315414 A t s _34189)). Qed.
Lemma lem3315416 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34189 : A) : (term76 A s t _34189) = (term160 A t s _34189).
Proof. exact (EQ_MP (@lem3315415 A t s _34189) (@lem0)). Qed.
Lemma lem3315417 {A : Type'} (_34189 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term160 A t s _34189.
Proof. exact (EQ_MP (@lem3315416 A t s _34189) (@lem3314883 A _34189 x s t x' h1)). Qed.
Lemma lem3315419 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315420 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34189 : A) : (term160 A t s _34189) = (term451 A s t _34189).
Proof. exact (@lem3315419 (term44 A s _34189) (t _34189)). Qed.
Lemma lem3315422 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315423 {A : Type'} (s : A -> Prop) (_34189 : A) : (term107 A s _34189) = (s _34189).
Proof. exact (@lem3315422 (s _34189)). Qed.
Lemma lem3315424 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315425 {A : Type'} (s : A -> Prop) (_34189 : A) : (term452 A s _34189) = (term28 A s _34189).
Proof. exact (MK_COMB (@lem3315424) (@lem3315423 A s _34189)). Qed.
Lemma lem3315426 {A : Type'} (t : A -> Prop) (_34189 : A) : (t _34189) = (t _34189).
Proof. exact (eq_refl (t _34189)). Qed.
Lemma lem3315427 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34189 : A) : (term451 A s t _34189) = (term30 A s t _34189).
Proof. exact (MK_COMB (@lem3315425 A s _34189) (@lem3315426 A t _34189)). Qed.
Lemma lem3315428 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34189 : A) : (term160 A t s _34189) = (term30 A s t _34189).
Proof. exact (TRANS (@lem3315420 A s t _34189) (@lem3315427 A s t _34189)). Qed.
Lemma lem3315431 {A : Type'} (_34189 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term30 A s t _34189.
Proof. exact (EQ_MP (@lem3315428 A s t _34189) (@lem3315417 A _34189 x s t x' h1)). Qed.
Lemma lem3315432 {A : Type'} (_34189 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term30 A s t _34189.
Proof. exact (@lem3315431 A _34189 x s t x' h1). Qed.
Lemma lem3315433 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : term30 A s t x.
Proof. exact (@lem3315432 A x x s t x' h1). Qed.
Lemma lem3315436 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : s x) (h2 : term264 A x s t x') : t x.
Proof. exact (@lem3315433 A x s t x' h2 (@lem3315388 A s x h1)). Qed.
Lemma lem3315437 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : s x) (h2 : term264 A x s t x') : term389 A t x.
Proof. exact (fun h0 : term44 A t x => @lem3315436 A x s t x' h1 h2). Qed.
Lemma lem3315439 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315440 {A : Type'} (t : A -> Prop) (x : A) : (term389 A t x) = (t x).
Proof. exact (@lem3315439 (t x)). Qed.
Lemma lem3315441 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : s x) (h2 : term264 A x s t x') : t x.
Proof. exact (EQ_MP (@lem3315440 A t x) (@lem3315437 A x s t x' h1 h2)). Qed.
Lemma lem3315444 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3315446 {A : Type'} (t : A -> Prop) (x : A) : (term44 A t x) = (term391 A t x).
Proof. exact (@lem3315444 (t x)). Qed.
Lemma lem3315449 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) : term391 A t x.
Proof. exact (EQ_MP (@lem3315446 A t x) (@lem3314885 A t x h1)). Qed.
Lemma lem3315452 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (@lem3315449 A t x h1 (@lem3315441 A x s t x' h2 h3)). Qed.
Lemma lem3315453 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : term392.
Proof. exact (fun h0 : ~ False => @lem3315452 A x s t x' h1 h2 h3). Qed.
Lemma lem3315455 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315456 : term392 = False.
Proof. exact (@lem3315455 False). Qed.
Lemma lem3315457 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315456) (@lem3315453 A x s t x' h1 h2 h3)). Qed.
Lemma lem3315493 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3315494 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term389 A t x.
Proof. exact (fun h0 : term44 A t x => @lem3315493 A t x h1). Qed.
Lemma lem3315496 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315497 {A : Type'} (t : A -> Prop) (x : A) : (term389 A t x) = (t x).
Proof. exact (@lem3315496 (t x)). Qed.
Lemma lem3315498 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3315497 A t x) (@lem3315494 A t x h1)). Qed.
Lemma lem3315501 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3315503 {A : Type'} (t : A -> Prop) (x : A) : (term44 A t x) = (term391 A t x).
Proof. exact (@lem3315501 (t x)). Qed.
Lemma lem3315506 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) : term391 A t x.
Proof. exact (EQ_MP (@lem3315503 A t x) (@lem3314911 A t x h1)). Qed.
Lemma lem3315509 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (@lem3315506 A t x h1 (@lem3315498 A t x h2)). Qed.
Lemma lem3315510 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : term392.
Proof. exact (fun h0 : ~ False => @lem3315509 A t x h1 h2). Qed.
Lemma lem3315512 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315513 : term392 = False.
Proof. exact (@lem3315512 False). Qed.
Lemma lem3315514 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3315513) (@lem3315510 A t x h1 h2)). Qed.
Lemma lem3315542 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term75 A s t x) : s x.
Proof. exact (proj1 (@lem3314484 A s t x h1)). Qed.
Lemma lem3315543 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term75 A s t x) : term389 A s x.
Proof. exact (fun h0 : term44 A s x => @lem3315542 A s t x h1). Qed.
Lemma lem3315545 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315546 {A : Type'} (s : A -> Prop) (x : A) : (term389 A s x) = (s x).
Proof. exact (@lem3315545 (s x)). Qed.
Lemma lem3315547 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term75 A s t x) : s x.
Proof. exact (EQ_MP (@lem3315546 A s x) (@lem3315543 A s t x h1)). Qed.
Lemma lem3315553 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3315554 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : (term76 A s t _34192) = (term160 A t s _34192).
Proof. exact (@lem3315553 (t _34192) (term44 A s _34192)). Qed.
Lemma lem3315560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3315561 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : (term449 A s t _34192) = (term450 A t s _34192).
Proof. exact (MK_COMB (@lem3315560) (@lem3315554 A t s _34192)). Qed.
Lemma lem3315567 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : (term160 A t s _34192) = (term160 A t s _34192).
Proof. exact (eq_refl (term160 A t s _34192)). Qed.
Lemma lem3315568 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : ((term76 A s t _34192) = (term160 A t s _34192)) = ((term160 A t s _34192) = (term160 A t s _34192)).
Proof. exact (MK_COMB (@lem3315561 A t s _34192) (@lem3315567 A t s _34192)). Qed.
Lemma lem3315570 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3315571 (x : Prop) : (x = x) = True.
Proof. exact (@lem3315570 Prop x). Qed.
Lemma lem3315572 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : ((term160 A t s _34192) = (term160 A t s _34192)) = True.
Proof. exact (@lem3315571 (term160 A t s _34192)). Qed.
Lemma lem3315573 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : ((term76 A s t _34192) = (term160 A t s _34192)) = True.
Proof. exact (TRANS (@lem3315568 A t s _34192) (@lem3315572 A t s _34192)). Qed.
Lemma lem3315574 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : True = ((term76 A s t _34192) = (term160 A t s _34192)).
Proof. exact (SYM (@lem3315573 A t s _34192)). Qed.
Lemma lem3315575 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34192 : A) : (term76 A s t _34192) = (term160 A t s _34192).
Proof. exact (EQ_MP (@lem3315574 A t s _34192) (@lem0)). Qed.
Lemma lem3315576 {A : Type'} (_34192 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term160 A t s _34192.
Proof. exact (EQ_MP (@lem3315575 A t s _34192) (@lem3314947 A _34192 x x'' s t h1)). Qed.
Lemma lem3315578 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315579 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34192 : A) : (term160 A t s _34192) = (term451 A s t _34192).
Proof. exact (@lem3315578 (term44 A s _34192) (t _34192)). Qed.
Lemma lem3315581 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315582 {A : Type'} (s : A -> Prop) (_34192 : A) : (term107 A s _34192) = (s _34192).
Proof. exact (@lem3315581 (s _34192)). Qed.
Lemma lem3315583 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315584 {A : Type'} (s : A -> Prop) (_34192 : A) : (term452 A s _34192) = (term28 A s _34192).
Proof. exact (MK_COMB (@lem3315583) (@lem3315582 A s _34192)). Qed.
Lemma lem3315585 {A : Type'} (t : A -> Prop) (_34192 : A) : (t _34192) = (t _34192).
Proof. exact (eq_refl (t _34192)). Qed.
Lemma lem3315586 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34192 : A) : (term451 A s t _34192) = (term30 A s t _34192).
Proof. exact (MK_COMB (@lem3315584 A s _34192) (@lem3315585 A t _34192)). Qed.
Lemma lem3315587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34192 : A) : (term160 A t s _34192) = (term30 A s t _34192).
Proof. exact (TRANS (@lem3315579 A s t _34192) (@lem3315586 A s t _34192)). Qed.
Lemma lem3315590 {A : Type'} (_34192 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term30 A s t _34192.
Proof. exact (EQ_MP (@lem3315587 A s t _34192) (@lem3315576 A _34192 x x'' s t h1)). Qed.
Lemma lem3315591 {A : Type'} (_34192 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term30 A s t _34192.
Proof. exact (@lem3315590 A _34192 x x'' s t h1). Qed.
Lemma lem3315592 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term30 A s t x.
Proof. exact (@lem3315591 A x x x'' s t h1). Qed.
Lemma lem3315595 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term75 A s t x) (h2 : term313 A x x'' s t) : t x.
Proof. exact (@lem3315592 A x x'' s t h2 (@lem3315547 A s t x h1)). Qed.
Lemma lem3315596 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term75 A s t x) (h2 : term313 A x x'' s t) : term389 A t x.
Proof. exact (fun h0 : term44 A t x => @lem3315595 A x x'' s t h1 h2). Qed.
Lemma lem3315598 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315599 {A : Type'} (t : A -> Prop) (x : A) : (term389 A t x) = (t x).
Proof. exact (@lem3315598 (t x)). Qed.
Lemma lem3315600 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term75 A s t x) (h2 : term313 A x x'' s t) : t x.
Proof. exact (EQ_MP (@lem3315599 A t x) (@lem3315596 A x x'' s t h1 h2)). Qed.
Lemma lem3315603 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3315605 {A : Type'} (t : A -> Prop) (x : A) : (term44 A t x) = (term391 A t x).
Proof. exact (@lem3315603 (t x)). Qed.
Lemma lem3315608 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term75 A s t x) : term391 A t x.
Proof. exact (EQ_MP (@lem3315605 A t x) (@lem3314935 A s t x h1)). Qed.
Lemma lem3315611 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term75 A s t x) (h2 : term313 A x x'' s t) : False.
Proof. exact (@lem3315608 A s t x h1 (@lem3315600 A x x'' s t h1 h2)). Qed.
Lemma lem3315612 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term75 A s t x) (h2 : term313 A x x'' s t) : term392.
Proof. exact (fun h0 : ~ False => @lem3315611 A x x'' s t h1 h2). Qed.
Lemma lem3315614 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315615 : term392 = False.
Proof. exact (@lem3315614 False). Qed.
Lemma lem3315616 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term75 A s t x) (h2 : term313 A x x'' s t) : False.
Proof. exact (EQ_MP (@lem3315615) (@lem3315612 A x x'' s t h1 h2)). Qed.
Lemma lem3315644 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3315645 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3315644 A x). Qed.
Lemma lem3315646 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (@lem3315645 A x''). Qed.
Lemma lem3315647 {A : Type'} (x'' : A) : term459 A x''.
Proof. exact (fun h0 : term460 A x'' => @lem3315646 A x''). Qed.
Lemma lem3315649 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315650 {A : Type'} (x'' : A) : (term459 A x'') = (x'' = x'').
Proof. exact (@lem3315649 (x'' = x'')). Qed.
Lemma lem3315651 {A : Type'} (x'' : A) : x'' = x''.
Proof. exact (EQ_MP (@lem3315650 A x'') (@lem3315647 A x'')). Qed.
Lemma lem3315657 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3315658 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : (term388 A x'' t _34193) = (term461 A t _34193 x'').
Proof. exact (@lem3315657 (t _34193) (term381 A _34193 x'')). Qed.
Lemma lem3315666 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3315667 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : (term462 A x'' t _34193) = (term463 A t _34193 x'').
Proof. exact (MK_COMB (@lem3315666) (@lem3315658 A t _34193 x'')). Qed.
Lemma lem3315675 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : (term461 A t _34193 x'') = (term461 A t _34193 x'').
Proof. exact (eq_refl (term461 A t _34193 x'')). Qed.
Lemma lem3315676 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : ((term388 A x'' t _34193) = (term461 A t _34193 x'')) = ((term461 A t _34193 x'') = (term461 A t _34193 x'')).
Proof. exact (MK_COMB (@lem3315667 A t _34193 x'') (@lem3315675 A t _34193 x'')). Qed.
Lemma lem3315678 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3315679 (x : Prop) : (x = x) = True.
Proof. exact (@lem3315678 Prop x). Qed.
Lemma lem3315680 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : ((term461 A t _34193 x'') = (term461 A t _34193 x'')) = True.
Proof. exact (@lem3315679 (term461 A t _34193 x'')). Qed.
Lemma lem3315681 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : ((term388 A x'' t _34193) = (term461 A t _34193 x'')) = True.
Proof. exact (TRANS (@lem3315676 A t _34193 x'') (@lem3315680 A t _34193 x'')). Qed.
Lemma lem3315682 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : True = ((term388 A x'' t _34193) = (term461 A t _34193 x'')).
Proof. exact (SYM (@lem3315681 A t _34193 x'')). Qed.
Lemma lem3315683 {A : Type'} (t : A -> Prop) (_34193 : A) (x'' : A) : (term388 A x'' t _34193) = (term461 A t _34193 x'').
Proof. exact (EQ_MP (@lem3315682 A t _34193 x'') (@lem0)). Qed.
Lemma lem3315684 {A : Type'} (_34193 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term461 A t _34193 x''.
Proof. exact (EQ_MP (@lem3315683 A t _34193 x'') (@lem3314967 A _34193 x x'' s t h1)). Qed.
Lemma lem3315686 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315687 {A : Type'} (x'' : A) (t : A -> Prop) (_34193 : A) : (term461 A t _34193 x'') = (term464 A x'' t _34193).
Proof. exact (@lem3315686 (term381 A _34193 x'') (t _34193)). Qed.
Lemma lem3315689 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315690 {A : Type'} (_34193 : A) (x'' : A) : (term424 A _34193 x'') = (_34193 = x'').
Proof. exact (@lem3315689 (_34193 = x'')). Qed.
Lemma lem3315691 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315692 {A : Type'} (_34193 : A) (x'' : A) : (term465 A _34193 x'') = (term466 A _34193 x'').
Proof. exact (MK_COMB (@lem3315691) (@lem3315690 A _34193 x'')). Qed.
Lemma lem3315693 {A : Type'} (t : A -> Prop) (_34193 : A) : (t _34193) = (t _34193).
Proof. exact (eq_refl (t _34193)). Qed.
Lemma lem3315694 {A : Type'} (x'' : A) (t : A -> Prop) (_34193 : A) : (term464 A x'' t _34193) = (term467 A x'' t _34193).
Proof. exact (MK_COMB (@lem3315692 A _34193 x'') (@lem3315693 A t _34193)). Qed.
Lemma lem3315695 {A : Type'} (x'' : A) (t : A -> Prop) (_34193 : A) : (term461 A t _34193 x'') = (term467 A x'' t _34193).
Proof. exact (TRANS (@lem3315687 A x'' t _34193) (@lem3315694 A x'' t _34193)). Qed.
Lemma lem3315698 {A : Type'} (_34193 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term467 A x'' t _34193.
Proof. exact (EQ_MP (@lem3315695 A x'' t _34193) (@lem3315684 A _34193 x x'' s t h1)). Qed.
Lemma lem3315699 {A : Type'} (_34193 : A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term467 A x'' t _34193.
Proof. exact (@lem3315698 A _34193 x x'' s t h1). Qed.
Lemma lem3315700 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term468 A t x''.
Proof. exact (@lem3315699 A x'' x x'' s t h1). Qed.
Lemma lem3315703 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : t x''.
Proof. exact (@lem3315700 A x x'' s t h1 (@lem3315651 A x'')). Qed.
Lemma lem3315704 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term389 A t x''.
Proof. exact (fun h0 : term44 A t x'' => @lem3315703 A x x'' s t h1). Qed.
Lemma lem3315706 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315707 {A : Type'} (t : A -> Prop) (x'' : A) : (term389 A t x'') = (t x'').
Proof. exact (@lem3315706 (t x'')). Qed.
Lemma lem3315708 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : t x''.
Proof. exact (EQ_MP (@lem3315707 A t x'') (@lem3315704 A x x'' s t h1)). Qed.
Lemma lem3315710 (b : Prop) (a : Prop) : (a \/ b) = (term406 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3315711 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34194 : A) : (term160 A s t _34194) = (term451 A t s _34194).
Proof. exact (@lem3315710 (term44 A t _34194) (s _34194)). Qed.
Lemma lem3315713 (a : Prop) : (term71 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3315714 {A : Type'} (t : A -> Prop) (_34194 : A) : (term107 A t _34194) = (t _34194).
Proof. exact (@lem3315713 (t _34194)). Qed.
Lemma lem3315715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3315716 {A : Type'} (t : A -> Prop) (_34194 : A) : (term452 A t _34194) = (term28 A t _34194).
Proof. exact (MK_COMB (@lem3315715) (@lem3315714 A t _34194)). Qed.
Lemma lem3315717 {A : Type'} (s : A -> Prop) (_34194 : A) : (s _34194) = (s _34194).
Proof. exact (eq_refl (s _34194)). Qed.
Lemma lem3315718 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34194 : A) : (term451 A t s _34194) = (term30 A t s _34194).
Proof. exact (MK_COMB (@lem3315716 A t _34194) (@lem3315717 A s _34194)). Qed.
Lemma lem3315719 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34194 : A) : (term160 A s t _34194) = (term30 A t s _34194).
Proof. exact (TRANS (@lem3315711 A t s _34194) (@lem3315718 A t s _34194)). Qed.
Lemma lem3315722 {A : Type'} (_34194 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term30 A t s _34194.
Proof. exact (EQ_MP (@lem3315719 A t s _34194) (@lem3314955 A _34194 s t h1)). Qed.
Lemma lem3315723 {A : Type'} (_34194 : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term30 A t s _34194.
Proof. exact (@lem3315722 A _34194 s t h1). Qed.
Lemma lem3315724 {A : Type'} (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) : term30 A t s x''.
Proof. exact (@lem3315723 A x'' s t h1). Qed.
Lemma lem3315727 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) (h2 : term313 A x x'' s t) : s x''.
Proof. exact (@lem3315724 A x'' s t h1 (@lem3315708 A x x'' s t h2)). Qed.
Lemma lem3315728 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) (h2 : term313 A x x'' s t) : term389 A s x''.
Proof. exact (fun h0 : term44 A s x'' => @lem3315727 A x x'' s t h1 h2). Qed.
Lemma lem3315730 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315731 {A : Type'} (s : A -> Prop) (x'' : A) : (term389 A s x'') = (s x'').
Proof. exact (@lem3315730 (s x'')). Qed.
Lemma lem3315732 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) (h2 : term313 A x x'' s t) : s x''.
Proof. exact (EQ_MP (@lem3315731 A s x'') (@lem3315728 A x x'' s t h1 h2)). Qed.
Lemma lem3315735 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3315737 {A : Type'} (s : A -> Prop) (x'' : A) : (term44 A s x'') = (term391 A s x'').
Proof. exact (@lem3315735 (s x'')). Qed.
Lemma lem3315740 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : term391 A s x''.
Proof. exact (EQ_MP (@lem3315737 A s x'') (@lem3314949 A x x'' s t h1)). Qed.
Lemma lem3315743 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) (h2 : term313 A x x'' s t) : False.
Proof. exact (@lem3315740 A x x'' s t h2 (@lem3315732 A x x'' s t h1 h2)). Qed.
Lemma lem3315744 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) (h2 : term313 A x x'' s t) : term392.
Proof. exact (fun h0 : ~ False => @lem3315743 A x x'' s t h1 h2). Qed.
Lemma lem3315746 (p : Prop) : (term390 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3315747 : term392 = False.
Proof. exact (@lem3315746 False). Qed.
Lemma lem3315748 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term175 A s t) (h2 : term313 A x x'' s t) : False.
Proof. exact (EQ_MP (@lem3315747) (@lem3315744 A x x'' s t h1 h2)). Qed.
Lemma lem3315749 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3315514 A t x h1 h2) (fun h3 : False => @lem3314913 A t x h2)). Qed.
Lemma lem3315750 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3315749 A t x h1 h2) (@lem3314913 A t x h2)). Qed.
Lemma lem3315751 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : (term44 A t x) = False.
Proof. exact (prop_ext (fun h3 : term44 A t x => @lem3315750 A t x h1 h2) (fun h3 : False => @lem3314911 A t x h1)). Qed.
Lemma lem3315752 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3315751 A t x h1 h2) (@lem3314911 A t x h1)). Qed.
Lemma lem3315753 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3315457 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314887 A s x h2)). Qed.
Lemma lem3315754 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315753 A x s t x' h1 h2 h3) (@lem3314887 A s x h2)). Qed.
Lemma lem3315755 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : (term44 A t x) = False.
Proof. exact (prop_ext (fun h4 : term44 A t x => @lem3315754 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314885 A t x h1)). Qed.
Lemma lem3315756 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315755 A x s t x' h1 h2 h3) (@lem3314885 A t x h1)). Qed.
Lemma lem3315757 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3315347 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314861 A t x h2)). Qed.
Lemma lem3315758 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315757 A x s t x' h1 h2 h3) (@lem3314861 A t x h2)). Qed.
Lemma lem3315759 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : (term44 A s x) = False.
Proof. exact (prop_ext (fun h4 : term44 A s x => @lem3315758 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314859 A s x h1)). Qed.
Lemma lem3315760 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315759 A x s t x' h1 h2 h3) (@lem3314859 A s x h1)). Qed.
Lemma lem3315761 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3315030 A s x h1 h2) (fun h3 : False => @lem3314835 A s x h2)). Qed.
Lemma lem3315762 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3315761 A s x h1 h2) (@lem3314835 A s x h2)). Qed.
Lemma lem3315763 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : (term44 A s x) = False.
Proof. exact (prop_ext (fun h3 : term44 A s x => @lem3315762 A s x h1 h2) (fun h3 : False => @lem3314833 A s x h1)). Qed.
Lemma lem3315764 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3315763 A s x h1 h2) (@lem3314833 A s x h1)). Qed.
Lemma lem3315765 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3315752 A t x h1 h2) (fun h3 : False => @lem3314689 A t x h2)). Qed.
Lemma lem3315766 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3315765 A t x h1 h2) (@lem3314689 A t x h2)). Qed.
Lemma lem3315767 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : (term44 A t x) = False.
Proof. exact (prop_ext (fun h3 : term44 A t x => @lem3315766 A t x h1 h2) (fun h3 : False => @lem3314685 A t x h1)). Qed.
Lemma lem3315768 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3315767 A t x h1 h2) (@lem3314685 A t x h1)). Qed.
Lemma lem3315769 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3315756 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314639 A s x h2)). Qed.
Lemma lem3315770 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315769 A x s t x' h1 h2 h3) (@lem3314639 A s x h2)). Qed.
Lemma lem3315771 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : (term44 A t x) = False.
Proof. exact (prop_ext (fun h4 : term44 A t x => @lem3315770 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314635 A t x h1)). Qed.
Lemma lem3315772 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315771 A x s t x' h1 h2 h3) (@lem3314635 A t x h1)). Qed.
Lemma lem3315773 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3315760 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314589 A t x h2)). Qed.
Lemma lem3315774 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315773 A x s t x' h1 h2 h3) (@lem3314589 A t x h2)). Qed.
Lemma lem3315775 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : (term44 A s x) = False.
Proof. exact (prop_ext (fun h4 : term44 A s x => @lem3315774 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314585 A s x h1)). Qed.
Lemma lem3315776 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315775 A x s t x' h1 h2 h3) (@lem3314585 A s x h1)). Qed.
Lemma lem3315777 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3315764 A s x h1 h2) (fun h3 : False => @lem3314539 A s x h2)). Qed.
Lemma lem3315778 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3315777 A s x h1 h2) (@lem3314539 A s x h2)). Qed.
Lemma lem3315779 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : (term44 A s x) = False.
Proof. exact (prop_ext (fun h3 : term44 A s x => @lem3315778 A s x h1 h2) (fun h3 : False => @lem3314535 A s x h1)). Qed.
Lemma lem3315780 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3315779 A s x h1 h2) (@lem3314535 A s x h1)). Qed.
Lemma lem3315781 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3315768 A t x h1 h2) (fun h3 : False => @lem3314689 A t x h2)). Qed.
Lemma lem3315782 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3315781 A t x h1 h2) (@lem3314689 A t x h2)). Qed.
Lemma lem3315783 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : (term44 A t x) = False.
Proof. exact (prop_ext (fun h3 : term44 A t x => @lem3315782 A t x h1 h2) (fun h3 : False => @lem3314685 A t x h1)). Qed.
Lemma lem3315784 {A : Type'} (t : A -> Prop) (x : A) (h1 : term44 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3315783 A t x h1 h2) (@lem3314685 A t x h1)). Qed.
Lemma lem3315785 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3315772 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314639 A s x h2)). Qed.
Lemma lem3315786 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315785 A x s t x' h1 h2 h3) (@lem3314639 A s x h2)). Qed.
Lemma lem3315787 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : (term44 A t x) = False.
Proof. exact (prop_ext (fun h4 : term44 A t x => @lem3315786 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314635 A t x h1)). Qed.
Lemma lem3315788 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : s x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315787 A x s t x' h1 h2 h3) (@lem3314635 A t x h1)). Qed.
Lemma lem3315789 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3315776 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314589 A t x h2)). Qed.
Lemma lem3315790 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315789 A x s t x' h1 h2 h3) (@lem3314589 A t x h2)). Qed.
Lemma lem3315791 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : (term44 A s x) = False.
Proof. exact (prop_ext (fun h4 : term44 A s x => @lem3315790 A x s t x' h1 h2 h3) (fun h4 : False => @lem3314585 A s x h1)). Qed.
Lemma lem3315792 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : t x) (h3 : term264 A x s t x') : False.
Proof. exact (EQ_MP (@lem3315791 A x s t x' h1 h2 h3) (@lem3314585 A s x h1)). Qed.
Lemma lem3315793 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3315780 A s x h1 h2) (fun h3 : False => @lem3314539 A s x h2)). Qed.
Lemma lem3315794 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3315793 A s x h1 h2) (@lem3314539 A s x h2)). Qed.
Lemma lem3315795 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : (term44 A s x) = False.
Proof. exact (prop_ext (fun h3 : term44 A s x => @lem3315794 A s x h1 h2) (fun h3 : False => @lem3314535 A s x h1)). Qed.
Lemma lem3315796 {A : Type'} (s : A -> Prop) (x : A) (h1 : term44 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3315795 A s x h1 h2) (@lem3314535 A s x h1)). Qed.
Lemma lem3315797 {A : Type'} (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term313 A x x'' s t) : False.
Proof. exact (or_elim (@lem3314481 A x x'' s t h1) (fun h0 : term75 A s t x => @lem3315616 A x x'' s t h0 h1) (fun h0 : term175 A s t => @lem3315748 A x x'' s t h0 h1)). Qed.
Lemma lem3315798 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A t x) (h2 : term264 A x s t x') : False.
Proof. exact (or_elim (@lem3314473 A x s t x' h2) (fun h0 : s x => @lem3315788 A x s t x' h1 h0 h2) (fun h0 : t x => @lem3315784 A t x h1 h0)). Qed.
Lemma lem3315799 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term44 A s x) (h2 : term264 A x s t x') : False.
Proof. exact (or_elim (@lem3314473 A x s t x' h2) (fun h0 : s x => @lem3315796 A s x h1 h0) (fun h0 : t x => @lem3315792 A x s t x' h1 h0 h2)). Qed.
Lemma lem3315800 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A -> A) (h1 : term264 A x s t x') : False.
Proof. exact (or_elim (@lem3314472 A x s t x' h1) (fun h0 : term44 A s x => @lem3315799 A x s t x' h0 h1) (fun h0 : term44 A t x => @lem3315798 A x s t x' h0 h1)). Qed.
Lemma lem3315801 {A : Type'} (x' : A -> A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term365 A x' x x'' s t) : False.
Proof. exact (or_elim (@lem3314465 A x' x x'' s t h1) (fun h0 : term264 A x s t x' => @lem3315800 A x s t x' h0) (fun h0 : term313 A x x'' s t => @lem3315797 A x x'' s t h0)). Qed.
Lemma lem3315802 {A : Type'} (x' : A -> A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term365 A x' x x'' s t) : (term365 A x' x x'' s t) = False.
Proof. exact (prop_ext (fun h2 : term365 A x' x x'' s t => @lem3315801 A x' x x'' s t h1) (fun h2 : False => @lem3314465 A x' x x'' s t h1)). Qed.
Lemma lem3315803 {A : Type'} (x' : A -> A) (x : A) (x'' : A) (s : A -> Prop) (t : A -> Prop) (h1 : term365 A x' x x'' s t) : False.
Proof. exact (EQ_MP (@lem3315802 A x' x x'' s t h1) (@lem3314465 A x' x x'' s t h1)). Qed.
Lemma lem3315804 {A : Type'} (x' : A -> A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term368 A x' x s t) : False.
Proof. exact (ex_elim (@lem3314301 A x' x s t h1) (fun x'' : A => fun h0 : term367 A x' x s t x'' => @lem3315803 A x' x x'' s t h0)). Qed.
Lemma lem3315805 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term370 A x s t) : False.
Proof. exact (ex_elim (@lem3314300 A x s t h1) (fun x' : A -> A => fun h0 : term369 A x s t x' => @lem3315804 A x' x s t h0)). Qed.
Lemma lem3315806 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term73 A s t) : False.
Proof. exact (ex_elim (@lem3314299 A s t h1) (fun x : A => fun h0 : term371 A s t x => @lem3315805 A x s t h0)). Qed.
Lemma lem3315807 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term73 A s t) : (term73 A s t) = False.
Proof. exact (prop_ext (fun h2 : term73 A s t => @lem3315806 A s t h1) (fun h2 : False => @lem3313500 A s t h1)). Qed.
Lemma lem3315808 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term73 A s t) : False.
Proof. exact (EQ_MP (@lem3315807 A s t h1) (@lem3313500 A s t h1)). Qed.
Lemma lem3315809 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term72 A s t.
Proof. exact (fun h0 : term73 A s t => @lem3315808 A s t h0). Qed.
Lemma lem3315810 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term59 A s t).
Proof. exact (EQ_MP (@lem3313499 A s t) (@lem3315809 A s t)). Qed.
Lemma lem3315815 {A : Type'} (s : A -> Prop) : term61 A s.
Proof. exact (fun t : A -> Prop => @lem3315810 A s t). Qed.
Lemma lem3315820 {A : Type'} : term63 A.
Proof. exact (fun s : A -> Prop => @lem3315815 A s). Qed.
Lemma lem3315821 {A : Type'} : term65 A.
Proof. exact (EQ_MP (@lem3313495 A) (@lem3315820 A)). Qed.
Lemma lem3315823 {A : Type'} : term65 A.
Proof. exact (@lem3313305 A (@lem3315821 A)). Qed.
Lemma lem3315824 {A : Type'} (h1 : term66 A) : False.
Proof. exact (@lem3315823 A (@lem3313289 A h1)). Qed.
Lemma lem3315825 {A : Type'} (h1 : term66 A) : (term66 A) = False.
Proof. exact (prop_ext (fun h2 : term66 A => @lem3315824 A h1) (fun h2 : False => @lem3313289 A h1)). Qed.
Lemma lem3315826 {A : Type'} (h1 : term66 A) : False.
Proof. exact (EQ_MP (@lem3315825 A h1) (@lem3313289 A h1)). Qed.
Lemma lem3315827 {A : Type'} : term65 A.
Proof. exact (fun h0 : term66 A => @lem3315826 A h0). Qed.
Lemma lem3315828 {A : Type'} : term63 A.
Proof. exact (EQ_MP (@lem3313288 A) (@lem3315827 A)). Qed.
Lemma lem3315829 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem3313284 A) (@lem3315828 A)). Qed.
Lemma lem3315830 {A : Type'} : term25 A.
Proof. exact (EQ_MP (@lem3313130 A) (@lem3315829 A)). Qed.
