Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DECOMPOSITION_term_abbrevs.
Require Import IN_INSERT_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1831_spec.
Require Import thm1843_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm32_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm82_spec.
Lemma lem3272041 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3272042 {A : Type'} (s : A -> Prop) (x : A) (h1 : term0 A s x) : term0 A s x.
Proof. exact (h1). Qed.
Lemma lem3272043 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term1 A s x t) : term1 A s x t.
Proof. exact (h1). Qed.
Lemma lem3272044 {A : Type'} (x : A) (t : A -> Prop) (h1 : term2 A x t) : term2 A x t.
Proof. exact (h1). Qed.
Lemma lem3272045 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : s = (@INSERT A x t)) : s = (@INSERT A x t).
Proof. exact (h1). Qed.
Lemma lem3272067 {A : Type'} (x : A) : term3 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem3272068 {A : Type'} (x : A) : (term3 A x) = (term4 A x).
Proof. exact (eq_refl (term3 A x)). Qed.
Lemma lem3272069 {A : Type'} (x : A) : term4 A x.
Proof. exact (EQ_MP (@lem3272068 A x) (@lem3272067 A x)). Qed.
Lemma lem3272070 {A : Type'} (x : A) (y : A) : term5 A x y.
Proof. exact (@lem3272069 A x y). Qed.
Lemma lem3272071 {A : Type'} (y : A) (x : A) : (term5 A x y) = (term6 A y x).
Proof. exact (eq_refl (term5 A x y)). Qed.
Lemma lem3272072 {A : Type'} (y : A) (x : A) : term6 A y x.
Proof. exact (EQ_MP (@lem3272071 A y x) (@lem3272070 A x y)). Qed.
Lemma lem3272073 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term7 A y x s.
Proof. exact (@lem3272072 A y x s). Qed.
Lemma lem3272074 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term7 A y x s) = ((term8 A x y s) = (term9 A y x s)).
Proof. exact (eq_refl (term7 A y x s)). Qed.
Lemma lem3272076 {A : Type'} (x : A) (t : A -> Prop) : term10 A x t.
Proof. exact (@lem82 (@IN A x t)). Qed.
Lemma lem3272079 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : s = (@INSERT A x t)) : s = (@INSERT A x t).
Proof. exact (h1). Qed.
Lemma lem3272080 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem3272081 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : s = (@INSERT A x t)) : (@IN A x s) = (term11 A x t).
Proof. exact (MK_COMB (@lem3272080 A x) (@lem3272079 A s x t h1)). Qed.
Lemma lem3272083 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3272074 A y x s) (@lem3272073 A y x s)). Qed.
Lemma lem3272084 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (@lem3272083 A y x s). Qed.
Lemma lem3272085 {A : Type'} (x : A) (t : A -> Prop) : (term11 A x t) = (term12 A x t).
Proof. exact (@lem3272084 A x x t). Qed.
Lemma lem3272089 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3272090 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3272089 A x). Qed.
Lemma lem3272091 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3272092 {A : Type'} (x : A) : (term13 A x) = (or True).
Proof. exact (MK_COMB (@lem3272091) (@lem3272090 A x)). Qed.
Lemma lem3272094 {A : Type'} (x : A) (t : A -> Prop) (h1 : term2 A x t) : (@IN A x t) = False.
Proof. exact (@lem3272076 A x t (@lem3272044 A x t h1)). Qed.
Lemma lem3272095 {A : Type'} (x : A) (t : A -> Prop) (h1 : term2 A x t) : (term12 A x t) = (True \/ False).
Proof. exact (MK_COMB (@lem3272092 A x) (@lem3272094 A x t h1)). Qed.
Lemma lem3272097 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem3272098 : (True \/ False) = True.
Proof. exact (@lem3272097 False). Qed.
Lemma lem3272099 {A : Type'} (x : A) (t : A -> Prop) (h1 : term2 A x t) : (term12 A x t) = True.
Proof. exact (TRANS (@lem3272095 A x t h1) (@lem3272098)). Qed.
Lemma lem3272100 {A : Type'} (x : A) (t : A -> Prop) (h1 : term2 A x t) : (term11 A x t) = True.
Proof. exact (TRANS (@lem3272085 A x t) (@lem3272099 A x t h1)). Qed.
Lemma lem3272101 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) (h2 : s = (@INSERT A x t)) : (@IN A x s) = True.
Proof. exact (TRANS (@lem3272081 A s x t h2) (@lem3272100 A x t h1)). Qed.
Lemma lem3272102 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) (h2 : s = (@INSERT A x t)) : True = (@IN A x s).
Proof. exact (SYM (@lem3272101 A s x t h1 h2)). Qed.
Lemma lem3272103 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) (h2 : s = (@INSERT A x t)) : @IN A x s.
Proof. exact (EQ_MP (@lem3272102 A s x t h1 h2) (@lem0)). Qed.
Lemma lem3272111 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3272112 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term14 A s t).
Proof. exact (@lem3272111 A s t). Qed.
Lemma lem3272113 {A : Type'} (s : A -> Prop) (x : A) : (s = (term15 A s x)) = (term16 A s x).
Proof. exact (@lem3272112 A s (term15 A s x)). Qed.
Lemma lem3272122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3272123 {A : Type'} (s : A -> Prop) (x : A) : (term17 A s x) = (term18 A s x).
Proof. exact (MK_COMB (@lem3272122) (@lem3272113 A s x)). Qed.
Lemma lem3272124 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = (term19 A s x).
Proof. exact (eq_refl (term19 A s x)). Qed.
Lemma lem3272125 {A : Type'} (s : A -> Prop) (x : A) : (term20 A s x) = (term21 A s x).
Proof. exact (MK_COMB (@lem3272123 A s x) (@lem3272124 A s x)). Qed.
Lemma lem3272128 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (term22 A x s).
Proof. exact (eq_refl (term22 A x s)). Qed.
Lemma lem3272129 {A : Type'} (s : A -> Prop) (x : A) : (term23 A s x) = (term24 A s x).
Proof. exact (MK_COMB (@lem3272128 A x s) (@lem3272125 A s x)). Qed.
Lemma lem3272132 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term23 A s x).
Proof. exact (SYM (@lem3272129 A s x)). Qed.
Lemma lem3272136 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3272137 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3272136 A P x). Qed.
Lemma lem3272138 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3272137 A s x). Qed.
Lemma lem3272139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3272140 {A : Type'} (s : A -> Prop) (x : A) : (term22 A x s) = (term25 A s x).
Proof. exact (MK_COMB (@lem3272139) (@lem3272138 A s x)). Qed.
Lemma lem3272150 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3272151 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3272150 A P x). Qed.
Lemma lem3272152 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3272151 A s x'). Qed.
Lemma lem3272153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3272154 {A : Type'} (s : A -> Prop) (x' : A) : (term26 A x' s) = (term27 A s x').
Proof. exact (MK_COMB (@lem3272153) (@lem3272152 A s x')). Qed.
Lemma lem3272156 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3272157 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term8 A x y s) = (term9 A y x s).
Proof. exact (@lem3272156 A y x s). Qed.
Lemma lem3272158 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : (term28 A x' s x) = (term29 A x' s x).
Proof. exact (@lem3272157 A x x' (@DELETE A s x)). Qed.
Lemma lem3272164 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3272165 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (@lem3272164 A s x y). Qed.
Lemma lem3272166 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term30 A x' s x) = (term31 A s x' x).
Proof. exact (@lem3272165 A s x' x). Qed.
Lemma lem3272170 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3272171 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3272170 A P x). Qed.
Lemma lem3272172 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3272171 A s x'). Qed.
Lemma lem3272173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3272174 {A : Type'} (s : A -> Prop) (x' : A) : (term32 A x' s) = (term33 A s x').
Proof. exact (MK_COMB (@lem3272173) (@lem3272172 A s x')). Qed.
Lemma lem3272177 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3272178 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term31 A s x' x) = (term35 A s x' x).
Proof. exact (MK_COMB (@lem3272174 A s x') (@lem3272177 A x' x)). Qed.
Lemma lem3272181 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term30 A x' s x) = (term35 A s x' x).
Proof. exact (TRANS (@lem3272166 A s x' x) (@lem3272178 A s x' x)). Qed.
Lemma lem3272182 {A : Type'} (x' : A) (x : A) : (term36 A x' x) = (term36 A x' x).
Proof. exact (eq_refl (term36 A x' x)). Qed.
Lemma lem3272183 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term29 A x' s x) = (term37 A s x' x).
Proof. exact (MK_COMB (@lem3272182 A x' x) (@lem3272181 A s x' x)). Qed.
Lemma lem3272186 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term28 A x' s x) = (term37 A s x' x).
Proof. exact (TRANS (@lem3272158 A x' s x) (@lem3272183 A s x' x)). Qed.
Lemma lem3272187 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((@IN A x' s) = (term28 A x' s x)) = ((s x') = (term37 A s x' x)).
Proof. exact (MK_COMB (@lem3272154 A s x') (@lem3272186 A s x' x)). Qed.
Lemma lem3272190 {A : Type'} (s : A -> Prop) (x : A) : (term38 A s x) = (term39 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3272187 A s x' x)). Qed.
Lemma lem3272191 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3272192 {A : Type'} (s : A -> Prop) (x : A) : (term16 A s x) = (term40 A s x).
Proof. exact (MK_COMB (@lem3272191 A) (@lem3272190 A s x)). Qed.
Lemma lem3272197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3272198 {A : Type'} (s : A -> Prop) (x : A) : (term18 A s x) = (term41 A s x).
Proof. exact (MK_COMB (@lem3272197) (@lem3272192 A s x)). Qed.
Lemma lem3272200 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3272201 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term30 A x s y) = (term31 A s x y).
Proof. exact (@lem3272200 A s x y). Qed.
Lemma lem3272202 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = (term43 A s x).
Proof. exact (@lem3272201 A s x x). Qed.
Lemma lem3272206 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3272207 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3272206 A P x). Qed.
Lemma lem3272208 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3272207 A s x). Qed.
Lemma lem3272209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3272210 {A : Type'} (s : A -> Prop) (x : A) : (term32 A x s) = (term33 A s x).
Proof. exact (MK_COMB (@lem3272209) (@lem3272208 A s x)). Qed.
Lemma lem3272212 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3272213 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem3272212 A x). Qed.
Lemma lem3272214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3272215 {A : Type'} (x : A) : (term44 A x) = (~ True).
Proof. exact (MK_COMB (@lem3272214) (@lem3272213 A x)). Qed.
Lemma lem3272217 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem3272218 {A : Type'} (x : A) : (term44 A x) = False.
Proof. exact (TRANS (@lem3272215 A x) (@lem3272217)). Qed.
Lemma lem3272219 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = (term45 A s x).
Proof. exact (MK_COMB (@lem3272210 A s x) (@lem3272218 A x)). Qed.
Lemma lem3272221 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem3272222 {A : Type'} (s : A -> Prop) (x : A) : (term45 A s x) = False.
Proof. exact (@lem3272221 (s x)). Qed.
Lemma lem3272223 {A : Type'} (s : A -> Prop) (x : A) : (term43 A s x) = False.
Proof. exact (TRANS (@lem3272219 A s x) (@lem3272222 A s x)). Qed.
Lemma lem3272224 {A : Type'} (s : A -> Prop) (x : A) : (term42 A s x) = False.
Proof. exact (TRANS (@lem3272202 A s x) (@lem3272223 A s x)). Qed.
Lemma lem3272225 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3272226 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = (~ False).
Proof. exact (MK_COMB (@lem3272225) (@lem3272224 A s x)). Qed.
Lemma lem3272228 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem3272229 {A : Type'} (s : A -> Prop) (x : A) : (term19 A s x) = True.
Proof. exact (TRANS (@lem3272226 A s x) (@lem3272228)). Qed.
Lemma lem3272230 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term46 A s x).
Proof. exact (MK_COMB (@lem3272198 A s x) (@lem3272229 A s x)). Qed.
Lemma lem3272232 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem3272233 {A : Type'} (s : A -> Prop) (x : A) : (term46 A s x) = (term40 A s x).
Proof. exact (@lem3272232 (term40 A s x)). Qed.
Lemma lem3272248 {A : Type'} (s : A -> Prop) (x : A) : (term21 A s x) = (term40 A s x).
Proof. exact (TRANS (@lem3272230 A s x) (@lem3272233 A s x)). Qed.
Lemma lem3272249 {A : Type'} (s : A -> Prop) (x : A) : (term24 A s x) = (term47 A s x).
Proof. exact (MK_COMB (@lem3272140 A s x) (@lem3272248 A s x)). Qed.
Lemma lem3272252 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term24 A s x).
Proof. exact (SYM (@lem3272249 A s x)). Qed.
Lemma lem3272254 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3272255 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term49 A s x).
Proof. exact (@lem3272254 (term47 A s x)). Qed.
Lemma lem3272256 {A : Type'} (s : A -> Prop) (x : A) : (term49 A s x) = (term47 A s x).
Proof. exact (SYM (@lem3272255 A s x)). Qed.
Lemma lem3272257 {A : Type'} (s : A -> Prop) (x : A) (h1 : term50 A s x) : term50 A s x.
Proof. exact (h1). Qed.
Lemma lem3272260 {A : Type'} (s : A -> Prop) (x : A) (h1 : term49 A s x) : term49 A s x.
Proof. exact (h1). Qed.
Lemma lem3272261 {A : Type'} (s : A -> Prop) (x : A) : term51 A s x.
Proof. exact (fun h0 : term49 A s x => @lem3272260 A s x h0). Qed.
Lemma lem3272262 {A : Type'} (s : A -> Prop) (x : A) (h1 : term51 A s x) : term51 A s x.
Proof. exact (h1). Qed.
Lemma lem3272263 {A : Type'} (s : A -> Prop) (x : A) (h1 : term49 A s x) : term49 A s x.
Proof. exact (h1). Qed.
Lemma lem3272264 {A : Type'} (s : A -> Prop) (x : A) (h1 : term49 A s x) (h2 : term51 A s x) : term49 A s x.
Proof. exact (@lem3272262 A s x h2 (@lem3272263 A s x h1)). Qed.
Lemma lem3272265 {A : Type'} (s : A -> Prop) (x : A) (h1 : term49 A s x) : term52 A s x.
Proof. exact (fun h0 : term51 A s x => @lem3272264 A s x h1 h0). Qed.
Lemma lem3272266 {A : Type'} (s : A -> Prop) (x : A) (h1 : term51 A s x) : term51 A s x.
Proof. exact (h1). Qed.
Lemma lem3272267 {A : Type'} (s : A -> Prop) (x : A) (h1 : term49 A s x) (h2 : term51 A s x) : term49 A s x.
Proof. exact (@lem3272265 A s x h1 (@lem3272266 A s x h2)). Qed.
Lemma lem3272268 {A : Type'} (s : A -> Prop) (x : A) (h1 : term51 A s x) : term51 A s x.
Proof. exact (fun h0 : term49 A s x => @lem3272267 A s x h0 h1). Qed.
Lemma lem3272269 {A : Type'} (s : A -> Prop) (x : A) : term53 A s x.
Proof. exact (fun h0 : term51 A s x => @lem3272268 A s x h0). Qed.
Lemma lem3272272 {A : Type'} (s : A -> Prop) (x : A) : term51 A s x.
Proof. exact (@lem3272269 A s x (@lem3272261 A s x)). Qed.
Lemma lem3272273 {A : Type'} (s : A -> Prop) (x : A) : term51 A s x.
Proof. exact (@lem3272272 A s x). Qed.
Lemma lem3272283 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3272284 {A : Type'} (s : A -> Prop) (x : A) : (term49 A s x) = (term54 A s x).
Proof. exact (@lem3272283 (term50 A s x)). Qed.
Lemma lem3272286 (t : Prop) : (term55 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3272287 {A : Type'} (s : A -> Prop) (x : A) : (term54 A s x) = (term47 A s x).
Proof. exact (@lem3272286 (term47 A s x)). Qed.
Lemma lem3272290 {A : Type'} (s : A -> Prop) (x : A) : (term49 A s x) = (term47 A s x).
Proof. exact (TRANS (@lem3272284 A s x) (@lem3272287 A s x)). Qed.
Lemma lem3272299 {A : Type'} (x : A) : (term56 A x) = (term57 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3272290 A s x)). Qed.
Lemma lem3272300 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3272301 {A : Type'} (x : A) : (term58 A x) = (term59 A x).
Proof. exact (MK_COMB (@lem3272300 A) (@lem3272299 A x)). Qed.
Lemma lem3272306 {A : Type'} : (term60 A) = (term61 A).
Proof. exact (fun_ext (fun x : A => @lem3272301 A x)). Qed.
Lemma lem3272307 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3272316 {A : Type'} : (term62 A) = (term63 A).
Proof. exact (MK_COMB (@lem3272307 A) (@lem3272306 A)). Qed.
Lemma lem3272331 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term37 A s x' x)) = ((s x') = (term37 A s x' x)).
Proof. exact (eq_refl ((s x') = (term37 A s x' x))). Qed.
Lemma lem3272332 {A : Type'} (s : A -> Prop) (x : A) : (term39 A s x) = (term39 A s x).
Proof. exact (fun_ext (fun x' : A => @lem3272331 A s x' x)). Qed.
Lemma lem3272333 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3272334 {A : Type'} (s : A -> Prop) (x : A) : (term40 A s x) = (term40 A s x).
Proof. exact (MK_COMB (@lem3272333 A) (@lem3272332 A s x)). Qed.
Lemma lem3272337 {A : Type'} (s : A -> Prop) (x : A) : (term25 A s x) = (term25 A s x).
Proof. exact (eq_refl (term25 A s x)). Qed.
Lemma lem3272338 {A : Type'} (s : A -> Prop) (x : A) : (term47 A s x) = (term47 A s x).
Proof. exact (MK_COMB (@lem3272337 A s x) (@lem3272334 A s x)). Qed.
Lemma lem3272339 {A : Type'} (x : A) : (term57 A x) = (term57 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3272338 A s x)). Qed.
Lemma lem3272340 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3272341 {A : Type'} (x : A) : (term59 A x) = (term59 A x).
Proof. exact (MK_COMB (@lem3272340 A) (@lem3272339 A x)). Qed.
Lemma lem3272342 {A : Type'} : (term61 A) = (term61 A).
Proof. exact (fun_ext (fun x : A => @lem3272341 A x)). Qed.
Lemma lem3272343 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3272344 {A : Type'} : (term63 A) = (term63 A).
Proof. exact (MK_COMB (@lem3272343 A) (@lem3272342 A)). Qed.
Lemma lem3272371 {A : Type'} : (term62 A) = (term63 A).
Proof. exact (TRANS (@lem3272316 A) (@lem3272344 A)). Qed.
Lemma lem3272372 {A : Type'} : (term63 A) = (term62 A).
Proof. exact (SYM (@lem3272371 A)). Qed.
Lemma lem3272375 (p : Prop) : p = (term48 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3272376 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : ((s x') = (term37 A s x' x)) = (term64 A s x' x).
Proof. exact (@lem3272375 ((s x') = (term37 A s x' x))). Qed.
Lemma lem3272377 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term64 A s x' x) = ((s x') = (term37 A s x' x)).
Proof. exact (SYM (@lem3272376 A s x' x)). Qed.
Lemma lem3272378 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term65 A s x' x) : term65 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3272384 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3272394 {A : Type'} (x' : A) (x : A) : (term66 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3272396 {A : Type'} (s : A -> Prop) (x' : A) : (term67 A s x') = (term67 A s x').
Proof. exact (eq_refl (term67 A s x')). Qed.
Lemma lem3272397 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term68 A s x' x) = (term69 A s x' x).
Proof. exact (MK_COMB (@lem3272396 A s x') (@lem3272394 A x' x)). Qed.
Lemma lem3272398 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term70 A s x' x) = (term68 A s x' x).
Proof. exact (@lem17045 (s x') (term34 A x' x)). Qed.
Lemma lem3272399 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term70 A s x' x) = (term69 A s x' x).
Proof. exact (TRANS (@lem3272398 A s x' x) (@lem3272397 A s x' x)). Qed.
Lemma lem3272404 {A : Type'} (x' : A) (x : A) : (term71 A x' x) = (term71 A x' x).
Proof. exact (eq_refl (term71 A x' x)). Qed.
Lemma lem3272405 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term72 A s x' x) = (term73 A s x' x).
Proof. exact (MK_COMB (@lem3272404 A x' x) (@lem3272399 A s x' x)). Qed.
Lemma lem3272406 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term74 A s x' x) = (term72 A s x' x).
Proof. exact (@lem17160 (x' = x) (term35 A s x' x)). Qed.
Lemma lem3272407 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term74 A s x' x) = (term73 A s x' x).
Proof. exact (TRANS (@lem3272406 A s x' x) (@lem3272405 A s x' x)). Qed.
Lemma lem3272413 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term75 A s x' x) = (term75 A s x' x).
Proof. exact (eq_refl (term75 A s x' x)). Qed.
Lemma lem3272415 {A : Type'} (s : A -> Prop) (x' : A) : (term33 A s x') = (term33 A s x').
Proof. exact (eq_refl (term33 A s x')). Qed.
Lemma lem3272416 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term76 A s x' x) = (term77 A s x' x).
Proof. exact (MK_COMB (@lem3272415 A s x') (@lem3272407 A s x' x)). Qed.
Lemma lem3272417 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3272418 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term78 A s x' x) = (term79 A s x' x).
Proof. exact (MK_COMB (@lem3272417) (@lem3272416 A s x' x)). Qed.
Lemma lem3272419 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term80 A s x' x) = (term81 A s x' x).
Proof. exact (MK_COMB (@lem3272418 A s x' x) (@lem3272413 A s x' x)). Qed.
Lemma lem3272420 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term65 A s x' x) = (term80 A s x' x).
Proof. exact (@lem17646 (s x') (term37 A s x' x)). Qed.
Lemma lem3272425 {A : Type'} (s : A -> Prop) (x' : A) (x : A) : (term65 A s x' x) = (term81 A s x' x).
Proof. exact (TRANS (@lem3272420 A s x' x) (@lem3272419 A s x' x)). Qed.
Lemma lem3272430 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3272492 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term65 A s x' x) : term81 A s x' x.
Proof. exact (EQ_MP (@lem3272425 A s x' x) (@lem3272378 A s x' x h1)). Qed.
Lemma lem3272493 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : term77 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3272494 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) : term75 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3272495 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : term73 A s x' x.
Proof. exact (proj2 (@lem3272493 A s x' x h1)). Qed.
Lemma lem3272497 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : term69 A s x' x.
Proof. exact (proj2 (@lem3272495 A s x' x h1)). Qed.
Lemma lem3272501 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) : term37 A s x' x.
Proof. exact (proj2 (@lem3272494 A s x' x h1)). Qed.
Lemma lem3272504 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : term35 A s x' x.
Proof. exact (h1). Qed.
Lemma lem3272522 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term82 A s x') : term82 A s x'.
Proof. exact (h1). Qed.
Lemma lem3272538 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3272542 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3272550 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3272574 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term82 A s x') : term82 A s x'.
Proof. exact (h1). Qed.
Lemma lem3272580 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : term34 A x' x.
Proof. exact (proj1 (@lem3272495 A s x' x h1)). Qed.
Lemma lem3272582 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3272584 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3272586 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) : term82 A s x'.
Proof. exact (proj1 (@lem3272494 A s x' x h1)). Qed.
Lemma lem3272588 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3272592 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) : term82 A s x'.
Proof. exact (proj1 (@lem3272494 A s x' x h1)). Qed.
Lemma lem3272638 {A : Type'} (x : A) : (term83 A x) = (term83 A x).
Proof. exact (eq_refl (term83 A x)). Qed.
Lemma lem3272639 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term84 A x x') = (term85 A x).
Proof. exact (MK_COMB (@lem3272638 A x) (@lem3272582 A x' x h1)). Qed.
Lemma lem3272640 {A : Type'} (x : A) : (term85 A x) = (term44 A x).
Proof. exact (eq_refl (term85 A x)). Qed.
Lemma lem3272641 {A : Type'} (x : A) (x' : A) : (term86 A x x') = (term86 A x x').
Proof. exact (eq_refl (term86 A x x')). Qed.
Lemma lem3272642 {A : Type'} (x' : A) (x : A) : ((term84 A x x') = (term85 A x)) = ((term84 A x x') = (term44 A x)).
Proof. exact (MK_COMB (@lem3272641 A x x') (@lem3272640 A x)). Qed.
Lemma lem3272643 {A : Type'} (x' : A) (x : A) : (term84 A x x') = (term34 A x' x).
Proof. exact (eq_refl (term84 A x x')). Qed.
Lemma lem3272644 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3272645 {A : Type'} (x' : A) (x : A) : (term86 A x x') = (term87 A x' x).
Proof. exact (MK_COMB (@lem3272644) (@lem3272643 A x' x)). Qed.
Lemma lem3272646 {A : Type'} (x : A) : (term44 A x) = (term44 A x).
Proof. exact (eq_refl (term44 A x)). Qed.
Lemma lem3272647 {A : Type'} (x' : A) (x : A) : ((term84 A x x') = (term44 A x)) = ((term34 A x' x) = (term44 A x)).
Proof. exact (MK_COMB (@lem3272645 A x' x) (@lem3272646 A x)). Qed.
Lemma lem3272648 {A : Type'} (x' : A) (x : A) : ((term84 A x x') = (term85 A x)) = ((term34 A x' x) = (term44 A x)).
Proof. exact (TRANS (@lem3272642 A x' x) (@lem3272647 A x' x)). Qed.
Lemma lem3272649 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term34 A x' x) = (term44 A x).
Proof. exact (EQ_MP (@lem3272648 A x' x) (@lem3272639 A x' x h1)). Qed.
Lemma lem3272650 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : term44 A x.
Proof. exact (EQ_MP (@lem3272649 A x' x h2) (@lem3272580 A s x' x h1)). Qed.
Lemma lem3272678 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3272679 {A : Type'} (s : A -> Prop) : (term88 A s) = (term88 A s).
Proof. exact (eq_refl (term88 A s)). Qed.
Lemma lem3272680 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term89 A s x') = (term89 A s x).
Proof. exact (MK_COMB (@lem3272679 A s) (@lem3272588 A x' x h1)). Qed.
Lemma lem3272681 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term82 A s x).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem3272682 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (term90 A s x').
Proof. exact (eq_refl (term90 A s x')). Qed.
Lemma lem3272683 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term89 A s x') = (term89 A s x)) = ((term89 A s x') = (term82 A s x)).
Proof. exact (MK_COMB (@lem3272682 A s x') (@lem3272681 A s x)). Qed.
Lemma lem3272684 {A : Type'} (s : A -> Prop) (x' : A) : (term89 A s x') = (term82 A s x').
Proof. exact (eq_refl (term89 A s x')). Qed.
Lemma lem3272685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3272686 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (term91 A s x').
Proof. exact (MK_COMB (@lem3272685) (@lem3272684 A s x')). Qed.
Lemma lem3272687 {A : Type'} (s : A -> Prop) (x : A) : (term82 A s x) = (term82 A s x).
Proof. exact (eq_refl (term82 A s x)). Qed.
Lemma lem3272688 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term89 A s x') = (term82 A s x)) = ((term82 A s x') = (term82 A s x)).
Proof. exact (MK_COMB (@lem3272686 A s x') (@lem3272687 A s x)). Qed.
Lemma lem3272689 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term89 A s x') = (term89 A s x)) = ((term82 A s x') = (term82 A s x)).
Proof. exact (TRANS (@lem3272683 A x' s x) (@lem3272688 A x' s x)). Qed.
Lemma lem3272690 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term82 A s x') = (term82 A s x).
Proof. exact (EQ_MP (@lem3272689 A x' s x) (@lem3272680 A s x' x h1)). Qed.
Lemma lem3272691 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) (h2 : x' = x) : term82 A s x.
Proof. exact (EQ_MP (@lem3272690 A s x' x h2) (@lem3272586 A s x' x h1)). Qed.
Lemma lem3272707 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : s x'.
Proof. exact (proj1 (@lem3272493 A s x' x h1)). Qed.
Lemma lem3272708 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : term92 A s x'.
Proof. exact (fun h0 : term82 A s x' => @lem3272707 A s x' x h1). Qed.
Lemma lem3272710 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272711 {A : Type'} (s : A -> Prop) (x' : A) : (term92 A s x') = (s x').
Proof. exact (@lem3272710 (s x')). Qed.
Lemma lem3272712 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3272711 A s x') (@lem3272708 A s x' x h1)). Qed.
Lemma lem3272715 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3272717 {A : Type'} (s : A -> Prop) (x' : A) : (term82 A s x') = (term94 A s x').
Proof. exact (@lem3272715 (s x')). Qed.
Lemma lem3272720 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term82 A s x') : term94 A s x'.
Proof. exact (EQ_MP (@lem3272717 A s x') (@lem3272574 A s x' h1)). Qed.
Lemma lem3272723 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : False.
Proof. exact (@lem3272720 A s x' h1 (@lem3272712 A s x' x h2)). Qed.
Lemma lem3272724 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : term95.
Proof. exact (fun h0 : ~ False => @lem3272723 A s x' x h1 h2). Qed.
Lemma lem3272726 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272727 : term95 = False.
Proof. exact (@lem3272726 False). Qed.
Lemma lem3272728 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : False.
Proof. exact (EQ_MP (@lem3272727) (@lem3272724 A s x' x h1 h2)). Qed.
Lemma lem3272744 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3272745 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3272744 A x). Qed.
Lemma lem3272746 {A : Type'} (x : A) : term96 A x.
Proof. exact (fun h0 : term44 A x => @lem3272745 A x). Qed.
Lemma lem3272748 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272749 {A : Type'} (x : A) : (term96 A x) = (x = x).
Proof. exact (@lem3272748 (x = x)). Qed.
Lemma lem3272750 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3272749 A x) (@lem3272746 A x)). Qed.
Lemma lem3272753 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3272755 {A : Type'} (x : A) : (term44 A x) = (term97 A x).
Proof. exact (@lem3272753 (x = x)). Qed.
Lemma lem3272758 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : term97 A x.
Proof. exact (EQ_MP (@lem3272755 A x) (@lem3272650 A s x' x h1 h2)). Qed.
Lemma lem3272761 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : False.
Proof. exact (@lem3272758 A s x' x h1 h2 (@lem3272750 A x)). Qed.
Lemma lem3272762 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : term95.
Proof. exact (fun h0 : ~ False => @lem3272761 A s x' x h1 h2). Qed.
Lemma lem3272764 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272765 : term95 = False.
Proof. exact (@lem3272764 False). Qed.
Lemma lem3272768 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3272769 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term92 A s x.
Proof. exact (fun h0 : term82 A s x => @lem3272768 A s x h1). Qed.
Lemma lem3272771 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272772 {A : Type'} (s : A -> Prop) (x : A) : (term92 A s x) = (s x).
Proof. exact (@lem3272771 (s x)). Qed.
Lemma lem3272773 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3272772 A s x) (@lem3272769 A s x h1)). Qed.
Lemma lem3272776 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3272778 {A : Type'} (s : A -> Prop) (x : A) : (term82 A s x) = (term94 A s x).
Proof. exact (@lem3272776 (s x)). Qed.
Lemma lem3272781 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) (h2 : x' = x) : term94 A s x.
Proof. exact (EQ_MP (@lem3272778 A s x) (@lem3272691 A s x' x h1 h2)). Qed.
Lemma lem3272784 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (@lem3272781 A s x' x h2 h3 (@lem3272773 A s x h1)). Qed.
Lemma lem3272785 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : term95.
Proof. exact (fun h0 : ~ False => @lem3272784 A s x' x h1 h2 h3). Qed.
Lemma lem3272787 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272788 : term95 = False.
Proof. exact (@lem3272787 False). Qed.
Lemma lem3272789 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272788) (@lem3272785 A s x' x h1 h2 h3)). Qed.
Lemma lem3272805 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : s x'.
Proof. exact (proj1 (@lem3272504 A s x' x h1)). Qed.
Lemma lem3272806 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : term92 A s x'.
Proof. exact (fun h0 : term82 A s x' => @lem3272805 A s x' x h1). Qed.
Lemma lem3272808 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272809 {A : Type'} (s : A -> Prop) (x' : A) : (term92 A s x') = (s x').
Proof. exact (@lem3272808 (s x')). Qed.
Lemma lem3272810 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term35 A s x' x) : s x'.
Proof. exact (EQ_MP (@lem3272809 A s x') (@lem3272806 A s x' x h1)). Qed.
Lemma lem3272813 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3272815 {A : Type'} (s : A -> Prop) (x' : A) : (term82 A s x') = (term94 A s x').
Proof. exact (@lem3272813 (s x')). Qed.
Lemma lem3272818 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) : term94 A s x'.
Proof. exact (EQ_MP (@lem3272815 A s x') (@lem3272592 A s x' x h1)). Qed.
Lemma lem3272821 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) (h2 : term35 A s x' x) : False.
Proof. exact (@lem3272818 A s x' x h1 (@lem3272810 A s x' x h2)). Qed.
Lemma lem3272822 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) (h2 : term35 A s x' x) : term95.
Proof. exact (fun h0 : ~ False => @lem3272821 A s x' x h1 h2). Qed.
Lemma lem3272824 (p : Prop) : (term93 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3272825 : term95 = False.
Proof. exact (@lem3272824 False). Qed.
Lemma lem3272826 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term75 A s x' x) (h2 : term35 A s x' x) : False.
Proof. exact (EQ_MP (@lem3272825) (@lem3272822 A s x' x h1 h2)). Qed.
Lemma lem3272827 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3272789 A s x' x h1 h2 h3) (fun h4 : False => @lem3272678 A s x h1)). Qed.
Lemma lem3272829 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272827 A s x' x h1 h2 h3) (@lem3272678 A s x h1)). Qed.
Lemma lem3272830 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272765) (@lem3272762 A s x' x h1 h2)). Qed.
Lemma lem3272831 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3272829 A s x' x h1 h2 h3) (fun h4 : False => @lem3272588 A x' x h3)). Qed.
Lemma lem3272832 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272831 A s x' x h1 h2 h3) (@lem3272588 A x' x h3)). Qed.
Lemma lem3272833 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3272832 A s x' x h1 h2 h3) (fun h4 : False => @lem3272584 A s x h1)). Qed.
Lemma lem3272834 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272833 A s x' x h1 h2 h3) (@lem3272584 A s x h1)). Qed.
Lemma lem3272835 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3272830 A s x' x h1 h2) (fun h3 : False => @lem3272582 A x' x h2)). Qed.
Lemma lem3272836 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272835 A s x' x h1 h2) (@lem3272582 A x' x h2)). Qed.
Lemma lem3272837 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : (term82 A s x') = False.
Proof. exact (prop_ext (fun h3 : term82 A s x' => @lem3272728 A s x' x h1 h2) (fun h3 : False => @lem3272574 A s x' h1)). Qed.
Lemma lem3272838 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : False.
Proof. exact (EQ_MP (@lem3272837 A s x' x h1 h2) (@lem3272574 A s x' h1)). Qed.
Lemma lem3272839 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3272834 A s x' x h1 h2 h3) (fun h4 : False => @lem3272550 A x' x h3)). Qed.
Lemma lem3272840 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272839 A s x' x h1 h2 h3) (@lem3272550 A x' x h3)). Qed.
Lemma lem3272841 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3272840 A s x' x h1 h2 h3) (fun h4 : False => @lem3272542 A s x h1)). Qed.
Lemma lem3272842 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272841 A s x' x h1 h2 h3) (@lem3272542 A s x h1)). Qed.
Lemma lem3272843 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3272836 A s x' x h1 h2) (fun h3 : False => @lem3272538 A x' x h2)). Qed.
Lemma lem3272844 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272843 A s x' x h1 h2) (@lem3272538 A x' x h2)). Qed.
Lemma lem3272845 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : (term82 A s x') = False.
Proof. exact (prop_ext (fun h3 : term82 A s x' => @lem3272838 A s x' x h1 h2) (fun h3 : False => @lem3272522 A s x' h1)). Qed.
Lemma lem3272846 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : False.
Proof. exact (EQ_MP (@lem3272845 A s x' x h1 h2) (@lem3272522 A s x' h1)). Qed.
Lemma lem3272847 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3272842 A s x' x h1 h2 h3) (fun h4 : False => @lem3272550 A x' x h3)). Qed.
Lemma lem3272848 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272847 A s x' x h1 h2 h3) (@lem3272550 A x' x h3)). Qed.
Lemma lem3272849 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3272848 A s x' x h1 h2 h3) (fun h4 : False => @lem3272542 A s x h1)). Qed.
Lemma lem3272850 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272849 A s x' x h1 h2 h3) (@lem3272542 A s x h1)). Qed.
Lemma lem3272851 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3272844 A s x' x h1 h2) (fun h3 : False => @lem3272538 A x' x h2)). Qed.
Lemma lem3272852 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3272851 A s x' x h1 h2) (@lem3272538 A x' x h2)). Qed.
Lemma lem3272853 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : (term82 A s x') = False.
Proof. exact (prop_ext (fun h3 : term82 A s x' => @lem3272846 A s x' x h1 h2) (fun h3 : False => @lem3272522 A s x' h1)). Qed.
Lemma lem3272854 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term82 A s x') (h2 : term77 A s x' x) : False.
Proof. exact (EQ_MP (@lem3272853 A s x' x h1 h2) (@lem3272522 A s x' h1)). Qed.
Lemma lem3272855 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : s x) (h2 : term75 A s x' x) : False.
Proof. exact (or_elim (@lem3272501 A s x' x h2) (fun h0 : x' = x => @lem3272850 A s x' x h1 h2 h0) (fun h0 : term35 A s x' x => @lem3272826 A s x' x h2 h0)). Qed.
Lemma lem3272856 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term77 A s x' x) : False.
Proof. exact (or_elim (@lem3272497 A s x' x h1) (fun h0 : term82 A s x' => @lem3272854 A s x' x h0 h1) (fun h0 : x' = x => @lem3272852 A s x' x h1 h0)). Qed.
Lemma lem3272857 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term65 A s x' x) (h2 : s x) : False.
Proof. exact (or_elim (@lem3272492 A s x' x h1) (fun h0 : term77 A s x' x => @lem3272856 A s x' x h0) (fun h0 : term75 A s x' x => @lem3272855 A s x' x h2 h0)). Qed.
Lemma lem3272858 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term65 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3272857 A x' s x h1 h2) (fun h3 : False => @lem3272430 A s x h2)). Qed.
Lemma lem3272859 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term65 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3272858 A x' s x h1 h2) (@lem3272430 A s x h2)). Qed.
Lemma lem3272860 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term65 A s x' x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3272859 A x' s x h1 h2) (fun h3 : False => @lem3272384 A s x h2)). Qed.
Lemma lem3272861 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term65 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3272860 A x' s x h1 h2) (@lem3272384 A s x h2)). Qed.
Lemma lem3272862 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term65 A s x' x) (h2 : s x) : (term65 A s x' x) = False.
Proof. exact (prop_ext (fun h3 : term65 A s x' x => @lem3272861 A x' s x h1 h2) (fun h3 : False => @lem3272378 A s x' x h1)). Qed.
Lemma lem3272863 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : term65 A s x' x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3272862 A x' s x h1 h2) (@lem3272378 A s x' x h1)). Qed.
Lemma lem3272864 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : term64 A s x' x.
Proof. exact (fun h0 : term65 A s x' x => @lem3272863 A x' s x h0 h1). Qed.
Lemma lem3272865 {A : Type'} (x' : A) (s : A -> Prop) (x : A) (h1 : s x) : (s x') = (term37 A s x' x).
Proof. exact (EQ_MP (@lem3272377 A s x' x) (@lem3272864 A x' s x h1)). Qed.
Lemma lem3272870 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term40 A s x.
Proof. exact (fun x' : A => @lem3272865 A x' s x h1). Qed.
Lemma lem3272871 {A : Type'} (s : A -> Prop) (x : A) : term47 A s x.
Proof. exact (fun h0 : s x => @lem3272870 A s x h0). Qed.
Lemma lem3272876 {A : Type'} (x : A) : term59 A x.
Proof. exact (fun s : A -> Prop => @lem3272871 A s x). Qed.
Lemma lem3272881 {A : Type'} : term63 A.
Proof. exact (fun x : A => @lem3272876 A x). Qed.
Lemma lem3272882 {A : Type'} : term62 A.
Proof. exact (EQ_MP (@lem3272372 A) (@lem3272881 A)). Qed.
Lemma lem3272883 {A : Type'} (x : A) : term98 A x.
Proof. exact (@lem3272882 A x). Qed.
Lemma lem3272884 {A : Type'} (x : A) : (term98 A x) = (term58 A x).
Proof. exact (eq_refl (term98 A x)). Qed.
Lemma lem3272885 {A : Type'} (x : A) : term58 A x.
Proof. exact (EQ_MP (@lem3272884 A x) (@lem3272883 A x)). Qed.
Lemma lem3272886 {A : Type'} (x : A) (s : A -> Prop) : term99 A x s.
Proof. exact (@lem3272885 A x s). Qed.
Lemma lem3272887 {A : Type'} (s : A -> Prop) (x : A) : (term99 A x s) = (term49 A s x).
Proof. exact (eq_refl (term99 A x s)). Qed.
Lemma lem3272888 {A : Type'} (s : A -> Prop) (x : A) : term49 A s x.
Proof. exact (EQ_MP (@lem3272887 A s x) (@lem3272886 A x s)). Qed.
Lemma lem3272890 {A : Type'} (s : A -> Prop) (x : A) : term49 A s x.
Proof. exact (@lem3272273 A s x (@lem3272888 A s x)). Qed.
Lemma lem3272891 {A : Type'} (s : A -> Prop) (x : A) (h1 : term50 A s x) : False.
Proof. exact (@lem3272890 A s x (@lem3272257 A s x h1)). Qed.
Lemma lem3272892 {A : Type'} (s : A -> Prop) (x : A) (h1 : term50 A s x) : (term50 A s x) = False.
Proof. exact (prop_ext (fun h2 : term50 A s x => @lem3272891 A s x h1) (fun h2 : False => @lem3272257 A s x h1)). Qed.
Lemma lem3272893 {A : Type'} (s : A -> Prop) (x : A) (h1 : term50 A s x) : False.
Proof. exact (EQ_MP (@lem3272892 A s x h1) (@lem3272257 A s x h1)). Qed.
Lemma lem3272894 {A : Type'} (s : A -> Prop) (x : A) : term49 A s x.
Proof. exact (fun h0 : term50 A s x => @lem3272893 A s x h0). Qed.
Lemma lem3272895 {A : Type'} (s : A -> Prop) (x : A) : term47 A s x.
Proof. exact (EQ_MP (@lem3272256 A s x) (@lem3272894 A s x)). Qed.
Lemma lem3272896 {A : Type'} (s : A -> Prop) (x : A) : term24 A s x.
Proof. exact (EQ_MP (@lem3272252 A s x) (@lem3272895 A s x)). Qed.
Lemma lem3272897 {A : Type'} (s : A -> Prop) (x : A) : term23 A s x.
Proof. exact (EQ_MP (@lem3272132 A s x) (@lem3272896 A s x)). Qed.
Lemma lem3272898 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term20 A s x.
Proof. exact (@lem3272897 A s x (@lem3272041 A x s h1)). Qed.
Lemma lem3272900 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term0 A s x.
Proof. exact (ex_intro (term100 A s x) (@DELETE A s x) (@lem3272898 A x s h1)). Qed.
Lemma lem3272901 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term1 A s x t) : term2 A x t.
Proof. exact (proj2 (@lem3272043 A s x t h1)). Qed.
Lemma lem3272902 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term1 A s x t) : s = (@INSERT A x t).
Proof. exact (proj1 (@lem3272043 A s x t h1)). Qed.
Lemma lem3272903 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) (h2 : s = (@INSERT A x t)) : (term2 A x t) = (@IN A x s).
Proof. exact (prop_ext (fun h3 : term2 A x t => @lem3272103 A s x t h1 h2) (fun h3 : @IN A x s => @lem3272044 A x t h1)). Qed.
Lemma lem3272904 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) (h2 : s = (@INSERT A x t)) : @IN A x s.
Proof. exact (EQ_MP (@lem3272903 A s x t h1 h2) (@lem3272044 A x t h1)). Qed.
Lemma lem3272905 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) (h2 : s = (@INSERT A x t)) : (s = (@INSERT A x t)) = (@IN A x s).
Proof. exact (prop_ext (fun h3 : s = (@INSERT A x t) => @lem3272904 A s x t h1 h2) (fun h3 : @IN A x s => @lem3272045 A s x t h2)). Qed.
Lemma lem3272906 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term2 A x t) (h2 : s = (@INSERT A x t)) : @IN A x s.
Proof. exact (EQ_MP (@lem3272905 A s x t h1 h2) (@lem3272045 A s x t h2)). Qed.
Lemma lem3272907 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term1 A s x t) (h2 : s = (@INSERT A x t)) : (term2 A x t) = (@IN A x s).
Proof. exact (prop_ext (fun h3 : term2 A x t => @lem3272906 A s x t h3 h2) (fun h3 : @IN A x s => @lem3272901 A s x t h1)). Qed.
Lemma lem3272908 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term1 A s x t) (h2 : s = (@INSERT A x t)) : @IN A x s.
Proof. exact (EQ_MP (@lem3272907 A s x t h1 h2) (@lem3272901 A s x t h1)). Qed.
Lemma lem3272909 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term1 A s x t) : (s = (@INSERT A x t)) = (@IN A x s).
Proof. exact (prop_ext (fun h2 : s = (@INSERT A x t) => @lem3272908 A s x t h1 h2) (fun h2 : @IN A x s => @lem3272902 A s x t h1)). Qed.
Lemma lem3272910 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term1 A s x t) : @IN A x s.
Proof. exact (EQ_MP (@lem3272909 A s x t h1) (@lem3272902 A s x t h1)). Qed.
Lemma lem3272911 {A : Type'} (s : A -> Prop) (x : A) (h1 : term0 A s x) : @IN A x s.
Proof. exact (ex_elim (@lem3272042 A s x h1) (fun t : A -> Prop => fun h0 : term100 A s x t => @lem3272910 A s x t h0)). Qed.
Lemma lem3272912 {A : Type'} (x : A) (s : A -> Prop) : term101 A x s.
Proof. exact (fun h0 : term0 A s x => @lem3272911 A s x h0). Qed.
Lemma lem3272913 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : (@IN A x s) = (term0 A s x).
Proof. exact (prop_ext (fun h2 : @IN A x s => @lem3272900 A x s h1) (fun h2 : term0 A s x => @lem3272041 A x s h1)). Qed.
Lemma lem3272914 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term0 A s x.
Proof. exact (EQ_MP (@lem3272913 A x s h1) (@lem3272041 A x s h1)). Qed.
Lemma lem3272915 {A : Type'} (s : A -> Prop) (x : A) : term102 A s x.
Proof. exact (fun h0 : @IN A x s => @lem3272914 A x s h0). Qed.
Lemma lem3272916 {A : Type'} (x : A) (s : A -> Prop) : term103 A x s.
Proof. exact (conj (@lem3272915 A s x) (@lem3272912 A x s)). Qed.
Lemma lem3272917 {A : Type'} (s : A -> Prop) (x : A) : (term103 A x s) = ((@IN A x s) = (term0 A s x)).
Proof. exact (@lem32 (@IN A x s) (term0 A s x)). Qed.
Lemma lem3272918 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (term0 A s x).
Proof. exact (EQ_MP (@lem3272917 A s x) (@lem3272916 A x s)). Qed.
Lemma lem3272923 {A : Type'} (s : A -> Prop) : term104 A s.
Proof. exact (fun x : A => @lem3272918 A s x). Qed.
Lemma lem3272928 {A : Type'} : term105 A.
Proof. exact (fun s : A -> Prop => @lem3272923 A s). Qed.
