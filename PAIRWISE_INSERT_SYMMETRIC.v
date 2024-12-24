Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_INSERT_SYMMETRIC_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import PAIRWISE_INSERT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
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
Lemma lem4807108 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4807109 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4807110 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4807109 t1) (@lem4807108 t1)). Qed.
Lemma lem4807111 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4807110 t1 t2). Qed.
Lemma lem4807112 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4807113 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4807112 t1 t2) (@lem4807111 t1 t2)). Qed.
Lemma lem4807114 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4807113 t1 t2 t3). Qed.
Lemma lem4807115 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4807116 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4807115 t1 t2 t3) (@lem4807114 t1 t2 t3)). Qed.
Lemma lem4807117 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4807116 t1 t2 t3)). Qed.
Lemma lem4807118 {_110698 : Type'} (r : type1402 _110698) : term7 _110698 r.
Proof. exact (@lem4807107 _110698 r). Qed.
Lemma lem4807119 {_110698 : Type'} (r : type1402 _110698) : (term7 _110698 r) = (term8 _110698 r).
Proof. exact (eq_refl (term7 _110698 r)). Qed.
Lemma lem4807120 {_110698 : Type'} (r : type1402 _110698) : term8 _110698 r.
Proof. exact (EQ_MP (@lem4807119 _110698 r) (@lem4807118 _110698 r)). Qed.
Lemma lem4807121 {_110698 : Type'} (r : type1402 _110698) (x : _110698) : term9 _110698 r x.
Proof. exact (@lem4807120 _110698 r x). Qed.
Lemma lem4807122 {_110698 : Type'} (x : _110698) (r : type1402 _110698) : (term9 _110698 r x) = (term10 _110698 x r).
Proof. exact (eq_refl (term9 _110698 r x)). Qed.
Lemma lem4807123 {_110698 : Type'} (x : _110698) (r : type1402 _110698) : term10 _110698 x r.
Proof. exact (EQ_MP (@lem4807122 _110698 x r) (@lem4807121 _110698 r x)). Qed.
Lemma lem4807124 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (s : _110698 -> Prop) : term11 _110698 x r s.
Proof. exact (@lem4807123 _110698 x r s). Qed.
Lemma lem4807125 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (s : _110698 -> Prop) : (term11 _110698 x r s) = ((term12 _110698 r x s) = (term13 _110698 x r s)).
Proof. exact (eq_refl (term11 _110698 x r s)). Qed.
Lemma lem4807152 {_110698 : Type'} (x : _110698) (r : type1402 _110698) (s : _110698 -> Prop) : (term12 _110698 r x s) = (term13 _110698 x r s).
Proof. exact (EQ_MP (@lem4807125 _110698 x r s) (@lem4807124 _110698 x r s)). Qed.
Lemma lem4807153 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term12 A r x s) = (term13 A x r s).
Proof. exact (@lem4807152 A x r s). Qed.
Lemma lem4807168 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4807169 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term14 A r x s) = (term15 A x r s).
Proof. exact (MK_COMB (@lem4807168) (@lem4807153 A x r s)). Qed.
Lemma lem4807182 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term16 A x r s) = (term16 A x r s).
Proof. exact (eq_refl (term16 A x r s)). Qed.
Lemma lem4807183 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term12 A r x s) = (term16 A x r s)) = ((term13 A x r s) = (term16 A x r s)).
Proof. exact (MK_COMB (@lem4807169 A x r s) (@lem4807182 A x r s)). Qed.
Lemma lem4807186 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term17 A s r x) = (term17 A s r x).
Proof. exact (eq_refl (term17 A s r x)). Qed.
Lemma lem4807187 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term18 A x r s) = (term19 A x r s).
Proof. exact (MK_COMB (@lem4807186 A s r x) (@lem4807183 A x r s)). Qed.
Lemma lem4807190 {A : Type'} (x : A) (r : type1402 A) : (term20 A x r) = (term21 A x r).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4807187 A x r s)). Qed.
Lemma lem4807191 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4807192 {A : Type'} (x : A) (r : type1402 A) : (term22 A x r) = (term23 A x r).
Proof. exact (MK_COMB (@lem4807191 A) (@lem4807190 A x r)). Qed.
Lemma lem4807197 {A : Type'} (r : type1402 A) : (term24 A r) = (term25 A r).
Proof. exact (fun_ext (fun x : A => @lem4807192 A x r)). Qed.
Lemma lem4807198 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807199 {A : Type'} (r : type1402 A) : (term26 A r) = (term27 A r).
Proof. exact (MK_COMB (@lem4807198 A) (@lem4807197 A r)). Qed.
Lemma lem4807204 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (fun_ext (fun r : type1402 A => @lem4807199 A r)). Qed.
Lemma lem4807205 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4807206 {A : Type'} : (term30 A) = (term31 A).
Proof. exact (MK_COMB (@lem4807205 A) (@lem4807204 A)). Qed.
Lemma lem4807211 {A : Type'} : (term31 A) = (term30 A).
Proof. exact (SYM (@lem4807206 A)). Qed.
Lemma lem4807213 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4807214 {A : Type'} : (term31 A) = (term33 A).
Proof. exact (@lem4807213 (term31 A)). Qed.
Lemma lem4807215 {A : Type'} : (term33 A) = (term31 A).
Proof. exact (SYM (@lem4807214 A)). Qed.
Lemma lem4807216 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem4807219 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem4807220 {A : Type'} : term35 A.
Proof. exact (fun h0 : term33 A => @lem4807219 A h0). Qed.
Lemma lem4807221 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem4807222 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem4807223 {A : Type'} (h1 : term33 A) (h2 : term35 A) : term33 A.
Proof. exact (@lem4807221 A h2 (@lem4807222 A h1)). Qed.
Lemma lem4807224 {A : Type'} (h1 : term33 A) : term36 A.
Proof. exact (fun h0 : term35 A => @lem4807223 A h1 h0). Qed.
Lemma lem4807225 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem4807226 {A : Type'} (h1 : term33 A) (h2 : term35 A) : term33 A.
Proof. exact (@lem4807224 A h1 (@lem4807225 A h2)). Qed.
Lemma lem4807227 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (fun h0 : term33 A => @lem4807226 A h0 h1). Qed.
Lemma lem4807228 {A : Type'} : term37 A.
Proof. exact (fun h0 : term35 A => @lem4807227 A h0). Qed.
Lemma lem4807231 {A : Type'} : term35 A.
Proof. exact (@lem4807228 A (@lem4807220 A)). Qed.
Lemma lem4807232 {A : Type'} : term35 A.
Proof. exact (@lem4807231 A). Qed.
Lemma lem4807234 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4807235 {A : Type'} : (term33 A) = (term38 A).
Proof. exact (@lem4807234 (term34 A)). Qed.
Lemma lem4807237 (t : Prop) : (term39 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4807238 {A : Type'} : (term38 A) = (term31 A).
Proof. exact (@lem4807237 (term31 A)). Qed.
Lemma lem4807285 {A : Type'} : (term33 A) = (term31 A).
Proof. exact (TRANS (@lem4807235 A) (@lem4807238 A)). Qed.
Lemma lem4807286 {A : Type'} (r : type1402 A) (s : A -> Prop) : (@pairwise A r s) = (@pairwise A r s).
Proof. exact (eq_refl (@pairwise A r s)). Qed.
Lemma lem4807297 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term40 A s r x y) = (term40 A s r x y).
Proof. exact (eq_refl (term40 A s r x y)). Qed.
Lemma lem4807298 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term41 A s r x) = (term41 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807297 A s r x y)). Qed.
Lemma lem4807299 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807300 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term42 A s r x) = (term42 A s r x).
Proof. exact (MK_COMB (@lem4807299 A) (@lem4807298 A s r x)). Qed.
Lemma lem4807301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807302 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term43 A s r x) = (term43 A s r x).
Proof. exact (MK_COMB (@lem4807301) (@lem4807300 A s r x)). Qed.
Lemma lem4807303 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term16 A x r s) = (term16 A x r s).
Proof. exact (MK_COMB (@lem4807302 A s r x) (@lem4807286 A r s)). Qed.
Lemma lem4807304 {A : Type'} (r : type1402 A) (s : A -> Prop) : (@pairwise A r s) = (@pairwise A r s).
Proof. exact (eq_refl (@pairwise A r s)). Qed.
Lemma lem4807319 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term44 A s r y x) = (term44 A s r y x).
Proof. exact (eq_refl (term44 A s r y x)). Qed.
Lemma lem4807320 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term45 A s r x) = (term45 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807319 A s r y x)). Qed.
Lemma lem4807321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807322 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term46 A s r x) = (term46 A s r x).
Proof. exact (MK_COMB (@lem4807321 A) (@lem4807320 A s r x)). Qed.
Lemma lem4807323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807324 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term47 A s r x) = (term47 A s r x).
Proof. exact (MK_COMB (@lem4807323) (@lem4807322 A s r x)). Qed.
Lemma lem4807325 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term13 A x r s) = (term13 A x r s).
Proof. exact (MK_COMB (@lem4807324 A s r x) (@lem4807304 A r s)). Qed.
Lemma lem4807326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4807327 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term15 A x r s) = (term15 A x r s).
Proof. exact (MK_COMB (@lem4807326) (@lem4807325 A x r s)). Qed.
Lemma lem4807328 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term13 A x r s) = (term16 A x r s)) = ((term13 A x r s) = (term16 A x r s)).
Proof. exact (MK_COMB (@lem4807327 A x r s) (@lem4807303 A x r s)). Qed.
Lemma lem4807337 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term48 A s r y x) = (term48 A s r y x).
Proof. exact (eq_refl (term48 A s r y x)). Qed.
Lemma lem4807338 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term49 A s r x) = (term49 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807337 A s r y x)). Qed.
Lemma lem4807339 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807340 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term50 A s r x) = (term50 A s r x).
Proof. exact (MK_COMB (@lem4807339 A) (@lem4807338 A s r x)). Qed.
Lemma lem4807341 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4807342 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term17 A s r x) = (term17 A s r x).
Proof. exact (MK_COMB (@lem4807341) (@lem4807340 A s r x)). Qed.
Lemma lem4807343 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term19 A x r s) = (term19 A x r s).
Proof. exact (MK_COMB (@lem4807342 A s r x) (@lem4807328 A x r s)). Qed.
Lemma lem4807344 {A : Type'} (x : A) (r : type1402 A) : (term21 A x r) = (term21 A x r).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4807343 A x r s)). Qed.
Lemma lem4807345 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4807346 {A : Type'} (x : A) (r : type1402 A) : (term23 A x r) = (term23 A x r).
Proof. exact (MK_COMB (@lem4807345 A) (@lem4807344 A x r)). Qed.
Lemma lem4807347 {A : Type'} (r : type1402 A) : (term25 A r) = (term25 A r).
Proof. exact (fun_ext (fun x : A => @lem4807346 A x r)). Qed.
Lemma lem4807348 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807349 {A : Type'} (r : type1402 A) : (term27 A r) = (term27 A r).
Proof. exact (MK_COMB (@lem4807348 A) (@lem4807347 A r)). Qed.
Lemma lem4807350 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (fun_ext (fun r : type1402 A => @lem4807349 A r)). Qed.
Lemma lem4807351 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem4807352 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (MK_COMB (@lem4807351 A) (@lem4807350 A)). Qed.
Lemma lem4807409 {A : Type'} : (term33 A) = (term31 A).
Proof. exact (TRANS (@lem4807285 A) (@lem4807352 A)). Qed.
Lemma lem4807410 {A : Type'} : (term31 A) = (term33 A).
Proof. exact (SYM (@lem4807409 A)). Qed.
Lemma lem4807411 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term50 A s r x.
Proof. exact (h1). Qed.
Lemma lem4807413 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4807414 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term13 A x r s) = (term16 A x r s)) = (term51 A x r s).
Proof. exact (@lem4807413 ((term13 A x r s) = (term16 A x r s))). Qed.
Lemma lem4807415 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term51 A x r s) = ((term13 A x r s) = (term16 A x r s)).
Proof. exact (SYM (@lem4807414 A x r s)). Qed.
Lemma lem4807416 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term52 A x r s) : term52 A x r s.
Proof. exact (h1). Qed.
Lemma lem4807432 {A : Type'} (r : type1402 A) (y : A) (x : A) : ((r x y) = (r y x)) = (term53 A r y x).
Proof. exact (@lem17784 (r x y) (r y x)). Qed.
Lemma lem4807434 {A : Type'} (y : A) (s : A -> Prop) : (term54 A y s) = (term54 A y s).
Proof. exact (eq_refl (term54 A y s)). Qed.
Lemma lem4807435 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term55 A s r y x) = (term56 A s r y x).
Proof. exact (MK_COMB (@lem4807434 A y s) (@lem4807432 A r y x)). Qed.
Lemma lem4807436 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term48 A s r y x) = (term55 A s r y x).
Proof. exact (@lem17265 (@IN A y s) ((r x y) = (r y x))). Qed.
Lemma lem4807437 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term48 A s r y x) = (term56 A s r y x).
Proof. exact (TRANS (@lem4807436 A s r y x) (@lem4807435 A s r y x)). Qed.
Lemma lem4807438 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term49 A s r x) = (term57 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807437 A s r y x)). Qed.
Lemma lem4807439 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807492 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term50 A s r x) = (term58 A s r x).
Proof. exact (MK_COMB (@lem4807439 A) (@lem4807438 A s r x)). Qed.
Lemma lem4807493 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term58 A s r x.
Proof. exact (EQ_MP (@lem4807492 A s r x) (@lem4807411 A s r x h1)). Qed.
Lemma lem4807499 {A : Type'} (y : A) (x : A) : (term59 A y x) = (y = x).
Proof. exact (@lem16933 (y = x)). Qed.
Lemma lem4807501 {A : Type'} (y : A) (s : A -> Prop) : (term54 A y s) = (term54 A y s).
Proof. exact (eq_refl (term54 A y s)). Qed.
Lemma lem4807502 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term60 A s y x) = (term61 A s y x).
Proof. exact (MK_COMB (@lem4807501 A y s) (@lem4807499 A y x)). Qed.
Lemma lem4807503 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term62 A s y x) = (term60 A s y x).
Proof. exact (@lem17045 (@IN A y s) (term63 A y x)). Qed.
Lemma lem4807504 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term62 A s y x) = (term61 A s y x).
Proof. exact (TRANS (@lem4807503 A s y x) (@lem4807502 A s y x)). Qed.
Lemma lem4807516 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term64 A r y x) = (term65 A r y x).
Proof. exact (@lem17045 (r x y) (r y x)). Qed.
Lemma lem4807519 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term66 A r y x) = (term66 A r y x).
Proof. exact (eq_refl (term66 A r y x)). Qed.
Lemma lem4807521 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term67 A s y x) = (term67 A s y x).
Proof. exact (eq_refl (term67 A s y x)). Qed.
Lemma lem4807522 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term68 A s r y x) = (term69 A s r y x).
Proof. exact (MK_COMB (@lem4807521 A s y x) (@lem4807516 A r y x)). Qed.
Lemma lem4807523 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term70 A s r y x) = (term68 A s r y x).
Proof. exact (@lem17362 (term71 A s y x) (term66 A r y x)). Qed.
Lemma lem4807524 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term70 A s r y x) = (term69 A s r y x).
Proof. exact (TRANS (@lem4807523 A s r y x) (@lem4807522 A s r y x)). Qed.
Lemma lem4807525 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807526 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term72 A s y x) = (term73 A s y x).
Proof. exact (MK_COMB (@lem4807525) (@lem4807504 A s y x)). Qed.
Lemma lem4807527 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term74 A s r y x) = (term75 A s r y x).
Proof. exact (MK_COMB (@lem4807526 A s y x) (@lem4807519 A r y x)). Qed.
Lemma lem4807528 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term44 A s r y x) = (term74 A s r y x).
Proof. exact (@lem17265 (term71 A s y x) (term66 A r y x)). Qed.
Lemma lem4807529 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term44 A s r y x) = (term75 A s r y x).
Proof. exact (TRANS (@lem4807528 A s r y x) (@lem4807527 A s r y x)). Qed.
Lemma lem4807530 {A : Type'} (P : A -> Prop) : (term76 A P) = (term77 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4807531 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term78 A s r x) = (term79 A s r x).
Proof. exact (@lem4807530 A (term45 A s r x)). Qed.
Lemma lem4807532 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term80 A s r x y) = (term44 A s r y x).
Proof. exact (eq_refl (term80 A s r x y)). Qed.
Lemma lem4807533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4807534 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term81 A s r x y) = (term70 A s r y x).
Proof. exact (MK_COMB (@lem4807533) (@lem4807532 A s r y x)). Qed.
Lemma lem4807535 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term81 A s r x y) = (term69 A s r y x).
Proof. exact (TRANS (@lem4807534 A s r y x) (@lem4807524 A s r y x)). Qed.
Lemma lem4807536 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term82 A s r x) = (term83 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807535 A s r y x)). Qed.
Lemma lem4807537 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807538 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term79 A s r x) = (term84 A s r x).
Proof. exact (MK_COMB (@lem4807537 A) (@lem4807536 A s r x)). Qed.
Lemma lem4807539 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term78 A s r x) = (term84 A s r x).
Proof. exact (TRANS (@lem4807531 A s r x) (@lem4807538 A s r x)). Qed.
Lemma lem4807540 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term45 A s r x) = (term85 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807529 A s r y x)). Qed.
Lemma lem4807541 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807542 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term46 A s r x) = (term86 A s r x).
Proof. exact (MK_COMB (@lem4807541 A) (@lem4807540 A s r x)). Qed.
Lemma lem4807543 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4807544 {A : Type'} (r : type1402 A) (s : A -> Prop) : (@pairwise A r s) = (@pairwise A r s).
Proof. exact (eq_refl (@pairwise A r s)). Qed.
Lemma lem4807545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807546 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term88 A s r x) = (term89 A s r x).
Proof. exact (MK_COMB (@lem4807545) (@lem4807539 A s r x)). Qed.
Lemma lem4807547 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term90 A x r s) = (term91 A x r s).
Proof. exact (MK_COMB (@lem4807546 A s r x) (@lem4807543 A r s)). Qed.
Lemma lem4807548 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term92 A x r s) = (term90 A x r s).
Proof. exact (@lem17045 (term46 A s r x) (@pairwise A r s)). Qed.
Lemma lem4807549 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term92 A x r s) = (term91 A x r s).
Proof. exact (TRANS (@lem4807548 A x r s) (@lem4807547 A x r s)). Qed.
Lemma lem4807550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807551 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term47 A s r x) = (term93 A s r x).
Proof. exact (MK_COMB (@lem4807550) (@lem4807542 A s r x)). Qed.
Lemma lem4807552 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term13 A x r s) = (term94 A x r s).
Proof. exact (MK_COMB (@lem4807551 A s r x) (@lem4807544 A r s)). Qed.
Lemma lem4807558 {A : Type'} (y : A) (x : A) : (term59 A y x) = (y = x).
Proof. exact (@lem16933 (y = x)). Qed.
Lemma lem4807560 {A : Type'} (y : A) (s : A -> Prop) : (term54 A y s) = (term54 A y s).
Proof. exact (eq_refl (term54 A y s)). Qed.
Lemma lem4807561 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term60 A s y x) = (term61 A s y x).
Proof. exact (MK_COMB (@lem4807560 A y s) (@lem4807558 A y x)). Qed.
Lemma lem4807562 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term62 A s y x) = (term60 A s y x).
Proof. exact (@lem17045 (@IN A y s) (term63 A y x)). Qed.
Lemma lem4807563 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term62 A s y x) = (term61 A s y x).
Proof. exact (TRANS (@lem4807562 A s y x) (@lem4807561 A s y x)). Qed.
Lemma lem4807568 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (r x y).
Proof. exact (eq_refl (r x y)). Qed.
Lemma lem4807573 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term95 A s r x y) = (term96 A s r x y).
Proof. exact (@lem17362 (term71 A s y x) (r x y)). Qed.
Lemma lem4807574 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807575 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term72 A s y x) = (term73 A s y x).
Proof. exact (MK_COMB (@lem4807574) (@lem4807563 A s y x)). Qed.
Lemma lem4807576 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term97 A s r x y) = (term98 A s r x y).
Proof. exact (MK_COMB (@lem4807575 A s y x) (@lem4807568 A r x y)). Qed.
Lemma lem4807577 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term40 A s r x y) = (term97 A s r x y).
Proof. exact (@lem17265 (term71 A s y x) (r x y)). Qed.
Lemma lem4807578 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term40 A s r x y) = (term98 A s r x y).
Proof. exact (TRANS (@lem4807577 A s r x y) (@lem4807576 A s r x y)). Qed.
Lemma lem4807579 {A : Type'} (P : A -> Prop) : (term76 A P) = (term77 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4807580 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term99 A s r x) = (term100 A s r x).
Proof. exact (@lem4807579 A (term41 A s r x)). Qed.
Lemma lem4807581 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term101 A s r x y) = (term40 A s r x y).
Proof. exact (eq_refl (term101 A s r x y)). Qed.
Lemma lem4807582 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4807583 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term102 A s r x y) = (term95 A s r x y).
Proof. exact (MK_COMB (@lem4807582) (@lem4807581 A s r x y)). Qed.
Lemma lem4807584 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term102 A s r x y) = (term96 A s r x y).
Proof. exact (TRANS (@lem4807583 A s r x y) (@lem4807573 A s r x y)). Qed.
Lemma lem4807585 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term103 A s r x) = (term104 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807584 A s r x y)). Qed.
Lemma lem4807586 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807587 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term100 A s r x) = (term105 A s r x).
Proof. exact (MK_COMB (@lem4807586 A) (@lem4807585 A s r x)). Qed.
Lemma lem4807588 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term99 A s r x) = (term105 A s r x).
Proof. exact (TRANS (@lem4807580 A s r x) (@lem4807587 A s r x)). Qed.
Lemma lem4807589 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term41 A s r x) = (term106 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807578 A s r x y)). Qed.
Lemma lem4807590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4807591 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term42 A s r x) = (term107 A s r x).
Proof. exact (MK_COMB (@lem4807590 A) (@lem4807589 A s r x)). Qed.
Lemma lem4807592 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4807593 {A : Type'} (r : type1402 A) (s : A -> Prop) : (@pairwise A r s) = (@pairwise A r s).
Proof. exact (eq_refl (@pairwise A r s)). Qed.
Lemma lem4807594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807595 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term108 A s r x) = (term109 A s r x).
Proof. exact (MK_COMB (@lem4807594) (@lem4807588 A s r x)). Qed.
Lemma lem4807596 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term110 A x r s) = (term111 A x r s).
Proof. exact (MK_COMB (@lem4807595 A s r x) (@lem4807592 A r s)). Qed.
Lemma lem4807597 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term112 A x r s) = (term110 A x r s).
Proof. exact (@lem17045 (term42 A s r x) (@pairwise A r s)). Qed.
Lemma lem4807598 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term112 A x r s) = (term111 A x r s).
Proof. exact (TRANS (@lem4807597 A x r s) (@lem4807596 A x r s)). Qed.
Lemma lem4807599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807600 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term43 A s r x) = (term113 A s r x).
Proof. exact (MK_COMB (@lem4807599) (@lem4807591 A s r x)). Qed.
Lemma lem4807601 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term16 A x r s) = (term114 A x r s).
Proof. exact (MK_COMB (@lem4807600 A s r x) (@lem4807593 A r s)). Qed.
Lemma lem4807602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807603 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term115 A x r s) = (term116 A x r s).
Proof. exact (MK_COMB (@lem4807602) (@lem4807549 A x r s)). Qed.
Lemma lem4807604 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term117 A x r s) = (term118 A x r s).
Proof. exact (MK_COMB (@lem4807603 A x r s) (@lem4807601 A x r s)). Qed.
Lemma lem4807605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807606 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term119 A x r s) = (term120 A x r s).
Proof. exact (MK_COMB (@lem4807605) (@lem4807552 A x r s)). Qed.
Lemma lem4807607 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term121 A x r s) = (term122 A x r s).
Proof. exact (MK_COMB (@lem4807606 A x r s) (@lem4807598 A x r s)). Qed.
Lemma lem4807608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807609 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term123 A x r s) = (term124 A x r s).
Proof. exact (MK_COMB (@lem4807608) (@lem4807607 A x r s)). Qed.
Lemma lem4807610 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term125 A x r s) = (term126 A x r s).
Proof. exact (MK_COMB (@lem4807609 A x r s) (@lem4807604 A x r s)). Qed.
Lemma lem4807611 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term52 A x r s) = (term125 A x r s).
Proof. exact (@lem17646 (term13 A x r s) (term16 A x r s)). Qed.
Lemma lem4807612 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term52 A x r s) = (term126 A x r s).
Proof. exact (TRANS (@lem4807611 A x r s) (@lem4807610 A x r s)). Qed.
Lemma lem4807807 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4807808 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (@lem4807807 A P Q). Qed.
Lemma lem4807809 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term129 A x r s) = (term130 A x r s).
Proof. exact (@lem4807808 A (term104 A s r x) (term87 A r s)). Qed.
Lemma lem4807810 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term131 A s r x y) = (term96 A s r x y).
Proof. exact (eq_refl (term131 A s r x y)). Qed.
Lemma lem4807811 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term132 A s r x) = (term104 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807810 A s r x y)). Qed.
Lemma lem4807812 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807813 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term133 A s r x) = (term105 A s r x).
Proof. exact (MK_COMB (@lem4807812 A) (@lem4807811 A s r x)). Qed.
Lemma lem4807814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807815 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term134 A s r x) = (term109 A s r x).
Proof. exact (MK_COMB (@lem4807814) (@lem4807813 A s r x)). Qed.
Lemma lem4807816 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4807817 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term129 A x r s) = (term111 A x r s).
Proof. exact (MK_COMB (@lem4807815 A s r x) (@lem4807816 A r s)). Qed.
Lemma lem4807818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4807819 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term135 A x r s) = (term136 A x r s).
Proof. exact (MK_COMB (@lem4807818) (@lem4807817 A x r s)). Qed.
Lemma lem4807820 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term131 A s r x y) = (term96 A s r x y).
Proof. exact (eq_refl (term131 A s r x y)). Qed.
Lemma lem4807821 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807822 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term137 A s r x y) = (term138 A s r x y).
Proof. exact (MK_COMB (@lem4807821) (@lem4807820 A s r x y)). Qed.
Lemma lem4807823 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4807824 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term139 A x y r s) = (term140 A x y r s).
Proof. exact (MK_COMB (@lem4807822 A s r x y) (@lem4807823 A r s)). Qed.
Lemma lem4807825 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term141 A x r s) = (term142 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807824 A x y r s)). Qed.
Lemma lem4807826 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807827 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term130 A x r s) = (term143 A x r s).
Proof. exact (MK_COMB (@lem4807826 A) (@lem4807825 A x r s)). Qed.
Lemma lem4807828 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term129 A x r s) = (term130 A x r s)) = ((term111 A x r s) = (term143 A x r s)).
Proof. exact (MK_COMB (@lem4807819 A x r s) (@lem4807827 A x r s)). Qed.
Lemma lem4807829 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term111 A x r s) = (term143 A x r s).
Proof. exact (EQ_MP (@lem4807828 A x r s) (@lem4807809 A x r s)). Qed.
Lemma lem4807830 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term120 A x r s) = (term120 A x r s).
Proof. exact (eq_refl (term120 A x r s)). Qed.
Lemma lem4807831 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term122 A x r s) = (term144 A x r s).
Proof. exact (MK_COMB (@lem4807830 A x r s) (@lem4807829 A x r s)). Qed.
Lemma lem4807833 {A : Type'} (P : Prop) (Q : A -> Prop) : (term145 A P Q) = (term146 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4807834 {A : Type'} (P : Prop) (Q : A -> Prop) : (term145 A P Q) = (term146 A P Q).
Proof. exact (@lem4807833 A P Q). Qed.
Lemma lem4807835 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term147 A x r s) = (term148 A x r s).
Proof. exact (@lem4807834 A (term94 A x r s) (term142 A x r s)). Qed.
Lemma lem4807836 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term149 A x r s y) = (term140 A x y r s).
Proof. exact (eq_refl (term149 A x r s y)). Qed.
Lemma lem4807837 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term150 A x r s) = (term142 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807836 A x y r s)). Qed.
Lemma lem4807838 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807839 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term151 A x r s) = (term143 A x r s).
Proof. exact (MK_COMB (@lem4807838 A) (@lem4807837 A x r s)). Qed.
Lemma lem4807840 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term120 A x r s) = (term120 A x r s).
Proof. exact (eq_refl (term120 A x r s)). Qed.
Lemma lem4807841 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term147 A x r s) = (term144 A x r s).
Proof. exact (MK_COMB (@lem4807840 A x r s) (@lem4807839 A x r s)). Qed.
Lemma lem4807842 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4807843 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term152 A x r s) = (term153 A x r s).
Proof. exact (MK_COMB (@lem4807842) (@lem4807841 A x r s)). Qed.
Lemma lem4807844 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term149 A x r s y) = (term140 A x y r s).
Proof. exact (eq_refl (term149 A x r s y)). Qed.
Lemma lem4807845 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term120 A x r s) = (term120 A x r s).
Proof. exact (eq_refl (term120 A x r s)). Qed.
Lemma lem4807846 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term154 A x r s y) = (term155 A x y r s).
Proof. exact (MK_COMB (@lem4807845 A x r s) (@lem4807844 A x y r s)). Qed.
Lemma lem4807847 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term156 A x r s) = (term157 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807846 A x y r s)). Qed.
Lemma lem4807848 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807849 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term148 A x r s) = (term158 A x r s).
Proof. exact (MK_COMB (@lem4807848 A) (@lem4807847 A x r s)). Qed.
Lemma lem4807850 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term147 A x r s) = (term148 A x r s)) = ((term144 A x r s) = (term158 A x r s)).
Proof. exact (MK_COMB (@lem4807843 A x r s) (@lem4807849 A x r s)). Qed.
Lemma lem4807851 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term144 A x r s) = (term158 A x r s).
Proof. exact (EQ_MP (@lem4807850 A x r s) (@lem4807835 A x r s)). Qed.
Lemma lem4807852 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term122 A x r s) = (term158 A x r s).
Proof. exact (TRANS (@lem4807831 A x r s) (@lem4807851 A x r s)). Qed.
Lemma lem4807853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807854 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term124 A x r s) = (term159 A x r s).
Proof. exact (MK_COMB (@lem4807853) (@lem4807852 A x r s)). Qed.
Lemma lem4807856 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4807857 {A : Type'} (P : A -> Prop) (Q : Prop) : (term127 A P Q) = (term128 A P Q).
Proof. exact (@lem4807856 A P Q). Qed.
Lemma lem4807858 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term160 A x r s) = (term161 A x r s).
Proof. exact (@lem4807857 A (term83 A s r x) (term87 A r s)). Qed.
Lemma lem4807859 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term162 A s r x y) = (term69 A s r y x).
Proof. exact (eq_refl (term162 A s r x y)). Qed.
Lemma lem4807860 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term163 A s r x) = (term83 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4807859 A s r y x)). Qed.
Lemma lem4807861 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807862 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term164 A s r x) = (term84 A s r x).
Proof. exact (MK_COMB (@lem4807861 A) (@lem4807860 A s r x)). Qed.
Lemma lem4807863 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807864 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term165 A s r x) = (term89 A s r x).
Proof. exact (MK_COMB (@lem4807863) (@lem4807862 A s r x)). Qed.
Lemma lem4807865 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4807866 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term160 A x r s) = (term91 A x r s).
Proof. exact (MK_COMB (@lem4807864 A s r x) (@lem4807865 A r s)). Qed.
Lemma lem4807867 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4807868 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term166 A x r s) = (term167 A x r s).
Proof. exact (MK_COMB (@lem4807867) (@lem4807866 A x r s)). Qed.
Lemma lem4807869 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term162 A s r x y) = (term69 A s r y x).
Proof. exact (eq_refl (term162 A s r x y)). Qed.
Lemma lem4807870 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807871 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term168 A s r x y) = (term169 A s r y x).
Proof. exact (MK_COMB (@lem4807870) (@lem4807869 A s r y x)). Qed.
Lemma lem4807872 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4807873 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term170 A x y r s) = (term171 A y x r s).
Proof. exact (MK_COMB (@lem4807871 A s r y x) (@lem4807872 A r s)). Qed.
Lemma lem4807874 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term172 A x r s) = (term173 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807873 A y x r s)). Qed.
Lemma lem4807875 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807876 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term161 A x r s) = (term174 A x r s).
Proof. exact (MK_COMB (@lem4807875 A) (@lem4807874 A x r s)). Qed.
Lemma lem4807877 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term160 A x r s) = (term161 A x r s)) = ((term91 A x r s) = (term174 A x r s)).
Proof. exact (MK_COMB (@lem4807868 A x r s) (@lem4807876 A x r s)). Qed.
Lemma lem4807878 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term91 A x r s) = (term174 A x r s).
Proof. exact (EQ_MP (@lem4807877 A x r s) (@lem4807858 A x r s)). Qed.
Lemma lem4807879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807880 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term116 A x r s) = (term175 A x r s).
Proof. exact (MK_COMB (@lem4807879) (@lem4807878 A x r s)). Qed.
Lemma lem4807881 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term114 A x r s) = (term114 A x r s).
Proof. exact (eq_refl (term114 A x r s)). Qed.
Lemma lem4807882 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term118 A x r s) = (term176 A x r s).
Proof. exact (MK_COMB (@lem4807880 A x r s) (@lem4807881 A x r s)). Qed.
Lemma lem4807884 {A : Type'} (P : A -> Prop) (Q : Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4807885 {A : Type'} (P : A -> Prop) (Q : Prop) : (term177 A P Q) = (term178 A P Q).
Proof. exact (@lem4807884 A P Q). Qed.
Lemma lem4807886 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term179 A x r s) = (term180 A x r s).
Proof. exact (@lem4807885 A (term173 A x r s) (term114 A x r s)). Qed.
Lemma lem4807887 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term181 A x r s y) = (term171 A y x r s).
Proof. exact (eq_refl (term181 A x r s y)). Qed.
Lemma lem4807888 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term182 A x r s) = (term173 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807887 A y x r s)). Qed.
Lemma lem4807889 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807890 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term183 A x r s) = (term174 A x r s).
Proof. exact (MK_COMB (@lem4807889 A) (@lem4807888 A x r s)). Qed.
Lemma lem4807891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807892 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term184 A x r s) = (term175 A x r s).
Proof. exact (MK_COMB (@lem4807891) (@lem4807890 A x r s)). Qed.
Lemma lem4807893 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term114 A x r s) = (term114 A x r s).
Proof. exact (eq_refl (term114 A x r s)). Qed.
Lemma lem4807894 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term179 A x r s) = (term176 A x r s).
Proof. exact (MK_COMB (@lem4807892 A x r s) (@lem4807893 A x r s)). Qed.
Lemma lem4807895 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4807896 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term185 A x r s) = (term186 A x r s).
Proof. exact (MK_COMB (@lem4807895) (@lem4807894 A x r s)). Qed.
Lemma lem4807897 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term181 A x r s y) = (term171 A y x r s).
Proof. exact (eq_refl (term181 A x r s y)). Qed.
Lemma lem4807898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4807899 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term187 A x r s y) = (term188 A y x r s).
Proof. exact (MK_COMB (@lem4807898) (@lem4807897 A y x r s)). Qed.
Lemma lem4807900 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term114 A x r s) = (term114 A x r s).
Proof. exact (eq_refl (term114 A x r s)). Qed.
Lemma lem4807901 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term189 A y x r s) = (term190 A y x r s).
Proof. exact (MK_COMB (@lem4807899 A y x r s) (@lem4807900 A x r s)). Qed.
Lemma lem4807902 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term191 A x r s) = (term192 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807901 A y x r s)). Qed.
Lemma lem4807903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807904 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term180 A x r s) = (term193 A x r s).
Proof. exact (MK_COMB (@lem4807903 A) (@lem4807902 A x r s)). Qed.
Lemma lem4807905 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term179 A x r s) = (term180 A x r s)) = ((term176 A x r s) = (term193 A x r s)).
Proof. exact (MK_COMB (@lem4807896 A x r s) (@lem4807904 A x r s)). Qed.
Lemma lem4807906 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term176 A x r s) = (term193 A x r s).
Proof. exact (EQ_MP (@lem4807905 A x r s) (@lem4807886 A x r s)). Qed.
Lemma lem4807907 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term118 A x r s) = (term193 A x r s).
Proof. exact (TRANS (@lem4807882 A x r s) (@lem4807906 A x r s)). Qed.
Lemma lem4807908 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term126 A x r s) = (term194 A x r s).
Proof. exact (MK_COMB (@lem4807854 A x r s) (@lem4807907 A x r s)). Qed.
Lemma lem4807910 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4807911 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term195 A P Q) = (term196 A P Q).
Proof. exact (@lem4807910 A P Q). Qed.
Lemma lem4807912 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term197 A x r s) = (term198 A x r s).
Proof. exact (@lem4807911 A (term157 A x r s) (term192 A x r s)). Qed.
Lemma lem4807913 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term199 A x r s y) = (term155 A x y r s).
Proof. exact (eq_refl (term199 A x r s y)). Qed.
Lemma lem4807914 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term200 A x r s) = (term157 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807913 A x y r s)). Qed.
Lemma lem4807915 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807916 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term201 A x r s) = (term158 A x r s).
Proof. exact (MK_COMB (@lem4807915 A) (@lem4807914 A x r s)). Qed.
Lemma lem4807917 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807918 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term202 A x r s) = (term159 A x r s).
Proof. exact (MK_COMB (@lem4807917) (@lem4807916 A x r s)). Qed.
Lemma lem4807919 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term203 A x r s y) = (term190 A y x r s).
Proof. exact (eq_refl (term203 A x r s y)). Qed.
Lemma lem4807920 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term204 A x r s) = (term192 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807919 A y x r s)). Qed.
Lemma lem4807921 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807922 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term205 A x r s) = (term193 A x r s).
Proof. exact (MK_COMB (@lem4807921 A) (@lem4807920 A x r s)). Qed.
Lemma lem4807923 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term197 A x r s) = (term194 A x r s).
Proof. exact (MK_COMB (@lem4807918 A x r s) (@lem4807922 A x r s)). Qed.
Lemma lem4807924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4807925 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term206 A x r s) = (term207 A x r s).
Proof. exact (MK_COMB (@lem4807924) (@lem4807923 A x r s)). Qed.
Lemma lem4807926 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term199 A x r s y) = (term155 A x y r s).
Proof. exact (eq_refl (term199 A x r s y)). Qed.
Lemma lem4807927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807928 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term208 A x r s y) = (term209 A x y r s).
Proof. exact (MK_COMB (@lem4807927) (@lem4807926 A x y r s)). Qed.
Lemma lem4807929 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term203 A x r s y) = (term190 A y x r s).
Proof. exact (eq_refl (term203 A x r s y)). Qed.
Lemma lem4807930 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term210 A x r s y) = (term211 A y x r s).
Proof. exact (MK_COMB (@lem4807928 A x y r s) (@lem4807929 A y x r s)). Qed.
Lemma lem4807931 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term212 A x r s) = (term213 A x r s).
Proof. exact (fun_ext (fun y : A => @lem4807930 A y x r s)). Qed.
Lemma lem4807932 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4807933 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term198 A x r s) = (term214 A x r s).
Proof. exact (MK_COMB (@lem4807932 A) (@lem4807931 A x r s)). Qed.
Lemma lem4807934 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : ((term197 A x r s) = (term198 A x r s)) = ((term194 A x r s) = (term214 A x r s)).
Proof. exact (MK_COMB (@lem4807925 A x r s) (@lem4807933 A x r s)). Qed.
Lemma lem4807935 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term194 A x r s) = (term214 A x r s).
Proof. exact (EQ_MP (@lem4807934 A x r s) (@lem4807912 A x r s)). Qed.
Lemma lem4807937 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term126 A x r s) = (term214 A x r s).
Proof. exact (TRANS (@lem4807908 A x r s) (@lem4807935 A x r s)). Qed.
Lemma lem4807938 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term52 A x r s) = (term214 A x r s).
Proof. exact (TRANS (@lem4807612 A x r s) (@lem4807937 A x r s)). Qed.
Lemma lem4807939 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term52 A x r s) : term214 A x r s.
Proof. exact (EQ_MP (@lem4807938 A x r s) (@lem4807416 A x r s h1)). Qed.
Lemma lem4807940 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term211 A y x r s) : term211 A y x r s.
Proof. exact (h1). Qed.
Lemma lem4807947 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4807948 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4807947 A (A -> Prop) f x). Qed.
Lemma lem4807949 {A : Type'} (r : type1402 A) (y : A) : (r y) = (@I (A -> A -> Prop) r y).
Proof. exact (@lem4807948 A r y). Qed.
Lemma lem4807950 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4807951 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (@I (A -> A -> Prop) r y x).
Proof. exact (MK_COMB (@lem4807949 A r y) (@lem4807950 A x)). Qed.
Lemma lem4807953 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4807954 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4807953 A Prop f x). Qed.
Lemma lem4807955 {A : Type'} (r : type1402 A) (y : A) (x : A) : (@I (A -> A -> Prop) r y x) = (term215 A r y x).
Proof. exact (@lem4807954 A (@I (A -> A -> Prop) r y) x). Qed.
Lemma lem4807957 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (term215 A r y x).
Proof. exact (TRANS (@lem4807951 A r y x) (@lem4807955 A r y x)). Qed.
Lemma lem4807958 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4807965 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4807966 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4807965 A (A -> Prop) f x). Qed.
Lemma lem4807967 {A : Type'} (r : type1402 A) (x : A) : (r x) = (@I (A -> A -> Prop) r x).
Proof. exact (@lem4807966 A r x). Qed.
Lemma lem4807968 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4807969 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (@I (A -> A -> Prop) r x y).
Proof. exact (MK_COMB (@lem4807967 A r x) (@lem4807968 A y)). Qed.
Lemma lem4807971 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4807972 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4807971 A Prop f x). Qed.
Lemma lem4807973 {A : Type'} (r : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) r x y) = (term215 A r x y).
Proof. exact (@lem4807972 A (@I (A -> A -> Prop) r x) y). Qed.
Lemma lem4807975 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (term215 A r x y).
Proof. exact (TRANS (@lem4807969 A r x y) (@lem4807973 A r x y)). Qed.
Lemma lem4807976 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term216 A r x y) = (term217 A r x y).
Proof. exact (MK_COMB (@lem4807958) (@lem4807975 A r x y)). Qed.
Lemma lem4807977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4807978 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term218 A r x y) = (term219 A r x y).
Proof. exact (MK_COMB (@lem4807977) (@lem4807976 A r x y)). Qed.
Lemma lem4807979 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term220 A r y x) = (term221 A r y x).
Proof. exact (MK_COMB (@lem4807978 A r x y) (@lem4807957 A r y x)). Qed.
Lemma lem4807980 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4807987 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4807988 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4807987 A (A -> Prop) f x). Qed.
Lemma lem4807989 {A : Type'} (r : type1402 A) (y : A) : (r y) = (@I (A -> A -> Prop) r y).
Proof. exact (@lem4807988 A r y). Qed.
Lemma lem4807990 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4807991 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (@I (A -> A -> Prop) r y x).
Proof. exact (MK_COMB (@lem4807989 A r y) (@lem4807990 A x)). Qed.
Lemma lem4807993 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4807994 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4807993 A Prop f x). Qed.
Lemma lem4807995 {A : Type'} (r : type1402 A) (y : A) (x : A) : (@I (A -> A -> Prop) r y x) = (term215 A r y x).
Proof. exact (@lem4807994 A (@I (A -> A -> Prop) r y) x). Qed.
Lemma lem4807997 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (term215 A r y x).
Proof. exact (TRANS (@lem4807991 A r y x) (@lem4807995 A r y x)). Qed.
Lemma lem4807998 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term216 A r y x) = (term217 A r y x).
Proof. exact (MK_COMB (@lem4807980) (@lem4807997 A r y x)). Qed.
Lemma lem4808005 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808006 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4808005 A (A -> Prop) f x). Qed.
Lemma lem4808007 {A : Type'} (r : type1402 A) (x : A) : (r x) = (@I (A -> A -> Prop) r x).
Proof. exact (@lem4808006 A r x). Qed.
Lemma lem4808008 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4808009 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (@I (A -> A -> Prop) r x y).
Proof. exact (MK_COMB (@lem4808007 A r x) (@lem4808008 A y)). Qed.
Lemma lem4808011 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808012 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4808011 A Prop f x). Qed.
Lemma lem4808013 {A : Type'} (r : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) r x y) = (term215 A r x y).
Proof. exact (@lem4808012 A (@I (A -> A -> Prop) r x) y). Qed.
Lemma lem4808015 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (term215 A r x y).
Proof. exact (TRANS (@lem4808009 A r x y) (@lem4808013 A r x y)). Qed.
Lemma lem4808016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4808017 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term222 A r x y) = (term223 A r x y).
Proof. exact (MK_COMB (@lem4808016) (@lem4808015 A r x y)). Qed.
Lemma lem4808018 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term224 A r y x) = (term225 A r y x).
Proof. exact (MK_COMB (@lem4808017 A r x y) (@lem4807998 A r y x)). Qed.
Lemma lem4808019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4808020 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term226 A r y x) = (term227 A r y x).
Proof. exact (MK_COMB (@lem4808019) (@lem4808018 A r y x)). Qed.
Lemma lem4808021 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term53 A r y x) = (term228 A r y x).
Proof. exact (MK_COMB (@lem4808020 A r y x) (@lem4807979 A r y x)). Qed.
Lemma lem4808030 {A : Type'} (y : A) (s : A -> Prop) : (term54 A y s) = (term54 A y s).
Proof. exact (eq_refl (term54 A y s)). Qed.
Lemma lem4808031 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term56 A s r y x) = (term229 A s r y x).
Proof. exact (MK_COMB (@lem4808030 A y s) (@lem4808021 A r y x)). Qed.
Lemma lem4808032 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term57 A s r x) = (term230 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4808031 A s r y x)). Qed.
Lemma lem4808033 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4808034 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term58 A s r x) = (term231 A s r x).
Proof. exact (MK_COMB (@lem4808033 A) (@lem4808032 A s r x)). Qed.
Lemma lem4808035 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term231 A s r x.
Proof. exact (EQ_MP (@lem4808034 A s r x) (@lem4807493 A s r x h1)). Qed.
Lemma lem4808040 {A : Type'} (r : type1402 A) (s : A -> Prop) : (@pairwise A r s) = (@pairwise A r s).
Proof. exact (eq_refl (@pairwise A r s)). Qed.
Lemma lem4808047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808048 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4808047 A (A -> Prop) f x). Qed.
Lemma lem4808049 {A : Type'} (r : type1402 A) (x : A) : (r x) = (@I (A -> A -> Prop) r x).
Proof. exact (@lem4808048 A r x). Qed.
Lemma lem4808050 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4808051 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (@I (A -> A -> Prop) r x y).
Proof. exact (MK_COMB (@lem4808049 A r x) (@lem4808050 A y)). Qed.
Lemma lem4808053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808054 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4808053 A Prop f x). Qed.
Lemma lem4808055 {A : Type'} (r : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) r x y) = (term215 A r x y).
Proof. exact (@lem4808054 A (@I (A -> A -> Prop) r x) y). Qed.
Lemma lem4808057 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (term215 A r x y).
Proof. exact (TRANS (@lem4808051 A r x y) (@lem4808055 A r x y)). Qed.
Lemma lem4808074 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term73 A s y x) = (term73 A s y x).
Proof. exact (eq_refl (term73 A s y x)). Qed.
Lemma lem4808075 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term98 A s r x y) = (term232 A s r x y).
Proof. exact (MK_COMB (@lem4808074 A s y x) (@lem4808057 A r x y)). Qed.
Lemma lem4808076 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term106 A s r x) = (term233 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4808075 A s r x y)). Qed.
Lemma lem4808077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4808078 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term107 A s r x) = (term234 A s r x).
Proof. exact (MK_COMB (@lem4808077 A) (@lem4808076 A s r x)). Qed.
Lemma lem4808079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4808080 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term113 A s r x) = (term235 A s r x).
Proof. exact (MK_COMB (@lem4808079) (@lem4808078 A s r x)). Qed.
Lemma lem4808081 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term114 A x r s) = (term236 A x r s).
Proof. exact (MK_COMB (@lem4808080 A s r x) (@lem4808040 A r s)). Qed.
Lemma lem4808088 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4808089 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4808096 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808097 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4808096 A (A -> Prop) f x). Qed.
Lemma lem4808098 {A : Type'} (r : type1402 A) (y : A) : (r y) = (@I (A -> A -> Prop) r y).
Proof. exact (@lem4808097 A r y). Qed.
Lemma lem4808099 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4808100 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (@I (A -> A -> Prop) r y x).
Proof. exact (MK_COMB (@lem4808098 A r y) (@lem4808099 A x)). Qed.
Lemma lem4808102 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808103 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4808102 A Prop f x). Qed.
Lemma lem4808104 {A : Type'} (r : type1402 A) (y : A) (x : A) : (@I (A -> A -> Prop) r y x) = (term215 A r y x).
Proof. exact (@lem4808103 A (@I (A -> A -> Prop) r y) x). Qed.
Lemma lem4808106 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (term215 A r y x).
Proof. exact (TRANS (@lem4808100 A r y x) (@lem4808104 A r y x)). Qed.
Lemma lem4808107 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term216 A r y x) = (term217 A r y x).
Proof. exact (MK_COMB (@lem4808089) (@lem4808106 A r y x)). Qed.
Lemma lem4808108 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4808115 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808116 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4808115 A (A -> Prop) f x). Qed.
Lemma lem4808117 {A : Type'} (r : type1402 A) (x : A) : (r x) = (@I (A -> A -> Prop) r x).
Proof. exact (@lem4808116 A r x). Qed.
Lemma lem4808118 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4808119 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (@I (A -> A -> Prop) r x y).
Proof. exact (MK_COMB (@lem4808117 A r x) (@lem4808118 A y)). Qed.
Lemma lem4808121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808122 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4808121 A Prop f x). Qed.
Lemma lem4808123 {A : Type'} (r : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) r x y) = (term215 A r x y).
Proof. exact (@lem4808122 A (@I (A -> A -> Prop) r x) y). Qed.
Lemma lem4808125 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (term215 A r x y).
Proof. exact (TRANS (@lem4808119 A r x y) (@lem4808123 A r x y)). Qed.
Lemma lem4808126 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term216 A r x y) = (term217 A r x y).
Proof. exact (MK_COMB (@lem4808108) (@lem4808125 A r x y)). Qed.
Lemma lem4808127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4808128 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term218 A r x y) = (term219 A r x y).
Proof. exact (MK_COMB (@lem4808127) (@lem4808126 A r x y)). Qed.
Lemma lem4808129 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term65 A r y x) = (term237 A r y x).
Proof. exact (MK_COMB (@lem4808128 A r x y) (@lem4808107 A r y x)). Qed.
Lemma lem4808146 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term67 A s y x) = (term67 A s y x).
Proof. exact (eq_refl (term67 A s y x)). Qed.
Lemma lem4808147 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term69 A s r y x) = (term238 A s r y x).
Proof. exact (MK_COMB (@lem4808146 A s y x) (@lem4808129 A r y x)). Qed.
Lemma lem4808148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4808149 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term169 A s r y x) = (term239 A s r y x).
Proof. exact (MK_COMB (@lem4808148) (@lem4808147 A s r y x)). Qed.
Lemma lem4808150 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term171 A y x r s) = (term240 A y x r s).
Proof. exact (MK_COMB (@lem4808149 A s r y x) (@lem4808088 A r s)). Qed.
Lemma lem4808151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4808152 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term188 A y x r s) = (term241 A y x r s).
Proof. exact (MK_COMB (@lem4808151) (@lem4808150 A y x r s)). Qed.
Lemma lem4808153 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term190 A y x r s) = (term242 A y x r s).
Proof. exact (MK_COMB (@lem4808152 A y x r s) (@lem4808081 A x r s)). Qed.
Lemma lem4808160 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term87 A r s).
Proof. exact (eq_refl (term87 A r s)). Qed.
Lemma lem4808161 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4808168 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808169 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4808168 A (A -> Prop) f x). Qed.
Lemma lem4808170 {A : Type'} (r : type1402 A) (x : A) : (r x) = (@I (A -> A -> Prop) r x).
Proof. exact (@lem4808169 A r x). Qed.
Lemma lem4808171 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4808172 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (@I (A -> A -> Prop) r x y).
Proof. exact (MK_COMB (@lem4808170 A r x) (@lem4808171 A y)). Qed.
Lemma lem4808174 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808175 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4808174 A Prop f x). Qed.
Lemma lem4808176 {A : Type'} (r : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) r x y) = (term215 A r x y).
Proof. exact (@lem4808175 A (@I (A -> A -> Prop) r x) y). Qed.
Lemma lem4808178 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (term215 A r x y).
Proof. exact (TRANS (@lem4808172 A r x y) (@lem4808176 A r x y)). Qed.
Lemma lem4808179 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term216 A r x y) = (term217 A r x y).
Proof. exact (MK_COMB (@lem4808161) (@lem4808178 A r x y)). Qed.
Lemma lem4808196 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term67 A s y x) = (term67 A s y x).
Proof. exact (eq_refl (term67 A s y x)). Qed.
Lemma lem4808197 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term96 A s r x y) = (term243 A s r x y).
Proof. exact (MK_COMB (@lem4808196 A s y x) (@lem4808179 A r x y)). Qed.
Lemma lem4808198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4808199 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term138 A s r x y) = (term244 A s r x y).
Proof. exact (MK_COMB (@lem4808198) (@lem4808197 A s r x y)). Qed.
Lemma lem4808200 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term140 A x y r s) = (term245 A x y r s).
Proof. exact (MK_COMB (@lem4808199 A s r x y) (@lem4808160 A r s)). Qed.
Lemma lem4808205 {A : Type'} (r : type1402 A) (s : A -> Prop) : (@pairwise A r s) = (@pairwise A r s).
Proof. exact (eq_refl (@pairwise A r s)). Qed.
Lemma lem4808212 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808213 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4808212 A (A -> Prop) f x). Qed.
Lemma lem4808214 {A : Type'} (r : type1402 A) (y : A) : (r y) = (@I (A -> A -> Prop) r y).
Proof. exact (@lem4808213 A r y). Qed.
Lemma lem4808215 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4808216 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (@I (A -> A -> Prop) r y x).
Proof. exact (MK_COMB (@lem4808214 A r y) (@lem4808215 A x)). Qed.
Lemma lem4808218 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808219 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4808218 A Prop f x). Qed.
Lemma lem4808220 {A : Type'} (r : type1402 A) (y : A) (x : A) : (@I (A -> A -> Prop) r y x) = (term215 A r y x).
Proof. exact (@lem4808219 A (@I (A -> A -> Prop) r y) x). Qed.
Lemma lem4808222 {A : Type'} (r : type1402 A) (y : A) (x : A) : (r y x) = (term215 A r y x).
Proof. exact (TRANS (@lem4808216 A r y x) (@lem4808220 A r y x)). Qed.
Lemma lem4808229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808230 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4808229 A (A -> Prop) f x). Qed.
Lemma lem4808231 {A : Type'} (r : type1402 A) (x : A) : (r x) = (@I (A -> A -> Prop) r x).
Proof. exact (@lem4808230 A r x). Qed.
Lemma lem4808232 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4808233 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (@I (A -> A -> Prop) r x y).
Proof. exact (MK_COMB (@lem4808231 A r x) (@lem4808232 A y)). Qed.
Lemma lem4808235 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4808236 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4808235 A Prop f x). Qed.
Lemma lem4808237 {A : Type'} (r : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) r x y) = (term215 A r x y).
Proof. exact (@lem4808236 A (@I (A -> A -> Prop) r x) y). Qed.
Lemma lem4808239 {A : Type'} (r : type1402 A) (x : A) (y : A) : (r x y) = (term215 A r x y).
Proof. exact (TRANS (@lem4808233 A r x y) (@lem4808237 A r x y)). Qed.
Lemma lem4808240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4808241 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term246 A r x y) = (term247 A r x y).
Proof. exact (MK_COMB (@lem4808240) (@lem4808239 A r x y)). Qed.
Lemma lem4808242 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term66 A r y x) = (term248 A r y x).
Proof. exact (MK_COMB (@lem4808241 A r x y) (@lem4808222 A r y x)). Qed.
Lemma lem4808259 {A : Type'} (s : A -> Prop) (y : A) (x : A) : (term73 A s y x) = (term73 A s y x).
Proof. exact (eq_refl (term73 A s y x)). Qed.
Lemma lem4808260 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term75 A s r y x) = (term249 A s r y x).
Proof. exact (MK_COMB (@lem4808259 A s y x) (@lem4808242 A r y x)). Qed.
Lemma lem4808261 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term85 A s r x) = (term250 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4808260 A s r y x)). Qed.
Lemma lem4808262 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4808263 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term86 A s r x) = (term251 A s r x).
Proof. exact (MK_COMB (@lem4808262 A) (@lem4808261 A s r x)). Qed.
Lemma lem4808264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4808265 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term93 A s r x) = (term252 A s r x).
Proof. exact (MK_COMB (@lem4808264) (@lem4808263 A s r x)). Qed.
Lemma lem4808266 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term94 A x r s) = (term253 A x r s).
Proof. exact (MK_COMB (@lem4808265 A s r x) (@lem4808205 A r s)). Qed.
Lemma lem4808267 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4808268 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : (term120 A x r s) = (term254 A x r s).
Proof. exact (MK_COMB (@lem4808267) (@lem4808266 A x r s)). Qed.
Lemma lem4808269 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term155 A x y r s) = (term255 A x y r s).
Proof. exact (MK_COMB (@lem4808268 A x r s) (@lem4808200 A x y r s)). Qed.
Lemma lem4808270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4808271 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) : (term209 A x y r s) = (term256 A x y r s).
Proof. exact (MK_COMB (@lem4808270) (@lem4808269 A x y r s)). Qed.
Lemma lem4808272 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) : (term211 A y x r s) = (term257 A y x r s).
Proof. exact (MK_COMB (@lem4808271 A x y r s) (@lem4808153 A y x r s)). Qed.
Lemma lem4808273 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term211 A y x r s) : term257 A y x r s.
Proof. exact (EQ_MP (@lem4808272 A y x r s) (@lem4807940 A y x r s h1)). Qed.
Lemma lem4808274 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term255 A x y r s.
Proof. exact (h1). Qed.
Lemma lem4808275 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term242 A y x r s.
Proof. exact (h1). Qed.
Lemma lem4808276 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term245 A x y r s.
Proof. exact (proj2 (@lem4808274 A x y r s h1)). Qed.
Lemma lem4808277 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term253 A x r s.
Proof. exact (proj1 (@lem4808274 A x y r s h1)). Qed.
Lemma lem4808279 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term251 A s r x.
Proof. exact (proj1 (@lem4808277 A x y r s h1)). Qed.
Lemma lem4808280 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term243 A s r x y.
Proof. exact (h1). Qed.
Lemma lem4808283 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term71 A s y x.
Proof. exact (proj1 (@lem4808280 A s r x y h1)). Qed.
Lemma lem4808286 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term236 A x r s.
Proof. exact (proj2 (@lem4808275 A y x r s h1)). Qed.
Lemma lem4808287 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term240 A y x r s.
Proof. exact (proj1 (@lem4808275 A y x r s h1)). Qed.
Lemma lem4808289 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term234 A s r x.
Proof. exact (proj1 (@lem4808286 A y x r s h1)). Qed.
Lemma lem4808290 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term238 A s r y x.
Proof. exact (h1). Qed.
Lemma lem4808292 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term237 A r y x.
Proof. exact (proj2 (@lem4808290 A s r y x h1)). Qed.
Lemma lem4808293 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term71 A s y x.
Proof. exact (proj1 (@lem4808290 A s r y x h1)). Qed.
Lemma lem4808356 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term249 A s r y x) = (term258 A s r y x).
Proof. exact (@lem19490 (term215 A r x y) (term61 A s y x) (term215 A r y x)). Qed.
Lemma lem4808357 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term250 A s r x) = (term259 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4808356 A s r y x)). Qed.
Lemma lem4808358 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4808360 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term251 A s r x) = (term260 A s r x).
Proof. exact (MK_COMB (@lem4808358 A) (@lem4808357 A s r x)). Qed.
Lemma lem4808361 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term260 A s r x.
Proof. exact (EQ_MP (@lem4808360 A s r x) (@lem4808279 A x y r s h1)). Qed.
Lemma lem4808449 {A : Type'} (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) : term87 A r s.
Proof. exact (h1). Qed.
Lemma lem4808498 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term232 A s r x y) = (term232 A s r x y).
Proof. exact (eq_refl (term232 A s r x y)). Qed.
Lemma lem4808499 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term233 A s r x) = (term233 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4808498 A s r x y)). Qed.
Lemma lem4808500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4808502 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term234 A s r x) = (term234 A s r x).
Proof. exact (MK_COMB (@lem4808500 A) (@lem4808499 A s r x)). Qed.
Lemma lem4808503 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term234 A s r x.
Proof. exact (EQ_MP (@lem4808502 A s r x) (@lem4808289 A y x r s h1)). Qed.
Lemma lem4808519 {A : Type'} (r : type1402 A) (x : A) (y : A) (h1 : term217 A r x y) : term217 A r x y.
Proof. exact (h1). Qed.
Lemma lem4808549 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) : (term229 A s r y x) = (term261 A s r y x).
Proof. exact (@lem19490 (term225 A r y x) (term262 A y s) (term221 A r y x)). Qed.
Lemma lem4808550 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term230 A s r x) = (term263 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4808549 A s r y x)). Qed.
Lemma lem4808551 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4808553 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term231 A s r x) = (term264 A s r x).
Proof. exact (MK_COMB (@lem4808551 A) (@lem4808550 A s r x)). Qed.
Lemma lem4808554 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term264 A s r x.
Proof. exact (EQ_MP (@lem4808553 A s r x) (@lem4808035 A s r x h1)). Qed.
Lemma lem4808568 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) : (term232 A s r x y) = (term232 A s r x y).
Proof. exact (eq_refl (term232 A s r x y)). Qed.
Lemma lem4808569 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term233 A s r x) = (term233 A s r x).
Proof. exact (fun_ext (fun y : A => @lem4808568 A s r x y)). Qed.
Lemma lem4808570 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4808572 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) : (term234 A s r x) = (term234 A s r x).
Proof. exact (MK_COMB (@lem4808570 A) (@lem4808569 A s r x)). Qed.
Lemma lem4808573 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term234 A s r x.
Proof. exact (EQ_MP (@lem4808572 A s r x) (@lem4808289 A y x r s h1)). Qed.
Lemma lem4808589 {A : Type'} (r : type1402 A) (y : A) (x : A) (h1 : term217 A r y x) : term217 A r y x.
Proof. exact (h1). Qed.
Lemma lem4808651 {A : Type'} (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) : term87 A r s.
Proof. exact (h1). Qed.
Lemma lem4808655 {A : Type'} (_59559 : A) (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term265 A s r x _59559.
Proof. exact (@lem4808361 A x y r s h1 _59559). Qed.
Lemma lem4808656 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59559 : A) (x : A) : (term265 A s r x _59559) = (term258 A s r _59559 x).
Proof. exact (eq_refl (term265 A s r x _59559)). Qed.
Lemma lem4808657 {A : Type'} (_59559 : A) (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term258 A s r _59559 x.
Proof. exact (EQ_MP (@lem4808656 A s r _59559 x) (@lem4808655 A _59559 x y r s h1)). Qed.
Lemma lem4808667 {A : Type'} (_59563 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term266 A s r x _59563.
Proof. exact (@lem4808503 A y x r s h1 _59563). Qed.
Lemma lem4808668 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59563 : A) : (term266 A s r x _59563) = (term232 A s r x _59563).
Proof. exact (eq_refl (term266 A s r x _59563)). Qed.
Lemma lem4808669 {A : Type'} (_59563 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term232 A s r x _59563.
Proof. exact (EQ_MP (@lem4808668 A s r x _59563) (@lem4808667 A _59563 y x r s h1)). Qed.
Lemma lem4808670 {A : Type'} (_59564 : A) (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term267 A s r x _59564.
Proof. exact (@lem4808554 A s r x h1 _59564). Qed.
Lemma lem4808671 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59564 : A) (x : A) : (term267 A s r x _59564) = (term261 A s r _59564 x).
Proof. exact (eq_refl (term267 A s r x _59564)). Qed.
Lemma lem4808672 {A : Type'} (_59564 : A) (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term261 A s r _59564 x.
Proof. exact (EQ_MP (@lem4808671 A s r _59564 x) (@lem4808670 A _59564 s r x h1)). Qed.
Lemma lem4808673 {A : Type'} (_59565 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term266 A s r x _59565.
Proof. exact (@lem4808573 A y x r s h1 _59565). Qed.
Lemma lem4808674 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59565 : A) : (term266 A s r x _59565) = (term232 A s r x _59565).
Proof. exact (eq_refl (term266 A s r x _59565)). Qed.
Lemma lem4808675 {A : Type'} (_59565 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term232 A s r x _59565.
Proof. exact (EQ_MP (@lem4808674 A s r x _59565) (@lem4808673 A _59565 y x r s h1)). Qed.
Lemma lem4808683 {A : Type'} (_59559 : A) (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term232 A s r x _59559.
Proof. exact (proj1 (@lem4808657 A _59559 x y r s h1)). Qed.
Lemma lem4808703 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term63 A y x.
Proof. exact (proj2 (@lem4808283 A s r x y h1)). Qed.
Lemma lem4808714 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : (term232 A s r x _59559) = (term268 A s r x _59559).
Proof. exact (@lem4807117 (term262 A _59559 s) (_59559 = x) (term215 A r x _59559)). Qed.
Lemma lem4808715 {A : Type'} (_59559 : A) (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term268 A s r x _59559.
Proof. exact (EQ_MP (@lem4808714 A s r x _59559) (@lem4808683 A _59559 x y r s h1)). Qed.
Lemma lem4808751 {A : Type'} (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) : term87 A r s.
Proof. exact (h1). Qed.
Lemma lem4808806 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59563 : A) : (term232 A s r x _59563) = (term268 A s r x _59563).
Proof. exact (@lem4807117 (term262 A _59563 s) (_59563 = x) (term215 A r x _59563)). Qed.
Lemma lem4808807 {A : Type'} (_59563 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term268 A s r x _59563.
Proof. exact (EQ_MP (@lem4808806 A s r x _59563) (@lem4808669 A _59563 y x r s h1)). Qed.
Lemma lem4808815 {A : Type'} (r : type1402 A) (x : A) (y : A) (h1 : term217 A r x y) : term217 A r x y.
Proof. exact (h1). Qed.
Lemma lem4808846 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59565 : A) : (term232 A s r x _59565) = (term268 A s r x _59565).
Proof. exact (@lem4807117 (term262 A _59565 s) (_59565 = x) (term215 A r x _59565)). Qed.
Lemma lem4808847 {A : Type'} (_59565 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term268 A s r x _59565.
Proof. exact (EQ_MP (@lem4808846 A s r x _59565) (@lem4808675 A _59565 y x r s h1)). Qed.
Lemma lem4808855 {A : Type'} (r : type1402 A) (y : A) (x : A) (h1 : term217 A r y x) : term217 A r y x.
Proof. exact (h1). Qed.
Lemma lem4808875 {A : Type'} (_59564 : A) (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term269 A s r _59564 x.
Proof. exact (proj2 (@lem4808672 A _59564 s r x h1)). Qed.
Lemma lem4808891 {A : Type'} (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) : term87 A r s.
Proof. exact (h1). Qed.
Lemma lem4808991 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : @IN A y s.
Proof. exact (proj1 (@lem4808283 A s r x y h1)). Qed.
Lemma lem4808992 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term270 A y s.
Proof. exact (fun h0 : term262 A y s => @lem4808991 A s r x y h1). Qed.
Lemma lem4808994 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4808995 {A : Type'} (y : A) (s : A -> Prop) : (term270 A y s) = (@IN A y s).
Proof. exact (@lem4808994 (@IN A y s)). Qed.
Lemma lem4808996 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : @IN A y s.
Proof. exact (EQ_MP (@lem4808995 A y s) (@lem4808992 A s r x y h1)). Qed.
Lemma lem4808998 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term217 A r x y.
Proof. exact (proj2 (@lem4808280 A s r x y h1)). Qed.
Lemma lem4808999 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term272 A r x y.
Proof. exact (fun h0 : term215 A r x y => @lem4808998 A s r x y h1). Qed.
Lemma lem4809001 (p : Prop) : (term273 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4809002 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term272 A r x y) = (term217 A r x y).
Proof. exact (@lem4809001 (term215 A r x y)). Qed.
Lemma lem4809003 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term217 A r x y.
Proof. exact (EQ_MP (@lem4809002 A r x y) (@lem4808999 A s r x y h1)). Qed.
Lemma lem4809009 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4809010 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : (term268 A s r x _59559) = (term274 A s r x _59559).
Proof. exact (@lem4809009 (_59559 = x) (term262 A _59559 s) (term215 A r x _59559)). Qed.
Lemma lem4809026 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809027 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : (term275 A s r x _59559) = (term276 A r x _59559 s).
Proof. exact (@lem4809026 (term215 A r x _59559) (term262 A _59559 s)). Qed.
Lemma lem4809033 {A : Type'} (_59559 : A) (x : A) : (term277 A _59559 x) = (term277 A _59559 x).
Proof. exact (eq_refl (term277 A _59559 x)). Qed.
Lemma lem4809034 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : (term274 A s r x _59559) = (term278 A r x _59559 s).
Proof. exact (MK_COMB (@lem4809033 A _59559 x) (@lem4809027 A r x _59559 s)). Qed.
Lemma lem4809045 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : (term268 A s r x _59559) = (term278 A r x _59559 s).
Proof. exact (TRANS (@lem4809010 A s r x _59559) (@lem4809034 A r x _59559 s)). Qed.
Lemma lem4809046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4809047 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : (term279 A s r x _59559) = (term280 A r x _59559 s).
Proof. exact (MK_COMB (@lem4809046) (@lem4809045 A r x _59559 s)). Qed.
Lemma lem4809063 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809064 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : (term275 A s r x _59559) = (term276 A r x _59559 s).
Proof. exact (@lem4809063 (term215 A r x _59559) (term262 A _59559 s)). Qed.
Lemma lem4809070 {A : Type'} (_59559 : A) (x : A) : (term277 A _59559 x) = (term277 A _59559 x).
Proof. exact (eq_refl (term277 A _59559 x)). Qed.
Lemma lem4809071 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : (term274 A s r x _59559) = (term278 A r x _59559 s).
Proof. exact (MK_COMB (@lem4809070 A _59559 x) (@lem4809064 A r x _59559 s)). Qed.
Lemma lem4809082 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : ((term268 A s r x _59559) = (term274 A s r x _59559)) = ((term278 A r x _59559 s) = (term278 A r x _59559 s)).
Proof. exact (MK_COMB (@lem4809047 A r x _59559 s) (@lem4809071 A r x _59559 s)). Qed.
Lemma lem4809084 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4809085 (x : Prop) : (x = x) = True.
Proof. exact (@lem4809084 Prop x). Qed.
Lemma lem4809086 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) (s : A -> Prop) : ((term278 A r x _59559 s) = (term278 A r x _59559 s)) = True.
Proof. exact (@lem4809085 (term278 A r x _59559 s)). Qed.
Lemma lem4809087 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : ((term268 A s r x _59559) = (term274 A s r x _59559)) = True.
Proof. exact (TRANS (@lem4809082 A r x _59559 s) (@lem4809086 A r x _59559 s)). Qed.
Lemma lem4809088 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : True = ((term268 A s r x _59559) = (term274 A s r x _59559)).
Proof. exact (SYM (@lem4809087 A s r x _59559)). Qed.
Lemma lem4809089 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : (term268 A s r x _59559) = (term274 A s r x _59559).
Proof. exact (EQ_MP (@lem4809088 A s r x _59559) (@lem0)). Qed.
Lemma lem4809090 {A : Type'} (_59559 : A) (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term274 A s r x _59559.
Proof. exact (EQ_MP (@lem4809089 A s r x _59559) (@lem4808715 A _59559 x y r s h1)). Qed.
Lemma lem4809092 (b : Prop) (a : Prop) : (a \/ b) = (term281 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4809093 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59559 : A) (x : A) : (term274 A s r x _59559) = (term282 A s r _59559 x).
Proof. exact (@lem4809092 (term275 A s r x _59559) (_59559 = x)). Qed.
Lemma lem4809095 (a : Prop) (b : Prop) : (term283 a b) = (term284 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4809096 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : (term285 A s r x _59559) = (term286 A s r x _59559).
Proof. exact (@lem4809095 (term262 A _59559 s) (term215 A r x _59559)). Qed.
Lemma lem4809098 (a : Prop) : (term39 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4809099 {A : Type'} (_59559 : A) (s : A -> Prop) : (term287 A _59559 s) = (@IN A _59559 s).
Proof. exact (@lem4809098 (@IN A _59559 s)). Qed.
Lemma lem4809100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4809101 {A : Type'} (_59559 : A) (s : A -> Prop) : (term288 A _59559 s) = (term289 A _59559 s).
Proof. exact (MK_COMB (@lem4809100) (@lem4809099 A _59559 s)). Qed.
Lemma lem4809102 {A : Type'} (r : type1402 A) (x : A) (_59559 : A) : (term217 A r x _59559) = (term217 A r x _59559).
Proof. exact (eq_refl (term217 A r x _59559)). Qed.
Lemma lem4809103 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : (term286 A s r x _59559) = (term290 A s r x _59559).
Proof. exact (MK_COMB (@lem4809101 A _59559 s) (@lem4809102 A r x _59559)). Qed.
Lemma lem4809104 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : (term285 A s r x _59559) = (term290 A s r x _59559).
Proof. exact (TRANS (@lem4809096 A s r x _59559) (@lem4809103 A s r x _59559)). Qed.
Lemma lem4809105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4809106 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59559 : A) : (term291 A s r x _59559) = (term292 A s r x _59559).
Proof. exact (MK_COMB (@lem4809105) (@lem4809104 A s r x _59559)). Qed.
Lemma lem4809107 {A : Type'} (_59559 : A) (x : A) : (_59559 = x) = (_59559 = x).
Proof. exact (eq_refl (_59559 = x)). Qed.
Lemma lem4809108 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59559 : A) (x : A) : (term282 A s r _59559 x) = (term293 A s r _59559 x).
Proof. exact (MK_COMB (@lem4809106 A s r x _59559) (@lem4809107 A _59559 x)). Qed.
Lemma lem4809109 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59559 : A) (x : A) : (term274 A s r x _59559) = (term293 A s r _59559 x).
Proof. exact (TRANS (@lem4809093 A s r _59559 x) (@lem4809108 A s r _59559 x)). Qed.
Lemma lem4809111 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term290 A s r x y.
Proof. exact (conj (@lem4808996 A s r x y h1) (@lem4809003 A s r x y h1)). Qed.
Lemma lem4809113 {A : Type'} (_59559 : A) (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term293 A s r _59559 x.
Proof. exact (EQ_MP (@lem4809109 A s r _59559 x) (@lem4809090 A _59559 x y r s h1)). Qed.
Lemma lem4809114 {A : Type'} (_59559 : A) (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term293 A s r _59559 x.
Proof. exact (@lem4809113 A _59559 x y r s h1). Qed.
Lemma lem4809115 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term293 A s r y x.
Proof. exact (@lem4809114 A y x y r s h1). Qed.
Lemma lem4809118 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term255 A x y r s) (h2 : term243 A s r x y) : y = x.
Proof. exact (@lem4809115 A x y r s h1 (@lem4809111 A s r x y h2)). Qed.
Lemma lem4809119 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term255 A x y r s) (h2 : term243 A s r x y) : term294 A y x.
Proof. exact (fun h0 : term63 A y x => @lem4809118 A s r x y h1 h2). Qed.
Lemma lem4809121 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809122 {A : Type'} (y : A) (x : A) : (term294 A y x) = (y = x).
Proof. exact (@lem4809121 (y = x)). Qed.
Lemma lem4809123 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term255 A x y r s) (h2 : term243 A s r x y) : y = x.
Proof. exact (EQ_MP (@lem4809122 A y x) (@lem4809119 A s r x y h1 h2)). Qed.
Lemma lem4809126 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4809128 {A : Type'} (y : A) (x : A) : (term63 A y x) = (term295 A y x).
Proof. exact (@lem4809126 (y = x)). Qed.
Lemma lem4809131 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term243 A s r x y) : term295 A y x.
Proof. exact (EQ_MP (@lem4809128 A y x) (@lem4808703 A s r x y h1)). Qed.
Lemma lem4809134 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term255 A x y r s) (h2 : term243 A s r x y) : False.
Proof. exact (@lem4809131 A s r x y h2 (@lem4809123 A s r x y h1 h2)). Qed.
Lemma lem4809135 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term255 A x y r s) (h2 : term243 A s r x y) : term296.
Proof. exact (fun h0 : ~ False => @lem4809134 A s r x y h1 h2). Qed.
Lemma lem4809137 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809138 : term296 = False.
Proof. exact (@lem4809137 False). Qed.
Lemma lem4809139 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (y : A) (h1 : term255 A x y r s) (h2 : term243 A s r x y) : False.
Proof. exact (EQ_MP (@lem4809138) (@lem4809135 A s r x y h1 h2)). Qed.
Lemma lem4809219 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : @pairwise A r s.
Proof. exact (proj2 (@lem4808277 A x y r s h1)). Qed.
Lemma lem4809220 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : term297 A r s.
Proof. exact (fun h0 : term87 A r s => @lem4809219 A x y r s h1). Qed.
Lemma lem4809222 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809223 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term297 A r s) = (@pairwise A r s).
Proof. exact (@lem4809222 (@pairwise A r s)). Qed.
Lemma lem4809224 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : @pairwise A r s.
Proof. exact (EQ_MP (@lem4809223 A r s) (@lem4809220 A x y r s h1)). Qed.
Lemma lem4809227 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4809229 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term298 A r s).
Proof. exact (@lem4809227 (@pairwise A r s)). Qed.
Lemma lem4809232 {A : Type'} (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) : term298 A r s.
Proof. exact (EQ_MP (@lem4809229 A r s) (@lem4808751 A r s h1)). Qed.
Lemma lem4809235 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : False.
Proof. exact (@lem4809232 A r s h1 (@lem4809224 A x y r s h2)). Qed.
Lemma lem4809236 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : term296.
Proof. exact (fun h0 : ~ False => @lem4809235 A x y r s h1 h2). Qed.
Lemma lem4809238 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809239 : term296 = False.
Proof. exact (@lem4809238 False). Qed.
Lemma lem4809240 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : False.
Proof. exact (EQ_MP (@lem4809239) (@lem4809236 A x y r s h1 h2)). Qed.
Lemma lem4809320 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : @IN A y s.
Proof. exact (proj1 (@lem4808293 A s r y x h1)). Qed.
Lemma lem4809321 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term270 A y s.
Proof. exact (fun h0 : term262 A y s => @lem4809320 A s r y x h1). Qed.
Lemma lem4809323 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809324 {A : Type'} (y : A) (s : A -> Prop) : (term270 A y s) = (@IN A y s).
Proof. exact (@lem4809323 (@IN A y s)). Qed.
Lemma lem4809325 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : @IN A y s.
Proof. exact (EQ_MP (@lem4809324 A y s) (@lem4809321 A s r y x h1)). Qed.
Lemma lem4809327 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term63 A y x.
Proof. exact (proj2 (@lem4808293 A s r y x h1)). Qed.
Lemma lem4809328 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term299 A y x.
Proof. exact (fun h0 : y = x => @lem4809327 A s r y x h1). Qed.
Lemma lem4809330 (p : Prop) : (term273 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4809331 {A : Type'} (y : A) (x : A) : (term299 A y x) = (term63 A y x).
Proof. exact (@lem4809330 (y = x)). Qed.
Lemma lem4809332 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term63 A y x.
Proof. exact (EQ_MP (@lem4809331 A y x) (@lem4809328 A s r y x h1)). Qed.
Lemma lem4809338 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4809339 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59563 : A) : (term268 A s r x _59563) = (term274 A s r x _59563).
Proof. exact (@lem4809338 (_59563 = x) (term262 A _59563 s) (term215 A r x _59563)). Qed.
Lemma lem4809355 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809356 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : (term275 A s r x _59563) = (term276 A r x _59563 s).
Proof. exact (@lem4809355 (term215 A r x _59563) (term262 A _59563 s)). Qed.
Lemma lem4809362 {A : Type'} (_59563 : A) (x : A) : (term277 A _59563 x) = (term277 A _59563 x).
Proof. exact (eq_refl (term277 A _59563 x)). Qed.
Lemma lem4809363 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : (term274 A s r x _59563) = (term278 A r x _59563 s).
Proof. exact (MK_COMB (@lem4809362 A _59563 x) (@lem4809356 A r x _59563 s)). Qed.
Lemma lem4809374 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : (term268 A s r x _59563) = (term278 A r x _59563 s).
Proof. exact (TRANS (@lem4809339 A s r x _59563) (@lem4809363 A r x _59563 s)). Qed.
Lemma lem4809375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4809376 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : (term279 A s r x _59563) = (term280 A r x _59563 s).
Proof. exact (MK_COMB (@lem4809375) (@lem4809374 A r x _59563 s)). Qed.
Lemma lem4809390 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809391 {A : Type'} (x : A) (_59563 : A) (s : A -> Prop) : (term61 A s _59563 x) = (term300 A x _59563 s).
Proof. exact (@lem4809390 (_59563 = x) (term262 A _59563 s)). Qed.
Lemma lem4809399 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) : (term223 A r x _59563) = (term223 A r x _59563).
Proof. exact (eq_refl (term223 A r x _59563)). Qed.
Lemma lem4809400 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : (term301 A r s _59563 x) = (term302 A r x _59563 s).
Proof. exact (MK_COMB (@lem4809399 A r x _59563) (@lem4809391 A x _59563 s)). Qed.
Lemma lem4809404 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4809405 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : (term302 A r x _59563 s) = (term278 A r x _59563 s).
Proof. exact (@lem4809404 (_59563 = x) (term215 A r x _59563) (term262 A _59563 s)). Qed.
Lemma lem4809423 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : (term301 A r s _59563 x) = (term278 A r x _59563 s).
Proof. exact (TRANS (@lem4809400 A r x _59563 s) (@lem4809405 A r x _59563 s)). Qed.
Lemma lem4809424 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : ((term268 A s r x _59563) = (term301 A r s _59563 x)) = ((term278 A r x _59563 s) = (term278 A r x _59563 s)).
Proof. exact (MK_COMB (@lem4809376 A r x _59563 s) (@lem4809423 A r x _59563 s)). Qed.
Lemma lem4809426 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4809427 (x : Prop) : (x = x) = True.
Proof. exact (@lem4809426 Prop x). Qed.
Lemma lem4809428 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) (s : A -> Prop) : ((term278 A r x _59563 s) = (term278 A r x _59563 s)) = True.
Proof. exact (@lem4809427 (term278 A r x _59563 s)). Qed.
Lemma lem4809429 {A : Type'} (r : type1402 A) (s : A -> Prop) (_59563 : A) (x : A) : ((term268 A s r x _59563) = (term301 A r s _59563 x)) = True.
Proof. exact (TRANS (@lem4809424 A r x _59563 s) (@lem4809428 A r x _59563 s)). Qed.
Lemma lem4809430 {A : Type'} (r : type1402 A) (s : A -> Prop) (_59563 : A) (x : A) : True = ((term268 A s r x _59563) = (term301 A r s _59563 x)).
Proof. exact (SYM (@lem4809429 A r s _59563 x)). Qed.
Lemma lem4809431 {A : Type'} (r : type1402 A) (s : A -> Prop) (_59563 : A) (x : A) : (term268 A s r x _59563) = (term301 A r s _59563 x).
Proof. exact (EQ_MP (@lem4809430 A r s _59563 x) (@lem0)). Qed.
Lemma lem4809432 {A : Type'} (_59563 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term301 A r s _59563 x.
Proof. exact (EQ_MP (@lem4809431 A r s _59563 x) (@lem4808807 A _59563 y x r s h1)). Qed.
Lemma lem4809434 (b : Prop) (a : Prop) : (a \/ b) = (term281 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4809435 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59563 : A) : (term301 A r s _59563 x) = (term303 A s r x _59563).
Proof. exact (@lem4809434 (term61 A s _59563 x) (term215 A r x _59563)). Qed.
Lemma lem4809437 (a : Prop) (b : Prop) : (term283 a b) = (term284 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4809438 {A : Type'} (s : A -> Prop) (_59563 : A) (x : A) : (term304 A s _59563 x) = (term305 A s _59563 x).
Proof. exact (@lem4809437 (term262 A _59563 s) (_59563 = x)). Qed.
Lemma lem4809440 (a : Prop) : (term39 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4809441 {A : Type'} (_59563 : A) (s : A -> Prop) : (term287 A _59563 s) = (@IN A _59563 s).
Proof. exact (@lem4809440 (@IN A _59563 s)). Qed.
Lemma lem4809442 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4809443 {A : Type'} (_59563 : A) (s : A -> Prop) : (term288 A _59563 s) = (term289 A _59563 s).
Proof. exact (MK_COMB (@lem4809442) (@lem4809441 A _59563 s)). Qed.
Lemma lem4809444 {A : Type'} (_59563 : A) (x : A) : (term63 A _59563 x) = (term63 A _59563 x).
Proof. exact (eq_refl (term63 A _59563 x)). Qed.
Lemma lem4809445 {A : Type'} (s : A -> Prop) (_59563 : A) (x : A) : (term305 A s _59563 x) = (term71 A s _59563 x).
Proof. exact (MK_COMB (@lem4809443 A _59563 s) (@lem4809444 A _59563 x)). Qed.
Lemma lem4809446 {A : Type'} (s : A -> Prop) (_59563 : A) (x : A) : (term304 A s _59563 x) = (term71 A s _59563 x).
Proof. exact (TRANS (@lem4809438 A s _59563 x) (@lem4809445 A s _59563 x)). Qed.
Lemma lem4809447 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4809448 {A : Type'} (s : A -> Prop) (_59563 : A) (x : A) : (term306 A s _59563 x) = (term307 A s _59563 x).
Proof. exact (MK_COMB (@lem4809447) (@lem4809446 A s _59563 x)). Qed.
Lemma lem4809449 {A : Type'} (r : type1402 A) (x : A) (_59563 : A) : (term215 A r x _59563) = (term215 A r x _59563).
Proof. exact (eq_refl (term215 A r x _59563)). Qed.
Lemma lem4809450 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59563 : A) : (term303 A s r x _59563) = (term308 A s r x _59563).
Proof. exact (MK_COMB (@lem4809448 A s _59563 x) (@lem4809449 A r x _59563)). Qed.
Lemma lem4809451 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59563 : A) : (term301 A r s _59563 x) = (term308 A s r x _59563).
Proof. exact (TRANS (@lem4809435 A s r x _59563) (@lem4809450 A s r x _59563)). Qed.
Lemma lem4809453 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term71 A s y x.
Proof. exact (conj (@lem4809325 A s r y x h1) (@lem4809332 A s r y x h1)). Qed.
Lemma lem4809455 {A : Type'} (_59563 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term308 A s r x _59563.
Proof. exact (EQ_MP (@lem4809451 A s r x _59563) (@lem4809432 A _59563 y x r s h1)). Qed.
Lemma lem4809456 {A : Type'} (_59563 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term308 A s r x _59563.
Proof. exact (@lem4809455 A _59563 y x r s h1). Qed.
Lemma lem4809457 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term308 A s r x y.
Proof. exact (@lem4809456 A y y x r s h1). Qed.
Lemma lem4809460 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term238 A s r y x) (h2 : term242 A y x r s) : term215 A r x y.
Proof. exact (@lem4809457 A y x r s h2 (@lem4809453 A s r y x h1)). Qed.
Lemma lem4809461 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term238 A s r y x) (h2 : term242 A y x r s) : term309 A r x y.
Proof. exact (fun h0 : term217 A r x y => @lem4809460 A y x r s h1 h2). Qed.
Lemma lem4809463 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809464 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term309 A r x y) = (term215 A r x y).
Proof. exact (@lem4809463 (term215 A r x y)). Qed.
Lemma lem4809465 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term238 A s r y x) (h2 : term242 A y x r s) : term215 A r x y.
Proof. exact (EQ_MP (@lem4809464 A r x y) (@lem4809461 A y x r s h1 h2)). Qed.
Lemma lem4809468 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4809470 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term217 A r x y) = (term310 A r x y).
Proof. exact (@lem4809468 (term215 A r x y)). Qed.
Lemma lem4809473 {A : Type'} (r : type1402 A) (x : A) (y : A) (h1 : term217 A r x y) : term310 A r x y.
Proof. exact (EQ_MP (@lem4809470 A r x y) (@lem4808815 A r x y h1)). Qed.
Lemma lem4809476 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : False.
Proof. exact (@lem4809473 A r x y h1 (@lem4809465 A y x r s h2 h3)). Qed.
Lemma lem4809477 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : term296.
Proof. exact (fun h0 : ~ False => @lem4809476 A y x r s h1 h2 h3). Qed.
Lemma lem4809479 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809480 : term296 = False.
Proof. exact (@lem4809479 False). Qed.
Lemma lem4809481 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809480) (@lem4809477 A y x r s h1 h2 h3)). Qed.
Lemma lem4809561 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : @IN A y s.
Proof. exact (proj1 (@lem4808293 A s r y x h1)). Qed.
Lemma lem4809562 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term270 A y s.
Proof. exact (fun h0 : term262 A y s => @lem4809561 A s r y x h1). Qed.
Lemma lem4809564 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809565 {A : Type'} (y : A) (s : A -> Prop) : (term270 A y s) = (@IN A y s).
Proof. exact (@lem4809564 (@IN A y s)). Qed.
Lemma lem4809566 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : @IN A y s.
Proof. exact (EQ_MP (@lem4809565 A y s) (@lem4809562 A s r y x h1)). Qed.
Lemma lem4809568 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : @IN A y s.
Proof. exact (proj1 (@lem4808293 A s r y x h1)). Qed.
Lemma lem4809569 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term270 A y s.
Proof. exact (fun h0 : term262 A y s => @lem4809568 A s r y x h1). Qed.
Lemma lem4809571 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809572 {A : Type'} (y : A) (s : A -> Prop) : (term270 A y s) = (@IN A y s).
Proof. exact (@lem4809571 (@IN A y s)). Qed.
Lemma lem4809573 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : @IN A y s.
Proof. exact (EQ_MP (@lem4809572 A y s) (@lem4809569 A s r y x h1)). Qed.
Lemma lem4809575 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term63 A y x.
Proof. exact (proj2 (@lem4808293 A s r y x h1)). Qed.
Lemma lem4809576 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term299 A y x.
Proof. exact (fun h0 : y = x => @lem4809575 A s r y x h1). Qed.
Lemma lem4809578 (p : Prop) : (term273 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4809579 {A : Type'} (y : A) (x : A) : (term299 A y x) = (term63 A y x).
Proof. exact (@lem4809578 (y = x)). Qed.
Lemma lem4809580 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term63 A y x.
Proof. exact (EQ_MP (@lem4809579 A y x) (@lem4809576 A s r y x h1)). Qed.
Lemma lem4809586 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4809587 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59565 : A) : (term268 A s r x _59565) = (term274 A s r x _59565).
Proof. exact (@lem4809586 (_59565 = x) (term262 A _59565 s) (term215 A r x _59565)). Qed.
Lemma lem4809603 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809604 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : (term275 A s r x _59565) = (term276 A r x _59565 s).
Proof. exact (@lem4809603 (term215 A r x _59565) (term262 A _59565 s)). Qed.
Lemma lem4809610 {A : Type'} (_59565 : A) (x : A) : (term277 A _59565 x) = (term277 A _59565 x).
Proof. exact (eq_refl (term277 A _59565 x)). Qed.
Lemma lem4809611 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : (term274 A s r x _59565) = (term278 A r x _59565 s).
Proof. exact (MK_COMB (@lem4809610 A _59565 x) (@lem4809604 A r x _59565 s)). Qed.
Lemma lem4809622 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : (term268 A s r x _59565) = (term278 A r x _59565 s).
Proof. exact (TRANS (@lem4809587 A s r x _59565) (@lem4809611 A r x _59565 s)). Qed.
Lemma lem4809623 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4809624 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : (term279 A s r x _59565) = (term280 A r x _59565 s).
Proof. exact (MK_COMB (@lem4809623) (@lem4809622 A r x _59565 s)). Qed.
Lemma lem4809638 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809639 {A : Type'} (x : A) (_59565 : A) (s : A -> Prop) : (term61 A s _59565 x) = (term300 A x _59565 s).
Proof. exact (@lem4809638 (_59565 = x) (term262 A _59565 s)). Qed.
Lemma lem4809647 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) : (term223 A r x _59565) = (term223 A r x _59565).
Proof. exact (eq_refl (term223 A r x _59565)). Qed.
Lemma lem4809648 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : (term301 A r s _59565 x) = (term302 A r x _59565 s).
Proof. exact (MK_COMB (@lem4809647 A r x _59565) (@lem4809639 A x _59565 s)). Qed.
Lemma lem4809652 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4809653 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : (term302 A r x _59565 s) = (term278 A r x _59565 s).
Proof. exact (@lem4809652 (_59565 = x) (term215 A r x _59565) (term262 A _59565 s)). Qed.
Lemma lem4809671 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : (term301 A r s _59565 x) = (term278 A r x _59565 s).
Proof. exact (TRANS (@lem4809648 A r x _59565 s) (@lem4809653 A r x _59565 s)). Qed.
Lemma lem4809672 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : ((term268 A s r x _59565) = (term301 A r s _59565 x)) = ((term278 A r x _59565 s) = (term278 A r x _59565 s)).
Proof. exact (MK_COMB (@lem4809624 A r x _59565 s) (@lem4809671 A r x _59565 s)). Qed.
Lemma lem4809674 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4809675 (x : Prop) : (x = x) = True.
Proof. exact (@lem4809674 Prop x). Qed.
Lemma lem4809676 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) (s : A -> Prop) : ((term278 A r x _59565 s) = (term278 A r x _59565 s)) = True.
Proof. exact (@lem4809675 (term278 A r x _59565 s)). Qed.
Lemma lem4809677 {A : Type'} (r : type1402 A) (s : A -> Prop) (_59565 : A) (x : A) : ((term268 A s r x _59565) = (term301 A r s _59565 x)) = True.
Proof. exact (TRANS (@lem4809672 A r x _59565 s) (@lem4809676 A r x _59565 s)). Qed.
Lemma lem4809678 {A : Type'} (r : type1402 A) (s : A -> Prop) (_59565 : A) (x : A) : True = ((term268 A s r x _59565) = (term301 A r s _59565 x)).
Proof. exact (SYM (@lem4809677 A r s _59565 x)). Qed.
Lemma lem4809679 {A : Type'} (r : type1402 A) (s : A -> Prop) (_59565 : A) (x : A) : (term268 A s r x _59565) = (term301 A r s _59565 x).
Proof. exact (EQ_MP (@lem4809678 A r s _59565 x) (@lem0)). Qed.
Lemma lem4809680 {A : Type'} (_59565 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term301 A r s _59565 x.
Proof. exact (EQ_MP (@lem4809679 A r s _59565 x) (@lem4808847 A _59565 y x r s h1)). Qed.
Lemma lem4809682 (b : Prop) (a : Prop) : (a \/ b) = (term281 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4809683 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59565 : A) : (term301 A r s _59565 x) = (term303 A s r x _59565).
Proof. exact (@lem4809682 (term61 A s _59565 x) (term215 A r x _59565)). Qed.
Lemma lem4809685 (a : Prop) (b : Prop) : (term283 a b) = (term284 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4809686 {A : Type'} (s : A -> Prop) (_59565 : A) (x : A) : (term304 A s _59565 x) = (term305 A s _59565 x).
Proof. exact (@lem4809685 (term262 A _59565 s) (_59565 = x)). Qed.
Lemma lem4809688 (a : Prop) : (term39 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4809689 {A : Type'} (_59565 : A) (s : A -> Prop) : (term287 A _59565 s) = (@IN A _59565 s).
Proof. exact (@lem4809688 (@IN A _59565 s)). Qed.
Lemma lem4809690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4809691 {A : Type'} (_59565 : A) (s : A -> Prop) : (term288 A _59565 s) = (term289 A _59565 s).
Proof. exact (MK_COMB (@lem4809690) (@lem4809689 A _59565 s)). Qed.
Lemma lem4809692 {A : Type'} (_59565 : A) (x : A) : (term63 A _59565 x) = (term63 A _59565 x).
Proof. exact (eq_refl (term63 A _59565 x)). Qed.
Lemma lem4809693 {A : Type'} (s : A -> Prop) (_59565 : A) (x : A) : (term305 A s _59565 x) = (term71 A s _59565 x).
Proof. exact (MK_COMB (@lem4809691 A _59565 s) (@lem4809692 A _59565 x)). Qed.
Lemma lem4809694 {A : Type'} (s : A -> Prop) (_59565 : A) (x : A) : (term304 A s _59565 x) = (term71 A s _59565 x).
Proof. exact (TRANS (@lem4809686 A s _59565 x) (@lem4809693 A s _59565 x)). Qed.
Lemma lem4809695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4809696 {A : Type'} (s : A -> Prop) (_59565 : A) (x : A) : (term306 A s _59565 x) = (term307 A s _59565 x).
Proof. exact (MK_COMB (@lem4809695) (@lem4809694 A s _59565 x)). Qed.
Lemma lem4809697 {A : Type'} (r : type1402 A) (x : A) (_59565 : A) : (term215 A r x _59565) = (term215 A r x _59565).
Proof. exact (eq_refl (term215 A r x _59565)). Qed.
Lemma lem4809698 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59565 : A) : (term303 A s r x _59565) = (term308 A s r x _59565).
Proof. exact (MK_COMB (@lem4809696 A s _59565 x) (@lem4809697 A r x _59565)). Qed.
Lemma lem4809699 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59565 : A) : (term301 A r s _59565 x) = (term308 A s r x _59565).
Proof. exact (TRANS (@lem4809683 A s r x _59565) (@lem4809698 A s r x _59565)). Qed.
Lemma lem4809701 {A : Type'} (s : A -> Prop) (r : type1402 A) (y : A) (x : A) (h1 : term238 A s r y x) : term71 A s y x.
Proof. exact (conj (@lem4809573 A s r y x h1) (@lem4809580 A s r y x h1)). Qed.
Lemma lem4809703 {A : Type'} (_59565 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term308 A s r x _59565.
Proof. exact (EQ_MP (@lem4809699 A s r x _59565) (@lem4809680 A _59565 y x r s h1)). Qed.
Lemma lem4809704 {A : Type'} (_59565 : A) (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term308 A s r x _59565.
Proof. exact (@lem4809703 A _59565 y x r s h1). Qed.
Lemma lem4809705 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term308 A s r x y.
Proof. exact (@lem4809704 A y y x r s h1). Qed.
Lemma lem4809708 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term238 A s r y x) (h2 : term242 A y x r s) : term215 A r x y.
Proof. exact (@lem4809705 A y x r s h2 (@lem4809701 A s r y x h1)). Qed.
Lemma lem4809709 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term238 A s r y x) (h2 : term242 A y x r s) : term309 A r x y.
Proof. exact (fun h0 : term217 A r x y => @lem4809708 A y x r s h1 h2). Qed.
Lemma lem4809711 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809712 {A : Type'} (r : type1402 A) (x : A) (y : A) : (term309 A r x y) = (term215 A r x y).
Proof. exact (@lem4809711 (term215 A r x y)). Qed.
Lemma lem4809713 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term238 A s r y x) (h2 : term242 A y x r s) : term215 A r x y.
Proof. exact (EQ_MP (@lem4809712 A r x y) (@lem4809709 A y x r s h1 h2)). Qed.
Lemma lem4809719 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4809720 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59564 : A) (x : A) : (term269 A s r _59564 x) = (term311 A s r _59564 x).
Proof. exact (@lem4809719 (term217 A r x _59564) (term262 A _59564 s) (term215 A r _59564 x)). Qed.
Lemma lem4809734 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809735 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term312 A s r _59564 x) = (term313 A r x _59564 s).
Proof. exact (@lem4809734 (term215 A r _59564 x) (term262 A _59564 s)). Qed.
Lemma lem4809741 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) : (term219 A r x _59564) = (term219 A r x _59564).
Proof. exact (eq_refl (term219 A r x _59564)). Qed.
Lemma lem4809742 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term311 A s r _59564 x) = (term314 A r x _59564 s).
Proof. exact (MK_COMB (@lem4809741 A r x _59564) (@lem4809735 A r x _59564 s)). Qed.
Lemma lem4809746 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4809747 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term314 A r x _59564 s) = (term315 A r x _59564 s).
Proof. exact (@lem4809746 (term215 A r _59564 x) (term217 A r x _59564) (term262 A _59564 s)). Qed.
Lemma lem4809763 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term311 A s r _59564 x) = (term315 A r x _59564 s).
Proof. exact (TRANS (@lem4809742 A r x _59564 s) (@lem4809747 A r x _59564 s)). Qed.
Lemma lem4809764 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term269 A s r _59564 x) = (term315 A r x _59564 s).
Proof. exact (TRANS (@lem4809720 A s r _59564 x) (@lem4809763 A r x _59564 s)). Qed.
Lemma lem4809765 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4809766 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term316 A s r _59564 x) = (term317 A r x _59564 s).
Proof. exact (MK_COMB (@lem4809765) (@lem4809764 A r x _59564 s)). Qed.
Lemma lem4809780 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4809781 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term318 A s r x _59564) = (term319 A r x _59564 s).
Proof. exact (@lem4809780 (term217 A r x _59564) (term262 A _59564 s)). Qed.
Lemma lem4809787 {A : Type'} (r : type1402 A) (_59564 : A) (x : A) : (term223 A r _59564 x) = (term223 A r _59564 x).
Proof. exact (eq_refl (term223 A r _59564 x)). Qed.
Lemma lem4809788 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : (term320 A s r x _59564) = (term315 A r x _59564 s).
Proof. exact (MK_COMB (@lem4809787 A r _59564 x) (@lem4809781 A r x _59564 s)). Qed.
Lemma lem4809799 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : ((term269 A s r _59564 x) = (term320 A s r x _59564)) = ((term315 A r x _59564 s) = (term315 A r x _59564 s)).
Proof. exact (MK_COMB (@lem4809766 A r x _59564 s) (@lem4809788 A r x _59564 s)). Qed.
Lemma lem4809801 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4809802 (x : Prop) : (x = x) = True.
Proof. exact (@lem4809801 Prop x). Qed.
Lemma lem4809803 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) (s : A -> Prop) : ((term315 A r x _59564 s) = (term315 A r x _59564 s)) = True.
Proof. exact (@lem4809802 (term315 A r x _59564 s)). Qed.
Lemma lem4809804 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59564 : A) : ((term269 A s r _59564 x) = (term320 A s r x _59564)) = True.
Proof. exact (TRANS (@lem4809799 A r x _59564 s) (@lem4809803 A r x _59564 s)). Qed.
Lemma lem4809805 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59564 : A) : True = ((term269 A s r _59564 x) = (term320 A s r x _59564)).
Proof. exact (SYM (@lem4809804 A s r x _59564)). Qed.
Lemma lem4809806 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59564 : A) : (term269 A s r _59564 x) = (term320 A s r x _59564).
Proof. exact (EQ_MP (@lem4809805 A s r x _59564) (@lem0)). Qed.
Lemma lem4809807 {A : Type'} (_59564 : A) (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term320 A s r x _59564.
Proof. exact (EQ_MP (@lem4809806 A s r x _59564) (@lem4808875 A _59564 s r x h1)). Qed.
Lemma lem4809809 (b : Prop) (a : Prop) : (a \/ b) = (term281 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4809810 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59564 : A) (x : A) : (term320 A s r x _59564) = (term321 A s r _59564 x).
Proof. exact (@lem4809809 (term318 A s r x _59564) (term215 A r _59564 x)). Qed.
Lemma lem4809812 (a : Prop) (b : Prop) : (term283 a b) = (term284 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4809813 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59564 : A) : (term322 A s r x _59564) = (term323 A s r x _59564).
Proof. exact (@lem4809812 (term262 A _59564 s) (term217 A r x _59564)). Qed.
Lemma lem4809815 (a : Prop) : (term39 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4809816 {A : Type'} (_59564 : A) (s : A -> Prop) : (term287 A _59564 s) = (@IN A _59564 s).
Proof. exact (@lem4809815 (@IN A _59564 s)). Qed.
Lemma lem4809817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4809818 {A : Type'} (_59564 : A) (s : A -> Prop) : (term288 A _59564 s) = (term289 A _59564 s).
Proof. exact (MK_COMB (@lem4809817) (@lem4809816 A _59564 s)). Qed.
Lemma lem4809820 (a : Prop) : (term39 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4809821 {A : Type'} (r : type1402 A) (x : A) (_59564 : A) : (term324 A r x _59564) = (term215 A r x _59564).
Proof. exact (@lem4809820 (term215 A r x _59564)). Qed.
Lemma lem4809822 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59564 : A) : (term323 A s r x _59564) = (term325 A s r x _59564).
Proof. exact (MK_COMB (@lem4809818 A _59564 s) (@lem4809821 A r x _59564)). Qed.
Lemma lem4809823 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59564 : A) : (term322 A s r x _59564) = (term325 A s r x _59564).
Proof. exact (TRANS (@lem4809813 A s r x _59564) (@lem4809822 A s r x _59564)). Qed.
Lemma lem4809824 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4809825 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (_59564 : A) : (term326 A s r x _59564) = (term327 A s r x _59564).
Proof. exact (MK_COMB (@lem4809824) (@lem4809823 A s r x _59564)). Qed.
Lemma lem4809826 {A : Type'} (r : type1402 A) (_59564 : A) (x : A) : (term215 A r _59564 x) = (term215 A r _59564 x).
Proof. exact (eq_refl (term215 A r _59564 x)). Qed.
Lemma lem4809827 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59564 : A) (x : A) : (term321 A s r _59564 x) = (term328 A s r _59564 x).
Proof. exact (MK_COMB (@lem4809825 A s r x _59564) (@lem4809826 A r _59564 x)). Qed.
Lemma lem4809828 {A : Type'} (s : A -> Prop) (r : type1402 A) (_59564 : A) (x : A) : (term320 A s r x _59564) = (term328 A s r _59564 x).
Proof. exact (TRANS (@lem4809810 A s r _59564 x) (@lem4809827 A s r _59564 x)). Qed.
Lemma lem4809830 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term238 A s r y x) (h2 : term242 A y x r s) : term325 A s r x y.
Proof. exact (conj (@lem4809566 A s r y x h1) (@lem4809713 A y x r s h1 h2)). Qed.
Lemma lem4809832 {A : Type'} (_59564 : A) (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term328 A s r _59564 x.
Proof. exact (EQ_MP (@lem4809828 A s r _59564 x) (@lem4809807 A _59564 s r x h1)). Qed.
Lemma lem4809833 {A : Type'} (_59564 : A) (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term328 A s r _59564 x.
Proof. exact (@lem4809832 A _59564 s r x h1). Qed.
Lemma lem4809834 {A : Type'} (y : A) (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term328 A s r y x.
Proof. exact (@lem4809833 A y s r x h1). Qed.
Lemma lem4809837 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : term215 A r y x.
Proof. exact (@lem4809834 A y s r x h1 (@lem4809830 A y x r s h2 h3)). Qed.
Lemma lem4809838 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : term309 A r y x.
Proof. exact (fun h0 : term217 A r y x => @lem4809837 A y x r s h1 h2 h3). Qed.
Lemma lem4809840 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809841 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term309 A r y x) = (term215 A r y x).
Proof. exact (@lem4809840 (term215 A r y x)). Qed.
Lemma lem4809842 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : term215 A r y x.
Proof. exact (EQ_MP (@lem4809841 A r y x) (@lem4809838 A y x r s h1 h2 h3)). Qed.
Lemma lem4809845 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4809847 {A : Type'} (r : type1402 A) (y : A) (x : A) : (term217 A r y x) = (term310 A r y x).
Proof. exact (@lem4809845 (term215 A r y x)). Qed.
Lemma lem4809850 {A : Type'} (r : type1402 A) (y : A) (x : A) (h1 : term217 A r y x) : term310 A r y x.
Proof. exact (EQ_MP (@lem4809847 A r y x) (@lem4808855 A r y x h1)). Qed.
Lemma lem4809853 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : False.
Proof. exact (@lem4809850 A r y x h2 (@lem4809842 A y x r s h1 h3 h4)). Qed.
Lemma lem4809854 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : term296.
Proof. exact (fun h0 : ~ False => @lem4809853 A y x r s h1 h2 h3 h4). Qed.
Lemma lem4809856 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809857 : term296 = False.
Proof. exact (@lem4809856 False). Qed.
Lemma lem4809858 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809857) (@lem4809854 A y x r s h1 h2 h3 h4)). Qed.
Lemma lem4809938 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : @pairwise A r s.
Proof. exact (proj2 (@lem4808286 A y x r s h1)). Qed.
Lemma lem4809939 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : term297 A r s.
Proof. exact (fun h0 : term87 A r s => @lem4809938 A y x r s h1). Qed.
Lemma lem4809941 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809942 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term297 A r s) = (@pairwise A r s).
Proof. exact (@lem4809941 (@pairwise A r s)). Qed.
Lemma lem4809943 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term242 A y x r s) : @pairwise A r s.
Proof. exact (EQ_MP (@lem4809942 A r s) (@lem4809939 A y x r s h1)). Qed.
Lemma lem4809946 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4809948 {A : Type'} (r : type1402 A) (s : A -> Prop) : (term87 A r s) = (term298 A r s).
Proof. exact (@lem4809946 (@pairwise A r s)). Qed.
Lemma lem4809951 {A : Type'} (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) : term298 A r s.
Proof. exact (EQ_MP (@lem4809948 A r s) (@lem4808891 A r s h1)). Qed.
Lemma lem4809954 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : False.
Proof. exact (@lem4809951 A r s h1 (@lem4809943 A y x r s h2)). Qed.
Lemma lem4809955 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : term296.
Proof. exact (fun h0 : ~ False => @lem4809954 A y x r s h1 h2). Qed.
Lemma lem4809957 (p : Prop) : (term271 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4809958 : term296 = False.
Proof. exact (@lem4809957 False). Qed.
Lemma lem4809959 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809958) (@lem4809955 A y x r s h1 h2)). Qed.
Lemma lem4809960 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : (term87 A r s) = False.
Proof. exact (prop_ext (fun h3 : term87 A r s => @lem4809959 A y x r s h1 h2) (fun h3 : False => @lem4808891 A r s h1)). Qed.
Lemma lem4809961 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809960 A y x r s h1 h2) (@lem4808891 A r s h1)). Qed.
Lemma lem4809962 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : (term217 A r y x) = False.
Proof. exact (prop_ext (fun h5 : term217 A r y x => @lem4809858 A y x r s h1 h2 h3 h4) (fun h5 : False => @lem4808855 A r y x h2)). Qed.
Lemma lem4809963 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809962 A y x r s h1 h2 h3 h4) (@lem4808855 A r y x h2)). Qed.
Lemma lem4809964 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : (term217 A r x y) = False.
Proof. exact (prop_ext (fun h4 : term217 A r x y => @lem4809481 A y x r s h1 h2 h3) (fun h4 : False => @lem4808815 A r x y h1)). Qed.
Lemma lem4809965 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809964 A y x r s h1 h2 h3) (@lem4808815 A r x y h1)). Qed.
Lemma lem4809966 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : (term87 A r s) = False.
Proof. exact (prop_ext (fun h3 : term87 A r s => @lem4809240 A x y r s h1 h2) (fun h3 : False => @lem4808751 A r s h1)). Qed.
Lemma lem4809967 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : False.
Proof. exact (EQ_MP (@lem4809966 A x y r s h1 h2) (@lem4808751 A r s h1)). Qed.
Lemma lem4809968 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : (term87 A r s) = False.
Proof. exact (prop_ext (fun h3 : term87 A r s => @lem4809961 A y x r s h1 h2) (fun h3 : False => @lem4808651 A r s h1)). Qed.
Lemma lem4809969 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809968 A y x r s h1 h2) (@lem4808651 A r s h1)). Qed.
Lemma lem4809970 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : (term217 A r y x) = False.
Proof. exact (prop_ext (fun h5 : term217 A r y x => @lem4809963 A y x r s h1 h2 h3 h4) (fun h5 : False => @lem4808589 A r y x h2)). Qed.
Lemma lem4809971 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809970 A y x r s h1 h2 h3 h4) (@lem4808589 A r y x h2)). Qed.
Lemma lem4809972 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : (term217 A r x y) = False.
Proof. exact (prop_ext (fun h4 : term217 A r x y => @lem4809965 A y x r s h1 h2 h3) (fun h4 : False => @lem4808519 A r x y h1)). Qed.
Lemma lem4809973 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809972 A y x r s h1 h2 h3) (@lem4808519 A r x y h1)). Qed.
Lemma lem4809974 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : (term87 A r s) = False.
Proof. exact (prop_ext (fun h3 : term87 A r s => @lem4809967 A x y r s h1 h2) (fun h3 : False => @lem4808449 A r s h1)). Qed.
Lemma lem4809975 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : False.
Proof. exact (EQ_MP (@lem4809974 A x y r s h1 h2) (@lem4808449 A r s h1)). Qed.
Lemma lem4809976 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : (term87 A r s) = False.
Proof. exact (prop_ext (fun h3 : term87 A r s => @lem4809969 A y x r s h1 h2) (fun h3 : False => @lem4808651 A r s h1)). Qed.
Lemma lem4809977 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809976 A y x r s h1 h2) (@lem4808651 A r s h1)). Qed.
Lemma lem4809978 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : (term217 A r y x) = False.
Proof. exact (prop_ext (fun h5 : term217 A r y x => @lem4809971 A y x r s h1 h2 h3 h4) (fun h5 : False => @lem4808589 A r y x h2)). Qed.
Lemma lem4809979 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term217 A r y x) (h3 : term238 A s r y x) (h4 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809978 A y x r s h1 h2 h3 h4) (@lem4808589 A r y x h2)). Qed.
Lemma lem4809980 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : (term217 A r x y) = False.
Proof. exact (prop_ext (fun h4 : term217 A r x y => @lem4809973 A y x r s h1 h2 h3) (fun h4 : False => @lem4808519 A r x y h1)). Qed.
Lemma lem4809981 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term217 A r x y) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : False.
Proof. exact (EQ_MP (@lem4809980 A y x r s h1 h2 h3) (@lem4808519 A r x y h1)). Qed.
Lemma lem4809982 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : (term87 A r s) = False.
Proof. exact (prop_ext (fun h3 : term87 A r s => @lem4809975 A x y r s h1 h2) (fun h3 : False => @lem4808449 A r s h1)). Qed.
Lemma lem4809983 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term87 A r s) (h2 : term255 A x y r s) : False.
Proof. exact (EQ_MP (@lem4809982 A x y r s h1 h2) (@lem4808449 A r s h1)). Qed.
Lemma lem4809984 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term238 A s r y x) (h3 : term242 A y x r s) : False.
Proof. exact (or_elim (@lem4808292 A s r y x h2) (fun h0 : term217 A r x y => @lem4809981 A y x r s h0 h2 h3) (fun h0 : term217 A r y x => @lem4809979 A y x r s h1 h0 h2 h3)). Qed.
Lemma lem4809985 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term242 A y x r s) : False.
Proof. exact (or_elim (@lem4808287 A y x r s h2) (fun h0 : term238 A s r y x => @lem4809984 A y x r s h1 h0 h2) (fun h0 : term87 A r s => @lem4809977 A y x r s h0 h2)). Qed.
Lemma lem4809986 {A : Type'} (x : A) (y : A) (r : type1402 A) (s : A -> Prop) (h1 : term255 A x y r s) : False.
Proof. exact (or_elim (@lem4808276 A x y r s h1) (fun h0 : term243 A s r x y => @lem4809139 A s r x y h1 h0) (fun h0 : term87 A r s => @lem4809983 A x y r s h0 h1)). Qed.
Lemma lem4809987 {A : Type'} (y : A) (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term211 A y x r s) : False.
Proof. exact (or_elim (@lem4808273 A y x r s h2) (fun h0 : term255 A x y r s => @lem4809986 A x y r s h0) (fun h0 : term242 A y x r s => @lem4809985 A y x r s h1 h0)). Qed.
Lemma lem4809988 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term52 A x r s) : False.
Proof. exact (ex_elim (@lem4807939 A x r s h2) (fun y : A => fun h0 : term213 A x r s y => @lem4809987 A y x r s h1 h0)). Qed.
Lemma lem4809989 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term52 A x r s) : (term52 A x r s) = False.
Proof. exact (prop_ext (fun h3 : term52 A x r s => @lem4809988 A x r s h1 h2) (fun h3 : False => @lem4807416 A x r s h2)). Qed.
Lemma lem4809990 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) (h1 : term50 A s r x) (h2 : term52 A x r s) : False.
Proof. exact (EQ_MP (@lem4809989 A x r s h1 h2) (@lem4807416 A x r s h2)). Qed.
Lemma lem4809991 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : term51 A x r s.
Proof. exact (fun h0 : term52 A x r s => @lem4809990 A x r s h1 h0). Qed.
Lemma lem4809992 {A : Type'} (s : A -> Prop) (r : type1402 A) (x : A) (h1 : term50 A s r x) : (term13 A x r s) = (term16 A x r s).
Proof. exact (EQ_MP (@lem4807415 A x r s) (@lem4809991 A s r x h1)). Qed.
Lemma lem4809993 {A : Type'} (x : A) (r : type1402 A) (s : A -> Prop) : term19 A x r s.
Proof. exact (fun h0 : term50 A s r x => @lem4809992 A s r x h0). Qed.
Lemma lem4809998 {A : Type'} (x : A) (r : type1402 A) : term23 A x r.
Proof. exact (fun s : A -> Prop => @lem4809993 A x r s). Qed.
Lemma lem4810003 {A : Type'} (r : type1402 A) : term27 A r.
Proof. exact (fun x : A => @lem4809998 A x r). Qed.
Lemma lem4810008 {A : Type'} : term31 A.
Proof. exact (fun r : type1402 A => @lem4810003 A r). Qed.
Lemma lem4810009 {A : Type'} : term33 A.
Proof. exact (EQ_MP (@lem4807410 A) (@lem4810008 A)). Qed.
Lemma lem4810011 {A : Type'} : term33 A.
Proof. exact (@lem4807232 A (@lem4810009 A)). Qed.
Lemma lem4810012 {A : Type'} (h1 : term34 A) : False.
Proof. exact (@lem4810011 A (@lem4807216 A h1)). Qed.
Lemma lem4810013 {A : Type'} (h1 : term34 A) : (term34 A) = False.
Proof. exact (prop_ext (fun h2 : term34 A => @lem4810012 A h1) (fun h2 : False => @lem4807216 A h1)). Qed.
Lemma lem4810014 {A : Type'} (h1 : term34 A) : False.
Proof. exact (EQ_MP (@lem4810013 A h1) (@lem4807216 A h1)). Qed.
Lemma lem4810015 {A : Type'} : term33 A.
Proof. exact (fun h0 : term34 A => @lem4810014 A h0). Qed.
Lemma lem4810016 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem4807215 A) (@lem4810015 A)). Qed.
Lemma lem4810017 {A : Type'} : term30 A.
Proof. exact (EQ_MP (@lem4807211 A) (@lem4810016 A)). Qed.
