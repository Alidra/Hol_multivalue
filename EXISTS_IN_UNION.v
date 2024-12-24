Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_IN_UNION_term_abbrevs.
Require Import IN_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem3210133 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem3210134 {A : Type'} (s : A -> Prop) : (term0 A s) = (term1 A s).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem3210135 {A : Type'} (s : A -> Prop) : term1 A s.
Proof. exact (EQ_MP (@lem3210134 A s) (@lem3210133 A s)). Qed.
Lemma lem3210136 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term2 A s t.
Proof. exact (@lem3210135 A s t). Qed.
Lemma lem3210137 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term3 A s t).
Proof. exact (eq_refl (term2 A s t)). Qed.
Lemma lem3210138 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term3 A s t.
Proof. exact (EQ_MP (@lem3210137 A s t) (@lem3210136 A s t)). Qed.
Lemma lem3210139 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term4 A s t x.
Proof. exact (@lem3210138 A s t x). Qed.
Lemma lem3210140 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term4 A s t x) = ((term5 A x s t) = (term6 A s x t)).
Proof. exact (eq_refl (term4 A s t x)). Qed.
Lemma lem3210163 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (EQ_MP (@lem3210140 A s x t) (@lem3210139 A s t x)). Qed.
Lemma lem3210164 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term5 A x s t) = (term6 A s x t).
Proof. exact (@lem3210163 A s x t). Qed.
Lemma lem3210167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3210168 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term7 A x s t) = (term8 A s x t).
Proof. exact (MK_COMB (@lem3210167) (@lem3210164 A s x t)). Qed.
Lemma lem3210169 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (P x).
Proof. exact (eq_refl (P x)). Qed.
Lemma lem3210170 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term9 A s t P x) = (term10 A s t P x).
Proof. exact (MK_COMB (@lem3210168 A s x t) (@lem3210169 A P x)). Qed.
Lemma lem3210173 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term11 A s t P) = (term12 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210170 A s t P x)). Qed.
Lemma lem3210174 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210175 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term13 A s t P) = (term14 A s t P).
Proof. exact (MK_COMB (@lem3210174 A) (@lem3210173 A s t P)). Qed.
Lemma lem3210180 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3210181 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term15 A s t P) = (term16 A s t P).
Proof. exact (MK_COMB (@lem3210180) (@lem3210175 A s t P)). Qed.
Lemma lem3210196 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term17 A s t P) = (term17 A s t P).
Proof. exact (eq_refl (term17 A s t P)). Qed.
Lemma lem3210197 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term13 A s t P) = (term17 A s t P)) = ((term14 A s t P) = (term17 A s t P)).
Proof. exact (MK_COMB (@lem3210181 A s t P) (@lem3210196 A s t P)). Qed.
Lemma lem3210200 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term18 A s P) = (term19 A s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3210197 A s t P)). Qed.
Lemma lem3210201 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3210202 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term20 A s P) = (term21 A s P).
Proof. exact (MK_COMB (@lem3210201 A) (@lem3210200 A s P)). Qed.
Lemma lem3210207 {A : Type'} (P : A -> Prop) : (term22 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3210202 A s P)). Qed.
Lemma lem3210208 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3210209 {A : Type'} (P : A -> Prop) : (term24 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem3210208 A) (@lem3210207 A P)). Qed.
Lemma lem3210214 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3210209 A P)). Qed.
Lemma lem3210215 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3210216 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem3210215 A) (@lem3210214 A)). Qed.
Lemma lem3210221 {A : Type'} : (term29 A) = (term28 A).
Proof. exact (SYM (@lem3210216 A)). Qed.
Lemma lem3210223 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3210224 {A : Type'} : (term29 A) = (term31 A).
Proof. exact (@lem3210223 (term29 A)). Qed.
Lemma lem3210225 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (SYM (@lem3210224 A)). Qed.
Lemma lem3210226 {A : Type'} (h1 : term32 A) : term32 A.
Proof. exact (h1). Qed.
Lemma lem3210229 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3210230 {A : Type'} : term33 A.
Proof. exact (fun h0 : term31 A => @lem3210229 A h0). Qed.
Lemma lem3210231 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3210232 {A : Type'} (h1 : term31 A) : term31 A.
Proof. exact (h1). Qed.
Lemma lem3210233 {A : Type'} (h1 : term31 A) (h2 : term33 A) : term31 A.
Proof. exact (@lem3210231 A h2 (@lem3210232 A h1)). Qed.
Lemma lem3210234 {A : Type'} (h1 : term31 A) : term34 A.
Proof. exact (fun h0 : term33 A => @lem3210233 A h1 h0). Qed.
Lemma lem3210235 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem3210236 {A : Type'} (h1 : term31 A) (h2 : term33 A) : term31 A.
Proof. exact (@lem3210234 A h1 (@lem3210235 A h2)). Qed.
Lemma lem3210237 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (fun h0 : term31 A => @lem3210236 A h0 h1). Qed.
Lemma lem3210238 {A : Type'} : term35 A.
Proof. exact (fun h0 : term33 A => @lem3210237 A h0). Qed.
Lemma lem3210241 {A : Type'} : term33 A.
Proof. exact (@lem3210238 A (@lem3210230 A)). Qed.
Lemma lem3210242 {A : Type'} : term33 A.
Proof. exact (@lem3210241 A). Qed.
Lemma lem3210244 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3210245 {A : Type'} : (term31 A) = (term36 A).
Proof. exact (@lem3210244 (term32 A)). Qed.
Lemma lem3210247 (t : Prop) : (term37 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3210248 {A : Type'} : (term36 A) = (term29 A).
Proof. exact (@lem3210247 (term29 A)). Qed.
Lemma lem3210371 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (TRANS (@lem3210245 A) (@lem3210248 A)). Qed.
Lemma lem3210376 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term38 A t P x) = (term38 A t P x).
Proof. exact (eq_refl (term38 A t P x)). Qed.
Lemma lem3210377 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term39 A t P) = (term39 A t P).
Proof. exact (fun_ext (fun x : A => @lem3210376 A t P x)). Qed.
Lemma lem3210378 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210379 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term40 A t P) = (term40 A t P).
Proof. exact (MK_COMB (@lem3210378 A) (@lem3210377 A t P)). Qed.
Lemma lem3210384 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term38 A s P x).
Proof. exact (eq_refl (term38 A s P x)). Qed.
Lemma lem3210385 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term39 A s P) = (term39 A s P).
Proof. exact (fun_ext (fun x : A => @lem3210384 A s P x)). Qed.
Lemma lem3210386 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210387 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term40 A s P) = (term40 A s P).
Proof. exact (MK_COMB (@lem3210386 A) (@lem3210385 A s P)). Qed.
Lemma lem3210388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210389 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term41 A s P) = (term41 A s P).
Proof. exact (MK_COMB (@lem3210388) (@lem3210387 A s P)). Qed.
Lemma lem3210390 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term17 A s t P) = (term17 A s t P).
Proof. exact (MK_COMB (@lem3210389 A s P) (@lem3210379 A t P)). Qed.
Lemma lem3210399 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term10 A s t P x) = (term10 A s t P x).
Proof. exact (eq_refl (term10 A s t P x)). Qed.
Lemma lem3210400 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term12 A s t P) = (term12 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210399 A s t P x)). Qed.
Lemma lem3210401 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210402 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term14 A s t P) = (term14 A s t P).
Proof. exact (MK_COMB (@lem3210401 A) (@lem3210400 A s t P)). Qed.
Lemma lem3210403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3210404 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term16 A s t P) = (term16 A s t P).
Proof. exact (MK_COMB (@lem3210403) (@lem3210402 A s t P)). Qed.
Lemma lem3210405 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term14 A s t P) = (term17 A s t P)) = ((term14 A s t P) = (term17 A s t P)).
Proof. exact (MK_COMB (@lem3210404 A s t P) (@lem3210390 A s t P)). Qed.
Lemma lem3210406 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term19 A s P) = (term19 A s P).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3210405 A s t P)). Qed.
Lemma lem3210407 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3210408 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term21 A s P) = (term21 A s P).
Proof. exact (MK_COMB (@lem3210407 A) (@lem3210406 A s P)). Qed.
Lemma lem3210409 {A : Type'} (P : A -> Prop) : (term23 A P) = (term23 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3210408 A s P)). Qed.
Lemma lem3210410 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3210411 {A : Type'} (P : A -> Prop) : (term25 A P) = (term25 A P).
Proof. exact (MK_COMB (@lem3210410 A) (@lem3210409 A P)). Qed.
Lemma lem3210412 {A : Type'} : (term27 A) = (term27 A).
Proof. exact (fun_ext (fun P : A -> Prop => @lem3210411 A P)). Qed.
Lemma lem3210413 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3210414 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem3210413 A) (@lem3210412 A)). Qed.
Lemma lem3210463 {A : Type'} : (term31 A) = (term29 A).
Proof. exact (TRANS (@lem3210371 A) (@lem3210414 A)). Qed.
Lemma lem3210464 {A : Type'} : (term29 A) = (term31 A).
Proof. exact (SYM (@lem3210463 A)). Qed.
Lemma lem3210466 (p : Prop) : p = (term30 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3210467 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term14 A s t P) = (term17 A s t P)) = (term42 A s t P).
Proof. exact (@lem3210466 ((term14 A s t P) = (term17 A s t P))). Qed.
Lemma lem3210468 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term42 A s t P) = ((term14 A s t P) = (term17 A s t P)).
Proof. exact (SYM (@lem3210467 A s t P)). Qed.
Lemma lem3210469 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : term43 A s t P.
Proof. exact (h1). Qed.
Lemma lem3210478 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term44 A s x t) = (term45 A s x t).
Proof. exact (@lem17160 (@IN A x s) (@IN A x t)). Qed.
Lemma lem3210482 {A : Type'} (P : A -> Prop) (x : A) : (term46 A P x) = (term46 A P x).
Proof. exact (eq_refl (term46 A P x)). Qed.
Lemma lem3210484 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210485 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term47 A s x t) = (term48 A s x t).
Proof. exact (MK_COMB (@lem3210484) (@lem3210478 A s x t)). Qed.
Lemma lem3210486 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term49 A s t P x) = (term50 A s t P x).
Proof. exact (MK_COMB (@lem3210485 A s x t) (@lem3210482 A P x)). Qed.
Lemma lem3210487 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term51 A s t P x) = (term49 A s t P x).
Proof. exact (@lem17045 (term6 A s x t) (P x)). Qed.
Lemma lem3210488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term51 A s t P x) = (term50 A s t P x).
Proof. exact (TRANS (@lem3210487 A s t P x) (@lem3210486 A s t P x)). Qed.
Lemma lem3210491 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term10 A s t P x) = (term10 A s t P x).
Proof. exact (eq_refl (term10 A s t P x)). Qed.
Lemma lem3210492 {A : Type'} (P : A -> Prop) : (term52 A P) = (term53 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3210493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term54 A s t P) = (term55 A s t P).
Proof. exact (@lem3210492 A (term12 A s t P)). Qed.
Lemma lem3210494 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term56 A s t P x) = (term10 A s t P x).
Proof. exact (eq_refl (term56 A s t P x)). Qed.
Lemma lem3210495 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3210496 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term57 A s t P x) = (term51 A s t P x).
Proof. exact (MK_COMB (@lem3210495) (@lem3210494 A s t P x)). Qed.
Lemma lem3210497 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term57 A s t P x) = (term50 A s t P x).
Proof. exact (TRANS (@lem3210496 A s t P x) (@lem3210488 A s t P x)). Qed.
Lemma lem3210498 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term58 A s t P) = (term59 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210497 A s t P x)). Qed.
Lemma lem3210499 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3210500 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term55 A s t P) = (term60 A s t P).
Proof. exact (MK_COMB (@lem3210499 A) (@lem3210498 A s t P)). Qed.
Lemma lem3210501 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term54 A s t P) = (term60 A s t P).
Proof. exact (TRANS (@lem3210493 A s t P) (@lem3210500 A s t P)). Qed.
Lemma lem3210502 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term12 A s t P) = (term12 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210491 A s t P x)). Qed.
Lemma lem3210503 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210504 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term14 A s t P) = (term14 A s t P).
Proof. exact (MK_COMB (@lem3210503 A) (@lem3210502 A s t P)). Qed.
Lemma lem3210513 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term61 A s P x) = (term62 A s P x).
Proof. exact (@lem17045 (@IN A x s) (P x)). Qed.
Lemma lem3210516 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term38 A s P x) = (term38 A s P x).
Proof. exact (eq_refl (term38 A s P x)). Qed.
Lemma lem3210517 {A : Type'} (P : A -> Prop) : (term52 A P) = (term53 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3210518 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term63 A s P) = (term64 A s P).
Proof. exact (@lem3210517 A (term39 A s P)). Qed.
Lemma lem3210519 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term65 A s P x) = (term38 A s P x).
Proof. exact (eq_refl (term65 A s P x)). Qed.
Lemma lem3210520 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3210521 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term66 A s P x) = (term61 A s P x).
Proof. exact (MK_COMB (@lem3210520) (@lem3210519 A s P x)). Qed.
Lemma lem3210522 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term66 A s P x) = (term62 A s P x).
Proof. exact (TRANS (@lem3210521 A s P x) (@lem3210513 A s P x)). Qed.
Lemma lem3210523 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term67 A s P) = (term68 A s P).
Proof. exact (fun_ext (fun x : A => @lem3210522 A s P x)). Qed.
Lemma lem3210524 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3210525 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term64 A s P) = (term69 A s P).
Proof. exact (MK_COMB (@lem3210524 A) (@lem3210523 A s P)). Qed.
Lemma lem3210526 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term63 A s P) = (term69 A s P).
Proof. exact (TRANS (@lem3210518 A s P) (@lem3210525 A s P)). Qed.
Lemma lem3210527 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term39 A s P) = (term39 A s P).
Proof. exact (fun_ext (fun x : A => @lem3210516 A s P x)). Qed.
Lemma lem3210528 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210529 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term40 A s P) = (term40 A s P).
Proof. exact (MK_COMB (@lem3210528 A) (@lem3210527 A s P)). Qed.
Lemma lem3210538 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term61 A t P x) = (term62 A t P x).
Proof. exact (@lem17045 (@IN A x t) (P x)). Qed.
Lemma lem3210541 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term38 A t P x) = (term38 A t P x).
Proof. exact (eq_refl (term38 A t P x)). Qed.
Lemma lem3210542 {A : Type'} (P : A -> Prop) : (term52 A P) = (term53 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3210543 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term63 A t P) = (term64 A t P).
Proof. exact (@lem3210542 A (term39 A t P)). Qed.
Lemma lem3210544 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term65 A t P x) = (term38 A t P x).
Proof. exact (eq_refl (term65 A t P x)). Qed.
Lemma lem3210545 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3210546 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term66 A t P x) = (term61 A t P x).
Proof. exact (MK_COMB (@lem3210545) (@lem3210544 A t P x)). Qed.
Lemma lem3210547 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term66 A t P x) = (term62 A t P x).
Proof. exact (TRANS (@lem3210546 A t P x) (@lem3210538 A t P x)). Qed.
Lemma lem3210548 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term67 A t P) = (term68 A t P).
Proof. exact (fun_ext (fun x : A => @lem3210547 A t P x)). Qed.
Lemma lem3210549 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3210550 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term64 A t P) = (term69 A t P).
Proof. exact (MK_COMB (@lem3210549 A) (@lem3210548 A t P)). Qed.
Lemma lem3210551 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term63 A t P) = (term69 A t P).
Proof. exact (TRANS (@lem3210543 A t P) (@lem3210550 A t P)). Qed.
Lemma lem3210552 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term39 A t P) = (term39 A t P).
Proof. exact (fun_ext (fun x : A => @lem3210541 A t P x)). Qed.
Lemma lem3210553 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210554 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term40 A t P) = (term40 A t P).
Proof. exact (MK_COMB (@lem3210553 A) (@lem3210552 A t P)). Qed.
Lemma lem3210555 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3210556 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term70 A s P) = (term71 A s P).
Proof. exact (MK_COMB (@lem3210555) (@lem3210526 A s P)). Qed.
Lemma lem3210557 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term72 A s t P) = (term73 A s t P).
Proof. exact (MK_COMB (@lem3210556 A s P) (@lem3210551 A t P)). Qed.
Lemma lem3210558 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term74 A s t P) = (term72 A s t P).
Proof. exact (@lem17160 (term40 A s P) (term40 A t P)). Qed.
Lemma lem3210559 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term74 A s t P) = (term73 A s t P).
Proof. exact (TRANS (@lem3210558 A s t P) (@lem3210557 A s t P)). Qed.
Lemma lem3210560 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210561 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term41 A s P) = (term41 A s P).
Proof. exact (MK_COMB (@lem3210560) (@lem3210529 A s P)). Qed.
Lemma lem3210562 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term17 A s t P) = (term17 A s t P).
Proof. exact (MK_COMB (@lem3210561 A s P) (@lem3210554 A t P)). Qed.
Lemma lem3210563 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3210564 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term75 A s t P) = (term76 A s t P).
Proof. exact (MK_COMB (@lem3210563) (@lem3210501 A s t P)). Qed.
Lemma lem3210565 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term77 A s t P) = (term78 A s t P).
Proof. exact (MK_COMB (@lem3210564 A s t P) (@lem3210562 A s t P)). Qed.
Lemma lem3210566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3210567 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term79 A s t P) = (term79 A s t P).
Proof. exact (MK_COMB (@lem3210566) (@lem3210504 A s t P)). Qed.
Lemma lem3210568 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term80 A s t P) = (term81 A s t P).
Proof. exact (MK_COMB (@lem3210567 A s t P) (@lem3210559 A s t P)). Qed.
Lemma lem3210569 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210570 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term82 A s t P) = (term83 A s t P).
Proof. exact (MK_COMB (@lem3210569) (@lem3210568 A s t P)). Qed.
Lemma lem3210571 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term84 A s t P) = (term85 A s t P).
Proof. exact (MK_COMB (@lem3210570 A s t P) (@lem3210565 A s t P)). Qed.
Lemma lem3210572 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term43 A s t P) = (term84 A s t P).
Proof. exact (@lem17646 (term14 A s t P) (term17 A s t P)). Qed.
Lemma lem3210573 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term43 A s t P) = (term85 A s t P).
Proof. exact (TRANS (@lem3210572 A s t P) (@lem3210571 A s t P)). Qed.
Lemma lem3210816 {A : Type'} (P : A -> Prop) (Q : Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3210817 {A : Type'} (P : A -> Prop) (Q : Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (@lem3210816 A P Q). Qed.
Lemma lem3210818 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term88 A s t P) = (term89 A s t P).
Proof. exact (@lem3210817 A (term12 A s t P) (term73 A s t P)). Qed.
Lemma lem3210819 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term56 A s t P x) = (term10 A s t P x).
Proof. exact (eq_refl (term56 A s t P x)). Qed.
Lemma lem3210820 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term90 A s t P) = (term12 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210819 A s t P x)). Qed.
Lemma lem3210821 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210822 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term91 A s t P) = (term14 A s t P).
Proof. exact (MK_COMB (@lem3210821 A) (@lem3210820 A s t P)). Qed.
Lemma lem3210823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3210824 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term92 A s t P) = (term79 A s t P).
Proof. exact (MK_COMB (@lem3210823) (@lem3210822 A s t P)). Qed.
Lemma lem3210825 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term73 A s t P) = (term73 A s t P).
Proof. exact (eq_refl (term73 A s t P)). Qed.
Lemma lem3210826 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term88 A s t P) = (term81 A s t P).
Proof. exact (MK_COMB (@lem3210824 A s t P) (@lem3210825 A s t P)). Qed.
Lemma lem3210827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3210828 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term93 A s t P) = (term94 A s t P).
Proof. exact (MK_COMB (@lem3210827) (@lem3210826 A s t P)). Qed.
Lemma lem3210829 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term56 A s t P x) = (term10 A s t P x).
Proof. exact (eq_refl (term56 A s t P x)). Qed.
Lemma lem3210830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3210831 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term95 A s t P x) = (term96 A s t P x).
Proof. exact (MK_COMB (@lem3210830) (@lem3210829 A s t P x)). Qed.
Lemma lem3210832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term73 A s t P) = (term73 A s t P).
Proof. exact (eq_refl (term73 A s t P)). Qed.
Lemma lem3210833 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term97 A x s t P) = (term98 A x s t P).
Proof. exact (MK_COMB (@lem3210831 A s t P x) (@lem3210832 A s t P)). Qed.
Lemma lem3210834 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term99 A s t P) = (term100 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210833 A x s t P)). Qed.
Lemma lem3210835 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210836 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term89 A s t P) = (term101 A s t P).
Proof. exact (MK_COMB (@lem3210835 A) (@lem3210834 A s t P)). Qed.
Lemma lem3210837 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term88 A s t P) = (term89 A s t P)) = ((term81 A s t P) = (term101 A s t P)).
Proof. exact (MK_COMB (@lem3210828 A s t P) (@lem3210836 A s t P)). Qed.
Lemma lem3210838 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term81 A s t P) = (term101 A s t P).
Proof. exact (EQ_MP (@lem3210837 A s t P) (@lem3210818 A s t P)). Qed.
Lemma lem3210839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term83 A s t P) = (term102 A s t P).
Proof. exact (MK_COMB (@lem3210839) (@lem3210838 A s t P)). Qed.
Lemma lem3210842 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3210843 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (@lem3210842 A P Q). Qed.
Lemma lem3210844 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term105 A s t P) = (term106 A s t P).
Proof. exact (@lem3210843 A (term39 A s P) (term39 A t P)). Qed.
Lemma lem3210845 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term65 A s P x) = (term38 A s P x).
Proof. exact (eq_refl (term65 A s P x)). Qed.
Lemma lem3210846 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term107 A s P) = (term39 A s P).
Proof. exact (fun_ext (fun x : A => @lem3210845 A s P x)). Qed.
Lemma lem3210847 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210848 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term108 A s P) = (term40 A s P).
Proof. exact (MK_COMB (@lem3210847 A) (@lem3210846 A s P)). Qed.
Lemma lem3210849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210850 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term109 A s P) = (term41 A s P).
Proof. exact (MK_COMB (@lem3210849) (@lem3210848 A s P)). Qed.
Lemma lem3210851 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term65 A t P x) = (term38 A t P x).
Proof. exact (eq_refl (term65 A t P x)). Qed.
Lemma lem3210852 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term107 A t P) = (term39 A t P).
Proof. exact (fun_ext (fun x : A => @lem3210851 A t P x)). Qed.
Lemma lem3210853 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210854 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term108 A t P) = (term40 A t P).
Proof. exact (MK_COMB (@lem3210853 A) (@lem3210852 A t P)). Qed.
Lemma lem3210855 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term105 A s t P) = (term17 A s t P).
Proof. exact (MK_COMB (@lem3210850 A s P) (@lem3210854 A t P)). Qed.
Lemma lem3210856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3210857 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term110 A s t P) = (term111 A s t P).
Proof. exact (MK_COMB (@lem3210856) (@lem3210855 A s t P)). Qed.
Lemma lem3210858 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term65 A s P x) = (term38 A s P x).
Proof. exact (eq_refl (term65 A s P x)). Qed.
Lemma lem3210859 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210860 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term112 A s P x) = (term113 A s P x).
Proof. exact (MK_COMB (@lem3210859) (@lem3210858 A s P x)). Qed.
Lemma lem3210861 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term65 A t P x) = (term38 A t P x).
Proof. exact (eq_refl (term65 A t P x)). Qed.
Lemma lem3210862 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term114 A s t P x) = (term115 A s t P x).
Proof. exact (MK_COMB (@lem3210860 A s P x) (@lem3210861 A t P x)). Qed.
Lemma lem3210863 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term116 A s t P) = (term117 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210862 A s t P x)). Qed.
Lemma lem3210864 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210865 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term106 A s t P) = (term118 A s t P).
Proof. exact (MK_COMB (@lem3210864 A) (@lem3210863 A s t P)). Qed.
Lemma lem3210866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term105 A s t P) = (term106 A s t P)) = ((term17 A s t P) = (term118 A s t P)).
Proof. exact (MK_COMB (@lem3210857 A s t P) (@lem3210865 A s t P)). Qed.
Lemma lem3210867 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term17 A s t P) = (term118 A s t P).
Proof. exact (EQ_MP (@lem3210866 A s t P) (@lem3210844 A s t P)). Qed.
Lemma lem3210868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term76 A s t P) = (term76 A s t P).
Proof. exact (eq_refl (term76 A s t P)). Qed.
Lemma lem3210869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term78 A s t P) = (term119 A s t P).
Proof. exact (MK_COMB (@lem3210868 A s t P) (@lem3210867 A s t P)). Qed.
Lemma lem3210871 {A : Type'} (P : Prop) (Q : A -> Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3210872 {A : Type'} (P : Prop) (Q : A -> Prop) : (term120 A P Q) = (term121 A P Q).
Proof. exact (@lem3210871 A P Q). Qed.
Lemma lem3210873 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term122 A s t P) = (term123 A s t P).
Proof. exact (@lem3210872 A (term60 A s t P) (term117 A s t P)). Qed.
Lemma lem3210874 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term124 A s t P x) = (term115 A s t P x).
Proof. exact (eq_refl (term124 A s t P x)). Qed.
Lemma lem3210875 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term125 A s t P) = (term117 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210874 A s t P x)). Qed.
Lemma lem3210876 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210877 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term126 A s t P) = (term118 A s t P).
Proof. exact (MK_COMB (@lem3210876 A) (@lem3210875 A s t P)). Qed.
Lemma lem3210878 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term76 A s t P) = (term76 A s t P).
Proof. exact (eq_refl (term76 A s t P)). Qed.
Lemma lem3210879 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term122 A s t P) = (term119 A s t P).
Proof. exact (MK_COMB (@lem3210878 A s t P) (@lem3210877 A s t P)). Qed.
Lemma lem3210880 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3210881 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term127 A s t P) = (term128 A s t P).
Proof. exact (MK_COMB (@lem3210880) (@lem3210879 A s t P)). Qed.
Lemma lem3210882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term124 A s t P x) = (term115 A s t P x).
Proof. exact (eq_refl (term124 A s t P x)). Qed.
Lemma lem3210883 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term76 A s t P) = (term76 A s t P).
Proof. exact (eq_refl (term76 A s t P)). Qed.
Lemma lem3210884 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term129 A s t P x) = (term130 A s t P x).
Proof. exact (MK_COMB (@lem3210883 A s t P) (@lem3210882 A s t P x)). Qed.
Lemma lem3210885 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term131 A s t P) = (term132 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210884 A s t P x)). Qed.
Lemma lem3210886 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term123 A s t P) = (term133 A s t P).
Proof. exact (MK_COMB (@lem3210886 A) (@lem3210885 A s t P)). Qed.
Lemma lem3210888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term122 A s t P) = (term123 A s t P)) = ((term119 A s t P) = (term133 A s t P)).
Proof. exact (MK_COMB (@lem3210881 A s t P) (@lem3210887 A s t P)). Qed.
Lemma lem3210889 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term119 A s t P) = (term133 A s t P).
Proof. exact (EQ_MP (@lem3210888 A s t P) (@lem3210873 A s t P)). Qed.
Lemma lem3210890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term78 A s t P) = (term133 A s t P).
Proof. exact (TRANS (@lem3210869 A s t P) (@lem3210889 A s t P)). Qed.
Lemma lem3210891 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term85 A s t P) = (term134 A s t P).
Proof. exact (MK_COMB (@lem3210840 A s t P) (@lem3210890 A s t P)). Qed.
Lemma lem3210893 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3210894 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (@lem3210893 A P Q). Qed.
Lemma lem3210895 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term135 A s t P) = (term136 A s t P).
Proof. exact (@lem3210894 A (term100 A s t P) (term132 A s t P)). Qed.
Lemma lem3210896 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term137 A s t P x) = (term98 A x s t P).
Proof. exact (eq_refl (term137 A s t P x)). Qed.
Lemma lem3210897 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term138 A s t P) = (term100 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210896 A x s t P)). Qed.
Lemma lem3210898 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210899 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term139 A s t P) = (term101 A s t P).
Proof. exact (MK_COMB (@lem3210898 A) (@lem3210897 A s t P)). Qed.
Lemma lem3210900 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210901 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term140 A s t P) = (term102 A s t P).
Proof. exact (MK_COMB (@lem3210900) (@lem3210899 A s t P)). Qed.
Lemma lem3210902 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term141 A s t P x) = (term130 A s t P x).
Proof. exact (eq_refl (term141 A s t P x)). Qed.
Lemma lem3210903 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term142 A s t P) = (term132 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210902 A s t P x)). Qed.
Lemma lem3210904 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210905 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term143 A s t P) = (term133 A s t P).
Proof. exact (MK_COMB (@lem3210904 A) (@lem3210903 A s t P)). Qed.
Lemma lem3210906 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term135 A s t P) = (term134 A s t P).
Proof. exact (MK_COMB (@lem3210901 A s t P) (@lem3210905 A s t P)). Qed.
Lemma lem3210907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3210908 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term144 A s t P) = (term145 A s t P).
Proof. exact (MK_COMB (@lem3210907) (@lem3210906 A s t P)). Qed.
Lemma lem3210909 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term137 A s t P x) = (term98 A x s t P).
Proof. exact (eq_refl (term137 A s t P x)). Qed.
Lemma lem3210910 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3210911 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term146 A s t P x) = (term147 A x s t P).
Proof. exact (MK_COMB (@lem3210910) (@lem3210909 A x s t P)). Qed.
Lemma lem3210912 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term141 A s t P x) = (term130 A s t P x).
Proof. exact (eq_refl (term141 A s t P x)). Qed.
Lemma lem3210913 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term148 A s t P x) = (term149 A s t P x).
Proof. exact (MK_COMB (@lem3210911 A x s t P) (@lem3210912 A s t P x)). Qed.
Lemma lem3210914 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term150 A s t P) = (term151 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210913 A s t P x)). Qed.
Lemma lem3210915 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3210916 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term136 A s t P) = (term152 A s t P).
Proof. exact (MK_COMB (@lem3210915 A) (@lem3210914 A s t P)). Qed.
Lemma lem3210917 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : ((term135 A s t P) = (term136 A s t P)) = ((term134 A s t P) = (term152 A s t P)).
Proof. exact (MK_COMB (@lem3210908 A s t P) (@lem3210916 A s t P)). Qed.
Lemma lem3210918 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term134 A s t P) = (term152 A s t P).
Proof. exact (EQ_MP (@lem3210917 A s t P) (@lem3210895 A s t P)). Qed.
Lemma lem3210920 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term85 A s t P) = (term152 A s t P).
Proof. exact (TRANS (@lem3210891 A s t P) (@lem3210918 A s t P)). Qed.
Lemma lem3210921 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term43 A s t P) = (term152 A s t P).
Proof. exact (TRANS (@lem3210573 A s t P) (@lem3210920 A s t P)). Qed.
Lemma lem3210922 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : term152 A s t P.
Proof. exact (EQ_MP (@lem3210921 A s t P) (@lem3210469 A s t P h1)). Qed.
Lemma lem3210923 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term149 A s t P x) : term149 A s t P x.
Proof. exact (h1). Qed.
Lemma lem3210948 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term115 A s t P x) = (term115 A s t P x).
Proof. exact (eq_refl (term115 A s t P x)). Qed.
Lemma lem3210973 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term50 A s t P x) = (term50 A s t P x).
Proof. exact (eq_refl (term50 A s t P x)). Qed.
Lemma lem3210974 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term59 A s t P) = (term59 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3210973 A s t P x)). Qed.
Lemma lem3210975 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3210976 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term60 A s t P) = (term60 A s t P).
Proof. exact (MK_COMB (@lem3210975 A) (@lem3210974 A s t P)). Qed.
Lemma lem3210977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3210978 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term76 A s t P) = (term76 A s t P).
Proof. exact (MK_COMB (@lem3210977) (@lem3210976 A s t P)). Qed.
Lemma lem3210979 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term130 A s t P x) = (term130 A s t P x).
Proof. exact (MK_COMB (@lem3210978 A s t P) (@lem3210948 A s t P x)). Qed.
Lemma lem3210994 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term62 A t P x) = (term62 A t P x).
Proof. exact (eq_refl (term62 A t P x)). Qed.
Lemma lem3210995 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term68 A t P) = (term68 A t P).
Proof. exact (fun_ext (fun x : A => @lem3210994 A t P x)). Qed.
Lemma lem3210996 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3210997 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term69 A t P) = (term69 A t P).
Proof. exact (MK_COMB (@lem3210996 A) (@lem3210995 A t P)). Qed.
Lemma lem3211012 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term62 A s P x) = (term62 A s P x).
Proof. exact (eq_refl (term62 A s P x)). Qed.
Lemma lem3211013 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term68 A s P) = (term68 A s P).
Proof. exact (fun_ext (fun x : A => @lem3211012 A s P x)). Qed.
Lemma lem3211014 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211015 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term69 A s P) = (term69 A s P).
Proof. exact (MK_COMB (@lem3211014 A) (@lem3211013 A s P)). Qed.
Lemma lem3211016 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3211017 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term71 A s P) = (term71 A s P).
Proof. exact (MK_COMB (@lem3211016) (@lem3211015 A s P)). Qed.
Lemma lem3211018 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term73 A s t P) = (term73 A s t P).
Proof. exact (MK_COMB (@lem3211017 A s P) (@lem3210997 A t P)). Qed.
Lemma lem3211039 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term96 A s t P x) = (term96 A s t P x).
Proof. exact (eq_refl (term96 A s t P x)). Qed.
Lemma lem3211040 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term98 A x s t P) = (term98 A x s t P).
Proof. exact (MK_COMB (@lem3211039 A s t P x) (@lem3211018 A s t P)). Qed.
Lemma lem3211041 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3211042 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term147 A x s t P) = (term147 A x s t P).
Proof. exact (MK_COMB (@lem3211041) (@lem3211040 A x s t P)). Qed.
Lemma lem3211043 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term149 A s t P x) = (term149 A s t P x).
Proof. exact (MK_COMB (@lem3211042 A x s t P) (@lem3210979 A s t P x)). Qed.
Lemma lem3211044 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term149 A s t P x) : term149 A s t P x.
Proof. exact (EQ_MP (@lem3211043 A s t P x) (@lem3210923 A s t P x h1)). Qed.
Lemma lem3211045 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term98 A x s t P.
Proof. exact (h1). Qed.
Lemma lem3211046 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term130 A s t P x.
Proof. exact (h1). Qed.
Lemma lem3211047 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term73 A s t P.
Proof. exact (proj2 (@lem3211045 A x s t P h1)). Qed.
Lemma lem3211048 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term10 A s t P x.
Proof. exact (proj1 (@lem3211045 A x s t P h1)). Qed.
Lemma lem3211049 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term69 A t P.
Proof. exact (proj2 (@lem3211047 A x s t P h1)). Qed.
Lemma lem3211050 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term69 A s P.
Proof. exact (proj1 (@lem3211047 A x s t P h1)). Qed.
Lemma lem3211052 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term6 A s x t.
Proof. exact (proj1 (@lem3211048 A x s t P h1)). Qed.
Lemma lem3211055 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term115 A s t P x.
Proof. exact (proj2 (@lem3211046 A s t P x h1)). Qed.
Lemma lem3211056 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term60 A s t P.
Proof. exact (proj1 (@lem3211046 A s t P x h1)). Qed.
Lemma lem3211057 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : term38 A s P x.
Proof. exact (h1). Qed.
Lemma lem3211058 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : term38 A t P x.
Proof. exact (h1). Qed.
Lemma lem3211070 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) : (term62 A s P x) = (term62 A s P x).
Proof. exact (eq_refl (term62 A s P x)). Qed.
Lemma lem3211071 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term68 A s P) = (term68 A s P).
Proof. exact (fun_ext (fun x : A => @lem3211070 A s P x)). Qed.
Lemma lem3211072 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211074 {A : Type'} (s : A -> Prop) (P : A -> Prop) : (term69 A s P) = (term69 A s P).
Proof. exact (MK_COMB (@lem3211072 A) (@lem3211071 A s P)). Qed.
Lemma lem3211075 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term69 A s P.
Proof. exact (EQ_MP (@lem3211074 A s P) (@lem3211050 A x s t P h1)). Qed.
Lemma lem3211096 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3211117 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) : (term62 A t P x) = (term62 A t P x).
Proof. exact (eq_refl (term62 A t P x)). Qed.
Lemma lem3211118 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term68 A t P) = (term68 A t P).
Proof. exact (fun_ext (fun x : A => @lem3211117 A t P x)). Qed.
Lemma lem3211119 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211121 {A : Type'} (t : A -> Prop) (P : A -> Prop) : (term69 A t P) = (term69 A t P).
Proof. exact (MK_COMB (@lem3211119 A) (@lem3211118 A t P)). Qed.
Lemma lem3211122 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term69 A t P.
Proof. exact (EQ_MP (@lem3211121 A t P) (@lem3211049 A x s t P h1)). Qed.
Lemma lem3211130 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3211148 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term50 A s t P x) = (term153 A s t P x).
Proof. exact (@lem19699 (term154 A x s) (term154 A x t) (term46 A P x)). Qed.
Lemma lem3211149 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term59 A s t P) = (term155 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3211148 A s t P x)). Qed.
Lemma lem3211150 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211152 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term60 A s t P) = (term156 A s t P).
Proof. exact (MK_COMB (@lem3211150 A) (@lem3211149 A s t P)). Qed.
Lemma lem3211153 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term156 A s t P.
Proof. exact (EQ_MP (@lem3211152 A s t P) (@lem3211056 A s t P x h1)). Qed.
Lemma lem3211179 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) : (term50 A s t P x) = (term153 A s t P x).
Proof. exact (@lem19699 (term154 A x s) (term154 A x t) (term46 A P x)). Qed.
Lemma lem3211180 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term59 A s t P) = (term155 A s t P).
Proof. exact (fun_ext (fun x : A => @lem3211179 A s t P x)). Qed.
Lemma lem3211181 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3211183 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term60 A s t P) = (term156 A s t P).
Proof. exact (MK_COMB (@lem3211181 A) (@lem3211180 A s t P)). Qed.
Lemma lem3211184 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term156 A s t P.
Proof. exact (EQ_MP (@lem3211183 A s t P) (@lem3211056 A s t P x h1)). Qed.
Lemma lem3211193 {A : Type'} (_33002 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term157 A s P _33002.
Proof. exact (@lem3211075 A x s t P h1 _33002). Qed.
Lemma lem3211194 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_33002 : A) : (term157 A s P _33002) = (term62 A s P _33002).
Proof. exact (eq_refl (term157 A s P _33002)). Qed.
Lemma lem3211202 {A : Type'} (_33005 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term157 A t P _33005.
Proof. exact (@lem3211122 A x s t P h1 _33005). Qed.
Lemma lem3211203 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33005 : A) : (term157 A t P _33005) = (term62 A t P _33005).
Proof. exact (eq_refl (term157 A t P _33005)). Qed.
Lemma lem3211205 {A : Type'} (_33006 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term158 A s t P _33006.
Proof. exact (@lem3211153 A s t P x h1 _33006). Qed.
Lemma lem3211206 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (_33006 : A) : (term158 A s t P _33006) = (term153 A s t P _33006).
Proof. exact (eq_refl (term158 A s t P _33006)). Qed.
Lemma lem3211207 {A : Type'} (_33006 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term153 A s t P _33006.
Proof. exact (EQ_MP (@lem3211206 A s t P _33006) (@lem3211205 A _33006 s t P x h1)). Qed.
Lemma lem3211208 {A : Type'} (_33007 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term158 A s t P _33007.
Proof. exact (@lem3211184 A s t P x h1 _33007). Qed.
Lemma lem3211209 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (_33007 : A) : (term158 A s t P _33007) = (term153 A s t P _33007).
Proof. exact (eq_refl (term158 A s t P _33007)). Qed.
Lemma lem3211210 {A : Type'} (_33007 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term153 A s t P _33007.
Proof. exact (EQ_MP (@lem3211209 A s t P _33007) (@lem3211208 A _33007 s t P x h1)). Qed.
Lemma lem3211220 {A : Type'} (_33002 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term62 A s P _33002.
Proof. exact (EQ_MP (@lem3211194 A s P _33002) (@lem3211193 A _33002 x s t P h1)). Qed.
Lemma lem3211230 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3211242 {A : Type'} (_33005 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term62 A t P _33005.
Proof. exact (EQ_MP (@lem3211203 A t P _33005) (@lem3211202 A _33005 x s t P h1)). Qed.
Lemma lem3211246 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3211256 {A : Type'} (_33006 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term62 A s P _33006.
Proof. exact (proj1 (@lem3211207 A _33006 s t P x h1)). Qed.
Lemma lem3211278 {A : Type'} (_33007 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term62 A t P _33007.
Proof. exact (proj2 (@lem3211210 A _33007 s t P x h1)). Qed.
Lemma lem3211280 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (h1). Qed.
Lemma lem3211281 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : term159 A x s.
Proof. exact (fun h0 : term154 A x s => @lem3211280 A x s h1). Qed.
Lemma lem3211283 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211284 {A : Type'} (x : A) (s : A -> Prop) : (term159 A x s) = (@IN A x s).
Proof. exact (@lem3211283 (@IN A x s)). Qed.
Lemma lem3211285 {A : Type'} (x : A) (s : A -> Prop) (h1 : @IN A x s) : @IN A x s.
Proof. exact (EQ_MP (@lem3211284 A x s) (@lem3211281 A x s h1)). Qed.
Lemma lem3211287 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : P x.
Proof. exact (proj2 (@lem3211048 A x s t P h1)). Qed.
Lemma lem3211288 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term161 A P x.
Proof. exact (fun h0 : term46 A P x => @lem3211287 A x s t P h1). Qed.
Lemma lem3211290 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211291 {A : Type'} (P : A -> Prop) (x : A) : (term161 A P x) = (P x).
Proof. exact (@lem3211290 (P x)). Qed.
Lemma lem3211292 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : P x.
Proof. exact (EQ_MP (@lem3211291 A P x) (@lem3211288 A x s t P h1)). Qed.
Lemma lem3211294 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3211295 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_33002 : A) : (term62 A s P _33002) = (term61 A s P _33002).
Proof. exact (@lem3211294 (@IN A _33002 s) (P _33002)). Qed.
Lemma lem3211297 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3211298 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_33002 : A) : (term61 A s P _33002) = (term164 A s P _33002).
Proof. exact (@lem3211297 (term38 A s P _33002)). Qed.
Lemma lem3211299 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_33002 : A) : (term62 A s P _33002) = (term164 A s P _33002).
Proof. exact (TRANS (@lem3211295 A s P _33002) (@lem3211298 A s P _33002)). Qed.
Lemma lem3211301 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : term38 A s P x.
Proof. exact (conj (@lem3211285 A x s h2) (@lem3211292 A x s t P h1)). Qed.
Lemma lem3211303 {A : Type'} (_33002 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term164 A s P _33002.
Proof. exact (EQ_MP (@lem3211299 A s P _33002) (@lem3211220 A _33002 x s t P h1)). Qed.
Lemma lem3211304 {A : Type'} (_33002 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term164 A s P _33002.
Proof. exact (@lem3211303 A _33002 x s t P h1). Qed.
Lemma lem3211305 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term164 A s P x.
Proof. exact (@lem3211304 A x x s t P h1). Qed.
Lemma lem3211308 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (@lem3211305 A x s t P h1 (@lem3211301 A t P x s h1 h2)). Qed.
Lemma lem3211309 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : term165.
Proof. exact (fun h0 : ~ False => @lem3211308 A t P x s h1 h2). Qed.
Lemma lem3211311 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211312 : term165 = False.
Proof. exact (@lem3211311 False). Qed.
Lemma lem3211313 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3211312) (@lem3211309 A t P x s h1 h2)). Qed.
Lemma lem3211315 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3211316 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : term159 A x t.
Proof. exact (fun h0 : term154 A x t => @lem3211315 A x t h1). Qed.
Lemma lem3211318 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211319 {A : Type'} (x : A) (t : A -> Prop) : (term159 A x t) = (@IN A x t).
Proof. exact (@lem3211318 (@IN A x t)). Qed.
Lemma lem3211320 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (EQ_MP (@lem3211319 A x t) (@lem3211316 A x t h1)). Qed.
Lemma lem3211322 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : P x.
Proof. exact (proj2 (@lem3211048 A x s t P h1)). Qed.
Lemma lem3211323 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term161 A P x.
Proof. exact (fun h0 : term46 A P x => @lem3211322 A x s t P h1). Qed.
Lemma lem3211325 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211326 {A : Type'} (P : A -> Prop) (x : A) : (term161 A P x) = (P x).
Proof. exact (@lem3211325 (P x)). Qed.
Lemma lem3211327 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : P x.
Proof. exact (EQ_MP (@lem3211326 A P x) (@lem3211323 A x s t P h1)). Qed.
Lemma lem3211329 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3211330 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33005 : A) : (term62 A t P _33005) = (term61 A t P _33005).
Proof. exact (@lem3211329 (@IN A _33005 t) (P _33005)). Qed.
Lemma lem3211332 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3211333 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33005 : A) : (term61 A t P _33005) = (term164 A t P _33005).
Proof. exact (@lem3211332 (term38 A t P _33005)). Qed.
Lemma lem3211334 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33005 : A) : (term62 A t P _33005) = (term164 A t P _33005).
Proof. exact (TRANS (@lem3211330 A t P _33005) (@lem3211333 A t P _33005)). Qed.
Lemma lem3211336 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : term38 A t P x.
Proof. exact (conj (@lem3211320 A x t h2) (@lem3211327 A x s t P h1)). Qed.
Lemma lem3211338 {A : Type'} (_33005 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term164 A t P _33005.
Proof. exact (EQ_MP (@lem3211334 A t P _33005) (@lem3211242 A _33005 x s t P h1)). Qed.
Lemma lem3211339 {A : Type'} (_33005 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term164 A t P _33005.
Proof. exact (@lem3211338 A _33005 x s t P h1). Qed.
Lemma lem3211340 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : term164 A t P x.
Proof. exact (@lem3211339 A x x s t P h1). Qed.
Lemma lem3211343 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (@lem3211340 A x s t P h1 (@lem3211336 A s P x t h1 h2)). Qed.
Lemma lem3211344 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : term165.
Proof. exact (fun h0 : ~ False => @lem3211343 A s P x t h1 h2). Qed.
Lemma lem3211346 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211347 : term165 = False.
Proof. exact (@lem3211346 False). Qed.
Lemma lem3211348 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3211347) (@lem3211344 A s P x t h1 h2)). Qed.
Lemma lem3211350 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : @IN A x s.
Proof. exact (proj1 (@lem3211057 A s P x h1)). Qed.
Lemma lem3211351 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : term159 A x s.
Proof. exact (fun h0 : term154 A x s => @lem3211350 A s P x h1). Qed.
Lemma lem3211353 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211354 {A : Type'} (x : A) (s : A -> Prop) : (term159 A x s) = (@IN A x s).
Proof. exact (@lem3211353 (@IN A x s)). Qed.
Lemma lem3211355 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : @IN A x s.
Proof. exact (EQ_MP (@lem3211354 A x s) (@lem3211351 A s P x h1)). Qed.
Lemma lem3211357 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : P x.
Proof. exact (proj2 (@lem3211057 A s P x h1)). Qed.
Lemma lem3211358 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : term161 A P x.
Proof. exact (fun h0 : term46 A P x => @lem3211357 A s P x h1). Qed.
Lemma lem3211360 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211361 {A : Type'} (P : A -> Prop) (x : A) : (term161 A P x) = (P x).
Proof. exact (@lem3211360 (P x)). Qed.
Lemma lem3211362 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : P x.
Proof. exact (EQ_MP (@lem3211361 A P x) (@lem3211358 A s P x h1)). Qed.
Lemma lem3211364 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3211365 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_33006 : A) : (term62 A s P _33006) = (term61 A s P _33006).
Proof. exact (@lem3211364 (@IN A _33006 s) (P _33006)). Qed.
Lemma lem3211367 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3211368 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_33006 : A) : (term61 A s P _33006) = (term164 A s P _33006).
Proof. exact (@lem3211367 (term38 A s P _33006)). Qed.
Lemma lem3211369 {A : Type'} (s : A -> Prop) (P : A -> Prop) (_33006 : A) : (term62 A s P _33006) = (term164 A s P _33006).
Proof. exact (TRANS (@lem3211365 A s P _33006) (@lem3211368 A s P _33006)). Qed.
Lemma lem3211371 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A s P x) : term38 A s P x.
Proof. exact (conj (@lem3211355 A s P x h1) (@lem3211362 A s P x h1)). Qed.
Lemma lem3211373 {A : Type'} (_33006 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term164 A s P _33006.
Proof. exact (EQ_MP (@lem3211369 A s P _33006) (@lem3211256 A _33006 s t P x h1)). Qed.
Lemma lem3211374 {A : Type'} (_33006 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term164 A s P _33006.
Proof. exact (@lem3211373 A _33006 s t P x h1). Qed.
Lemma lem3211375 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term164 A s P x.
Proof. exact (@lem3211374 A x s t P x h1). Qed.
Lemma lem3211378 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) (h2 : term38 A s P x) : False.
Proof. exact (@lem3211375 A s t P x h1 (@lem3211371 A s P x h2)). Qed.
Lemma lem3211379 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) (h2 : term38 A s P x) : term165.
Proof. exact (fun h0 : ~ False => @lem3211378 A t s P x h1 h2). Qed.
Lemma lem3211381 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211382 : term165 = False.
Proof. exact (@lem3211381 False). Qed.
Lemma lem3211383 {A : Type'} (t : A -> Prop) (s : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) (h2 : term38 A s P x) : False.
Proof. exact (EQ_MP (@lem3211382) (@lem3211379 A t s P x h1 h2)). Qed.
Lemma lem3211385 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : @IN A x t.
Proof. exact (proj1 (@lem3211058 A t P x h1)). Qed.
Lemma lem3211386 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : term159 A x t.
Proof. exact (fun h0 : term154 A x t => @lem3211385 A t P x h1). Qed.
Lemma lem3211388 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211389 {A : Type'} (x : A) (t : A -> Prop) : (term159 A x t) = (@IN A x t).
Proof. exact (@lem3211388 (@IN A x t)). Qed.
Lemma lem3211390 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : @IN A x t.
Proof. exact (EQ_MP (@lem3211389 A x t) (@lem3211386 A t P x h1)). Qed.
Lemma lem3211392 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : P x.
Proof. exact (proj2 (@lem3211058 A t P x h1)). Qed.
Lemma lem3211393 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : term161 A P x.
Proof. exact (fun h0 : term46 A P x => @lem3211392 A t P x h1). Qed.
Lemma lem3211395 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211396 {A : Type'} (P : A -> Prop) (x : A) : (term161 A P x) = (P x).
Proof. exact (@lem3211395 (P x)). Qed.
Lemma lem3211397 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : P x.
Proof. exact (EQ_MP (@lem3211396 A P x) (@lem3211393 A t P x h1)). Qed.
Lemma lem3211399 (a : Prop) (b : Prop) : (term162 a b) = (term163 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3211400 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33007 : A) : (term62 A t P _33007) = (term61 A t P _33007).
Proof. exact (@lem3211399 (@IN A _33007 t) (P _33007)). Qed.
Lemma lem3211402 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3211403 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33007 : A) : (term61 A t P _33007) = (term164 A t P _33007).
Proof. exact (@lem3211402 (term38 A t P _33007)). Qed.
Lemma lem3211404 {A : Type'} (t : A -> Prop) (P : A -> Prop) (_33007 : A) : (term62 A t P _33007) = (term164 A t P _33007).
Proof. exact (TRANS (@lem3211400 A t P _33007) (@lem3211403 A t P _33007)). Qed.
Lemma lem3211406 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term38 A t P x) : term38 A t P x.
Proof. exact (conj (@lem3211390 A t P x h1) (@lem3211397 A t P x h1)). Qed.
Lemma lem3211408 {A : Type'} (_33007 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term164 A t P _33007.
Proof. exact (EQ_MP (@lem3211404 A t P _33007) (@lem3211278 A _33007 s t P x h1)). Qed.
Lemma lem3211409 {A : Type'} (_33007 : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term164 A t P _33007.
Proof. exact (@lem3211408 A _33007 s t P x h1). Qed.
Lemma lem3211410 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : term164 A t P x.
Proof. exact (@lem3211409 A x s t P x h1). Qed.
Lemma lem3211413 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) (h2 : term38 A t P x) : False.
Proof. exact (@lem3211410 A s t P x h1 (@lem3211406 A t P x h2)). Qed.
Lemma lem3211414 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) (h2 : term38 A t P x) : term165.
Proof. exact (fun h0 : ~ False => @lem3211413 A s t P x h1 h2). Qed.
Lemma lem3211416 (p : Prop) : (term160 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3211417 : term165 = False.
Proof. exact (@lem3211416 False). Qed.
Lemma lem3211418 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) (h2 : term38 A t P x) : False.
Proof. exact (EQ_MP (@lem3211417) (@lem3211414 A s t P x h1 h2)). Qed.
Lemma lem3211419 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3211348 A s P x t h1 h2) (fun h3 : False => @lem3211246 A x t h2)). Qed.
Lemma lem3211420 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3211419 A s P x t h1 h2) (@lem3211246 A x t h2)). Qed.
Lemma lem3211421 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem3211313 A t P x s h1 h2) (fun h3 : False => @lem3211230 A x s h2)). Qed.
Lemma lem3211422 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3211421 A t P x s h1 h2) (@lem3211230 A x s h2)). Qed.
Lemma lem3211423 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3211420 A s P x t h1 h2) (fun h3 : False => @lem3211130 A x t h2)). Qed.
Lemma lem3211424 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3211423 A s P x t h1 h2) (@lem3211130 A x t h2)). Qed.
Lemma lem3211425 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem3211422 A t P x s h1 h2) (fun h3 : False => @lem3211096 A x s h2)). Qed.
Lemma lem3211426 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3211425 A t P x s h1 h2) (@lem3211096 A x s h2)). Qed.
Lemma lem3211427 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : (@IN A x t) = False.
Proof. exact (prop_ext (fun h3 : @IN A x t => @lem3211424 A s P x t h1 h2) (fun h3 : False => @lem3211130 A x t h2)). Qed.
Lemma lem3211428 {A : Type'} (s : A -> Prop) (P : A -> Prop) (x : A) (t : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x t) : False.
Proof. exact (EQ_MP (@lem3211427 A s P x t h1 h2) (@lem3211130 A x t h2)). Qed.
Lemma lem3211429 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : (@IN A x s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x s => @lem3211426 A t P x s h1 h2) (fun h3 : False => @lem3211096 A x s h2)). Qed.
Lemma lem3211430 {A : Type'} (t : A -> Prop) (P : A -> Prop) (x : A) (s : A -> Prop) (h1 : term98 A x s t P) (h2 : @IN A x s) : False.
Proof. exact (EQ_MP (@lem3211429 A t P x s h1 h2) (@lem3211096 A x s h2)). Qed.
Lemma lem3211431 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term130 A s t P x) : False.
Proof. exact (or_elim (@lem3211055 A s t P x h1) (fun h0 : term38 A s P x => @lem3211383 A t s P x h1 h0) (fun h0 : term38 A t P x => @lem3211418 A s t P x h1 h0)). Qed.
Lemma lem3211432 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term98 A x s t P) : False.
Proof. exact (or_elim (@lem3211052 A x s t P h1) (fun h0 : @IN A x s => @lem3211430 A t P x s h1 h0) (fun h0 : @IN A x t => @lem3211428 A s P x t h1 h0)). Qed.
Lemma lem3211433 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term149 A s t P x) : False.
Proof. exact (or_elim (@lem3211044 A s t P x h1) (fun h0 : term98 A x s t P => @lem3211432 A x s t P h0) (fun h0 : term130 A s t P x => @lem3211431 A s t P x h0)). Qed.
Lemma lem3211434 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term149 A s t P x) : (term149 A s t P x) = False.
Proof. exact (prop_ext (fun h2 : term149 A s t P x => @lem3211433 A s t P x h1) (fun h2 : False => @lem3211044 A s t P x h1)). Qed.
Lemma lem3211435 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (x : A) (h1 : term149 A s t P x) : False.
Proof. exact (EQ_MP (@lem3211434 A s t P x h1) (@lem3211044 A s t P x h1)). Qed.
Lemma lem3211436 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : False.
Proof. exact (ex_elim (@lem3210922 A s t P h1) (fun x : A => fun h0 : term151 A s t P x => @lem3211435 A s t P x h0)). Qed.
Lemma lem3211437 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : (term43 A s t P) = False.
Proof. exact (prop_ext (fun h2 : term43 A s t P => @lem3211436 A s t P h1) (fun h2 : False => @lem3210469 A s t P h1)). Qed.
Lemma lem3211438 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) (h1 : term43 A s t P) : False.
Proof. exact (EQ_MP (@lem3211437 A s t P h1) (@lem3210469 A s t P h1)). Qed.
Lemma lem3211439 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : term42 A s t P.
Proof. exact (fun h0 : term43 A s t P => @lem3211438 A s t P h0). Qed.
Lemma lem3211440 {A : Type'} (s : A -> Prop) (t : A -> Prop) (P : A -> Prop) : (term14 A s t P) = (term17 A s t P).
Proof. exact (EQ_MP (@lem3210468 A s t P) (@lem3211439 A s t P)). Qed.
Lemma lem3211445 {A : Type'} (s : A -> Prop) (P : A -> Prop) : term21 A s P.
Proof. exact (fun t : A -> Prop => @lem3211440 A s t P). Qed.
Lemma lem3211450 {A : Type'} (P : A -> Prop) : term25 A P.
Proof. exact (fun s : A -> Prop => @lem3211445 A s P). Qed.
Lemma lem3211455 {A : Type'} : term29 A.
Proof. exact (fun P : A -> Prop => @lem3211450 A P). Qed.
Lemma lem3211456 {A : Type'} : term31 A.
Proof. exact (EQ_MP (@lem3210464 A) (@lem3211455 A)). Qed.
Lemma lem3211458 {A : Type'} : term31 A.
Proof. exact (@lem3210242 A (@lem3211456 A)). Qed.
Lemma lem3211459 {A : Type'} (h1 : term32 A) : False.
Proof. exact (@lem3211458 A (@lem3210226 A h1)). Qed.
Lemma lem3211460 {A : Type'} (h1 : term32 A) : (term32 A) = False.
Proof. exact (prop_ext (fun h2 : term32 A => @lem3211459 A h1) (fun h2 : False => @lem3210226 A h1)). Qed.
Lemma lem3211461 {A : Type'} (h1 : term32 A) : False.
Proof. exact (EQ_MP (@lem3211460 A h1) (@lem3210226 A h1)). Qed.
Lemma lem3211462 {A : Type'} : term31 A.
Proof. exact (fun h0 : term32 A => @lem3211461 A h0). Qed.
Lemma lem3211463 {A : Type'} : term29 A.
Proof. exact (EQ_MP (@lem3210225 A) (@lem3211462 A)). Qed.
Lemma lem3211464 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem3210221 A) (@lem3211463 A)). Qed.
