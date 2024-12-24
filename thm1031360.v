Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1031360_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1005477_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm912739_spec.
Require Import thm912741_spec.
Lemma lem1017021 : term0 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1017022 : (term0 = (BIT1 0)) = (term1 = term2).
Proof. exact (@lem1005477 0 (BIT1 0)). Qed.
Lemma lem1017023 : term1 = term2.
Proof. exact (EQ_MP (@lem1017022) (@lem1017021)). Qed.
Lemma lem1017025 : term3 = term4.
Proof. exact (@lem912741). Qed.
Lemma lem1017026 : (term3 = term4) = (term5 = term6).
Proof. exact (@lem1005477 (BIT1 0) term4). Qed.
Lemma lem1017027 : term5 = term6.
Proof. exact (EQ_MP (@lem1017026) (@lem1017025)). Qed.
Lemma lem1017039 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term7 A r0 add r1 mul pwr) : term7 A r0 add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017040 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term8 A r0 add r1 mul pwr) : term8 A r0 add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017041 {A : Type'} (add : type1400 A) (h1 : term9 A add) : term9 A add.
Proof. exact (h1). Qed.
Lemma lem1017042 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term10 A r0 add r1 mul pwr) : term10 A r0 add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017043 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (h1). Qed.
Lemma lem1017044 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term12 A r0 add r1 mul pwr) : term12 A r0 add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017045 {A : Type'} (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term13 A add r0.
Proof. exact (h1). Qed.
Lemma lem1017046 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term14 A r0 add r1 mul pwr) : term14 A r0 add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017047 {A : Type'} (mul : type1400 A) (h1 : term9 A mul) : term9 A mul.
Proof. exact (h1). Qed.
Lemma lem1017048 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term15 A r0 add r1 mul pwr) : term15 A r0 add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017049 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (h1). Qed.
Lemma lem1017050 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term16 A r0 add r1 mul pwr) : term16 A r0 add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017051 {A : Type'} (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term13 A mul r1.
Proof. exact (h1). Qed.
Lemma lem1017052 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term17 A add r1 mul pwr) : term17 A add r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017053 {A : Type'} (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term18 A mul r0.
Proof. exact (h1). Qed.
Lemma lem1017054 {A : Type'} (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term19 A r1 mul pwr) : term19 A r1 mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017055 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term20 A add mul.
Proof. exact (h1). Qed.
Lemma lem1017056 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term21 A mul pwr.
Proof. exact (h1). Qed.
Lemma lem1017057 {A : Type'} (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : term22 A pwr r1.
Proof. exact (h1). Qed.
Lemma lem1017058 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term23 A add r1 mul r0) : term23 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1017060 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1017061 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term23 A add r1 mul r0) = (term25 A add r1 mul r0).
Proof. exact (@lem1017060 (term23 A add r1 mul r0)). Qed.
Lemma lem1017062 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term25 A add r1 mul r0) = (term23 A add r1 mul r0).
Proof. exact (SYM (@lem1017061 A add r1 mul r0)). Qed.
Lemma lem1017063 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term26 A add r1 mul r0) : term26 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1017066 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term27 A pwr add r1 mul r0) : term27 A pwr add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1017067 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term28 A pwr add r1 mul r0.
Proof. exact (fun h0 : term27 A pwr add r1 mul r0 => @lem1017066 A pwr add r1 mul r0 h0). Qed.
Lemma lem1017068 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term28 A pwr add r1 mul r0) : term28 A pwr add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1017069 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term27 A pwr add r1 mul r0) : term27 A pwr add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1017070 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term27 A pwr add r1 mul r0) (h2 : term28 A pwr add r1 mul r0) : term27 A pwr add r1 mul r0.
Proof. exact (@lem1017068 A pwr add r1 mul r0 h2 (@lem1017069 A pwr add r1 mul r0 h1)). Qed.
Lemma lem1017071 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term27 A pwr add r1 mul r0) : term29 A pwr add r1 mul r0.
Proof. exact (fun h0 : term28 A pwr add r1 mul r0 => @lem1017070 A pwr add r1 mul r0 h1 h0). Qed.
Lemma lem1017072 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term28 A pwr add r1 mul r0) : term28 A pwr add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1017073 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term27 A pwr add r1 mul r0) (h2 : term28 A pwr add r1 mul r0) : term27 A pwr add r1 mul r0.
Proof. exact (@lem1017071 A pwr add r1 mul r0 h1 (@lem1017072 A pwr add r1 mul r0 h2)). Qed.
Lemma lem1017074 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term28 A pwr add r1 mul r0) : term28 A pwr add r1 mul r0.
Proof. exact (fun h0 : term27 A pwr add r1 mul r0 => @lem1017073 A pwr add r1 mul r0 h0 h1). Qed.
Lemma lem1017075 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term30 A pwr add r1 mul r0.
Proof. exact (fun h0 : term28 A pwr add r1 mul r0 => @lem1017074 A pwr add r1 mul r0 h0). Qed.
Lemma lem1017078 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term28 A pwr add r1 mul r0.
Proof. exact (@lem1017075 A pwr add r1 mul r0 (@lem1017067 A pwr add r1 mul r0)). Qed.
Lemma lem1017079 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term28 A pwr add r1 mul r0.
Proof. exact (@lem1017078 A pwr add r1 mul r0). Qed.
Lemma lem1017197 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1017198 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term25 A add r1 mul r0) = (term31 A add r1 mul r0).
Proof. exact (@lem1017197 (term26 A add r1 mul r0)). Qed.
Lemma lem1017200 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1017201 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term31 A add r1 mul r0) = (term23 A add r1 mul r0).
Proof. exact (@lem1017200 (term23 A add r1 mul r0)). Qed.
Lemma lem1017204 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term25 A add r1 mul r0) = (term23 A add r1 mul r0).
Proof. exact (TRANS (@lem1017198 A add r1 mul r0) (@lem1017201 A add r1 mul r0)). Qed.
Lemma lem1017309 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term33 A mul pwr) = (term33 A mul pwr).
Proof. exact (eq_refl (term33 A mul pwr)). Qed.
Lemma lem1017310 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term34 A pwr add r1 mul r0) = (term35 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017309 A mul pwr) (@lem1017204 A add r1 mul r0)). Qed.
Lemma lem1017313 {A : Type'} (pwr : type1423 A) (r1 : A) : (term36 A pwr r1) = (term36 A pwr r1).
Proof. exact (eq_refl (term36 A pwr r1)). Qed.
Lemma lem1017314 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term37 A pwr add r1 mul r0) = (term38 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017313 A pwr r1) (@lem1017310 A pwr add r1 mul r0)). Qed.
Lemma lem1017317 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term39 A add mul) = (term39 A add mul).
Proof. exact (eq_refl (term39 A add mul)). Qed.
Lemma lem1017318 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term40 A pwr add r1 mul r0) = (term41 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017317 A add mul) (@lem1017314 A pwr add r1 mul r0)). Qed.
Lemma lem1017321 {A : Type'} (mul : type1400 A) (r0 : A) : (term42 A mul r0) = (term42 A mul r0).
Proof. exact (eq_refl (term42 A mul r0)). Qed.
Lemma lem1017322 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term43 A pwr add r1 mul r0) = (term44 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017321 A mul r0) (@lem1017318 A pwr add r1 mul r0)). Qed.
Lemma lem1017325 {A : Type'} (mul : type1400 A) (r1 : A) : (term45 A mul r1) = (term45 A mul r1).
Proof. exact (eq_refl (term45 A mul r1)). Qed.
Lemma lem1017326 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term46 A pwr add r1 mul r0) = (term47 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017325 A mul r1) (@lem1017322 A pwr add r1 mul r0)). Qed.
Lemma lem1017329 {A : Type'} (mul : type1400 A) : (term48 A mul) = (term48 A mul).
Proof. exact (eq_refl (term48 A mul)). Qed.
Lemma lem1017330 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term49 A pwr add r1 mul r0) = (term50 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017329 A mul) (@lem1017326 A pwr add r1 mul r0)). Qed.
Lemma lem1017333 {A : Type'} (mul : type1400 A) : (term51 A mul) = (term51 A mul).
Proof. exact (eq_refl (term51 A mul)). Qed.
Lemma lem1017334 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term52 A pwr add r1 mul r0) = (term53 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017333 A mul) (@lem1017330 A pwr add r1 mul r0)). Qed.
Lemma lem1017337 {A : Type'} (add : type1400 A) (r0 : A) : (term45 A add r0) = (term45 A add r0).
Proof. exact (eq_refl (term45 A add r0)). Qed.
Lemma lem1017338 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term54 A pwr add r1 mul r0) = (term55 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017337 A add r0) (@lem1017334 A pwr add r1 mul r0)). Qed.
Lemma lem1017341 {A : Type'} (add : type1400 A) : (term48 A add) = (term48 A add).
Proof. exact (eq_refl (term48 A add)). Qed.
Lemma lem1017342 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term56 A pwr add r1 mul r0) = (term57 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017341 A add) (@lem1017338 A pwr add r1 mul r0)). Qed.
Lemma lem1017345 {A : Type'} (add : type1400 A) : (term51 A add) = (term51 A add).
Proof. exact (eq_refl (term51 A add)). Qed.
Lemma lem1017346 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term27 A pwr add r1 mul r0) = (term58 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017345 A add) (@lem1017342 A pwr add r1 mul r0)). Qed.
Lemma lem1017349 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term59 A add r1 mul r0) = (term60 A add r1 mul r0).
Proof. exact (fun_ext (fun pwr : type1423 A => @lem1017346 A pwr add r1 mul r0)). Qed.
Lemma lem1017350 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem1017351 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term61 A add r1 mul r0) = (term62 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017350 A) (@lem1017349 A add r1 mul r0)). Qed.
Lemma lem1017356 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term63 A r1 mul r0) = (term64 A r1 mul r0).
Proof. exact (fun_ext (fun add : type1400 A => @lem1017351 A add r1 mul r0)). Qed.
Lemma lem1017357 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1017358 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term65 A r1 mul r0) = (term66 A r1 mul r0).
Proof. exact (MK_COMB (@lem1017357 A) (@lem1017356 A r1 mul r0)). Qed.
Lemma lem1017363 {A : Type'} (mul : type1400 A) (r0 : A) : (term67 A mul r0) = (term68 A mul r0).
Proof. exact (fun_ext (fun r1 : A => @lem1017358 A r1 mul r0)). Qed.
Lemma lem1017364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017365 {A : Type'} (mul : type1400 A) (r0 : A) : (term69 A mul r0) = (term70 A mul r0).
Proof. exact (MK_COMB (@lem1017364 A) (@lem1017363 A mul r0)). Qed.
Lemma lem1017370 {A : Type'} (r0 : A) : (term71 A r0) = (term72 A r0).
Proof. exact (fun_ext (fun mul : type1400 A => @lem1017365 A mul r0)). Qed.
Lemma lem1017371 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1017372 {A : Type'} (r0 : A) : (term73 A r0) = (term74 A r0).
Proof. exact (MK_COMB (@lem1017371 A) (@lem1017370 A r0)). Qed.
Lemma lem1017377 {A : Type'} : (term75 A) = (term76 A).
Proof. exact (fun_ext (fun r0 : A => @lem1017372 A r0)). Qed.
Lemma lem1017378 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017387 {A : Type'} : (term77 A) = (term78 A).
Proof. exact (MK_COMB (@lem1017378 A) (@lem1017377 A)). Qed.
Lemma lem1017388 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : ((mul x r0) = r0) = ((mul x r0) = r0).
Proof. exact (eq_refl ((mul x r0) = r0)). Qed.
Lemma lem1017389 {A : Type'} (mul : type1400 A) (r0 : A) : (term79 A mul r0) = (term79 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1017388 A mul x r0)). Qed.
Lemma lem1017390 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017391 {A : Type'} (mul : type1400 A) (r0 : A) : (term80 A mul r0) = (term80 A mul r0).
Proof. exact (MK_COMB (@lem1017390 A) (@lem1017389 A mul r0)). Qed.
Lemma lem1017392 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : ((mul x r1) = x) = ((mul x r1) = x).
Proof. exact (eq_refl ((mul x r1) = x)). Qed.
Lemma lem1017393 {A : Type'} (mul : type1400 A) (r1 : A) : (term81 A mul r1) = (term81 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1017392 A mul r1 x)). Qed.
Lemma lem1017394 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017395 {A : Type'} (mul : type1400 A) (r1 : A) : (term82 A mul r1) = (term82 A mul r1).
Proof. exact (MK_COMB (@lem1017394 A) (@lem1017393 A mul r1)). Qed.
Lemma lem1017396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017397 {A : Type'} (mul : type1400 A) (r1 : A) : (term83 A mul r1) = (term83 A mul r1).
Proof. exact (MK_COMB (@lem1017396) (@lem1017395 A mul r1)). Qed.
Lemma lem1017398 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term84 A r1 mul r0) = (term84 A r1 mul r0).
Proof. exact (MK_COMB (@lem1017397 A mul r1) (@lem1017391 A mul r0)). Qed.
Lemma lem1017399 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : ((term85 A mul add m n p) = (term86 A add m mul n p)) = ((term85 A mul add m n p) = (term86 A add m mul n p)).
Proof. exact (eq_refl ((term85 A mul add m n p) = (term86 A add m mul n p))). Qed.
Lemma lem1017400 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term87 A add m mul n) = (term87 A add m mul n).
Proof. exact (fun_ext (fun p : A => @lem1017399 A add m mul n p)). Qed.
Lemma lem1017401 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017402 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term88 A add m mul n) = (term88 A add m mul n).
Proof. exact (MK_COMB (@lem1017401 A) (@lem1017400 A add m mul n)). Qed.
Lemma lem1017403 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term89 A add m mul) = (term89 A add m mul).
Proof. exact (fun_ext (fun n : A => @lem1017402 A add m mul n)). Qed.
Lemma lem1017404 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017405 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term90 A add m mul) = (term90 A add m mul).
Proof. exact (MK_COMB (@lem1017404 A) (@lem1017403 A add m mul)). Qed.
Lemma lem1017406 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term91 A add mul) = (term91 A add mul).
Proof. exact (fun_ext (fun m : A => @lem1017405 A add m mul)). Qed.
Lemma lem1017407 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017408 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term92 A add mul) = (term92 A add mul).
Proof. exact (MK_COMB (@lem1017407 A) (@lem1017406 A add mul)). Qed.
Lemma lem1017409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017410 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term93 A add mul) = (term93 A add mul).
Proof. exact (MK_COMB (@lem1017409) (@lem1017408 A add mul)). Qed.
Lemma lem1017411 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term94 A add r1 mul r0) = (term94 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017410 A add mul) (@lem1017398 A r1 mul r0)). Qed.
Lemma lem1017412 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : ((term95 A m mul n p) = (term95 A n mul m p)) = ((term95 A m mul n p) = (term95 A n mul m p)).
Proof. exact (eq_refl ((term95 A m mul n p) = (term95 A n mul m p))). Qed.
Lemma lem1017413 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term96 A n mul m) = (term96 A n mul m).
Proof. exact (fun_ext (fun p : A => @lem1017412 A n mul m p)). Qed.
Lemma lem1017414 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017415 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term97 A n mul m) = (term97 A n mul m).
Proof. exact (MK_COMB (@lem1017414 A) (@lem1017413 A n mul m)). Qed.
Lemma lem1017416 {A : Type'} (mul : type1400 A) (m : A) : (term98 A mul m) = (term98 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1017415 A n mul m)). Qed.
Lemma lem1017417 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017418 {A : Type'} (mul : type1400 A) (m : A) : (term99 A mul m) = (term99 A mul m).
Proof. exact (MK_COMB (@lem1017417 A) (@lem1017416 A mul m)). Qed.
Lemma lem1017419 {A : Type'} (mul : type1400 A) : (term100 A mul) = (term100 A mul).
Proof. exact (fun_ext (fun m : A => @lem1017418 A mul m)). Qed.
Lemma lem1017420 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017421 {A : Type'} (mul : type1400 A) : (term101 A mul) = (term101 A mul).
Proof. exact (MK_COMB (@lem1017420 A) (@lem1017419 A mul)). Qed.
Lemma lem1017422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017423 {A : Type'} (mul : type1400 A) : (term102 A mul) = (term102 A mul).
Proof. exact (MK_COMB (@lem1017422) (@lem1017421 A mul)). Qed.
Lemma lem1017424 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term103 A add r1 mul r0) = (term103 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017423 A mul) (@lem1017411 A add r1 mul r0)). Qed.
Lemma lem1017425 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : ((term104 A mul m n p) = (term95 A m mul n p)) = ((term104 A mul m n p) = (term95 A m mul n p)).
Proof. exact (eq_refl ((term104 A mul m n p) = (term95 A m mul n p))). Qed.
Lemma lem1017426 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term105 A m mul n) = (term105 A m mul n).
Proof. exact (fun_ext (fun p : A => @lem1017425 A m mul n p)). Qed.
Lemma lem1017427 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017428 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term106 A m mul n) = (term106 A m mul n).
Proof. exact (MK_COMB (@lem1017427 A) (@lem1017426 A m mul n)). Qed.
Lemma lem1017429 {A : Type'} (m : A) (mul : type1400 A) : (term107 A m mul) = (term107 A m mul).
Proof. exact (fun_ext (fun n : A => @lem1017428 A m mul n)). Qed.
Lemma lem1017430 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017431 {A : Type'} (m : A) (mul : type1400 A) : (term108 A m mul) = (term108 A m mul).
Proof. exact (MK_COMB (@lem1017430 A) (@lem1017429 A m mul)). Qed.
Lemma lem1017432 {A : Type'} (mul : type1400 A) : (term109 A mul) = (term109 A mul).
Proof. exact (fun_ext (fun m : A => @lem1017431 A m mul)). Qed.
Lemma lem1017433 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017434 {A : Type'} (mul : type1400 A) : (term110 A mul) = (term110 A mul).
Proof. exact (MK_COMB (@lem1017433 A) (@lem1017432 A mul)). Qed.
Lemma lem1017435 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017436 {A : Type'} (mul : type1400 A) : (term111 A mul) = (term111 A mul).
Proof. exact (MK_COMB (@lem1017435) (@lem1017434 A mul)). Qed.
Lemma lem1017437 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term112 A add r1 mul r0) = (term112 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017436 A mul) (@lem1017424 A add r1 mul r0)). Qed.
Lemma lem1017438 {A : Type'} (mul : type1400 A) (n : A) (m : A) : ((mul m n) = (mul n m)) = ((mul m n) = (mul n m)).
Proof. exact (eq_refl ((mul m n) = (mul n m))). Qed.
Lemma lem1017439 {A : Type'} (mul : type1400 A) (m : A) : (term113 A mul m) = (term113 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1017438 A mul n m)). Qed.
Lemma lem1017440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017441 {A : Type'} (mul : type1400 A) (m : A) : (term114 A mul m) = (term114 A mul m).
Proof. exact (MK_COMB (@lem1017440 A) (@lem1017439 A mul m)). Qed.
Lemma lem1017442 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun m : A => @lem1017441 A mul m)). Qed.
Lemma lem1017443 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017444 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1017443 A) (@lem1017442 A mul)). Qed.
Lemma lem1017445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017446 {A : Type'} (mul : type1400 A) : (term116 A mul) = (term116 A mul).
Proof. exact (MK_COMB (@lem1017445) (@lem1017444 A mul)). Qed.
Lemma lem1017447 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term117 A add r1 mul r0) = (term117 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017446 A mul) (@lem1017437 A add r1 mul r0)). Qed.
Lemma lem1017448 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : ((add x r0) = x) = ((add x r0) = x).
Proof. exact (eq_refl ((add x r0) = x)). Qed.
Lemma lem1017449 {A : Type'} (add : type1400 A) (r0 : A) : (term81 A add r0) = (term81 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1017448 A add r0 x)). Qed.
Lemma lem1017450 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017451 {A : Type'} (add : type1400 A) (r0 : A) : (term82 A add r0) = (term82 A add r0).
Proof. exact (MK_COMB (@lem1017450 A) (@lem1017449 A add r0)). Qed.
Lemma lem1017452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017453 {A : Type'} (add : type1400 A) (r0 : A) : (term83 A add r0) = (term83 A add r0).
Proof. exact (MK_COMB (@lem1017452) (@lem1017451 A add r0)). Qed.
Lemma lem1017454 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term118 A add r1 mul r0) = (term118 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017453 A add r0) (@lem1017447 A add r1 mul r0)). Qed.
Lemma lem1017455 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : ((term95 A m add n p) = (term95 A n add m p)) = ((term95 A m add n p) = (term95 A n add m p)).
Proof. exact (eq_refl ((term95 A m add n p) = (term95 A n add m p))). Qed.
Lemma lem1017456 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term96 A n add m) = (term96 A n add m).
Proof. exact (fun_ext (fun p : A => @lem1017455 A n add m p)). Qed.
Lemma lem1017457 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017458 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term97 A n add m) = (term97 A n add m).
Proof. exact (MK_COMB (@lem1017457 A) (@lem1017456 A n add m)). Qed.
Lemma lem1017459 {A : Type'} (add : type1400 A) (m : A) : (term98 A add m) = (term98 A add m).
Proof. exact (fun_ext (fun n : A => @lem1017458 A n add m)). Qed.
Lemma lem1017460 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017461 {A : Type'} (add : type1400 A) (m : A) : (term99 A add m) = (term99 A add m).
Proof. exact (MK_COMB (@lem1017460 A) (@lem1017459 A add m)). Qed.
Lemma lem1017462 {A : Type'} (add : type1400 A) : (term100 A add) = (term100 A add).
Proof. exact (fun_ext (fun m : A => @lem1017461 A add m)). Qed.
Lemma lem1017463 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017464 {A : Type'} (add : type1400 A) : (term101 A add) = (term101 A add).
Proof. exact (MK_COMB (@lem1017463 A) (@lem1017462 A add)). Qed.
Lemma lem1017465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017466 {A : Type'} (add : type1400 A) : (term102 A add) = (term102 A add).
Proof. exact (MK_COMB (@lem1017465) (@lem1017464 A add)). Qed.
Lemma lem1017467 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term119 A add r1 mul r0) = (term119 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017466 A add) (@lem1017454 A add r1 mul r0)). Qed.
Lemma lem1017468 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : ((term104 A add m n p) = (term95 A m add n p)) = ((term104 A add m n p) = (term95 A m add n p)).
Proof. exact (eq_refl ((term104 A add m n p) = (term95 A m add n p))). Qed.
Lemma lem1017469 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term105 A m add n) = (term105 A m add n).
Proof. exact (fun_ext (fun p : A => @lem1017468 A m add n p)). Qed.
Lemma lem1017470 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017471 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term106 A m add n) = (term106 A m add n).
Proof. exact (MK_COMB (@lem1017470 A) (@lem1017469 A m add n)). Qed.
Lemma lem1017472 {A : Type'} (m : A) (add : type1400 A) : (term107 A m add) = (term107 A m add).
Proof. exact (fun_ext (fun n : A => @lem1017471 A m add n)). Qed.
Lemma lem1017473 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017474 {A : Type'} (m : A) (add : type1400 A) : (term108 A m add) = (term108 A m add).
Proof. exact (MK_COMB (@lem1017473 A) (@lem1017472 A m add)). Qed.
Lemma lem1017475 {A : Type'} (add : type1400 A) : (term109 A add) = (term109 A add).
Proof. exact (fun_ext (fun m : A => @lem1017474 A m add)). Qed.
Lemma lem1017476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017477 {A : Type'} (add : type1400 A) : (term110 A add) = (term110 A add).
Proof. exact (MK_COMB (@lem1017476 A) (@lem1017475 A add)). Qed.
Lemma lem1017478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017479 {A : Type'} (add : type1400 A) : (term111 A add) = (term111 A add).
Proof. exact (MK_COMB (@lem1017478) (@lem1017477 A add)). Qed.
Lemma lem1017480 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term120 A add r1 mul r0) = (term120 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017479 A add) (@lem1017467 A add r1 mul r0)). Qed.
Lemma lem1017481 {A : Type'} (add : type1400 A) (n : A) (m : A) : ((add m n) = (add n m)) = ((add m n) = (add n m)).
Proof. exact (eq_refl ((add m n) = (add n m))). Qed.
Lemma lem1017482 {A : Type'} (add : type1400 A) (m : A) : (term113 A add m) = (term113 A add m).
Proof. exact (fun_ext (fun n : A => @lem1017481 A add n m)). Qed.
Lemma lem1017483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017484 {A : Type'} (add : type1400 A) (m : A) : (term114 A add m) = (term114 A add m).
Proof. exact (MK_COMB (@lem1017483 A) (@lem1017482 A add m)). Qed.
Lemma lem1017485 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun m : A => @lem1017484 A add m)). Qed.
Lemma lem1017486 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017487 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1017486 A) (@lem1017485 A add)). Qed.
Lemma lem1017488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1017489 {A : Type'} (add : type1400 A) : (term116 A add) = (term116 A add).
Proof. exact (MK_COMB (@lem1017488) (@lem1017487 A add)). Qed.
Lemma lem1017490 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term23 A add r1 mul r0) = (term23 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017489 A add) (@lem1017480 A add r1 mul r0)). Qed.
Lemma lem1017491 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : ((term121 A pwr x n) = (term122 A mul pwr x n)) = ((term121 A pwr x n) = (term122 A mul pwr x n)).
Proof. exact (eq_refl ((term121 A pwr x n) = (term122 A mul pwr x n))). Qed.
Lemma lem1017492 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term123 A mul pwr x) = (term123 A mul pwr x).
Proof. exact (fun_ext (fun n : nat => @lem1017491 A mul pwr x n)). Qed.
Lemma lem1017493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1017494 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term124 A mul pwr x) = (term124 A mul pwr x).
Proof. exact (MK_COMB (@lem1017493) (@lem1017492 A mul pwr x)). Qed.
Lemma lem1017495 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term125 A mul pwr) = (term125 A mul pwr).
Proof. exact (fun_ext (fun x : A => @lem1017494 A mul pwr x)). Qed.
Lemma lem1017496 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017497 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term21 A mul pwr) = (term21 A mul pwr).
Proof. exact (MK_COMB (@lem1017496 A) (@lem1017495 A mul pwr)). Qed.
Lemma lem1017498 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017499 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term33 A mul pwr) = (term33 A mul pwr).
Proof. exact (MK_COMB (@lem1017498) (@lem1017497 A mul pwr)). Qed.
Lemma lem1017500 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term35 A pwr add r1 mul r0) = (term35 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017499 A mul pwr) (@lem1017490 A add r1 mul r0)). Qed.
Lemma lem1017501 {A : Type'} (pwr : type1423 A) (x : A) (r1 : A) : ((term126 A pwr x) = r1) = ((term126 A pwr x) = r1).
Proof. exact (eq_refl ((term126 A pwr x) = r1)). Qed.
Lemma lem1017502 {A : Type'} (pwr : type1423 A) (r1 : A) : (term127 A pwr r1) = (term127 A pwr r1).
Proof. exact (fun_ext (fun x : A => @lem1017501 A pwr x r1)). Qed.
Lemma lem1017503 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017504 {A : Type'} (pwr : type1423 A) (r1 : A) : (term22 A pwr r1) = (term22 A pwr r1).
Proof. exact (MK_COMB (@lem1017503 A) (@lem1017502 A pwr r1)). Qed.
Lemma lem1017505 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017506 {A : Type'} (pwr : type1423 A) (r1 : A) : (term36 A pwr r1) = (term36 A pwr r1).
Proof. exact (MK_COMB (@lem1017505) (@lem1017504 A pwr r1)). Qed.
Lemma lem1017507 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term38 A pwr add r1 mul r0) = (term38 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017506 A pwr r1) (@lem1017500 A pwr add r1 mul r0)). Qed.
Lemma lem1017508 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : ((term128 A mul x add y z) = (term129 A add y mul x z)) = ((term128 A mul x add y z) = (term129 A add y mul x z)).
Proof. exact (eq_refl ((term128 A mul x add y z) = (term129 A add y mul x z))). Qed.
Lemma lem1017509 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term130 A add y mul x) = (term130 A add y mul x).
Proof. exact (fun_ext (fun z : A => @lem1017508 A add y mul x z)). Qed.
Lemma lem1017510 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017511 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term131 A add y mul x) = (term131 A add y mul x).
Proof. exact (MK_COMB (@lem1017510 A) (@lem1017509 A add y mul x)). Qed.
Lemma lem1017512 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term132 A add mul x) = (term132 A add mul x).
Proof. exact (fun_ext (fun y : A => @lem1017511 A add y mul x)). Qed.
Lemma lem1017513 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017514 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term133 A add mul x) = (term133 A add mul x).
Proof. exact (MK_COMB (@lem1017513 A) (@lem1017512 A add mul x)). Qed.
Lemma lem1017515 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term134 A add mul) = (term134 A add mul).
Proof. exact (fun_ext (fun x : A => @lem1017514 A add mul x)). Qed.
Lemma lem1017516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017517 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term20 A add mul) = (term20 A add mul).
Proof. exact (MK_COMB (@lem1017516 A) (@lem1017515 A add mul)). Qed.
Lemma lem1017518 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017519 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term39 A add mul) = (term39 A add mul).
Proof. exact (MK_COMB (@lem1017518) (@lem1017517 A add mul)). Qed.
Lemma lem1017520 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term41 A pwr add r1 mul r0) = (term41 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017519 A add mul) (@lem1017507 A pwr add r1 mul r0)). Qed.
Lemma lem1017521 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : ((mul r0 x) = r0) = ((mul r0 x) = r0).
Proof. exact (eq_refl ((mul r0 x) = r0)). Qed.
Lemma lem1017522 {A : Type'} (mul : type1400 A) (r0 : A) : (term135 A mul r0) = (term135 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1017521 A mul x r0)). Qed.
Lemma lem1017523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017524 {A : Type'} (mul : type1400 A) (r0 : A) : (term18 A mul r0) = (term18 A mul r0).
Proof. exact (MK_COMB (@lem1017523 A) (@lem1017522 A mul r0)). Qed.
Lemma lem1017525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017526 {A : Type'} (mul : type1400 A) (r0 : A) : (term42 A mul r0) = (term42 A mul r0).
Proof. exact (MK_COMB (@lem1017525) (@lem1017524 A mul r0)). Qed.
Lemma lem1017527 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term44 A pwr add r1 mul r0) = (term44 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017526 A mul r0) (@lem1017520 A pwr add r1 mul r0)). Qed.
Lemma lem1017528 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : ((mul r1 x) = x) = ((mul r1 x) = x).
Proof. exact (eq_refl ((mul r1 x) = x)). Qed.
Lemma lem1017529 {A : Type'} (mul : type1400 A) (r1 : A) : (term136 A mul r1) = (term136 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1017528 A mul r1 x)). Qed.
Lemma lem1017530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017531 {A : Type'} (mul : type1400 A) (r1 : A) : (term13 A mul r1) = (term13 A mul r1).
Proof. exact (MK_COMB (@lem1017530 A) (@lem1017529 A mul r1)). Qed.
Lemma lem1017532 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017533 {A : Type'} (mul : type1400 A) (r1 : A) : (term45 A mul r1) = (term45 A mul r1).
Proof. exact (MK_COMB (@lem1017532) (@lem1017531 A mul r1)). Qed.
Lemma lem1017534 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term47 A pwr add r1 mul r0) = (term47 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017533 A mul r1) (@lem1017527 A pwr add r1 mul r0)). Qed.
Lemma lem1017535 {A : Type'} (mul : type1400 A) (y : A) (x : A) : ((mul x y) = (mul y x)) = ((mul x y) = (mul y x)).
Proof. exact (eq_refl ((mul x y) = (mul y x))). Qed.
Lemma lem1017536 {A : Type'} (mul : type1400 A) (x : A) : (term113 A mul x) = (term113 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1017535 A mul y x)). Qed.
Lemma lem1017537 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017538 {A : Type'} (mul : type1400 A) (x : A) : (term114 A mul x) = (term114 A mul x).
Proof. exact (MK_COMB (@lem1017537 A) (@lem1017536 A mul x)). Qed.
Lemma lem1017539 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun x : A => @lem1017538 A mul x)). Qed.
Lemma lem1017540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017541 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1017540 A) (@lem1017539 A mul)). Qed.
Lemma lem1017542 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017543 {A : Type'} (mul : type1400 A) : (term48 A mul) = (term48 A mul).
Proof. exact (MK_COMB (@lem1017542) (@lem1017541 A mul)). Qed.
Lemma lem1017544 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term50 A pwr add r1 mul r0) = (term50 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017543 A mul) (@lem1017534 A pwr add r1 mul r0)). Qed.
Lemma lem1017545 {A : Type'} (mul : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x mul y z) = (term104 A mul x y z)) = ((term95 A x mul y z) = (term104 A mul x y z)).
Proof. exact (eq_refl ((term95 A x mul y z) = (term104 A mul x y z))). Qed.
Lemma lem1017546 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term137 A mul x y) = (term137 A mul x y).
Proof. exact (fun_ext (fun z : A => @lem1017545 A mul x y z)). Qed.
Lemma lem1017547 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017548 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term138 A mul x y) = (term138 A mul x y).
Proof. exact (MK_COMB (@lem1017547 A) (@lem1017546 A mul x y)). Qed.
Lemma lem1017549 {A : Type'} (mul : type1400 A) (x : A) : (term139 A mul x) = (term139 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1017548 A mul x y)). Qed.
Lemma lem1017550 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017551 {A : Type'} (mul : type1400 A) (x : A) : (term140 A mul x) = (term140 A mul x).
Proof. exact (MK_COMB (@lem1017550 A) (@lem1017549 A mul x)). Qed.
Lemma lem1017552 {A : Type'} (mul : type1400 A) : (term141 A mul) = (term141 A mul).
Proof. exact (fun_ext (fun x : A => @lem1017551 A mul x)). Qed.
Lemma lem1017553 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017554 {A : Type'} (mul : type1400 A) : (term9 A mul) = (term9 A mul).
Proof. exact (MK_COMB (@lem1017553 A) (@lem1017552 A mul)). Qed.
Lemma lem1017555 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017556 {A : Type'} (mul : type1400 A) : (term51 A mul) = (term51 A mul).
Proof. exact (MK_COMB (@lem1017555) (@lem1017554 A mul)). Qed.
Lemma lem1017557 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term53 A pwr add r1 mul r0) = (term53 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017556 A mul) (@lem1017544 A pwr add r1 mul r0)). Qed.
Lemma lem1017558 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : ((add r0 x) = x) = ((add r0 x) = x).
Proof. exact (eq_refl ((add r0 x) = x)). Qed.
Lemma lem1017559 {A : Type'} (add : type1400 A) (r0 : A) : (term136 A add r0) = (term136 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1017558 A add r0 x)). Qed.
Lemma lem1017560 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017561 {A : Type'} (add : type1400 A) (r0 : A) : (term13 A add r0) = (term13 A add r0).
Proof. exact (MK_COMB (@lem1017560 A) (@lem1017559 A add r0)). Qed.
Lemma lem1017562 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017563 {A : Type'} (add : type1400 A) (r0 : A) : (term45 A add r0) = (term45 A add r0).
Proof. exact (MK_COMB (@lem1017562) (@lem1017561 A add r0)). Qed.
Lemma lem1017564 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term55 A pwr add r1 mul r0) = (term55 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017563 A add r0) (@lem1017557 A pwr add r1 mul r0)). Qed.
Lemma lem1017565 {A : Type'} (add : type1400 A) (y : A) (x : A) : ((add x y) = (add y x)) = ((add x y) = (add y x)).
Proof. exact (eq_refl ((add x y) = (add y x))). Qed.
Lemma lem1017566 {A : Type'} (add : type1400 A) (x : A) : (term113 A add x) = (term113 A add x).
Proof. exact (fun_ext (fun y : A => @lem1017565 A add y x)). Qed.
Lemma lem1017567 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017568 {A : Type'} (add : type1400 A) (x : A) : (term114 A add x) = (term114 A add x).
Proof. exact (MK_COMB (@lem1017567 A) (@lem1017566 A add x)). Qed.
Lemma lem1017569 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun x : A => @lem1017568 A add x)). Qed.
Lemma lem1017570 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017571 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1017570 A) (@lem1017569 A add)). Qed.
Lemma lem1017572 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017573 {A : Type'} (add : type1400 A) : (term48 A add) = (term48 A add).
Proof. exact (MK_COMB (@lem1017572) (@lem1017571 A add)). Qed.
Lemma lem1017574 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term57 A pwr add r1 mul r0) = (term57 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017573 A add) (@lem1017564 A pwr add r1 mul r0)). Qed.
Lemma lem1017575 {A : Type'} (add : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x add y z) = (term104 A add x y z)) = ((term95 A x add y z) = (term104 A add x y z)).
Proof. exact (eq_refl ((term95 A x add y z) = (term104 A add x y z))). Qed.
Lemma lem1017576 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term137 A add x y) = (term137 A add x y).
Proof. exact (fun_ext (fun z : A => @lem1017575 A add x y z)). Qed.
Lemma lem1017577 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017578 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term138 A add x y) = (term138 A add x y).
Proof. exact (MK_COMB (@lem1017577 A) (@lem1017576 A add x y)). Qed.
Lemma lem1017579 {A : Type'} (add : type1400 A) (x : A) : (term139 A add x) = (term139 A add x).
Proof. exact (fun_ext (fun y : A => @lem1017578 A add x y)). Qed.
Lemma lem1017580 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017581 {A : Type'} (add : type1400 A) (x : A) : (term140 A add x) = (term140 A add x).
Proof. exact (MK_COMB (@lem1017580 A) (@lem1017579 A add x)). Qed.
Lemma lem1017582 {A : Type'} (add : type1400 A) : (term141 A add) = (term141 A add).
Proof. exact (fun_ext (fun x : A => @lem1017581 A add x)). Qed.
Lemma lem1017583 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017584 {A : Type'} (add : type1400 A) : (term9 A add) = (term9 A add).
Proof. exact (MK_COMB (@lem1017583 A) (@lem1017582 A add)). Qed.
Lemma lem1017585 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1017586 {A : Type'} (add : type1400 A) : (term51 A add) = (term51 A add).
Proof. exact (MK_COMB (@lem1017585) (@lem1017584 A add)). Qed.
Lemma lem1017587 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term58 A pwr add r1 mul r0) = (term58 A pwr add r1 mul r0).
Proof. exact (MK_COMB (@lem1017586 A add) (@lem1017574 A pwr add r1 mul r0)). Qed.
Lemma lem1017588 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term60 A add r1 mul r0) = (term60 A add r1 mul r0).
Proof. exact (fun_ext (fun pwr : type1423 A => @lem1017587 A pwr add r1 mul r0)). Qed.
Lemma lem1017589 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem1017590 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term62 A add r1 mul r0) = (term62 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1017589 A) (@lem1017588 A add r1 mul r0)). Qed.
Lemma lem1017591 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term64 A r1 mul r0) = (term64 A r1 mul r0).
Proof. exact (fun_ext (fun add : type1400 A => @lem1017590 A add r1 mul r0)). Qed.
Lemma lem1017592 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1017593 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term66 A r1 mul r0) = (term66 A r1 mul r0).
Proof. exact (MK_COMB (@lem1017592 A) (@lem1017591 A r1 mul r0)). Qed.
Lemma lem1017594 {A : Type'} (mul : type1400 A) (r0 : A) : (term68 A mul r0) = (term68 A mul r0).
Proof. exact (fun_ext (fun r1 : A => @lem1017593 A r1 mul r0)). Qed.
Lemma lem1017595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017596 {A : Type'} (mul : type1400 A) (r0 : A) : (term70 A mul r0) = (term70 A mul r0).
Proof. exact (MK_COMB (@lem1017595 A) (@lem1017594 A mul r0)). Qed.
Lemma lem1017597 {A : Type'} (r0 : A) : (term72 A r0) = (term72 A r0).
Proof. exact (fun_ext (fun mul : type1400 A => @lem1017596 A mul r0)). Qed.
Lemma lem1017598 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1017599 {A : Type'} (r0 : A) : (term74 A r0) = (term74 A r0).
Proof. exact (MK_COMB (@lem1017598 A) (@lem1017597 A r0)). Qed.
Lemma lem1017600 {A : Type'} : (term76 A) = (term76 A).
Proof. exact (fun_ext (fun r0 : A => @lem1017599 A r0)). Qed.
Lemma lem1017601 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017602 {A : Type'} : (term78 A) = (term78 A).
Proof. exact (MK_COMB (@lem1017601 A) (@lem1017600 A)). Qed.
Lemma lem1017919 {A : Type'} : (term77 A) = (term78 A).
Proof. exact (TRANS (@lem1017387 A) (@lem1017602 A)). Qed.
Lemma lem1017920 {A : Type'} : (term78 A) = (term77 A).
Proof. exact (SYM (@lem1017919 A)). Qed.
Lemma lem1017921 {A : Type'} (add : type1400 A) (h1 : term9 A add) : term9 A add.
Proof. exact (h1). Qed.
Lemma lem1017922 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (h1). Qed.
Lemma lem1017923 {A : Type'} (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term13 A add r0.
Proof. exact (h1). Qed.
Lemma lem1017924 {A : Type'} (mul : type1400 A) (h1 : term9 A mul) : term9 A mul.
Proof. exact (h1). Qed.
Lemma lem1017925 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (h1). Qed.
Lemma lem1017926 {A : Type'} (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term13 A mul r1.
Proof. exact (h1). Qed.
Lemma lem1017927 {A : Type'} (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term18 A mul r0.
Proof. exact (h1). Qed.
Lemma lem1017928 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term20 A add mul.
Proof. exact (h1). Qed.
Lemma lem1017932 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1017933 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term23 A add r1 mul r0) = (term25 A add r1 mul r0).
Proof. exact (@lem1017932 (term23 A add r1 mul r0)). Qed.
Lemma lem1017934 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term25 A add r1 mul r0) = (term23 A add r1 mul r0).
Proof. exact (SYM (@lem1017933 A add r1 mul r0)). Qed.
Lemma lem1017935 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term26 A add r1 mul r0) : term26 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1017936 {A : Type'} (add : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x add y z) = (term104 A add x y z)) = ((term95 A x add y z) = (term104 A add x y z)).
Proof. exact (eq_refl ((term95 A x add y z) = (term104 A add x y z))). Qed.
Lemma lem1017937 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term137 A add x y) = (term137 A add x y).
Proof. exact (fun_ext (fun z : A => @lem1017936 A add x y z)). Qed.
Lemma lem1017938 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017939 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term138 A add x y) = (term138 A add x y).
Proof. exact (MK_COMB (@lem1017938 A) (@lem1017937 A add x y)). Qed.
Lemma lem1017940 {A : Type'} (add : type1400 A) (x : A) : (term139 A add x) = (term139 A add x).
Proof. exact (fun_ext (fun y : A => @lem1017939 A add x y)). Qed.
Lemma lem1017941 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017942 {A : Type'} (add : type1400 A) (x : A) : (term140 A add x) = (term140 A add x).
Proof. exact (MK_COMB (@lem1017941 A) (@lem1017940 A add x)). Qed.
Lemma lem1017943 {A : Type'} (add : type1400 A) : (term141 A add) = (term141 A add).
Proof. exact (fun_ext (fun x : A => @lem1017942 A add x)). Qed.
Lemma lem1017944 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017961 {A : Type'} (add : type1400 A) : (term9 A add) = (term9 A add).
Proof. exact (MK_COMB (@lem1017944 A) (@lem1017943 A add)). Qed.
Lemma lem1017962 {A : Type'} (add : type1400 A) (h1 : term9 A add) : term9 A add.
Proof. exact (EQ_MP (@lem1017961 A add) (@lem1017921 A add h1)). Qed.
Lemma lem1017963 {A : Type'} (add : type1400 A) (y : A) (x : A) : ((add x y) = (add y x)) = ((add x y) = (add y x)).
Proof. exact (eq_refl ((add x y) = (add y x))). Qed.
Lemma lem1017964 {A : Type'} (add : type1400 A) (x : A) : (term113 A add x) = (term113 A add x).
Proof. exact (fun_ext (fun y : A => @lem1017963 A add y x)). Qed.
Lemma lem1017965 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017966 {A : Type'} (add : type1400 A) (x : A) : (term114 A add x) = (term114 A add x).
Proof. exact (MK_COMB (@lem1017965 A) (@lem1017964 A add x)). Qed.
Lemma lem1017967 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun x : A => @lem1017966 A add x)). Qed.
Lemma lem1017968 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017981 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1017968 A) (@lem1017967 A add)). Qed.
Lemma lem1017982 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (EQ_MP (@lem1017981 A add) (@lem1017922 A add h1)). Qed.
Lemma lem1017983 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : ((add r0 x) = x) = ((add r0 x) = x).
Proof. exact (eq_refl ((add r0 x) = x)). Qed.
Lemma lem1017984 {A : Type'} (add : type1400 A) (r0 : A) : (term136 A add r0) = (term136 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1017983 A add r0 x)). Qed.
Lemma lem1017985 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017994 {A : Type'} (add : type1400 A) (r0 : A) : (term13 A add r0) = (term13 A add r0).
Proof. exact (MK_COMB (@lem1017985 A) (@lem1017984 A add r0)). Qed.
Lemma lem1017995 {A : Type'} (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term13 A add r0.
Proof. exact (EQ_MP (@lem1017994 A add r0) (@lem1017923 A add r0 h1)). Qed.
Lemma lem1017996 {A : Type'} (mul : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x mul y z) = (term104 A mul x y z)) = ((term95 A x mul y z) = (term104 A mul x y z)).
Proof. exact (eq_refl ((term95 A x mul y z) = (term104 A mul x y z))). Qed.
Lemma lem1017997 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term137 A mul x y) = (term137 A mul x y).
Proof. exact (fun_ext (fun z : A => @lem1017996 A mul x y z)). Qed.
Lemma lem1017998 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1017999 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term138 A mul x y) = (term138 A mul x y).
Proof. exact (MK_COMB (@lem1017998 A) (@lem1017997 A mul x y)). Qed.
Lemma lem1018000 {A : Type'} (mul : type1400 A) (x : A) : (term139 A mul x) = (term139 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1017999 A mul x y)). Qed.
Lemma lem1018001 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018002 {A : Type'} (mul : type1400 A) (x : A) : (term140 A mul x) = (term140 A mul x).
Proof. exact (MK_COMB (@lem1018001 A) (@lem1018000 A mul x)). Qed.
Lemma lem1018003 {A : Type'} (mul : type1400 A) : (term141 A mul) = (term141 A mul).
Proof. exact (fun_ext (fun x : A => @lem1018002 A mul x)). Qed.
Lemma lem1018004 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018021 {A : Type'} (mul : type1400 A) : (term9 A mul) = (term9 A mul).
Proof. exact (MK_COMB (@lem1018004 A) (@lem1018003 A mul)). Qed.
Lemma lem1018022 {A : Type'} (mul : type1400 A) (h1 : term9 A mul) : term9 A mul.
Proof. exact (EQ_MP (@lem1018021 A mul) (@lem1017924 A mul h1)). Qed.
Lemma lem1018023 {A : Type'} (mul : type1400 A) (y : A) (x : A) : ((mul x y) = (mul y x)) = ((mul x y) = (mul y x)).
Proof. exact (eq_refl ((mul x y) = (mul y x))). Qed.
Lemma lem1018024 {A : Type'} (mul : type1400 A) (x : A) : (term113 A mul x) = (term113 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1018023 A mul y x)). Qed.
Lemma lem1018025 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018026 {A : Type'} (mul : type1400 A) (x : A) : (term114 A mul x) = (term114 A mul x).
Proof. exact (MK_COMB (@lem1018025 A) (@lem1018024 A mul x)). Qed.
Lemma lem1018027 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun x : A => @lem1018026 A mul x)). Qed.
Lemma lem1018028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018041 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1018028 A) (@lem1018027 A mul)). Qed.
Lemma lem1018042 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (EQ_MP (@lem1018041 A mul) (@lem1017925 A mul h1)). Qed.
Lemma lem1018043 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : ((mul r1 x) = x) = ((mul r1 x) = x).
Proof. exact (eq_refl ((mul r1 x) = x)). Qed.
Lemma lem1018044 {A : Type'} (mul : type1400 A) (r1 : A) : (term136 A mul r1) = (term136 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1018043 A mul r1 x)). Qed.
Lemma lem1018045 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018054 {A : Type'} (mul : type1400 A) (r1 : A) : (term13 A mul r1) = (term13 A mul r1).
Proof. exact (MK_COMB (@lem1018045 A) (@lem1018044 A mul r1)). Qed.
Lemma lem1018055 {A : Type'} (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term13 A mul r1.
Proof. exact (EQ_MP (@lem1018054 A mul r1) (@lem1017926 A mul r1 h1)). Qed.
Lemma lem1018056 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : ((mul r0 x) = r0) = ((mul r0 x) = r0).
Proof. exact (eq_refl ((mul r0 x) = r0)). Qed.
Lemma lem1018057 {A : Type'} (mul : type1400 A) (r0 : A) : (term135 A mul r0) = (term135 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1018056 A mul x r0)). Qed.
Lemma lem1018058 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018067 {A : Type'} (mul : type1400 A) (r0 : A) : (term18 A mul r0) = (term18 A mul r0).
Proof. exact (MK_COMB (@lem1018058 A) (@lem1018057 A mul r0)). Qed.
Lemma lem1018068 {A : Type'} (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term18 A mul r0.
Proof. exact (EQ_MP (@lem1018067 A mul r0) (@lem1017927 A mul r0 h1)). Qed.
Lemma lem1018069 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : ((term128 A mul x add y z) = (term129 A add y mul x z)) = ((term128 A mul x add y z) = (term129 A add y mul x z)).
Proof. exact (eq_refl ((term128 A mul x add y z) = (term129 A add y mul x z))). Qed.
Lemma lem1018070 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term130 A add y mul x) = (term130 A add y mul x).
Proof. exact (fun_ext (fun z : A => @lem1018069 A add y mul x z)). Qed.
Lemma lem1018071 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018072 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term131 A add y mul x) = (term131 A add y mul x).
Proof. exact (MK_COMB (@lem1018071 A) (@lem1018070 A add y mul x)). Qed.
Lemma lem1018073 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term132 A add mul x) = (term132 A add mul x).
Proof. exact (fun_ext (fun y : A => @lem1018072 A add y mul x)). Qed.
Lemma lem1018074 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018075 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term133 A add mul x) = (term133 A add mul x).
Proof. exact (MK_COMB (@lem1018074 A) (@lem1018073 A add mul x)). Qed.
Lemma lem1018076 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term134 A add mul) = (term134 A add mul).
Proof. exact (fun_ext (fun x : A => @lem1018075 A add mul x)). Qed.
Lemma lem1018077 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1018094 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term20 A add mul) = (term20 A add mul).
Proof. exact (MK_COMB (@lem1018077 A) (@lem1018076 A add mul)). Qed.
Lemma lem1018095 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term20 A add mul.
Proof. exact (EQ_MP (@lem1018094 A add mul) (@lem1017928 A add mul h1)). Qed.
Lemma lem1018130 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018131 {A : Type'} (add : type1400 A) (m : A) : (term144 A add m) = (term145 A add m).
Proof. exact (@lem1018130 A (term113 A add m)). Qed.
Lemma lem1018132 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term146 A add m n) = ((add m n) = (add n m)).
Proof. exact (eq_refl (term146 A add m n)). Qed.
Lemma lem1018133 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018135 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term147 A add m n) = (term148 A add n m).
Proof. exact (MK_COMB (@lem1018133) (@lem1018132 A add n m)). Qed.
Lemma lem1018136 {A : Type'} (add : type1400 A) (m : A) : (term149 A add m) = (term150 A add m).
Proof. exact (fun_ext (fun n : A => @lem1018135 A add n m)). Qed.
Lemma lem1018137 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018138 {A : Type'} (add : type1400 A) (m : A) : (term145 A add m) = (term151 A add m).
Proof. exact (MK_COMB (@lem1018137 A) (@lem1018136 A add m)). Qed.
Lemma lem1018139 {A : Type'} (add : type1400 A) (m : A) : (term144 A add m) = (term151 A add m).
Proof. exact (TRANS (@lem1018131 A add m) (@lem1018138 A add m)). Qed.
Lemma lem1018140 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018141 {A : Type'} (add : type1400 A) : (term152 A add) = (term153 A add).
Proof. exact (@lem1018140 A (term115 A add)). Qed.
Lemma lem1018142 {A : Type'} (add : type1400 A) (m : A) : (term154 A add m) = (term114 A add m).
Proof. exact (eq_refl (term154 A add m)). Qed.
Lemma lem1018143 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018144 {A : Type'} (add : type1400 A) (m : A) : (term155 A add m) = (term144 A add m).
Proof. exact (MK_COMB (@lem1018143) (@lem1018142 A add m)). Qed.
Lemma lem1018145 {A : Type'} (add : type1400 A) (m : A) : (term155 A add m) = (term151 A add m).
Proof. exact (TRANS (@lem1018144 A add m) (@lem1018139 A add m)). Qed.
Lemma lem1018146 {A : Type'} (add : type1400 A) : (term156 A add) = (term157 A add).
Proof. exact (fun_ext (fun m : A => @lem1018145 A add m)). Qed.
Lemma lem1018147 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018148 {A : Type'} (add : type1400 A) : (term153 A add) = (term158 A add).
Proof. exact (MK_COMB (@lem1018147 A) (@lem1018146 A add)). Qed.
Lemma lem1018149 {A : Type'} (add : type1400 A) : (term152 A add) = (term158 A add).
Proof. exact (TRANS (@lem1018141 A add) (@lem1018148 A add)). Qed.
Lemma lem1018151 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018152 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term159 A m add n) = (term160 A m add n).
Proof. exact (@lem1018151 A (term105 A m add n)). Qed.
Lemma lem1018153 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term161 A m add n p) = ((term104 A add m n p) = (term95 A m add n p)).
Proof. exact (eq_refl (term161 A m add n p)). Qed.
Lemma lem1018154 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018156 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term162 A m add n p) = (term163 A m add n p).
Proof. exact (MK_COMB (@lem1018154) (@lem1018153 A m add n p)). Qed.
Lemma lem1018157 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term164 A m add n) = (term165 A m add n).
Proof. exact (fun_ext (fun p : A => @lem1018156 A m add n p)). Qed.
Lemma lem1018158 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018159 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term160 A m add n) = (term166 A m add n).
Proof. exact (MK_COMB (@lem1018158 A) (@lem1018157 A m add n)). Qed.
Lemma lem1018160 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term159 A m add n) = (term166 A m add n).
Proof. exact (TRANS (@lem1018152 A m add n) (@lem1018159 A m add n)). Qed.
Lemma lem1018161 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018162 {A : Type'} (m : A) (add : type1400 A) : (term167 A m add) = (term168 A m add).
Proof. exact (@lem1018161 A (term107 A m add)). Qed.
Lemma lem1018163 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term169 A m add n) = (term106 A m add n).
Proof. exact (eq_refl (term169 A m add n)). Qed.
Lemma lem1018164 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018165 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term170 A m add n) = (term159 A m add n).
Proof. exact (MK_COMB (@lem1018164) (@lem1018163 A m add n)). Qed.
Lemma lem1018166 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term170 A m add n) = (term166 A m add n).
Proof. exact (TRANS (@lem1018165 A m add n) (@lem1018160 A m add n)). Qed.
Lemma lem1018167 {A : Type'} (m : A) (add : type1400 A) : (term171 A m add) = (term172 A m add).
Proof. exact (fun_ext (fun n : A => @lem1018166 A m add n)). Qed.
Lemma lem1018168 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018169 {A : Type'} (m : A) (add : type1400 A) : (term168 A m add) = (term173 A m add).
Proof. exact (MK_COMB (@lem1018168 A) (@lem1018167 A m add)). Qed.
Lemma lem1018170 {A : Type'} (m : A) (add : type1400 A) : (term167 A m add) = (term173 A m add).
Proof. exact (TRANS (@lem1018162 A m add) (@lem1018169 A m add)). Qed.
Lemma lem1018171 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018172 {A : Type'} (add : type1400 A) : (term174 A add) = (term175 A add).
Proof. exact (@lem1018171 A (term109 A add)). Qed.
Lemma lem1018173 {A : Type'} (m : A) (add : type1400 A) : (term176 A add m) = (term108 A m add).
Proof. exact (eq_refl (term176 A add m)). Qed.
Lemma lem1018174 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018175 {A : Type'} (m : A) (add : type1400 A) : (term177 A add m) = (term167 A m add).
Proof. exact (MK_COMB (@lem1018174) (@lem1018173 A m add)). Qed.
Lemma lem1018176 {A : Type'} (m : A) (add : type1400 A) : (term177 A add m) = (term173 A m add).
Proof. exact (TRANS (@lem1018175 A m add) (@lem1018170 A m add)). Qed.
Lemma lem1018177 {A : Type'} (add : type1400 A) : (term178 A add) = (term179 A add).
Proof. exact (fun_ext (fun m : A => @lem1018176 A m add)). Qed.
Lemma lem1018178 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018179 {A : Type'} (add : type1400 A) : (term175 A add) = (term180 A add).
Proof. exact (MK_COMB (@lem1018178 A) (@lem1018177 A add)). Qed.
Lemma lem1018180 {A : Type'} (add : type1400 A) : (term174 A add) = (term180 A add).
Proof. exact (TRANS (@lem1018172 A add) (@lem1018179 A add)). Qed.
Lemma lem1018182 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018183 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term181 A n add m) = (term182 A n add m).
Proof. exact (@lem1018182 A (term96 A n add m)). Qed.
Lemma lem1018184 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term183 A n add m p) = ((term95 A m add n p) = (term95 A n add m p)).
Proof. exact (eq_refl (term183 A n add m p)). Qed.
Lemma lem1018185 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018187 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term184 A n add m p) = (term185 A n add m p).
Proof. exact (MK_COMB (@lem1018185) (@lem1018184 A n add m p)). Qed.
Lemma lem1018188 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term186 A n add m) = (term187 A n add m).
Proof. exact (fun_ext (fun p : A => @lem1018187 A n add m p)). Qed.
Lemma lem1018189 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018190 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term182 A n add m) = (term188 A n add m).
Proof. exact (MK_COMB (@lem1018189 A) (@lem1018188 A n add m)). Qed.
Lemma lem1018191 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term181 A n add m) = (term188 A n add m).
Proof. exact (TRANS (@lem1018183 A n add m) (@lem1018190 A n add m)). Qed.
Lemma lem1018192 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018193 {A : Type'} (add : type1400 A) (m : A) : (term189 A add m) = (term190 A add m).
Proof. exact (@lem1018192 A (term98 A add m)). Qed.
Lemma lem1018194 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term191 A add m n) = (term97 A n add m).
Proof. exact (eq_refl (term191 A add m n)). Qed.
Lemma lem1018195 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018196 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term192 A add m n) = (term181 A n add m).
Proof. exact (MK_COMB (@lem1018195) (@lem1018194 A n add m)). Qed.
Lemma lem1018197 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term192 A add m n) = (term188 A n add m).
Proof. exact (TRANS (@lem1018196 A n add m) (@lem1018191 A n add m)). Qed.
Lemma lem1018198 {A : Type'} (add : type1400 A) (m : A) : (term193 A add m) = (term194 A add m).
Proof. exact (fun_ext (fun n : A => @lem1018197 A n add m)). Qed.
Lemma lem1018199 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018200 {A : Type'} (add : type1400 A) (m : A) : (term190 A add m) = (term195 A add m).
Proof. exact (MK_COMB (@lem1018199 A) (@lem1018198 A add m)). Qed.
Lemma lem1018201 {A : Type'} (add : type1400 A) (m : A) : (term189 A add m) = (term195 A add m).
Proof. exact (TRANS (@lem1018193 A add m) (@lem1018200 A add m)). Qed.
Lemma lem1018202 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018203 {A : Type'} (add : type1400 A) : (term196 A add) = (term197 A add).
Proof. exact (@lem1018202 A (term100 A add)). Qed.
Lemma lem1018204 {A : Type'} (add : type1400 A) (m : A) : (term198 A add m) = (term99 A add m).
Proof. exact (eq_refl (term198 A add m)). Qed.
Lemma lem1018205 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018206 {A : Type'} (add : type1400 A) (m : A) : (term199 A add m) = (term189 A add m).
Proof. exact (MK_COMB (@lem1018205) (@lem1018204 A add m)). Qed.
Lemma lem1018207 {A : Type'} (add : type1400 A) (m : A) : (term199 A add m) = (term195 A add m).
Proof. exact (TRANS (@lem1018206 A add m) (@lem1018201 A add m)). Qed.
Lemma lem1018208 {A : Type'} (add : type1400 A) : (term200 A add) = (term201 A add).
Proof. exact (fun_ext (fun m : A => @lem1018207 A add m)). Qed.
Lemma lem1018209 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018210 {A : Type'} (add : type1400 A) : (term197 A add) = (term202 A add).
Proof. exact (MK_COMB (@lem1018209 A) (@lem1018208 A add)). Qed.
Lemma lem1018211 {A : Type'} (add : type1400 A) : (term196 A add) = (term202 A add).
Proof. exact (TRANS (@lem1018203 A add) (@lem1018210 A add)). Qed.
Lemma lem1018213 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018214 {A : Type'} (add : type1400 A) (r0 : A) : (term203 A add r0) = (term204 A add r0).
Proof. exact (@lem1018213 A (term81 A add r0)). Qed.
Lemma lem1018215 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : (term205 A add r0 x) = ((add x r0) = x).
Proof. exact (eq_refl (term205 A add r0 x)). Qed.
Lemma lem1018216 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018218 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : (term206 A add r0 x) = (term207 A add r0 x).
Proof. exact (MK_COMB (@lem1018216) (@lem1018215 A add r0 x)). Qed.
Lemma lem1018219 {A : Type'} (add : type1400 A) (r0 : A) : (term208 A add r0) = (term209 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1018218 A add r0 x)). Qed.
Lemma lem1018220 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018221 {A : Type'} (add : type1400 A) (r0 : A) : (term204 A add r0) = (term210 A add r0).
Proof. exact (MK_COMB (@lem1018220 A) (@lem1018219 A add r0)). Qed.
Lemma lem1018222 {A : Type'} (add : type1400 A) (r0 : A) : (term203 A add r0) = (term210 A add r0).
Proof. exact (TRANS (@lem1018214 A add r0) (@lem1018221 A add r0)). Qed.
Lemma lem1018224 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018225 {A : Type'} (mul : type1400 A) (m : A) : (term144 A mul m) = (term145 A mul m).
Proof. exact (@lem1018224 A (term113 A mul m)). Qed.
Lemma lem1018226 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term146 A mul m n) = ((mul m n) = (mul n m)).
Proof. exact (eq_refl (term146 A mul m n)). Qed.
Lemma lem1018227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018229 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term147 A mul m n) = (term148 A mul n m).
Proof. exact (MK_COMB (@lem1018227) (@lem1018226 A mul n m)). Qed.
Lemma lem1018230 {A : Type'} (mul : type1400 A) (m : A) : (term149 A mul m) = (term150 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1018229 A mul n m)). Qed.
Lemma lem1018231 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018232 {A : Type'} (mul : type1400 A) (m : A) : (term145 A mul m) = (term151 A mul m).
Proof. exact (MK_COMB (@lem1018231 A) (@lem1018230 A mul m)). Qed.
Lemma lem1018233 {A : Type'} (mul : type1400 A) (m : A) : (term144 A mul m) = (term151 A mul m).
Proof. exact (TRANS (@lem1018225 A mul m) (@lem1018232 A mul m)). Qed.
Lemma lem1018234 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018235 {A : Type'} (mul : type1400 A) : (term152 A mul) = (term153 A mul).
Proof. exact (@lem1018234 A (term115 A mul)). Qed.
Lemma lem1018236 {A : Type'} (mul : type1400 A) (m : A) : (term154 A mul m) = (term114 A mul m).
Proof. exact (eq_refl (term154 A mul m)). Qed.
Lemma lem1018237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018238 {A : Type'} (mul : type1400 A) (m : A) : (term155 A mul m) = (term144 A mul m).
Proof. exact (MK_COMB (@lem1018237) (@lem1018236 A mul m)). Qed.
Lemma lem1018239 {A : Type'} (mul : type1400 A) (m : A) : (term155 A mul m) = (term151 A mul m).
Proof. exact (TRANS (@lem1018238 A mul m) (@lem1018233 A mul m)). Qed.
Lemma lem1018240 {A : Type'} (mul : type1400 A) : (term156 A mul) = (term157 A mul).
Proof. exact (fun_ext (fun m : A => @lem1018239 A mul m)). Qed.
Lemma lem1018241 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018242 {A : Type'} (mul : type1400 A) : (term153 A mul) = (term158 A mul).
Proof. exact (MK_COMB (@lem1018241 A) (@lem1018240 A mul)). Qed.
Lemma lem1018243 {A : Type'} (mul : type1400 A) : (term152 A mul) = (term158 A mul).
Proof. exact (TRANS (@lem1018235 A mul) (@lem1018242 A mul)). Qed.
Lemma lem1018245 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018246 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term159 A m mul n) = (term160 A m mul n).
Proof. exact (@lem1018245 A (term105 A m mul n)). Qed.
Lemma lem1018247 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term161 A m mul n p) = ((term104 A mul m n p) = (term95 A m mul n p)).
Proof. exact (eq_refl (term161 A m mul n p)). Qed.
Lemma lem1018248 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018250 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term162 A m mul n p) = (term163 A m mul n p).
Proof. exact (MK_COMB (@lem1018248) (@lem1018247 A m mul n p)). Qed.
Lemma lem1018251 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term164 A m mul n) = (term165 A m mul n).
Proof. exact (fun_ext (fun p : A => @lem1018250 A m mul n p)). Qed.
Lemma lem1018252 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018253 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term160 A m mul n) = (term166 A m mul n).
Proof. exact (MK_COMB (@lem1018252 A) (@lem1018251 A m mul n)). Qed.
Lemma lem1018254 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term159 A m mul n) = (term166 A m mul n).
Proof. exact (TRANS (@lem1018246 A m mul n) (@lem1018253 A m mul n)). Qed.
Lemma lem1018255 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018256 {A : Type'} (m : A) (mul : type1400 A) : (term167 A m mul) = (term168 A m mul).
Proof. exact (@lem1018255 A (term107 A m mul)). Qed.
Lemma lem1018257 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term169 A m mul n) = (term106 A m mul n).
Proof. exact (eq_refl (term169 A m mul n)). Qed.
Lemma lem1018258 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018259 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term170 A m mul n) = (term159 A m mul n).
Proof. exact (MK_COMB (@lem1018258) (@lem1018257 A m mul n)). Qed.
Lemma lem1018260 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term170 A m mul n) = (term166 A m mul n).
Proof. exact (TRANS (@lem1018259 A m mul n) (@lem1018254 A m mul n)). Qed.
Lemma lem1018261 {A : Type'} (m : A) (mul : type1400 A) : (term171 A m mul) = (term172 A m mul).
Proof. exact (fun_ext (fun n : A => @lem1018260 A m mul n)). Qed.
Lemma lem1018262 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018263 {A : Type'} (m : A) (mul : type1400 A) : (term168 A m mul) = (term173 A m mul).
Proof. exact (MK_COMB (@lem1018262 A) (@lem1018261 A m mul)). Qed.
Lemma lem1018264 {A : Type'} (m : A) (mul : type1400 A) : (term167 A m mul) = (term173 A m mul).
Proof. exact (TRANS (@lem1018256 A m mul) (@lem1018263 A m mul)). Qed.
Lemma lem1018265 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018266 {A : Type'} (mul : type1400 A) : (term174 A mul) = (term175 A mul).
Proof. exact (@lem1018265 A (term109 A mul)). Qed.
Lemma lem1018267 {A : Type'} (m : A) (mul : type1400 A) : (term176 A mul m) = (term108 A m mul).
Proof. exact (eq_refl (term176 A mul m)). Qed.
Lemma lem1018268 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018269 {A : Type'} (m : A) (mul : type1400 A) : (term177 A mul m) = (term167 A m mul).
Proof. exact (MK_COMB (@lem1018268) (@lem1018267 A m mul)). Qed.
Lemma lem1018270 {A : Type'} (m : A) (mul : type1400 A) : (term177 A mul m) = (term173 A m mul).
Proof. exact (TRANS (@lem1018269 A m mul) (@lem1018264 A m mul)). Qed.
Lemma lem1018271 {A : Type'} (mul : type1400 A) : (term178 A mul) = (term179 A mul).
Proof. exact (fun_ext (fun m : A => @lem1018270 A m mul)). Qed.
Lemma lem1018272 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018273 {A : Type'} (mul : type1400 A) : (term175 A mul) = (term180 A mul).
Proof. exact (MK_COMB (@lem1018272 A) (@lem1018271 A mul)). Qed.
Lemma lem1018274 {A : Type'} (mul : type1400 A) : (term174 A mul) = (term180 A mul).
Proof. exact (TRANS (@lem1018266 A mul) (@lem1018273 A mul)). Qed.
Lemma lem1018276 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018277 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term181 A n mul m) = (term182 A n mul m).
Proof. exact (@lem1018276 A (term96 A n mul m)). Qed.
Lemma lem1018278 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term183 A n mul m p) = ((term95 A m mul n p) = (term95 A n mul m p)).
Proof. exact (eq_refl (term183 A n mul m p)). Qed.
Lemma lem1018279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018281 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term184 A n mul m p) = (term185 A n mul m p).
Proof. exact (MK_COMB (@lem1018279) (@lem1018278 A n mul m p)). Qed.
Lemma lem1018282 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term186 A n mul m) = (term187 A n mul m).
Proof. exact (fun_ext (fun p : A => @lem1018281 A n mul m p)). Qed.
Lemma lem1018283 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018284 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term182 A n mul m) = (term188 A n mul m).
Proof. exact (MK_COMB (@lem1018283 A) (@lem1018282 A n mul m)). Qed.
Lemma lem1018285 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term181 A n mul m) = (term188 A n mul m).
Proof. exact (TRANS (@lem1018277 A n mul m) (@lem1018284 A n mul m)). Qed.
Lemma lem1018286 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018287 {A : Type'} (mul : type1400 A) (m : A) : (term189 A mul m) = (term190 A mul m).
Proof. exact (@lem1018286 A (term98 A mul m)). Qed.
Lemma lem1018288 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term191 A mul m n) = (term97 A n mul m).
Proof. exact (eq_refl (term191 A mul m n)). Qed.
Lemma lem1018289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018290 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term192 A mul m n) = (term181 A n mul m).
Proof. exact (MK_COMB (@lem1018289) (@lem1018288 A n mul m)). Qed.
Lemma lem1018291 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term192 A mul m n) = (term188 A n mul m).
Proof. exact (TRANS (@lem1018290 A n mul m) (@lem1018285 A n mul m)). Qed.
Lemma lem1018292 {A : Type'} (mul : type1400 A) (m : A) : (term193 A mul m) = (term194 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1018291 A n mul m)). Qed.
Lemma lem1018293 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018294 {A : Type'} (mul : type1400 A) (m : A) : (term190 A mul m) = (term195 A mul m).
Proof. exact (MK_COMB (@lem1018293 A) (@lem1018292 A mul m)). Qed.
Lemma lem1018295 {A : Type'} (mul : type1400 A) (m : A) : (term189 A mul m) = (term195 A mul m).
Proof. exact (TRANS (@lem1018287 A mul m) (@lem1018294 A mul m)). Qed.
Lemma lem1018296 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018297 {A : Type'} (mul : type1400 A) : (term196 A mul) = (term197 A mul).
Proof. exact (@lem1018296 A (term100 A mul)). Qed.
Lemma lem1018298 {A : Type'} (mul : type1400 A) (m : A) : (term198 A mul m) = (term99 A mul m).
Proof. exact (eq_refl (term198 A mul m)). Qed.
Lemma lem1018299 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018300 {A : Type'} (mul : type1400 A) (m : A) : (term199 A mul m) = (term189 A mul m).
Proof. exact (MK_COMB (@lem1018299) (@lem1018298 A mul m)). Qed.
Lemma lem1018301 {A : Type'} (mul : type1400 A) (m : A) : (term199 A mul m) = (term195 A mul m).
Proof. exact (TRANS (@lem1018300 A mul m) (@lem1018295 A mul m)). Qed.
Lemma lem1018302 {A : Type'} (mul : type1400 A) : (term200 A mul) = (term201 A mul).
Proof. exact (fun_ext (fun m : A => @lem1018301 A mul m)). Qed.
Lemma lem1018303 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018304 {A : Type'} (mul : type1400 A) : (term197 A mul) = (term202 A mul).
Proof. exact (MK_COMB (@lem1018303 A) (@lem1018302 A mul)). Qed.
Lemma lem1018305 {A : Type'} (mul : type1400 A) : (term196 A mul) = (term202 A mul).
Proof. exact (TRANS (@lem1018297 A mul) (@lem1018304 A mul)). Qed.
Lemma lem1018307 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018308 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term211 A add m mul n) = (term212 A add m mul n).
Proof. exact (@lem1018307 A (term87 A add m mul n)). Qed.
Lemma lem1018309 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term213 A add m mul n p) = ((term85 A mul add m n p) = (term86 A add m mul n p)).
Proof. exact (eq_refl (term213 A add m mul n p)). Qed.
Lemma lem1018310 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018312 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term214 A add m mul n p) = (term215 A add m mul n p).
Proof. exact (MK_COMB (@lem1018310) (@lem1018309 A add m mul n p)). Qed.
Lemma lem1018313 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term216 A add m mul n) = (term217 A add m mul n).
Proof. exact (fun_ext (fun p : A => @lem1018312 A add m mul n p)). Qed.
Lemma lem1018314 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018315 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term212 A add m mul n) = (term218 A add m mul n).
Proof. exact (MK_COMB (@lem1018314 A) (@lem1018313 A add m mul n)). Qed.
Lemma lem1018316 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term211 A add m mul n) = (term218 A add m mul n).
Proof. exact (TRANS (@lem1018308 A add m mul n) (@lem1018315 A add m mul n)). Qed.
Lemma lem1018317 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018318 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term219 A add m mul) = (term220 A add m mul).
Proof. exact (@lem1018317 A (term89 A add m mul)). Qed.
Lemma lem1018319 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term221 A add m mul n) = (term88 A add m mul n).
Proof. exact (eq_refl (term221 A add m mul n)). Qed.
Lemma lem1018320 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018321 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term222 A add m mul n) = (term211 A add m mul n).
Proof. exact (MK_COMB (@lem1018320) (@lem1018319 A add m mul n)). Qed.
Lemma lem1018322 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term222 A add m mul n) = (term218 A add m mul n).
Proof. exact (TRANS (@lem1018321 A add m mul n) (@lem1018316 A add m mul n)). Qed.
Lemma lem1018323 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term223 A add m mul) = (term224 A add m mul).
Proof. exact (fun_ext (fun n : A => @lem1018322 A add m mul n)). Qed.
Lemma lem1018324 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018325 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term220 A add m mul) = (term225 A add m mul).
Proof. exact (MK_COMB (@lem1018324 A) (@lem1018323 A add m mul)). Qed.
Lemma lem1018326 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term219 A add m mul) = (term225 A add m mul).
Proof. exact (TRANS (@lem1018318 A add m mul) (@lem1018325 A add m mul)). Qed.
Lemma lem1018327 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018328 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term226 A add mul) = (term227 A add mul).
Proof. exact (@lem1018327 A (term91 A add mul)). Qed.
Lemma lem1018329 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term228 A add mul m) = (term90 A add m mul).
Proof. exact (eq_refl (term228 A add mul m)). Qed.
Lemma lem1018330 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018331 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term229 A add mul m) = (term219 A add m mul).
Proof. exact (MK_COMB (@lem1018330) (@lem1018329 A add m mul)). Qed.
Lemma lem1018332 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term229 A add mul m) = (term225 A add m mul).
Proof. exact (TRANS (@lem1018331 A add m mul) (@lem1018326 A add m mul)). Qed.
Lemma lem1018333 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term230 A add mul) = (term231 A add mul).
Proof. exact (fun_ext (fun m : A => @lem1018332 A add m mul)). Qed.
Lemma lem1018334 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018335 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term227 A add mul) = (term232 A add mul).
Proof. exact (MK_COMB (@lem1018334 A) (@lem1018333 A add mul)). Qed.
Lemma lem1018336 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term226 A add mul) = (term232 A add mul).
Proof. exact (TRANS (@lem1018328 A add mul) (@lem1018335 A add mul)). Qed.
Lemma lem1018338 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018339 {A : Type'} (mul : type1400 A) (r1 : A) : (term203 A mul r1) = (term204 A mul r1).
Proof. exact (@lem1018338 A (term81 A mul r1)). Qed.
Lemma lem1018340 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term205 A mul r1 x) = ((mul x r1) = x).
Proof. exact (eq_refl (term205 A mul r1 x)). Qed.
Lemma lem1018341 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018343 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term206 A mul r1 x) = (term207 A mul r1 x).
Proof. exact (MK_COMB (@lem1018341) (@lem1018340 A mul r1 x)). Qed.
Lemma lem1018344 {A : Type'} (mul : type1400 A) (r1 : A) : (term208 A mul r1) = (term209 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1018343 A mul r1 x)). Qed.
Lemma lem1018345 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018346 {A : Type'} (mul : type1400 A) (r1 : A) : (term204 A mul r1) = (term210 A mul r1).
Proof. exact (MK_COMB (@lem1018345 A) (@lem1018344 A mul r1)). Qed.
Lemma lem1018347 {A : Type'} (mul : type1400 A) (r1 : A) : (term203 A mul r1) = (term210 A mul r1).
Proof. exact (TRANS (@lem1018339 A mul r1) (@lem1018346 A mul r1)). Qed.
Lemma lem1018349 {A : Type'} (P : A -> Prop) : (term142 A P) = (term143 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1018350 {A : Type'} (mul : type1400 A) (r0 : A) : (term233 A mul r0) = (term234 A mul r0).
Proof. exact (@lem1018349 A (term79 A mul r0)). Qed.
Lemma lem1018351 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : (term235 A mul r0 x) = ((mul x r0) = r0).
Proof. exact (eq_refl (term235 A mul r0 x)). Qed.
Lemma lem1018352 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1018354 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : (term236 A mul r0 x) = (term237 A mul x r0).
Proof. exact (MK_COMB (@lem1018352) (@lem1018351 A mul x r0)). Qed.
Lemma lem1018355 {A : Type'} (mul : type1400 A) (r0 : A) : (term238 A mul r0) = (term239 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1018354 A mul x r0)). Qed.
Lemma lem1018356 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018357 {A : Type'} (mul : type1400 A) (r0 : A) : (term234 A mul r0) = (term240 A mul r0).
Proof. exact (MK_COMB (@lem1018356 A) (@lem1018355 A mul r0)). Qed.
Lemma lem1018358 {A : Type'} (mul : type1400 A) (r0 : A) : (term233 A mul r0) = (term240 A mul r0).
Proof. exact (TRANS (@lem1018350 A mul r0) (@lem1018357 A mul r0)). Qed.
Lemma lem1018359 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018360 {A : Type'} (mul : type1400 A) (r1 : A) : (term241 A mul r1) = (term242 A mul r1).
Proof. exact (MK_COMB (@lem1018359) (@lem1018347 A mul r1)). Qed.
Lemma lem1018361 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term243 A r1 mul r0) = (term244 A r1 mul r0).
Proof. exact (MK_COMB (@lem1018360 A mul r1) (@lem1018358 A mul r0)). Qed.
Lemma lem1018362 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term245 A r1 mul r0) = (term243 A r1 mul r0).
Proof. exact (@lem17045 (term82 A mul r1) (term80 A mul r0)). Qed.
Lemma lem1018363 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term245 A r1 mul r0) = (term244 A r1 mul r0).
Proof. exact (TRANS (@lem1018362 A r1 mul r0) (@lem1018361 A r1 mul r0)). Qed.
Lemma lem1018364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018365 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term246 A add mul) = (term247 A add mul).
Proof. exact (MK_COMB (@lem1018364) (@lem1018336 A add mul)). Qed.
Lemma lem1018366 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term248 A add r1 mul r0) = (term249 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018365 A add mul) (@lem1018363 A r1 mul r0)). Qed.
Lemma lem1018367 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term250 A add r1 mul r0) = (term248 A add r1 mul r0).
Proof. exact (@lem17045 (term92 A add mul) (term84 A r1 mul r0)). Qed.
Lemma lem1018368 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term250 A add r1 mul r0) = (term249 A add r1 mul r0).
Proof. exact (TRANS (@lem1018367 A add r1 mul r0) (@lem1018366 A add r1 mul r0)). Qed.
Lemma lem1018369 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018370 {A : Type'} (mul : type1400 A) : (term251 A mul) = (term252 A mul).
Proof. exact (MK_COMB (@lem1018369) (@lem1018305 A mul)). Qed.
Lemma lem1018371 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term253 A add r1 mul r0) = (term254 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018370 A mul) (@lem1018368 A add r1 mul r0)). Qed.
Lemma lem1018372 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term255 A add r1 mul r0) = (term253 A add r1 mul r0).
Proof. exact (@lem17045 (term101 A mul) (term94 A add r1 mul r0)). Qed.
Lemma lem1018373 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term255 A add r1 mul r0) = (term254 A add r1 mul r0).
Proof. exact (TRANS (@lem1018372 A add r1 mul r0) (@lem1018371 A add r1 mul r0)). Qed.
Lemma lem1018374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018375 {A : Type'} (mul : type1400 A) : (term256 A mul) = (term257 A mul).
Proof. exact (MK_COMB (@lem1018374) (@lem1018274 A mul)). Qed.
Lemma lem1018376 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term258 A add r1 mul r0) = (term259 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018375 A mul) (@lem1018373 A add r1 mul r0)). Qed.
Lemma lem1018377 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term260 A add r1 mul r0) = (term258 A add r1 mul r0).
Proof. exact (@lem17045 (term110 A mul) (term103 A add r1 mul r0)). Qed.
Lemma lem1018378 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term260 A add r1 mul r0) = (term259 A add r1 mul r0).
Proof. exact (TRANS (@lem1018377 A add r1 mul r0) (@lem1018376 A add r1 mul r0)). Qed.
Lemma lem1018379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018380 {A : Type'} (mul : type1400 A) : (term261 A mul) = (term262 A mul).
Proof. exact (MK_COMB (@lem1018379) (@lem1018243 A mul)). Qed.
Lemma lem1018381 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term263 A add r1 mul r0) = (term264 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018380 A mul) (@lem1018378 A add r1 mul r0)). Qed.
Lemma lem1018382 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term265 A add r1 mul r0) = (term263 A add r1 mul r0).
Proof. exact (@lem17045 (term11 A mul) (term112 A add r1 mul r0)). Qed.
Lemma lem1018383 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term265 A add r1 mul r0) = (term264 A add r1 mul r0).
Proof. exact (TRANS (@lem1018382 A add r1 mul r0) (@lem1018381 A add r1 mul r0)). Qed.
Lemma lem1018384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018385 {A : Type'} (add : type1400 A) (r0 : A) : (term241 A add r0) = (term242 A add r0).
Proof. exact (MK_COMB (@lem1018384) (@lem1018222 A add r0)). Qed.
Lemma lem1018386 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term266 A add r1 mul r0) = (term267 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018385 A add r0) (@lem1018383 A add r1 mul r0)). Qed.
Lemma lem1018387 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term268 A add r1 mul r0) = (term266 A add r1 mul r0).
Proof. exact (@lem17045 (term82 A add r0) (term117 A add r1 mul r0)). Qed.
Lemma lem1018388 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term268 A add r1 mul r0) = (term267 A add r1 mul r0).
Proof. exact (TRANS (@lem1018387 A add r1 mul r0) (@lem1018386 A add r1 mul r0)). Qed.
Lemma lem1018389 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018390 {A : Type'} (add : type1400 A) : (term251 A add) = (term252 A add).
Proof. exact (MK_COMB (@lem1018389) (@lem1018211 A add)). Qed.
Lemma lem1018391 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term269 A add r1 mul r0) = (term270 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018390 A add) (@lem1018388 A add r1 mul r0)). Qed.
Lemma lem1018392 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term271 A add r1 mul r0) = (term269 A add r1 mul r0).
Proof. exact (@lem17045 (term101 A add) (term118 A add r1 mul r0)). Qed.
Lemma lem1018393 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term271 A add r1 mul r0) = (term270 A add r1 mul r0).
Proof. exact (TRANS (@lem1018392 A add r1 mul r0) (@lem1018391 A add r1 mul r0)). Qed.
Lemma lem1018394 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018395 {A : Type'} (add : type1400 A) : (term256 A add) = (term257 A add).
Proof. exact (MK_COMB (@lem1018394) (@lem1018180 A add)). Qed.
Lemma lem1018396 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term272 A add r1 mul r0) = (term273 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018395 A add) (@lem1018393 A add r1 mul r0)). Qed.
Lemma lem1018397 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term274 A add r1 mul r0) = (term272 A add r1 mul r0).
Proof. exact (@lem17045 (term110 A add) (term119 A add r1 mul r0)). Qed.
Lemma lem1018398 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term274 A add r1 mul r0) = (term273 A add r1 mul r0).
Proof. exact (TRANS (@lem1018397 A add r1 mul r0) (@lem1018396 A add r1 mul r0)). Qed.
Lemma lem1018399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018400 {A : Type'} (add : type1400 A) : (term261 A add) = (term262 A add).
Proof. exact (MK_COMB (@lem1018399) (@lem1018149 A add)). Qed.
Lemma lem1018401 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term275 A add r1 mul r0) = (term276 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018400 A add) (@lem1018398 A add r1 mul r0)). Qed.
Lemma lem1018402 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term26 A add r1 mul r0) = (term275 A add r1 mul r0).
Proof. exact (@lem17045 (term11 A add) (term120 A add r1 mul r0)). Qed.
Lemma lem1018403 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term26 A add r1 mul r0) = (term276 A add r1 mul r0).
Proof. exact (TRANS (@lem1018402 A add r1 mul r0) (@lem1018401 A add r1 mul r0)). Qed.
Lemma lem1018494 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018495 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018494 A P Q). Qed.
Lemma lem1018496 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term279 A r1 mul r0) = (term280 A r1 mul r0).
Proof. exact (@lem1018495 A (term209 A mul r1) (term239 A mul r0)). Qed.
Lemma lem1018497 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term281 A mul r1 x) = (term207 A mul r1 x).
Proof. exact (eq_refl (term281 A mul r1 x)). Qed.
Lemma lem1018498 {A : Type'} (mul : type1400 A) (r1 : A) : (term282 A mul r1) = (term209 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1018497 A mul r1 x)). Qed.
Lemma lem1018499 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018500 {A : Type'} (mul : type1400 A) (r1 : A) : (term283 A mul r1) = (term210 A mul r1).
Proof. exact (MK_COMB (@lem1018499 A) (@lem1018498 A mul r1)). Qed.
Lemma lem1018501 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018502 {A : Type'} (mul : type1400 A) (r1 : A) : (term284 A mul r1) = (term242 A mul r1).
Proof. exact (MK_COMB (@lem1018501) (@lem1018500 A mul r1)). Qed.
Lemma lem1018503 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : (term285 A mul r0 x) = (term237 A mul x r0).
Proof. exact (eq_refl (term285 A mul r0 x)). Qed.
Lemma lem1018504 {A : Type'} (mul : type1400 A) (r0 : A) : (term286 A mul r0) = (term239 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1018503 A mul x r0)). Qed.
Lemma lem1018505 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018506 {A : Type'} (mul : type1400 A) (r0 : A) : (term287 A mul r0) = (term240 A mul r0).
Proof. exact (MK_COMB (@lem1018505 A) (@lem1018504 A mul r0)). Qed.
Lemma lem1018507 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term279 A r1 mul r0) = (term244 A r1 mul r0).
Proof. exact (MK_COMB (@lem1018502 A mul r1) (@lem1018506 A mul r0)). Qed.
Lemma lem1018508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018509 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term288 A r1 mul r0) = (term289 A r1 mul r0).
Proof. exact (MK_COMB (@lem1018508) (@lem1018507 A r1 mul r0)). Qed.
Lemma lem1018510 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term281 A mul r1 x) = (term207 A mul r1 x).
Proof. exact (eq_refl (term281 A mul r1 x)). Qed.
Lemma lem1018511 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018512 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term290 A mul r1 x) = (term291 A mul r1 x).
Proof. exact (MK_COMB (@lem1018511) (@lem1018510 A mul r1 x)). Qed.
Lemma lem1018513 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : (term285 A mul r0 x) = (term237 A mul x r0).
Proof. exact (eq_refl (term285 A mul r0 x)). Qed.
Lemma lem1018514 {A : Type'} (r1 : A) (mul : type1400 A) (x : A) (r0 : A) : (term292 A r1 mul r0 x) = (term293 A r1 mul x r0).
Proof. exact (MK_COMB (@lem1018512 A mul r1 x) (@lem1018513 A mul x r0)). Qed.
Lemma lem1018515 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term294 A r1 mul r0) = (term295 A r1 mul r0).
Proof. exact (fun_ext (fun x : A => @lem1018514 A r1 mul x r0)). Qed.
Lemma lem1018516 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018517 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term280 A r1 mul r0) = (term296 A r1 mul r0).
Proof. exact (MK_COMB (@lem1018516 A) (@lem1018515 A r1 mul r0)). Qed.
Lemma lem1018518 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : ((term279 A r1 mul r0) = (term280 A r1 mul r0)) = ((term244 A r1 mul r0) = (term296 A r1 mul r0)).
Proof. exact (MK_COMB (@lem1018509 A r1 mul r0) (@lem1018517 A r1 mul r0)). Qed.
Lemma lem1018519 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term244 A r1 mul r0) = (term296 A r1 mul r0).
Proof. exact (EQ_MP (@lem1018518 A r1 mul r0) (@lem1018496 A r1 mul r0)). Qed.
Lemma lem1018520 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term247 A add mul) = (term247 A add mul).
Proof. exact (eq_refl (term247 A add mul)). Qed.
Lemma lem1018521 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term249 A add r1 mul r0) = (term297 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018520 A add mul) (@lem1018519 A r1 mul r0)). Qed.
Lemma lem1018523 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018524 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018523 A P Q). Qed.
Lemma lem1018525 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term298 A add r1 mul r0) = (term299 A add r1 mul r0).
Proof. exact (@lem1018524 A (term231 A add mul) (term295 A r1 mul r0)). Qed.
Lemma lem1018526 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term300 A add mul m) = (term225 A add m mul).
Proof. exact (eq_refl (term300 A add mul m)). Qed.
Lemma lem1018527 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term301 A add mul) = (term231 A add mul).
Proof. exact (fun_ext (fun m : A => @lem1018526 A add m mul)). Qed.
Lemma lem1018528 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018529 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term302 A add mul) = (term232 A add mul).
Proof. exact (MK_COMB (@lem1018528 A) (@lem1018527 A add mul)). Qed.
Lemma lem1018530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018531 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term303 A add mul) = (term247 A add mul).
Proof. exact (MK_COMB (@lem1018530) (@lem1018529 A add mul)). Qed.
Lemma lem1018532 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term304 A r1 mul r0 m) = (term293 A r1 mul m r0).
Proof. exact (eq_refl (term304 A r1 mul r0 m)). Qed.
Lemma lem1018533 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term305 A r1 mul r0) = (term295 A r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018532 A r1 mul m r0)). Qed.
Lemma lem1018534 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018535 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term306 A r1 mul r0) = (term296 A r1 mul r0).
Proof. exact (MK_COMB (@lem1018534 A) (@lem1018533 A r1 mul r0)). Qed.
Lemma lem1018536 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term298 A add r1 mul r0) = (term297 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018531 A add mul) (@lem1018535 A r1 mul r0)). Qed.
Lemma lem1018537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018538 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term307 A add r1 mul r0) = (term308 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018537) (@lem1018536 A add r1 mul r0)). Qed.
Lemma lem1018539 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term300 A add mul m) = (term225 A add m mul).
Proof. exact (eq_refl (term300 A add mul m)). Qed.
Lemma lem1018540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018541 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term309 A add mul m) = (term310 A add m mul).
Proof. exact (MK_COMB (@lem1018540) (@lem1018539 A add m mul)). Qed.
Lemma lem1018542 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term304 A r1 mul r0 m) = (term293 A r1 mul m r0).
Proof. exact (eq_refl (term304 A r1 mul r0 m)). Qed.
Lemma lem1018543 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term311 A add r1 mul r0 m) = (term312 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018541 A add m mul) (@lem1018542 A r1 mul m r0)). Qed.
Lemma lem1018544 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term313 A add r1 mul r0) = (term314 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018543 A add r1 mul m r0)). Qed.
Lemma lem1018545 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018546 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term299 A add r1 mul r0) = (term315 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018545 A) (@lem1018544 A add r1 mul r0)). Qed.
Lemma lem1018547 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term298 A add r1 mul r0) = (term299 A add r1 mul r0)) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1018538 A add r1 mul r0) (@lem1018546 A add r1 mul r0)). Qed.
Lemma lem1018548 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term297 A add r1 mul r0) = (term315 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1018547 A add r1 mul r0) (@lem1018525 A add r1 mul r0)). Qed.
Lemma lem1018551 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term316 A add r1 mul r0) = (term316 A add r1 mul r0).
Proof. exact (eq_refl (term316 A add r1 mul r0)). Qed.
Lemma lem1018552 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term316 A add r1 mul r0) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0)).
Proof. exact (eq_refl (term316 A add r1 mul r0)). Qed.
Lemma lem1018553 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term317 A add r1 mul r0) = (term317 A add r1 mul r0).
Proof. exact (eq_refl (term317 A add r1 mul r0)). Qed.
Lemma lem1018554 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term316 A add r1 mul r0) = (term316 A add r1 mul r0)) = ((term316 A add r1 mul r0) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0))).
Proof. exact (MK_COMB (@lem1018553 A add r1 mul r0) (@lem1018552 A add r1 mul r0)). Qed.
Lemma lem1018555 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term316 A add r1 mul r0) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0)).
Proof. exact (eq_refl (term316 A add r1 mul r0)). Qed.
Lemma lem1018556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018557 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term317 A add r1 mul r0) = (term318 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018556) (@lem1018555 A add r1 mul r0)). Qed.
Lemma lem1018558 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term297 A add r1 mul r0) = (term315 A add r1 mul r0)) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0)).
Proof. exact (eq_refl ((term297 A add r1 mul r0) = (term315 A add r1 mul r0))). Qed.
Lemma lem1018559 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term316 A add r1 mul r0) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0))) = (((term297 A add r1 mul r0) = (term315 A add r1 mul r0)) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0))).
Proof. exact (MK_COMB (@lem1018557 A add r1 mul r0) (@lem1018558 A add r1 mul r0)). Qed.
Lemma lem1018560 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term316 A add r1 mul r0) = (term316 A add r1 mul r0)) = (((term297 A add r1 mul r0) = (term315 A add r1 mul r0)) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0))).
Proof. exact (TRANS (@lem1018554 A add r1 mul r0) (@lem1018559 A add r1 mul r0)). Qed.
Lemma lem1018561 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term297 A add r1 mul r0) = (term315 A add r1 mul r0)) = ((term297 A add r1 mul r0) = (term315 A add r1 mul r0)).
Proof. exact (EQ_MP (@lem1018560 A add r1 mul r0) (@lem1018551 A add r1 mul r0)). Qed.
Lemma lem1018562 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term297 A add r1 mul r0) = (term315 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1018561 A add r1 mul r0) (@lem1018548 A add r1 mul r0)). Qed.
Lemma lem1018564 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1018565 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (@lem1018564 A P Q). Qed.
Lemma lem1018566 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term321 A add r1 mul m r0) = (term322 A add r1 mul m r0).
Proof. exact (@lem1018565 A (term224 A add m mul) (term293 A r1 mul m r0)). Qed.
Lemma lem1018567 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term323 A add m mul n) = (term218 A add m mul n).
Proof. exact (eq_refl (term323 A add m mul n)). Qed.
Lemma lem1018568 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term324 A add m mul) = (term224 A add m mul).
Proof. exact (fun_ext (fun n : A => @lem1018567 A add m mul n)). Qed.
Lemma lem1018569 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018570 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term325 A add m mul) = (term225 A add m mul).
Proof. exact (MK_COMB (@lem1018569 A) (@lem1018568 A add m mul)). Qed.
Lemma lem1018571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018572 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term326 A add m mul) = (term310 A add m mul).
Proof. exact (MK_COMB (@lem1018571) (@lem1018570 A add m mul)). Qed.
Lemma lem1018573 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term293 A r1 mul m r0) = (term293 A r1 mul m r0).
Proof. exact (eq_refl (term293 A r1 mul m r0)). Qed.
Lemma lem1018574 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term321 A add r1 mul m r0) = (term312 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018572 A add m mul) (@lem1018573 A r1 mul m r0)). Qed.
Lemma lem1018575 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018576 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term327 A add r1 mul m r0) = (term328 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018575) (@lem1018574 A add r1 mul m r0)). Qed.
Lemma lem1018577 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term323 A add m mul n) = (term218 A add m mul n).
Proof. exact (eq_refl (term323 A add m mul n)). Qed.
Lemma lem1018578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018579 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term329 A add m mul n) = (term330 A add m mul n).
Proof. exact (MK_COMB (@lem1018578) (@lem1018577 A add m mul n)). Qed.
Lemma lem1018580 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term293 A r1 mul m r0) = (term293 A r1 mul m r0).
Proof. exact (eq_refl (term293 A r1 mul m r0)). Qed.
Lemma lem1018581 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term331 A add n r1 mul m r0) = (term332 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018579 A add m mul n) (@lem1018580 A r1 mul m r0)). Qed.
Lemma lem1018582 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term333 A add r1 mul m r0) = (term334 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018581 A add n r1 mul m r0)). Qed.
Lemma lem1018583 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018584 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term322 A add r1 mul m r0) = (term335 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018583 A) (@lem1018582 A add r1 mul m r0)). Qed.
Lemma lem1018585 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term321 A add r1 mul m r0) = (term322 A add r1 mul m r0)) = ((term312 A add r1 mul m r0) = (term335 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018576 A add r1 mul m r0) (@lem1018584 A add r1 mul m r0)). Qed.
Lemma lem1018586 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term312 A add r1 mul m r0) = (term335 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1018585 A add r1 mul m r0) (@lem1018566 A add r1 mul m r0)). Qed.
Lemma lem1018588 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1018589 {A : Type'} (P : A -> Prop) (Q : Prop) : (term319 A P Q) = (term320 A P Q).
Proof. exact (@lem1018588 A P Q). Qed.
Lemma lem1018590 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term336 A add n r1 mul m r0) = (term337 A add n r1 mul m r0).
Proof. exact (@lem1018589 A (term217 A add m mul n) (term293 A r1 mul m r0)). Qed.
Lemma lem1018591 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term338 A add m mul n p) = (term215 A add m mul n p).
Proof. exact (eq_refl (term338 A add m mul n p)). Qed.
Lemma lem1018592 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term339 A add m mul n) = (term217 A add m mul n).
Proof. exact (fun_ext (fun p : A => @lem1018591 A add m mul n p)). Qed.
Lemma lem1018593 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018594 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term340 A add m mul n) = (term218 A add m mul n).
Proof. exact (MK_COMB (@lem1018593 A) (@lem1018592 A add m mul n)). Qed.
Lemma lem1018595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018596 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term341 A add m mul n) = (term330 A add m mul n).
Proof. exact (MK_COMB (@lem1018595) (@lem1018594 A add m mul n)). Qed.
Lemma lem1018597 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term293 A r1 mul m r0) = (term293 A r1 mul m r0).
Proof. exact (eq_refl (term293 A r1 mul m r0)). Qed.
Lemma lem1018598 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term336 A add n r1 mul m r0) = (term332 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018596 A add m mul n) (@lem1018597 A r1 mul m r0)). Qed.
Lemma lem1018599 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018600 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term342 A add n r1 mul m r0) = (term343 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018599) (@lem1018598 A add n r1 mul m r0)). Qed.
Lemma lem1018601 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term338 A add m mul n p) = (term215 A add m mul n p).
Proof. exact (eq_refl (term338 A add m mul n p)). Qed.
Lemma lem1018602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018603 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term344 A add m mul n p) = (term345 A add m mul n p).
Proof. exact (MK_COMB (@lem1018602) (@lem1018601 A add m mul n p)). Qed.
Lemma lem1018604 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term293 A r1 mul m r0) = (term293 A r1 mul m r0).
Proof. exact (eq_refl (term293 A r1 mul m r0)). Qed.
Lemma lem1018605 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term346 A add n p r1 mul m r0) = (term347 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1018603 A add m mul n p) (@lem1018604 A r1 mul m r0)). Qed.
Lemma lem1018606 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term348 A add n r1 mul m r0) = (term349 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018605 A add n p r1 mul m r0)). Qed.
Lemma lem1018607 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018608 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term337 A add n r1 mul m r0) = (term350 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018607 A) (@lem1018606 A add n r1 mul m r0)). Qed.
Lemma lem1018609 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term336 A add n r1 mul m r0) = (term337 A add n r1 mul m r0)) = ((term332 A add n r1 mul m r0) = (term350 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018600 A add n r1 mul m r0) (@lem1018608 A add n r1 mul m r0)). Qed.
Lemma lem1018610 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term332 A add n r1 mul m r0) = (term350 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1018609 A add n r1 mul m r0) (@lem1018590 A add n r1 mul m r0)). Qed.
Lemma lem1018611 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term334 A add r1 mul m r0) = (term351 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018610 A add n r1 mul m r0)). Qed.
Lemma lem1018612 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018613 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term335 A add r1 mul m r0) = (term352 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018612 A) (@lem1018611 A add r1 mul m r0)). Qed.
Lemma lem1018614 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term312 A add r1 mul m r0) = (term352 A add r1 mul m r0).
Proof. exact (TRANS (@lem1018586 A add r1 mul m r0) (@lem1018613 A add r1 mul m r0)). Qed.
Lemma lem1018615 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term314 A add r1 mul r0) = (term353 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018614 A add r1 mul m r0)). Qed.
Lemma lem1018616 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018617 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term315 A add r1 mul r0) = (term354 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018616 A) (@lem1018615 A add r1 mul r0)). Qed.
Lemma lem1018618 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term297 A add r1 mul r0) = (term354 A add r1 mul r0).
Proof. exact (TRANS (@lem1018562 A add r1 mul r0) (@lem1018617 A add r1 mul r0)). Qed.
Lemma lem1018619 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term249 A add r1 mul r0) = (term354 A add r1 mul r0).
Proof. exact (TRANS (@lem1018521 A add r1 mul r0) (@lem1018618 A add r1 mul r0)). Qed.
Lemma lem1018620 {A : Type'} (mul : type1400 A) : (term252 A mul) = (term252 A mul).
Proof. exact (eq_refl (term252 A mul)). Qed.
Lemma lem1018621 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term254 A add r1 mul r0) = (term355 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018620 A mul) (@lem1018619 A add r1 mul r0)). Qed.
Lemma lem1018623 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018624 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018623 A P Q). Qed.
Lemma lem1018625 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term356 A add r1 mul r0) = (term357 A add r1 mul r0).
Proof. exact (@lem1018624 A (term201 A mul) (term353 A add r1 mul r0)). Qed.
Lemma lem1018626 {A : Type'} (mul : type1400 A) (m : A) : (term358 A mul m) = (term195 A mul m).
Proof. exact (eq_refl (term358 A mul m)). Qed.
Lemma lem1018627 {A : Type'} (mul : type1400 A) : (term359 A mul) = (term201 A mul).
Proof. exact (fun_ext (fun m : A => @lem1018626 A mul m)). Qed.
Lemma lem1018628 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018629 {A : Type'} (mul : type1400 A) : (term360 A mul) = (term202 A mul).
Proof. exact (MK_COMB (@lem1018628 A) (@lem1018627 A mul)). Qed.
Lemma lem1018630 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018631 {A : Type'} (mul : type1400 A) : (term361 A mul) = (term252 A mul).
Proof. exact (MK_COMB (@lem1018630) (@lem1018629 A mul)). Qed.
Lemma lem1018632 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term362 A add r1 mul r0 m) = (term352 A add r1 mul m r0).
Proof. exact (eq_refl (term362 A add r1 mul r0 m)). Qed.
Lemma lem1018633 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term363 A add r1 mul r0) = (term353 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018632 A add r1 mul m r0)). Qed.
Lemma lem1018634 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018635 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term364 A add r1 mul r0) = (term354 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018634 A) (@lem1018633 A add r1 mul r0)). Qed.
Lemma lem1018636 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term356 A add r1 mul r0) = (term355 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018631 A mul) (@lem1018635 A add r1 mul r0)). Qed.
Lemma lem1018637 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018638 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term365 A add r1 mul r0) = (term366 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018637) (@lem1018636 A add r1 mul r0)). Qed.
Lemma lem1018639 {A : Type'} (mul : type1400 A) (m : A) : (term358 A mul m) = (term195 A mul m).
Proof. exact (eq_refl (term358 A mul m)). Qed.
Lemma lem1018640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018641 {A : Type'} (mul : type1400 A) (m : A) : (term367 A mul m) = (term368 A mul m).
Proof. exact (MK_COMB (@lem1018640) (@lem1018639 A mul m)). Qed.
Lemma lem1018642 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term362 A add r1 mul r0 m) = (term352 A add r1 mul m r0).
Proof. exact (eq_refl (term362 A add r1 mul r0 m)). Qed.
Lemma lem1018643 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term369 A add r1 mul r0 m) = (term370 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018641 A mul m) (@lem1018642 A add r1 mul m r0)). Qed.
Lemma lem1018644 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term371 A add r1 mul r0) = (term372 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018643 A add r1 mul m r0)). Qed.
Lemma lem1018645 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018646 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term357 A add r1 mul r0) = (term373 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018645 A) (@lem1018644 A add r1 mul r0)). Qed.
Lemma lem1018647 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term356 A add r1 mul r0) = (term357 A add r1 mul r0)) = ((term355 A add r1 mul r0) = (term373 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1018638 A add r1 mul r0) (@lem1018646 A add r1 mul r0)). Qed.
Lemma lem1018648 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term355 A add r1 mul r0) = (term373 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1018647 A add r1 mul r0) (@lem1018625 A add r1 mul r0)). Qed.
Lemma lem1018650 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018651 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018650 A P Q). Qed.
Lemma lem1018652 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term374 A add r1 mul m r0) = (term375 A add r1 mul m r0).
Proof. exact (@lem1018651 A (term194 A mul m) (term351 A add r1 mul m r0)). Qed.
Lemma lem1018653 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term376 A mul m n) = (term188 A n mul m).
Proof. exact (eq_refl (term376 A mul m n)). Qed.
Lemma lem1018654 {A : Type'} (mul : type1400 A) (m : A) : (term377 A mul m) = (term194 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1018653 A n mul m)). Qed.
Lemma lem1018655 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018656 {A : Type'} (mul : type1400 A) (m : A) : (term378 A mul m) = (term195 A mul m).
Proof. exact (MK_COMB (@lem1018655 A) (@lem1018654 A mul m)). Qed.
Lemma lem1018657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018658 {A : Type'} (mul : type1400 A) (m : A) : (term379 A mul m) = (term368 A mul m).
Proof. exact (MK_COMB (@lem1018657) (@lem1018656 A mul m)). Qed.
Lemma lem1018659 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term380 A add r1 mul m r0 n) = (term350 A add n r1 mul m r0).
Proof. exact (eq_refl (term380 A add r1 mul m r0 n)). Qed.
Lemma lem1018660 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term381 A add r1 mul m r0) = (term351 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018659 A add n r1 mul m r0)). Qed.
Lemma lem1018661 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018662 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term382 A add r1 mul m r0) = (term352 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018661 A) (@lem1018660 A add r1 mul m r0)). Qed.
Lemma lem1018663 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term374 A add r1 mul m r0) = (term370 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018658 A mul m) (@lem1018662 A add r1 mul m r0)). Qed.
Lemma lem1018664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018665 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term383 A add r1 mul m r0) = (term384 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018664) (@lem1018663 A add r1 mul m r0)). Qed.
Lemma lem1018666 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term376 A mul m n) = (term188 A n mul m).
Proof. exact (eq_refl (term376 A mul m n)). Qed.
Lemma lem1018667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018668 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term385 A mul m n) = (term386 A n mul m).
Proof. exact (MK_COMB (@lem1018667) (@lem1018666 A n mul m)). Qed.
Lemma lem1018669 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term380 A add r1 mul m r0 n) = (term350 A add n r1 mul m r0).
Proof. exact (eq_refl (term380 A add r1 mul m r0 n)). Qed.
Lemma lem1018670 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term387 A add r1 mul m r0 n) = (term388 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018668 A n mul m) (@lem1018669 A add n r1 mul m r0)). Qed.
Lemma lem1018671 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term389 A add r1 mul m r0) = (term390 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018670 A add n r1 mul m r0)). Qed.
Lemma lem1018672 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018673 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term375 A add r1 mul m r0) = (term391 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018672 A) (@lem1018671 A add r1 mul m r0)). Qed.
Lemma lem1018674 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term374 A add r1 mul m r0) = (term375 A add r1 mul m r0)) = ((term370 A add r1 mul m r0) = (term391 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018665 A add r1 mul m r0) (@lem1018673 A add r1 mul m r0)). Qed.
Lemma lem1018675 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term370 A add r1 mul m r0) = (term391 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1018674 A add r1 mul m r0) (@lem1018652 A add r1 mul m r0)). Qed.
Lemma lem1018677 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018678 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018677 A P Q). Qed.
Lemma lem1018679 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term392 A add n r1 mul m r0) = (term393 A add n r1 mul m r0).
Proof. exact (@lem1018678 A (term187 A n mul m) (term349 A add n r1 mul m r0)). Qed.
Lemma lem1018680 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term394 A n mul m p) = (term185 A n mul m p).
Proof. exact (eq_refl (term394 A n mul m p)). Qed.
Lemma lem1018681 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term395 A n mul m) = (term187 A n mul m).
Proof. exact (fun_ext (fun p : A => @lem1018680 A n mul m p)). Qed.
Lemma lem1018682 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018683 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term396 A n mul m) = (term188 A n mul m).
Proof. exact (MK_COMB (@lem1018682 A) (@lem1018681 A n mul m)). Qed.
Lemma lem1018684 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018685 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term397 A n mul m) = (term386 A n mul m).
Proof. exact (MK_COMB (@lem1018684) (@lem1018683 A n mul m)). Qed.
Lemma lem1018686 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term398 A add n r1 mul m r0 p) = (term347 A add n p r1 mul m r0).
Proof. exact (eq_refl (term398 A add n r1 mul m r0 p)). Qed.
Lemma lem1018687 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term399 A add n r1 mul m r0) = (term349 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018686 A add n p r1 mul m r0)). Qed.
Lemma lem1018688 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018689 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term400 A add n r1 mul m r0) = (term350 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018688 A) (@lem1018687 A add n r1 mul m r0)). Qed.
Lemma lem1018690 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term392 A add n r1 mul m r0) = (term388 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018685 A n mul m) (@lem1018689 A add n r1 mul m r0)). Qed.
Lemma lem1018691 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018692 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term401 A add n r1 mul m r0) = (term402 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018691) (@lem1018690 A add n r1 mul m r0)). Qed.
Lemma lem1018693 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term394 A n mul m p) = (term185 A n mul m p).
Proof. exact (eq_refl (term394 A n mul m p)). Qed.
Lemma lem1018694 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018695 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term403 A n mul m p) = (term404 A n mul m p).
Proof. exact (MK_COMB (@lem1018694) (@lem1018693 A n mul m p)). Qed.
Lemma lem1018696 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term398 A add n r1 mul m r0 p) = (term347 A add n p r1 mul m r0).
Proof. exact (eq_refl (term398 A add n r1 mul m r0 p)). Qed.
Lemma lem1018697 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term405 A add n r1 mul m r0 p) = (term406 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1018695 A n mul m p) (@lem1018696 A add n p r1 mul m r0)). Qed.
Lemma lem1018698 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term407 A add n r1 mul m r0) = (term408 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018697 A add n p r1 mul m r0)). Qed.
Lemma lem1018699 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018700 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term393 A add n r1 mul m r0) = (term409 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018699 A) (@lem1018698 A add n r1 mul m r0)). Qed.
Lemma lem1018701 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term392 A add n r1 mul m r0) = (term393 A add n r1 mul m r0)) = ((term388 A add n r1 mul m r0) = (term409 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018692 A add n r1 mul m r0) (@lem1018700 A add n r1 mul m r0)). Qed.
Lemma lem1018702 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term388 A add n r1 mul m r0) = (term409 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1018701 A add n r1 mul m r0) (@lem1018679 A add n r1 mul m r0)). Qed.
Lemma lem1018703 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term390 A add r1 mul m r0) = (term410 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018702 A add n r1 mul m r0)). Qed.
Lemma lem1018704 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018705 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term391 A add r1 mul m r0) = (term411 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018704 A) (@lem1018703 A add r1 mul m r0)). Qed.
Lemma lem1018706 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term370 A add r1 mul m r0) = (term411 A add r1 mul m r0).
Proof. exact (TRANS (@lem1018675 A add r1 mul m r0) (@lem1018705 A add r1 mul m r0)). Qed.
Lemma lem1018707 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term372 A add r1 mul r0) = (term412 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018706 A add r1 mul m r0)). Qed.
Lemma lem1018708 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018709 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term373 A add r1 mul r0) = (term413 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018708 A) (@lem1018707 A add r1 mul r0)). Qed.
Lemma lem1018710 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term355 A add r1 mul r0) = (term413 A add r1 mul r0).
Proof. exact (TRANS (@lem1018648 A add r1 mul r0) (@lem1018709 A add r1 mul r0)). Qed.
Lemma lem1018711 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term254 A add r1 mul r0) = (term413 A add r1 mul r0).
Proof. exact (TRANS (@lem1018621 A add r1 mul r0) (@lem1018710 A add r1 mul r0)). Qed.
Lemma lem1018712 {A : Type'} (mul : type1400 A) : (term257 A mul) = (term257 A mul).
Proof. exact (eq_refl (term257 A mul)). Qed.
Lemma lem1018713 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term259 A add r1 mul r0) = (term414 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018712 A mul) (@lem1018711 A add r1 mul r0)). Qed.
Lemma lem1018715 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018716 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018715 A P Q). Qed.
Lemma lem1018717 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term415 A add r1 mul r0) = (term416 A add r1 mul r0).
Proof. exact (@lem1018716 A (term179 A mul) (term412 A add r1 mul r0)). Qed.
Lemma lem1018718 {A : Type'} (m : A) (mul : type1400 A) : (term417 A mul m) = (term173 A m mul).
Proof. exact (eq_refl (term417 A mul m)). Qed.
Lemma lem1018719 {A : Type'} (mul : type1400 A) : (term418 A mul) = (term179 A mul).
Proof. exact (fun_ext (fun m : A => @lem1018718 A m mul)). Qed.
Lemma lem1018720 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018721 {A : Type'} (mul : type1400 A) : (term419 A mul) = (term180 A mul).
Proof. exact (MK_COMB (@lem1018720 A) (@lem1018719 A mul)). Qed.
Lemma lem1018722 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018723 {A : Type'} (mul : type1400 A) : (term420 A mul) = (term257 A mul).
Proof. exact (MK_COMB (@lem1018722) (@lem1018721 A mul)). Qed.
Lemma lem1018724 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term421 A add r1 mul r0 m) = (term411 A add r1 mul m r0).
Proof. exact (eq_refl (term421 A add r1 mul r0 m)). Qed.
Lemma lem1018725 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term422 A add r1 mul r0) = (term412 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018724 A add r1 mul m r0)). Qed.
Lemma lem1018726 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018727 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term423 A add r1 mul r0) = (term413 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018726 A) (@lem1018725 A add r1 mul r0)). Qed.
Lemma lem1018728 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term415 A add r1 mul r0) = (term414 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018723 A mul) (@lem1018727 A add r1 mul r0)). Qed.
Lemma lem1018729 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018730 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term424 A add r1 mul r0) = (term425 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018729) (@lem1018728 A add r1 mul r0)). Qed.
Lemma lem1018731 {A : Type'} (m : A) (mul : type1400 A) : (term417 A mul m) = (term173 A m mul).
Proof. exact (eq_refl (term417 A mul m)). Qed.
Lemma lem1018732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018733 {A : Type'} (m : A) (mul : type1400 A) : (term426 A mul m) = (term427 A m mul).
Proof. exact (MK_COMB (@lem1018732) (@lem1018731 A m mul)). Qed.
Lemma lem1018734 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term421 A add r1 mul r0 m) = (term411 A add r1 mul m r0).
Proof. exact (eq_refl (term421 A add r1 mul r0 m)). Qed.
Lemma lem1018735 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term428 A add r1 mul r0 m) = (term429 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018733 A m mul) (@lem1018734 A add r1 mul m r0)). Qed.
Lemma lem1018736 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term430 A add r1 mul r0) = (term431 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018735 A add r1 mul m r0)). Qed.
Lemma lem1018737 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018738 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term416 A add r1 mul r0) = (term432 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018737 A) (@lem1018736 A add r1 mul r0)). Qed.
Lemma lem1018739 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term415 A add r1 mul r0) = (term416 A add r1 mul r0)) = ((term414 A add r1 mul r0) = (term432 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1018730 A add r1 mul r0) (@lem1018738 A add r1 mul r0)). Qed.
Lemma lem1018740 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term414 A add r1 mul r0) = (term432 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1018739 A add r1 mul r0) (@lem1018717 A add r1 mul r0)). Qed.
Lemma lem1018742 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018743 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018742 A P Q). Qed.
Lemma lem1018744 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term433 A add r1 mul m r0) = (term434 A add r1 mul m r0).
Proof. exact (@lem1018743 A (term172 A m mul) (term410 A add r1 mul m r0)). Qed.
Lemma lem1018745 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term435 A m mul n) = (term166 A m mul n).
Proof. exact (eq_refl (term435 A m mul n)). Qed.
Lemma lem1018746 {A : Type'} (m : A) (mul : type1400 A) : (term436 A m mul) = (term172 A m mul).
Proof. exact (fun_ext (fun n : A => @lem1018745 A m mul n)). Qed.
Lemma lem1018747 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018748 {A : Type'} (m : A) (mul : type1400 A) : (term437 A m mul) = (term173 A m mul).
Proof. exact (MK_COMB (@lem1018747 A) (@lem1018746 A m mul)). Qed.
Lemma lem1018749 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018750 {A : Type'} (m : A) (mul : type1400 A) : (term438 A m mul) = (term427 A m mul).
Proof. exact (MK_COMB (@lem1018749) (@lem1018748 A m mul)). Qed.
Lemma lem1018751 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term439 A add r1 mul m r0 n) = (term409 A add n r1 mul m r0).
Proof. exact (eq_refl (term439 A add r1 mul m r0 n)). Qed.
Lemma lem1018752 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term440 A add r1 mul m r0) = (term410 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018751 A add n r1 mul m r0)). Qed.
Lemma lem1018753 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018754 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term441 A add r1 mul m r0) = (term411 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018753 A) (@lem1018752 A add r1 mul m r0)). Qed.
Lemma lem1018755 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term433 A add r1 mul m r0) = (term429 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018750 A m mul) (@lem1018754 A add r1 mul m r0)). Qed.
Lemma lem1018756 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018757 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term442 A add r1 mul m r0) = (term443 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018756) (@lem1018755 A add r1 mul m r0)). Qed.
Lemma lem1018758 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term435 A m mul n) = (term166 A m mul n).
Proof. exact (eq_refl (term435 A m mul n)). Qed.
Lemma lem1018759 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018760 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term444 A m mul n) = (term445 A m mul n).
Proof. exact (MK_COMB (@lem1018759) (@lem1018758 A m mul n)). Qed.
Lemma lem1018761 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term439 A add r1 mul m r0 n) = (term409 A add n r1 mul m r0).
Proof. exact (eq_refl (term439 A add r1 mul m r0 n)). Qed.
Lemma lem1018762 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term446 A add r1 mul m r0 n) = (term447 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018760 A m mul n) (@lem1018761 A add n r1 mul m r0)). Qed.
Lemma lem1018763 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term448 A add r1 mul m r0) = (term449 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018762 A add n r1 mul m r0)). Qed.
Lemma lem1018764 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018765 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term434 A add r1 mul m r0) = (term450 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018764 A) (@lem1018763 A add r1 mul m r0)). Qed.
Lemma lem1018766 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term433 A add r1 mul m r0) = (term434 A add r1 mul m r0)) = ((term429 A add r1 mul m r0) = (term450 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018757 A add r1 mul m r0) (@lem1018765 A add r1 mul m r0)). Qed.
Lemma lem1018767 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term429 A add r1 mul m r0) = (term450 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1018766 A add r1 mul m r0) (@lem1018744 A add r1 mul m r0)). Qed.
Lemma lem1018769 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018770 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018769 A P Q). Qed.
Lemma lem1018771 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term451 A add n r1 mul m r0) = (term452 A add n r1 mul m r0).
Proof. exact (@lem1018770 A (term165 A m mul n) (term408 A add n r1 mul m r0)). Qed.
Lemma lem1018772 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term453 A m mul n p) = (term163 A m mul n p).
Proof. exact (eq_refl (term453 A m mul n p)). Qed.
Lemma lem1018773 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term454 A m mul n) = (term165 A m mul n).
Proof. exact (fun_ext (fun p : A => @lem1018772 A m mul n p)). Qed.
Lemma lem1018774 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018775 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term455 A m mul n) = (term166 A m mul n).
Proof. exact (MK_COMB (@lem1018774 A) (@lem1018773 A m mul n)). Qed.
Lemma lem1018776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018777 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term456 A m mul n) = (term445 A m mul n).
Proof. exact (MK_COMB (@lem1018776) (@lem1018775 A m mul n)). Qed.
Lemma lem1018778 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term457 A add n r1 mul m r0 p) = (term406 A add n p r1 mul m r0).
Proof. exact (eq_refl (term457 A add n r1 mul m r0 p)). Qed.
Lemma lem1018779 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term458 A add n r1 mul m r0) = (term408 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018778 A add n p r1 mul m r0)). Qed.
Lemma lem1018780 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018781 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term459 A add n r1 mul m r0) = (term409 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018780 A) (@lem1018779 A add n r1 mul m r0)). Qed.
Lemma lem1018782 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term451 A add n r1 mul m r0) = (term447 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018777 A m mul n) (@lem1018781 A add n r1 mul m r0)). Qed.
Lemma lem1018783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018784 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term460 A add n r1 mul m r0) = (term461 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018783) (@lem1018782 A add n r1 mul m r0)). Qed.
Lemma lem1018785 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term453 A m mul n p) = (term163 A m mul n p).
Proof. exact (eq_refl (term453 A m mul n p)). Qed.
Lemma lem1018786 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018787 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term462 A m mul n p) = (term463 A m mul n p).
Proof. exact (MK_COMB (@lem1018786) (@lem1018785 A m mul n p)). Qed.
Lemma lem1018788 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term457 A add n r1 mul m r0 p) = (term406 A add n p r1 mul m r0).
Proof. exact (eq_refl (term457 A add n r1 mul m r0 p)). Qed.
Lemma lem1018789 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term464 A add n r1 mul m r0 p) = (term465 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1018787 A m mul n p) (@lem1018788 A add n p r1 mul m r0)). Qed.
Lemma lem1018790 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term466 A add n r1 mul m r0) = (term467 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018789 A add n p r1 mul m r0)). Qed.
Lemma lem1018791 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018792 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term452 A add n r1 mul m r0) = (term468 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018791 A) (@lem1018790 A add n r1 mul m r0)). Qed.
Lemma lem1018793 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term451 A add n r1 mul m r0) = (term452 A add n r1 mul m r0)) = ((term447 A add n r1 mul m r0) = (term468 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018784 A add n r1 mul m r0) (@lem1018792 A add n r1 mul m r0)). Qed.
Lemma lem1018794 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term447 A add n r1 mul m r0) = (term468 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1018793 A add n r1 mul m r0) (@lem1018771 A add n r1 mul m r0)). Qed.
Lemma lem1018795 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term449 A add r1 mul m r0) = (term469 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018794 A add n r1 mul m r0)). Qed.
Lemma lem1018796 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018797 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term450 A add r1 mul m r0) = (term470 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018796 A) (@lem1018795 A add r1 mul m r0)). Qed.
Lemma lem1018798 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term429 A add r1 mul m r0) = (term470 A add r1 mul m r0).
Proof. exact (TRANS (@lem1018767 A add r1 mul m r0) (@lem1018797 A add r1 mul m r0)). Qed.
Lemma lem1018799 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term431 A add r1 mul r0) = (term471 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018798 A add r1 mul m r0)). Qed.
Lemma lem1018800 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018801 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term432 A add r1 mul r0) = (term472 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018800 A) (@lem1018799 A add r1 mul r0)). Qed.
Lemma lem1018802 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term414 A add r1 mul r0) = (term472 A add r1 mul r0).
Proof. exact (TRANS (@lem1018740 A add r1 mul r0) (@lem1018801 A add r1 mul r0)). Qed.
Lemma lem1018803 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term259 A add r1 mul r0) = (term472 A add r1 mul r0).
Proof. exact (TRANS (@lem1018713 A add r1 mul r0) (@lem1018802 A add r1 mul r0)). Qed.
Lemma lem1018804 {A : Type'} (mul : type1400 A) : (term262 A mul) = (term262 A mul).
Proof. exact (eq_refl (term262 A mul)). Qed.
Lemma lem1018805 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term264 A add r1 mul r0) = (term473 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018804 A mul) (@lem1018803 A add r1 mul r0)). Qed.
Lemma lem1018807 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018808 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018807 A P Q). Qed.
Lemma lem1018809 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term474 A add r1 mul r0) = (term475 A add r1 mul r0).
Proof. exact (@lem1018808 A (term157 A mul) (term471 A add r1 mul r0)). Qed.
Lemma lem1018810 {A : Type'} (mul : type1400 A) (m : A) : (term476 A mul m) = (term151 A mul m).
Proof. exact (eq_refl (term476 A mul m)). Qed.
Lemma lem1018811 {A : Type'} (mul : type1400 A) : (term477 A mul) = (term157 A mul).
Proof. exact (fun_ext (fun m : A => @lem1018810 A mul m)). Qed.
Lemma lem1018812 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018813 {A : Type'} (mul : type1400 A) : (term478 A mul) = (term158 A mul).
Proof. exact (MK_COMB (@lem1018812 A) (@lem1018811 A mul)). Qed.
Lemma lem1018814 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018815 {A : Type'} (mul : type1400 A) : (term479 A mul) = (term262 A mul).
Proof. exact (MK_COMB (@lem1018814) (@lem1018813 A mul)). Qed.
Lemma lem1018816 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term480 A add r1 mul r0 m) = (term470 A add r1 mul m r0).
Proof. exact (eq_refl (term480 A add r1 mul r0 m)). Qed.
Lemma lem1018817 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term481 A add r1 mul r0) = (term471 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018816 A add r1 mul m r0)). Qed.
Lemma lem1018818 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018819 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term482 A add r1 mul r0) = (term472 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018818 A) (@lem1018817 A add r1 mul r0)). Qed.
Lemma lem1018820 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term474 A add r1 mul r0) = (term473 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018815 A mul) (@lem1018819 A add r1 mul r0)). Qed.
Lemma lem1018821 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018822 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term483 A add r1 mul r0) = (term484 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018821) (@lem1018820 A add r1 mul r0)). Qed.
Lemma lem1018823 {A : Type'} (mul : type1400 A) (m : A) : (term476 A mul m) = (term151 A mul m).
Proof. exact (eq_refl (term476 A mul m)). Qed.
Lemma lem1018824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018825 {A : Type'} (mul : type1400 A) (m : A) : (term485 A mul m) = (term486 A mul m).
Proof. exact (MK_COMB (@lem1018824) (@lem1018823 A mul m)). Qed.
Lemma lem1018826 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term480 A add r1 mul r0 m) = (term470 A add r1 mul m r0).
Proof. exact (eq_refl (term480 A add r1 mul r0 m)). Qed.
Lemma lem1018827 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term487 A add r1 mul r0 m) = (term488 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018825 A mul m) (@lem1018826 A add r1 mul m r0)). Qed.
Lemma lem1018828 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term489 A add r1 mul r0) = (term490 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018827 A add r1 mul m r0)). Qed.
Lemma lem1018829 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018830 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term475 A add r1 mul r0) = (term491 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018829 A) (@lem1018828 A add r1 mul r0)). Qed.
Lemma lem1018831 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term474 A add r1 mul r0) = (term475 A add r1 mul r0)) = ((term473 A add r1 mul r0) = (term491 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1018822 A add r1 mul r0) (@lem1018830 A add r1 mul r0)). Qed.
Lemma lem1018832 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term473 A add r1 mul r0) = (term491 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1018831 A add r1 mul r0) (@lem1018809 A add r1 mul r0)). Qed.
Lemma lem1018834 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018834 A P Q). Qed.
Lemma lem1018836 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term492 A add r1 mul m r0) = (term493 A add r1 mul m r0).
Proof. exact (@lem1018835 A (term150 A mul m) (term469 A add r1 mul m r0)). Qed.
Lemma lem1018837 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term494 A mul m n) = (term148 A mul n m).
Proof. exact (eq_refl (term494 A mul m n)). Qed.
Lemma lem1018838 {A : Type'} (mul : type1400 A) (m : A) : (term495 A mul m) = (term150 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1018837 A mul n m)). Qed.
Lemma lem1018839 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018840 {A : Type'} (mul : type1400 A) (m : A) : (term496 A mul m) = (term151 A mul m).
Proof. exact (MK_COMB (@lem1018839 A) (@lem1018838 A mul m)). Qed.
Lemma lem1018841 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018842 {A : Type'} (mul : type1400 A) (m : A) : (term497 A mul m) = (term486 A mul m).
Proof. exact (MK_COMB (@lem1018841) (@lem1018840 A mul m)). Qed.
Lemma lem1018843 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term498 A add r1 mul m r0 n) = (term468 A add n r1 mul m r0).
Proof. exact (eq_refl (term498 A add r1 mul m r0 n)). Qed.
Lemma lem1018844 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term499 A add r1 mul m r0) = (term469 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018843 A add n r1 mul m r0)). Qed.
Lemma lem1018845 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018846 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term500 A add r1 mul m r0) = (term470 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018845 A) (@lem1018844 A add r1 mul m r0)). Qed.
Lemma lem1018847 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term492 A add r1 mul m r0) = (term488 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018842 A mul m) (@lem1018846 A add r1 mul m r0)). Qed.
Lemma lem1018848 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018849 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term501 A add r1 mul m r0) = (term502 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018848) (@lem1018847 A add r1 mul m r0)). Qed.
Lemma lem1018850 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term494 A mul m n) = (term148 A mul n m).
Proof. exact (eq_refl (term494 A mul m n)). Qed.
Lemma lem1018851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018852 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term503 A mul m n) = (term504 A mul n m).
Proof. exact (MK_COMB (@lem1018851) (@lem1018850 A mul n m)). Qed.
Lemma lem1018853 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term498 A add r1 mul m r0 n) = (term468 A add n r1 mul m r0).
Proof. exact (eq_refl (term498 A add r1 mul m r0 n)). Qed.
Lemma lem1018854 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term505 A add r1 mul m r0 n) = (term506 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018852 A mul n m) (@lem1018853 A add n r1 mul m r0)). Qed.
Lemma lem1018855 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term507 A add r1 mul m r0) = (term508 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018854 A add n r1 mul m r0)). Qed.
Lemma lem1018856 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018857 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term493 A add r1 mul m r0) = (term509 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018856 A) (@lem1018855 A add r1 mul m r0)). Qed.
Lemma lem1018858 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term492 A add r1 mul m r0) = (term493 A add r1 mul m r0)) = ((term488 A add r1 mul m r0) = (term509 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018849 A add r1 mul m r0) (@lem1018857 A add r1 mul m r0)). Qed.
Lemma lem1018859 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term488 A add r1 mul m r0) = (term509 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1018858 A add r1 mul m r0) (@lem1018836 A add r1 mul m r0)). Qed.
Lemma lem1018861 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1018862 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (@lem1018861 A P Q). Qed.
Lemma lem1018863 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term512 A add n r1 mul m r0) = (term513 A add n r1 mul m r0).
Proof. exact (@lem1018862 A (term148 A mul n m) (term467 A add n r1 mul m r0)). Qed.
Lemma lem1018864 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term514 A add n r1 mul m r0 p) = (term465 A add n p r1 mul m r0).
Proof. exact (eq_refl (term514 A add n r1 mul m r0 p)). Qed.
Lemma lem1018865 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term515 A add n r1 mul m r0) = (term467 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018864 A add n p r1 mul m r0)). Qed.
Lemma lem1018866 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018867 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term516 A add n r1 mul m r0) = (term468 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018866 A) (@lem1018865 A add n r1 mul m r0)). Qed.
Lemma lem1018868 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term504 A mul n m) = (term504 A mul n m).
Proof. exact (eq_refl (term504 A mul n m)). Qed.
Lemma lem1018869 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term512 A add n r1 mul m r0) = (term506 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018868 A mul n m) (@lem1018867 A add n r1 mul m r0)). Qed.
Lemma lem1018870 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018871 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term517 A add n r1 mul m r0) = (term518 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018870) (@lem1018869 A add n r1 mul m r0)). Qed.
Lemma lem1018872 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term514 A add n r1 mul m r0 p) = (term465 A add n p r1 mul m r0).
Proof. exact (eq_refl (term514 A add n r1 mul m r0 p)). Qed.
Lemma lem1018873 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term504 A mul n m) = (term504 A mul n m).
Proof. exact (eq_refl (term504 A mul n m)). Qed.
Lemma lem1018874 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term519 A add n r1 mul m r0 p) = (term520 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1018873 A mul n m) (@lem1018872 A add n p r1 mul m r0)). Qed.
Lemma lem1018875 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term521 A add n r1 mul m r0) = (term522 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018874 A add n p r1 mul m r0)). Qed.
Lemma lem1018876 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018877 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term513 A add n r1 mul m r0) = (term523 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018876 A) (@lem1018875 A add n r1 mul m r0)). Qed.
Lemma lem1018878 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term512 A add n r1 mul m r0) = (term513 A add n r1 mul m r0)) = ((term506 A add n r1 mul m r0) = (term523 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018871 A add n r1 mul m r0) (@lem1018877 A add n r1 mul m r0)). Qed.
Lemma lem1018879 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term506 A add n r1 mul m r0) = (term523 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1018878 A add n r1 mul m r0) (@lem1018863 A add n r1 mul m r0)). Qed.
Lemma lem1018880 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term508 A add r1 mul m r0) = (term524 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018879 A add n r1 mul m r0)). Qed.
Lemma lem1018881 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018882 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term509 A add r1 mul m r0) = (term525 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018881 A) (@lem1018880 A add r1 mul m r0)). Qed.
Lemma lem1018883 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term488 A add r1 mul m r0) = (term525 A add r1 mul m r0).
Proof. exact (TRANS (@lem1018859 A add r1 mul m r0) (@lem1018882 A add r1 mul m r0)). Qed.
Lemma lem1018884 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term490 A add r1 mul r0) = (term526 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018883 A add r1 mul m r0)). Qed.
Lemma lem1018885 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018886 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term491 A add r1 mul r0) = (term527 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018885 A) (@lem1018884 A add r1 mul r0)). Qed.
Lemma lem1018887 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term473 A add r1 mul r0) = (term527 A add r1 mul r0).
Proof. exact (TRANS (@lem1018832 A add r1 mul r0) (@lem1018886 A add r1 mul r0)). Qed.
Lemma lem1018888 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term264 A add r1 mul r0) = (term527 A add r1 mul r0).
Proof. exact (TRANS (@lem1018805 A add r1 mul r0) (@lem1018887 A add r1 mul r0)). Qed.
Lemma lem1018889 {A : Type'} (add : type1400 A) (r0 : A) : (term242 A add r0) = (term242 A add r0).
Proof. exact (eq_refl (term242 A add r0)). Qed.
Lemma lem1018890 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term267 A add r1 mul r0) = (term528 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018889 A add r0) (@lem1018888 A add r1 mul r0)). Qed.
Lemma lem1018892 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018893 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018892 A P Q). Qed.
Lemma lem1018894 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term529 A add r1 mul r0) = (term530 A add r1 mul r0).
Proof. exact (@lem1018893 A (term209 A add r0) (term526 A add r1 mul r0)). Qed.
Lemma lem1018895 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term281 A add r0 m) = (term207 A add r0 m).
Proof. exact (eq_refl (term281 A add r0 m)). Qed.
Lemma lem1018896 {A : Type'} (add : type1400 A) (r0 : A) : (term282 A add r0) = (term209 A add r0).
Proof. exact (fun_ext (fun m : A => @lem1018895 A add r0 m)). Qed.
Lemma lem1018897 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018898 {A : Type'} (add : type1400 A) (r0 : A) : (term283 A add r0) = (term210 A add r0).
Proof. exact (MK_COMB (@lem1018897 A) (@lem1018896 A add r0)). Qed.
Lemma lem1018899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018900 {A : Type'} (add : type1400 A) (r0 : A) : (term284 A add r0) = (term242 A add r0).
Proof. exact (MK_COMB (@lem1018899) (@lem1018898 A add r0)). Qed.
Lemma lem1018901 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term531 A add r1 mul r0 m) = (term525 A add r1 mul m r0).
Proof. exact (eq_refl (term531 A add r1 mul r0 m)). Qed.
Lemma lem1018902 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term532 A add r1 mul r0) = (term526 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018901 A add r1 mul m r0)). Qed.
Lemma lem1018903 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018904 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term533 A add r1 mul r0) = (term527 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018903 A) (@lem1018902 A add r1 mul r0)). Qed.
Lemma lem1018905 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term529 A add r1 mul r0) = (term528 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018900 A add r0) (@lem1018904 A add r1 mul r0)). Qed.
Lemma lem1018906 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018907 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term534 A add r1 mul r0) = (term535 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018906) (@lem1018905 A add r1 mul r0)). Qed.
Lemma lem1018908 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term281 A add r0 m) = (term207 A add r0 m).
Proof. exact (eq_refl (term281 A add r0 m)). Qed.
Lemma lem1018909 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018910 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term290 A add r0 m) = (term291 A add r0 m).
Proof. exact (MK_COMB (@lem1018909) (@lem1018908 A add r0 m)). Qed.
Lemma lem1018911 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term531 A add r1 mul r0 m) = (term525 A add r1 mul m r0).
Proof. exact (eq_refl (term531 A add r1 mul r0 m)). Qed.
Lemma lem1018912 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term536 A add r1 mul r0 m) = (term537 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018910 A add r0 m) (@lem1018911 A add r1 mul m r0)). Qed.
Lemma lem1018913 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term538 A add r1 mul r0) = (term539 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018912 A add r1 mul m r0)). Qed.
Lemma lem1018914 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018915 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term530 A add r1 mul r0) = (term540 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018914 A) (@lem1018913 A add r1 mul r0)). Qed.
Lemma lem1018916 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term529 A add r1 mul r0) = (term530 A add r1 mul r0)) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1018907 A add r1 mul r0) (@lem1018915 A add r1 mul r0)). Qed.
Lemma lem1018917 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term528 A add r1 mul r0) = (term540 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1018916 A add r1 mul r0) (@lem1018894 A add r1 mul r0)). Qed.
Lemma lem1018920 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term541 A add r1 mul r0) = (term541 A add r1 mul r0).
Proof. exact (eq_refl (term541 A add r1 mul r0)). Qed.
Lemma lem1018921 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term541 A add r1 mul r0) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0)).
Proof. exact (eq_refl (term541 A add r1 mul r0)). Qed.
Lemma lem1018922 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term542 A add r1 mul r0) = (term542 A add r1 mul r0).
Proof. exact (eq_refl (term542 A add r1 mul r0)). Qed.
Lemma lem1018923 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term541 A add r1 mul r0) = (term541 A add r1 mul r0)) = ((term541 A add r1 mul r0) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0))).
Proof. exact (MK_COMB (@lem1018922 A add r1 mul r0) (@lem1018921 A add r1 mul r0)). Qed.
Lemma lem1018924 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term541 A add r1 mul r0) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0)).
Proof. exact (eq_refl (term541 A add r1 mul r0)). Qed.
Lemma lem1018925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018926 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term542 A add r1 mul r0) = (term543 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018925) (@lem1018924 A add r1 mul r0)). Qed.
Lemma lem1018927 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term528 A add r1 mul r0) = (term540 A add r1 mul r0)) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0)).
Proof. exact (eq_refl ((term528 A add r1 mul r0) = (term540 A add r1 mul r0))). Qed.
Lemma lem1018928 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term541 A add r1 mul r0) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0))) = (((term528 A add r1 mul r0) = (term540 A add r1 mul r0)) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0))).
Proof. exact (MK_COMB (@lem1018926 A add r1 mul r0) (@lem1018927 A add r1 mul r0)). Qed.
Lemma lem1018929 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term541 A add r1 mul r0) = (term541 A add r1 mul r0)) = (((term528 A add r1 mul r0) = (term540 A add r1 mul r0)) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0))).
Proof. exact (TRANS (@lem1018923 A add r1 mul r0) (@lem1018928 A add r1 mul r0)). Qed.
Lemma lem1018930 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term528 A add r1 mul r0) = (term540 A add r1 mul r0)) = ((term528 A add r1 mul r0) = (term540 A add r1 mul r0)).
Proof. exact (EQ_MP (@lem1018929 A add r1 mul r0) (@lem1018920 A add r1 mul r0)). Qed.
Lemma lem1018931 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term528 A add r1 mul r0) = (term540 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1018930 A add r1 mul r0) (@lem1018917 A add r1 mul r0)). Qed.
Lemma lem1018933 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1018934 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (@lem1018933 A P Q). Qed.
Lemma lem1018935 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term544 A add r1 mul m r0) = (term545 A add r1 mul m r0).
Proof. exact (@lem1018934 A (term207 A add r0 m) (term524 A add r1 mul m r0)). Qed.
Lemma lem1018936 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term546 A add r1 mul m r0 n) = (term523 A add n r1 mul m r0).
Proof. exact (eq_refl (term546 A add r1 mul m r0 n)). Qed.
Lemma lem1018937 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term547 A add r1 mul m r0) = (term524 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018936 A add n r1 mul m r0)). Qed.
Lemma lem1018938 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018939 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term548 A add r1 mul m r0) = (term525 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018938 A) (@lem1018937 A add r1 mul m r0)). Qed.
Lemma lem1018940 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term291 A add r0 m) = (term291 A add r0 m).
Proof. exact (eq_refl (term291 A add r0 m)). Qed.
Lemma lem1018941 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term544 A add r1 mul m r0) = (term537 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018940 A add r0 m) (@lem1018939 A add r1 mul m r0)). Qed.
Lemma lem1018942 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018943 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term549 A add r1 mul m r0) = (term550 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018942) (@lem1018941 A add r1 mul m r0)). Qed.
Lemma lem1018944 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term546 A add r1 mul m r0 n) = (term523 A add n r1 mul m r0).
Proof. exact (eq_refl (term546 A add r1 mul m r0 n)). Qed.
Lemma lem1018945 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term291 A add r0 m) = (term291 A add r0 m).
Proof. exact (eq_refl (term291 A add r0 m)). Qed.
Lemma lem1018946 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term551 A add r1 mul m r0 n) = (term552 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018945 A add r0 m) (@lem1018944 A add n r1 mul m r0)). Qed.
Lemma lem1018947 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term553 A add r1 mul m r0) = (term554 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018946 A add n r1 mul m r0)). Qed.
Lemma lem1018948 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018949 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term545 A add r1 mul m r0) = (term555 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018948 A) (@lem1018947 A add r1 mul m r0)). Qed.
Lemma lem1018950 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term544 A add r1 mul m r0) = (term545 A add r1 mul m r0)) = ((term537 A add r1 mul m r0) = (term555 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018943 A add r1 mul m r0) (@lem1018949 A add r1 mul m r0)). Qed.
Lemma lem1018951 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term537 A add r1 mul m r0) = (term555 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1018950 A add r1 mul m r0) (@lem1018935 A add r1 mul m r0)). Qed.
Lemma lem1018953 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1018954 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (@lem1018953 A P Q). Qed.
Lemma lem1018955 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term556 A add n r1 mul m r0) = (term557 A add n r1 mul m r0).
Proof. exact (@lem1018954 A (term207 A add r0 m) (term522 A add n r1 mul m r0)). Qed.
Lemma lem1018956 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term558 A add n r1 mul m r0 p) = (term520 A add n p r1 mul m r0).
Proof. exact (eq_refl (term558 A add n r1 mul m r0 p)). Qed.
Lemma lem1018957 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term559 A add n r1 mul m r0) = (term522 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018956 A add n p r1 mul m r0)). Qed.
Lemma lem1018958 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018959 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term560 A add n r1 mul m r0) = (term523 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018958 A) (@lem1018957 A add n r1 mul m r0)). Qed.
Lemma lem1018960 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term291 A add r0 m) = (term291 A add r0 m).
Proof. exact (eq_refl (term291 A add r0 m)). Qed.
Lemma lem1018961 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term556 A add n r1 mul m r0) = (term552 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018960 A add r0 m) (@lem1018959 A add n r1 mul m r0)). Qed.
Lemma lem1018962 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018963 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term561 A add n r1 mul m r0) = (term562 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018962) (@lem1018961 A add n r1 mul m r0)). Qed.
Lemma lem1018964 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term558 A add n r1 mul m r0 p) = (term520 A add n p r1 mul m r0).
Proof. exact (eq_refl (term558 A add n r1 mul m r0 p)). Qed.
Lemma lem1018965 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term291 A add r0 m) = (term291 A add r0 m).
Proof. exact (eq_refl (term291 A add r0 m)). Qed.
Lemma lem1018966 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term563 A add n r1 mul m r0 p) = (term564 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1018965 A add r0 m) (@lem1018964 A add n p r1 mul m r0)). Qed.
Lemma lem1018967 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term565 A add n r1 mul m r0) = (term566 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1018966 A add n p r1 mul m r0)). Qed.
Lemma lem1018968 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018969 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term557 A add n r1 mul m r0) = (term567 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1018968 A) (@lem1018967 A add n r1 mul m r0)). Qed.
Lemma lem1018970 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term556 A add n r1 mul m r0) = (term557 A add n r1 mul m r0)) = ((term552 A add n r1 mul m r0) = (term567 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1018963 A add n r1 mul m r0) (@lem1018969 A add n r1 mul m r0)). Qed.
Lemma lem1018971 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term552 A add n r1 mul m r0) = (term567 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1018970 A add n r1 mul m r0) (@lem1018955 A add n r1 mul m r0)). Qed.
Lemma lem1018972 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term554 A add r1 mul m r0) = (term568 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1018971 A add n r1 mul m r0)). Qed.
Lemma lem1018973 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018974 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term555 A add r1 mul m r0) = (term569 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1018973 A) (@lem1018972 A add r1 mul m r0)). Qed.
Lemma lem1018975 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term537 A add r1 mul m r0) = (term569 A add r1 mul m r0).
Proof. exact (TRANS (@lem1018951 A add r1 mul m r0) (@lem1018974 A add r1 mul m r0)). Qed.
Lemma lem1018976 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term539 A add r1 mul r0) = (term570 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018975 A add r1 mul m r0)). Qed.
Lemma lem1018977 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018978 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term540 A add r1 mul r0) = (term571 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018977 A) (@lem1018976 A add r1 mul r0)). Qed.
Lemma lem1018979 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term528 A add r1 mul r0) = (term571 A add r1 mul r0).
Proof. exact (TRANS (@lem1018931 A add r1 mul r0) (@lem1018978 A add r1 mul r0)). Qed.
Lemma lem1018980 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term267 A add r1 mul r0) = (term571 A add r1 mul r0).
Proof. exact (TRANS (@lem1018890 A add r1 mul r0) (@lem1018979 A add r1 mul r0)). Qed.
Lemma lem1018981 {A : Type'} (add : type1400 A) : (term252 A add) = (term252 A add).
Proof. exact (eq_refl (term252 A add)). Qed.
Lemma lem1018982 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term270 A add r1 mul r0) = (term572 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018981 A add) (@lem1018980 A add r1 mul r0)). Qed.
Lemma lem1018984 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1018985 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1018984 A P Q). Qed.
Lemma lem1018986 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term573 A add r1 mul r0) = (term574 A add r1 mul r0).
Proof. exact (@lem1018985 A (term201 A add) (term570 A add r1 mul r0)). Qed.
Lemma lem1018987 {A : Type'} (add : type1400 A) (m : A) : (term358 A add m) = (term195 A add m).
Proof. exact (eq_refl (term358 A add m)). Qed.
Lemma lem1018988 {A : Type'} (add : type1400 A) : (term359 A add) = (term201 A add).
Proof. exact (fun_ext (fun m : A => @lem1018987 A add m)). Qed.
Lemma lem1018989 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018990 {A : Type'} (add : type1400 A) : (term360 A add) = (term202 A add).
Proof. exact (MK_COMB (@lem1018989 A) (@lem1018988 A add)). Qed.
Lemma lem1018991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1018992 {A : Type'} (add : type1400 A) : (term361 A add) = (term252 A add).
Proof. exact (MK_COMB (@lem1018991) (@lem1018990 A add)). Qed.
Lemma lem1018993 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term575 A add r1 mul r0 m) = (term569 A add r1 mul m r0).
Proof. exact (eq_refl (term575 A add r1 mul r0 m)). Qed.
Lemma lem1018994 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term576 A add r1 mul r0) = (term570 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1018993 A add r1 mul m r0)). Qed.
Lemma lem1018995 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1018996 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term577 A add r1 mul r0) = (term571 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018995 A) (@lem1018994 A add r1 mul r0)). Qed.
Lemma lem1018997 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term573 A add r1 mul r0) = (term572 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018992 A add) (@lem1018996 A add r1 mul r0)). Qed.
Lemma lem1018998 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1018999 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term578 A add r1 mul r0) = (term579 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1018998) (@lem1018997 A add r1 mul r0)). Qed.
Lemma lem1019000 {A : Type'} (add : type1400 A) (m : A) : (term358 A add m) = (term195 A add m).
Proof. exact (eq_refl (term358 A add m)). Qed.
Lemma lem1019001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019002 {A : Type'} (add : type1400 A) (m : A) : (term367 A add m) = (term368 A add m).
Proof. exact (MK_COMB (@lem1019001) (@lem1019000 A add m)). Qed.
Lemma lem1019003 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term575 A add r1 mul r0 m) = (term569 A add r1 mul m r0).
Proof. exact (eq_refl (term575 A add r1 mul r0 m)). Qed.
Lemma lem1019004 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term580 A add r1 mul r0 m) = (term581 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019002 A add m) (@lem1019003 A add r1 mul m r0)). Qed.
Lemma lem1019005 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term582 A add r1 mul r0) = (term583 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019004 A add r1 mul m r0)). Qed.
Lemma lem1019006 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019007 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term574 A add r1 mul r0) = (term584 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019006 A) (@lem1019005 A add r1 mul r0)). Qed.
Lemma lem1019008 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term573 A add r1 mul r0) = (term574 A add r1 mul r0)) = ((term572 A add r1 mul r0) = (term584 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1018999 A add r1 mul r0) (@lem1019007 A add r1 mul r0)). Qed.
Lemma lem1019009 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term572 A add r1 mul r0) = (term584 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1019008 A add r1 mul r0) (@lem1018986 A add r1 mul r0)). Qed.
Lemma lem1019011 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1019012 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1019011 A P Q). Qed.
Lemma lem1019013 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term585 A add r1 mul m r0) = (term586 A add r1 mul m r0).
Proof. exact (@lem1019012 A (term194 A add m) (term568 A add r1 mul m r0)). Qed.
Lemma lem1019014 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term376 A add m n) = (term188 A n add m).
Proof. exact (eq_refl (term376 A add m n)). Qed.
Lemma lem1019015 {A : Type'} (add : type1400 A) (m : A) : (term377 A add m) = (term194 A add m).
Proof. exact (fun_ext (fun n : A => @lem1019014 A n add m)). Qed.
Lemma lem1019016 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019017 {A : Type'} (add : type1400 A) (m : A) : (term378 A add m) = (term195 A add m).
Proof. exact (MK_COMB (@lem1019016 A) (@lem1019015 A add m)). Qed.
Lemma lem1019018 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019019 {A : Type'} (add : type1400 A) (m : A) : (term379 A add m) = (term368 A add m).
Proof. exact (MK_COMB (@lem1019018) (@lem1019017 A add m)). Qed.
Lemma lem1019020 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term587 A add r1 mul m r0 n) = (term567 A add n r1 mul m r0).
Proof. exact (eq_refl (term587 A add r1 mul m r0 n)). Qed.
Lemma lem1019021 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term588 A add r1 mul m r0) = (term568 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019020 A add n r1 mul m r0)). Qed.
Lemma lem1019022 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019023 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term589 A add r1 mul m r0) = (term569 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019022 A) (@lem1019021 A add r1 mul m r0)). Qed.
Lemma lem1019024 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term585 A add r1 mul m r0) = (term581 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019019 A add m) (@lem1019023 A add r1 mul m r0)). Qed.
Lemma lem1019025 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019026 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term590 A add r1 mul m r0) = (term591 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019025) (@lem1019024 A add r1 mul m r0)). Qed.
Lemma lem1019027 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term376 A add m n) = (term188 A n add m).
Proof. exact (eq_refl (term376 A add m n)). Qed.
Lemma lem1019028 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019029 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term385 A add m n) = (term386 A n add m).
Proof. exact (MK_COMB (@lem1019028) (@lem1019027 A n add m)). Qed.
Lemma lem1019030 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term587 A add r1 mul m r0 n) = (term567 A add n r1 mul m r0).
Proof. exact (eq_refl (term587 A add r1 mul m r0 n)). Qed.
Lemma lem1019031 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term592 A add r1 mul m r0 n) = (term593 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019029 A n add m) (@lem1019030 A add n r1 mul m r0)). Qed.
Lemma lem1019032 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term594 A add r1 mul m r0) = (term595 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019031 A add n r1 mul m r0)). Qed.
Lemma lem1019033 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019034 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term586 A add r1 mul m r0) = (term596 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019033 A) (@lem1019032 A add r1 mul m r0)). Qed.
Lemma lem1019035 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term585 A add r1 mul m r0) = (term586 A add r1 mul m r0)) = ((term581 A add r1 mul m r0) = (term596 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1019026 A add r1 mul m r0) (@lem1019034 A add r1 mul m r0)). Qed.
Lemma lem1019036 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term581 A add r1 mul m r0) = (term596 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1019035 A add r1 mul m r0) (@lem1019013 A add r1 mul m r0)). Qed.
Lemma lem1019038 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1019039 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1019038 A P Q). Qed.
Lemma lem1019040 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term597 A add n r1 mul m r0) = (term598 A add n r1 mul m r0).
Proof. exact (@lem1019039 A (term187 A n add m) (term566 A add n r1 mul m r0)). Qed.
Lemma lem1019041 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term394 A n add m p) = (term185 A n add m p).
Proof. exact (eq_refl (term394 A n add m p)). Qed.
Lemma lem1019042 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term395 A n add m) = (term187 A n add m).
Proof. exact (fun_ext (fun p : A => @lem1019041 A n add m p)). Qed.
Lemma lem1019043 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019044 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term396 A n add m) = (term188 A n add m).
Proof. exact (MK_COMB (@lem1019043 A) (@lem1019042 A n add m)). Qed.
Lemma lem1019045 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019046 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term397 A n add m) = (term386 A n add m).
Proof. exact (MK_COMB (@lem1019045) (@lem1019044 A n add m)). Qed.
Lemma lem1019047 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term599 A add n r1 mul m r0 p) = (term564 A add n p r1 mul m r0).
Proof. exact (eq_refl (term599 A add n r1 mul m r0 p)). Qed.
Lemma lem1019048 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term600 A add n r1 mul m r0) = (term566 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1019047 A add n p r1 mul m r0)). Qed.
Lemma lem1019049 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019050 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term601 A add n r1 mul m r0) = (term567 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019049 A) (@lem1019048 A add n r1 mul m r0)). Qed.
Lemma lem1019051 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term597 A add n r1 mul m r0) = (term593 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019046 A n add m) (@lem1019050 A add n r1 mul m r0)). Qed.
Lemma lem1019052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019053 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term602 A add n r1 mul m r0) = (term603 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019052) (@lem1019051 A add n r1 mul m r0)). Qed.
Lemma lem1019054 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term394 A n add m p) = (term185 A n add m p).
Proof. exact (eq_refl (term394 A n add m p)). Qed.
Lemma lem1019055 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019056 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term403 A n add m p) = (term404 A n add m p).
Proof. exact (MK_COMB (@lem1019055) (@lem1019054 A n add m p)). Qed.
Lemma lem1019057 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term599 A add n r1 mul m r0 p) = (term564 A add n p r1 mul m r0).
Proof. exact (eq_refl (term599 A add n r1 mul m r0 p)). Qed.
Lemma lem1019058 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term604 A add n r1 mul m r0 p) = (term605 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1019056 A n add m p) (@lem1019057 A add n p r1 mul m r0)). Qed.
Lemma lem1019059 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term606 A add n r1 mul m r0) = (term607 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1019058 A add n p r1 mul m r0)). Qed.
Lemma lem1019060 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019061 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term598 A add n r1 mul m r0) = (term608 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019060 A) (@lem1019059 A add n r1 mul m r0)). Qed.
Lemma lem1019062 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term597 A add n r1 mul m r0) = (term598 A add n r1 mul m r0)) = ((term593 A add n r1 mul m r0) = (term608 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1019053 A add n r1 mul m r0) (@lem1019061 A add n r1 mul m r0)). Qed.
Lemma lem1019063 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term593 A add n r1 mul m r0) = (term608 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1019062 A add n r1 mul m r0) (@lem1019040 A add n r1 mul m r0)). Qed.
Lemma lem1019064 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term595 A add r1 mul m r0) = (term609 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019063 A add n r1 mul m r0)). Qed.
Lemma lem1019065 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019066 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term596 A add r1 mul m r0) = (term610 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019065 A) (@lem1019064 A add r1 mul m r0)). Qed.
Lemma lem1019067 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term581 A add r1 mul m r0) = (term610 A add r1 mul m r0).
Proof. exact (TRANS (@lem1019036 A add r1 mul m r0) (@lem1019066 A add r1 mul m r0)). Qed.
Lemma lem1019068 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term583 A add r1 mul r0) = (term611 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019067 A add r1 mul m r0)). Qed.
Lemma lem1019069 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019070 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term584 A add r1 mul r0) = (term612 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019069 A) (@lem1019068 A add r1 mul r0)). Qed.
Lemma lem1019071 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term572 A add r1 mul r0) = (term612 A add r1 mul r0).
Proof. exact (TRANS (@lem1019009 A add r1 mul r0) (@lem1019070 A add r1 mul r0)). Qed.
Lemma lem1019072 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term270 A add r1 mul r0) = (term612 A add r1 mul r0).
Proof. exact (TRANS (@lem1018982 A add r1 mul r0) (@lem1019071 A add r1 mul r0)). Qed.
Lemma lem1019073 {A : Type'} (add : type1400 A) : (term257 A add) = (term257 A add).
Proof. exact (eq_refl (term257 A add)). Qed.
Lemma lem1019074 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term273 A add r1 mul r0) = (term613 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019073 A add) (@lem1019072 A add r1 mul r0)). Qed.
Lemma lem1019076 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1019077 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1019076 A P Q). Qed.
Lemma lem1019078 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term614 A add r1 mul r0) = (term615 A add r1 mul r0).
Proof. exact (@lem1019077 A (term179 A add) (term611 A add r1 mul r0)). Qed.
Lemma lem1019079 {A : Type'} (m : A) (add : type1400 A) : (term417 A add m) = (term173 A m add).
Proof. exact (eq_refl (term417 A add m)). Qed.
Lemma lem1019080 {A : Type'} (add : type1400 A) : (term418 A add) = (term179 A add).
Proof. exact (fun_ext (fun m : A => @lem1019079 A m add)). Qed.
Lemma lem1019081 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019082 {A : Type'} (add : type1400 A) : (term419 A add) = (term180 A add).
Proof. exact (MK_COMB (@lem1019081 A) (@lem1019080 A add)). Qed.
Lemma lem1019083 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019084 {A : Type'} (add : type1400 A) : (term420 A add) = (term257 A add).
Proof. exact (MK_COMB (@lem1019083) (@lem1019082 A add)). Qed.
Lemma lem1019085 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term616 A add r1 mul r0 m) = (term610 A add r1 mul m r0).
Proof. exact (eq_refl (term616 A add r1 mul r0 m)). Qed.
Lemma lem1019086 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term617 A add r1 mul r0) = (term611 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019085 A add r1 mul m r0)). Qed.
Lemma lem1019087 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019088 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term618 A add r1 mul r0) = (term612 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019087 A) (@lem1019086 A add r1 mul r0)). Qed.
Lemma lem1019089 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term614 A add r1 mul r0) = (term613 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019084 A add) (@lem1019088 A add r1 mul r0)). Qed.
Lemma lem1019090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019091 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term619 A add r1 mul r0) = (term620 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019090) (@lem1019089 A add r1 mul r0)). Qed.
Lemma lem1019092 {A : Type'} (m : A) (add : type1400 A) : (term417 A add m) = (term173 A m add).
Proof. exact (eq_refl (term417 A add m)). Qed.
Lemma lem1019093 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019094 {A : Type'} (m : A) (add : type1400 A) : (term426 A add m) = (term427 A m add).
Proof. exact (MK_COMB (@lem1019093) (@lem1019092 A m add)). Qed.
Lemma lem1019095 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term616 A add r1 mul r0 m) = (term610 A add r1 mul m r0).
Proof. exact (eq_refl (term616 A add r1 mul r0 m)). Qed.
Lemma lem1019096 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term621 A add r1 mul r0 m) = (term622 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019094 A m add) (@lem1019095 A add r1 mul m r0)). Qed.
Lemma lem1019097 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term623 A add r1 mul r0) = (term624 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019096 A add r1 mul m r0)). Qed.
Lemma lem1019098 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019099 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term615 A add r1 mul r0) = (term625 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019098 A) (@lem1019097 A add r1 mul r0)). Qed.
Lemma lem1019100 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term614 A add r1 mul r0) = (term615 A add r1 mul r0)) = ((term613 A add r1 mul r0) = (term625 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1019091 A add r1 mul r0) (@lem1019099 A add r1 mul r0)). Qed.
Lemma lem1019101 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term613 A add r1 mul r0) = (term625 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1019100 A add r1 mul r0) (@lem1019078 A add r1 mul r0)). Qed.
Lemma lem1019103 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1019104 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1019103 A P Q). Qed.
Lemma lem1019105 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term626 A add r1 mul m r0) = (term627 A add r1 mul m r0).
Proof. exact (@lem1019104 A (term172 A m add) (term609 A add r1 mul m r0)). Qed.
Lemma lem1019106 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term435 A m add n) = (term166 A m add n).
Proof. exact (eq_refl (term435 A m add n)). Qed.
Lemma lem1019107 {A : Type'} (m : A) (add : type1400 A) : (term436 A m add) = (term172 A m add).
Proof. exact (fun_ext (fun n : A => @lem1019106 A m add n)). Qed.
Lemma lem1019108 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019109 {A : Type'} (m : A) (add : type1400 A) : (term437 A m add) = (term173 A m add).
Proof. exact (MK_COMB (@lem1019108 A) (@lem1019107 A m add)). Qed.
Lemma lem1019110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019111 {A : Type'} (m : A) (add : type1400 A) : (term438 A m add) = (term427 A m add).
Proof. exact (MK_COMB (@lem1019110) (@lem1019109 A m add)). Qed.
Lemma lem1019112 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term628 A add r1 mul m r0 n) = (term608 A add n r1 mul m r0).
Proof. exact (eq_refl (term628 A add r1 mul m r0 n)). Qed.
Lemma lem1019113 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term629 A add r1 mul m r0) = (term609 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019112 A add n r1 mul m r0)). Qed.
Lemma lem1019114 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019115 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term630 A add r1 mul m r0) = (term610 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019114 A) (@lem1019113 A add r1 mul m r0)). Qed.
Lemma lem1019116 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term626 A add r1 mul m r0) = (term622 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019111 A m add) (@lem1019115 A add r1 mul m r0)). Qed.
Lemma lem1019117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019118 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term631 A add r1 mul m r0) = (term632 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019117) (@lem1019116 A add r1 mul m r0)). Qed.
Lemma lem1019119 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term435 A m add n) = (term166 A m add n).
Proof. exact (eq_refl (term435 A m add n)). Qed.
Lemma lem1019120 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019121 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term444 A m add n) = (term445 A m add n).
Proof. exact (MK_COMB (@lem1019120) (@lem1019119 A m add n)). Qed.
Lemma lem1019122 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term628 A add r1 mul m r0 n) = (term608 A add n r1 mul m r0).
Proof. exact (eq_refl (term628 A add r1 mul m r0 n)). Qed.
Lemma lem1019123 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term633 A add r1 mul m r0 n) = (term634 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019121 A m add n) (@lem1019122 A add n r1 mul m r0)). Qed.
Lemma lem1019124 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term635 A add r1 mul m r0) = (term636 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019123 A add n r1 mul m r0)). Qed.
Lemma lem1019125 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019126 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term627 A add r1 mul m r0) = (term637 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019125 A) (@lem1019124 A add r1 mul m r0)). Qed.
Lemma lem1019127 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term626 A add r1 mul m r0) = (term627 A add r1 mul m r0)) = ((term622 A add r1 mul m r0) = (term637 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1019118 A add r1 mul m r0) (@lem1019126 A add r1 mul m r0)). Qed.
Lemma lem1019128 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term622 A add r1 mul m r0) = (term637 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1019127 A add r1 mul m r0) (@lem1019105 A add r1 mul m r0)). Qed.
Lemma lem1019130 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1019131 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1019130 A P Q). Qed.
Lemma lem1019132 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term638 A add n r1 mul m r0) = (term639 A add n r1 mul m r0).
Proof. exact (@lem1019131 A (term165 A m add n) (term607 A add n r1 mul m r0)). Qed.
Lemma lem1019133 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term453 A m add n p) = (term163 A m add n p).
Proof. exact (eq_refl (term453 A m add n p)). Qed.
Lemma lem1019134 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term454 A m add n) = (term165 A m add n).
Proof. exact (fun_ext (fun p : A => @lem1019133 A m add n p)). Qed.
Lemma lem1019135 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019136 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term455 A m add n) = (term166 A m add n).
Proof. exact (MK_COMB (@lem1019135 A) (@lem1019134 A m add n)). Qed.
Lemma lem1019137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019138 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term456 A m add n) = (term445 A m add n).
Proof. exact (MK_COMB (@lem1019137) (@lem1019136 A m add n)). Qed.
Lemma lem1019139 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term640 A add n r1 mul m r0 p) = (term605 A add n p r1 mul m r0).
Proof. exact (eq_refl (term640 A add n r1 mul m r0 p)). Qed.
Lemma lem1019140 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term641 A add n r1 mul m r0) = (term607 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1019139 A add n p r1 mul m r0)). Qed.
Lemma lem1019141 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019142 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term642 A add n r1 mul m r0) = (term608 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019141 A) (@lem1019140 A add n r1 mul m r0)). Qed.
Lemma lem1019143 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term638 A add n r1 mul m r0) = (term634 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019138 A m add n) (@lem1019142 A add n r1 mul m r0)). Qed.
Lemma lem1019144 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019145 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term643 A add n r1 mul m r0) = (term644 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019144) (@lem1019143 A add n r1 mul m r0)). Qed.
Lemma lem1019146 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term453 A m add n p) = (term163 A m add n p).
Proof. exact (eq_refl (term453 A m add n p)). Qed.
Lemma lem1019147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019148 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term462 A m add n p) = (term463 A m add n p).
Proof. exact (MK_COMB (@lem1019147) (@lem1019146 A m add n p)). Qed.
Lemma lem1019149 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term640 A add n r1 mul m r0 p) = (term605 A add n p r1 mul m r0).
Proof. exact (eq_refl (term640 A add n r1 mul m r0 p)). Qed.
Lemma lem1019150 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term645 A add n r1 mul m r0 p) = (term646 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1019148 A m add n p) (@lem1019149 A add n p r1 mul m r0)). Qed.
Lemma lem1019151 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term647 A add n r1 mul m r0) = (term648 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1019150 A add n p r1 mul m r0)). Qed.
Lemma lem1019152 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019153 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term639 A add n r1 mul m r0) = (term649 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019152 A) (@lem1019151 A add n r1 mul m r0)). Qed.
Lemma lem1019154 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term638 A add n r1 mul m r0) = (term639 A add n r1 mul m r0)) = ((term634 A add n r1 mul m r0) = (term649 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1019145 A add n r1 mul m r0) (@lem1019153 A add n r1 mul m r0)). Qed.
Lemma lem1019155 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term634 A add n r1 mul m r0) = (term649 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1019154 A add n r1 mul m r0) (@lem1019132 A add n r1 mul m r0)). Qed.
Lemma lem1019156 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term636 A add r1 mul m r0) = (term650 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019155 A add n r1 mul m r0)). Qed.
Lemma lem1019157 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019158 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term637 A add r1 mul m r0) = (term651 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019157 A) (@lem1019156 A add r1 mul m r0)). Qed.
Lemma lem1019159 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term622 A add r1 mul m r0) = (term651 A add r1 mul m r0).
Proof. exact (TRANS (@lem1019128 A add r1 mul m r0) (@lem1019158 A add r1 mul m r0)). Qed.
Lemma lem1019160 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term624 A add r1 mul r0) = (term652 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019159 A add r1 mul m r0)). Qed.
Lemma lem1019161 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019162 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term625 A add r1 mul r0) = (term653 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019161 A) (@lem1019160 A add r1 mul r0)). Qed.
Lemma lem1019163 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term613 A add r1 mul r0) = (term653 A add r1 mul r0).
Proof. exact (TRANS (@lem1019101 A add r1 mul r0) (@lem1019162 A add r1 mul r0)). Qed.
Lemma lem1019164 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term273 A add r1 mul r0) = (term653 A add r1 mul r0).
Proof. exact (TRANS (@lem1019074 A add r1 mul r0) (@lem1019163 A add r1 mul r0)). Qed.
Lemma lem1019165 {A : Type'} (add : type1400 A) : (term262 A add) = (term262 A add).
Proof. exact (eq_refl (term262 A add)). Qed.
Lemma lem1019166 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term276 A add r1 mul r0) = (term654 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019165 A add) (@lem1019164 A add r1 mul r0)). Qed.
Lemma lem1019168 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1019169 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1019168 A P Q). Qed.
Lemma lem1019170 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term655 A add r1 mul r0) = (term656 A add r1 mul r0).
Proof. exact (@lem1019169 A (term157 A add) (term652 A add r1 mul r0)). Qed.
Lemma lem1019171 {A : Type'} (add : type1400 A) (m : A) : (term476 A add m) = (term151 A add m).
Proof. exact (eq_refl (term476 A add m)). Qed.
Lemma lem1019172 {A : Type'} (add : type1400 A) : (term477 A add) = (term157 A add).
Proof. exact (fun_ext (fun m : A => @lem1019171 A add m)). Qed.
Lemma lem1019173 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019174 {A : Type'} (add : type1400 A) : (term478 A add) = (term158 A add).
Proof. exact (MK_COMB (@lem1019173 A) (@lem1019172 A add)). Qed.
Lemma lem1019175 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019176 {A : Type'} (add : type1400 A) : (term479 A add) = (term262 A add).
Proof. exact (MK_COMB (@lem1019175) (@lem1019174 A add)). Qed.
Lemma lem1019177 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term657 A add r1 mul r0 m) = (term651 A add r1 mul m r0).
Proof. exact (eq_refl (term657 A add r1 mul r0 m)). Qed.
Lemma lem1019178 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term658 A add r1 mul r0) = (term652 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019177 A add r1 mul m r0)). Qed.
Lemma lem1019179 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019180 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term659 A add r1 mul r0) = (term653 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019179 A) (@lem1019178 A add r1 mul r0)). Qed.
Lemma lem1019181 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term655 A add r1 mul r0) = (term654 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019176 A add) (@lem1019180 A add r1 mul r0)). Qed.
Lemma lem1019182 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019183 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term660 A add r1 mul r0) = (term661 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019182) (@lem1019181 A add r1 mul r0)). Qed.
Lemma lem1019184 {A : Type'} (add : type1400 A) (m : A) : (term476 A add m) = (term151 A add m).
Proof. exact (eq_refl (term476 A add m)). Qed.
Lemma lem1019185 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019186 {A : Type'} (add : type1400 A) (m : A) : (term485 A add m) = (term486 A add m).
Proof. exact (MK_COMB (@lem1019185) (@lem1019184 A add m)). Qed.
Lemma lem1019187 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term657 A add r1 mul r0 m) = (term651 A add r1 mul m r0).
Proof. exact (eq_refl (term657 A add r1 mul r0 m)). Qed.
Lemma lem1019188 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term662 A add r1 mul r0 m) = (term663 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019186 A add m) (@lem1019187 A add r1 mul m r0)). Qed.
Lemma lem1019189 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term664 A add r1 mul r0) = (term665 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019188 A add r1 mul m r0)). Qed.
Lemma lem1019190 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019191 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term656 A add r1 mul r0) = (term666 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019190 A) (@lem1019189 A add r1 mul r0)). Qed.
Lemma lem1019192 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : ((term655 A add r1 mul r0) = (term656 A add r1 mul r0)) = ((term654 A add r1 mul r0) = (term666 A add r1 mul r0)).
Proof. exact (MK_COMB (@lem1019183 A add r1 mul r0) (@lem1019191 A add r1 mul r0)). Qed.
Lemma lem1019193 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term654 A add r1 mul r0) = (term666 A add r1 mul r0).
Proof. exact (EQ_MP (@lem1019192 A add r1 mul r0) (@lem1019170 A add r1 mul r0)). Qed.
Lemma lem1019195 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1019196 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term277 A P Q) = (term278 A P Q).
Proof. exact (@lem1019195 A P Q). Qed.
Lemma lem1019197 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term667 A add r1 mul m r0) = (term668 A add r1 mul m r0).
Proof. exact (@lem1019196 A (term150 A add m) (term650 A add r1 mul m r0)). Qed.
Lemma lem1019198 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term494 A add m n) = (term148 A add n m).
Proof. exact (eq_refl (term494 A add m n)). Qed.
Lemma lem1019199 {A : Type'} (add : type1400 A) (m : A) : (term495 A add m) = (term150 A add m).
Proof. exact (fun_ext (fun n : A => @lem1019198 A add n m)). Qed.
Lemma lem1019200 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019201 {A : Type'} (add : type1400 A) (m : A) : (term496 A add m) = (term151 A add m).
Proof. exact (MK_COMB (@lem1019200 A) (@lem1019199 A add m)). Qed.
Lemma lem1019202 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019203 {A : Type'} (add : type1400 A) (m : A) : (term497 A add m) = (term486 A add m).
Proof. exact (MK_COMB (@lem1019202) (@lem1019201 A add m)). Qed.
Lemma lem1019204 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term669 A add r1 mul m r0 n) = (term649 A add n r1 mul m r0).
Proof. exact (eq_refl (term669 A add r1 mul m r0 n)). Qed.
Lemma lem1019205 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term670 A add r1 mul m r0) = (term650 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019204 A add n r1 mul m r0)). Qed.
Lemma lem1019206 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019207 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term671 A add r1 mul m r0) = (term651 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019206 A) (@lem1019205 A add r1 mul m r0)). Qed.
Lemma lem1019208 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term667 A add r1 mul m r0) = (term663 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019203 A add m) (@lem1019207 A add r1 mul m r0)). Qed.
Lemma lem1019209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019210 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term672 A add r1 mul m r0) = (term673 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019209) (@lem1019208 A add r1 mul m r0)). Qed.
Lemma lem1019211 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term494 A add m n) = (term148 A add n m).
Proof. exact (eq_refl (term494 A add m n)). Qed.
Lemma lem1019212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1019213 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term503 A add m n) = (term504 A add n m).
Proof. exact (MK_COMB (@lem1019212) (@lem1019211 A add n m)). Qed.
Lemma lem1019214 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term669 A add r1 mul m r0 n) = (term649 A add n r1 mul m r0).
Proof. exact (eq_refl (term669 A add r1 mul m r0 n)). Qed.
Lemma lem1019215 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term674 A add r1 mul m r0 n) = (term675 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019213 A add n m) (@lem1019214 A add n r1 mul m r0)). Qed.
Lemma lem1019216 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term676 A add r1 mul m r0) = (term677 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019215 A add n r1 mul m r0)). Qed.
Lemma lem1019217 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019218 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term668 A add r1 mul m r0) = (term678 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019217 A) (@lem1019216 A add r1 mul m r0)). Qed.
Lemma lem1019219 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term667 A add r1 mul m r0) = (term668 A add r1 mul m r0)) = ((term663 A add r1 mul m r0) = (term678 A add r1 mul m r0)).
Proof. exact (MK_COMB (@lem1019210 A add r1 mul m r0) (@lem1019218 A add r1 mul m r0)). Qed.
Lemma lem1019220 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term663 A add r1 mul m r0) = (term678 A add r1 mul m r0).
Proof. exact (EQ_MP (@lem1019219 A add r1 mul m r0) (@lem1019197 A add r1 mul m r0)). Qed.
Lemma lem1019222 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1019223 {A : Type'} (P : Prop) (Q : A -> Prop) : (term510 A P Q) = (term511 A P Q).
Proof. exact (@lem1019222 A P Q). Qed.
Lemma lem1019224 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term679 A add n r1 mul m r0) = (term680 A add n r1 mul m r0).
Proof. exact (@lem1019223 A (term148 A add n m) (term648 A add n r1 mul m r0)). Qed.
Lemma lem1019225 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term681 A add n r1 mul m r0 p) = (term646 A add n p r1 mul m r0).
Proof. exact (eq_refl (term681 A add n r1 mul m r0 p)). Qed.
Lemma lem1019226 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term682 A add n r1 mul m r0) = (term648 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1019225 A add n p r1 mul m r0)). Qed.
Lemma lem1019227 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019228 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term683 A add n r1 mul m r0) = (term649 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019227 A) (@lem1019226 A add n r1 mul m r0)). Qed.
Lemma lem1019229 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term504 A add n m) = (term504 A add n m).
Proof. exact (eq_refl (term504 A add n m)). Qed.
Lemma lem1019230 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term679 A add n r1 mul m r0) = (term675 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019229 A add n m) (@lem1019228 A add n r1 mul m r0)). Qed.
Lemma lem1019231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1019232 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term684 A add n r1 mul m r0) = (term685 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019231) (@lem1019230 A add n r1 mul m r0)). Qed.
Lemma lem1019233 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term681 A add n r1 mul m r0 p) = (term646 A add n p r1 mul m r0).
Proof. exact (eq_refl (term681 A add n r1 mul m r0 p)). Qed.
Lemma lem1019234 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term504 A add n m) = (term504 A add n m).
Proof. exact (eq_refl (term504 A add n m)). Qed.
Lemma lem1019235 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term686 A add n r1 mul m r0 p) = (term687 A add n p r1 mul m r0).
Proof. exact (MK_COMB (@lem1019234 A add n m) (@lem1019233 A add n p r1 mul m r0)). Qed.
Lemma lem1019236 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term688 A add n r1 mul m r0) = (term689 A add n r1 mul m r0).
Proof. exact (fun_ext (fun p : A => @lem1019235 A add n p r1 mul m r0)). Qed.
Lemma lem1019237 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019238 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term680 A add n r1 mul m r0) = (term690 A add n r1 mul m r0).
Proof. exact (MK_COMB (@lem1019237 A) (@lem1019236 A add n r1 mul m r0)). Qed.
Lemma lem1019239 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : ((term679 A add n r1 mul m r0) = (term680 A add n r1 mul m r0)) = ((term675 A add n r1 mul m r0) = (term690 A add n r1 mul m r0)).
Proof. exact (MK_COMB (@lem1019232 A add n r1 mul m r0) (@lem1019238 A add n r1 mul m r0)). Qed.
Lemma lem1019240 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term675 A add n r1 mul m r0) = (term690 A add n r1 mul m r0).
Proof. exact (EQ_MP (@lem1019239 A add n r1 mul m r0) (@lem1019224 A add n r1 mul m r0)). Qed.
Lemma lem1019241 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term677 A add r1 mul m r0) = (term691 A add r1 mul m r0).
Proof. exact (fun_ext (fun n : A => @lem1019240 A add n r1 mul m r0)). Qed.
Lemma lem1019242 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019243 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term678 A add r1 mul m r0) = (term692 A add r1 mul m r0).
Proof. exact (MK_COMB (@lem1019242 A) (@lem1019241 A add r1 mul m r0)). Qed.
Lemma lem1019244 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term663 A add r1 mul m r0) = (term692 A add r1 mul m r0).
Proof. exact (TRANS (@lem1019220 A add r1 mul m r0) (@lem1019243 A add r1 mul m r0)). Qed.
Lemma lem1019245 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term665 A add r1 mul r0) = (term693 A add r1 mul r0).
Proof. exact (fun_ext (fun m : A => @lem1019244 A add r1 mul m r0)). Qed.
Lemma lem1019246 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1019247 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term666 A add r1 mul r0) = (term694 A add r1 mul r0).
Proof. exact (MK_COMB (@lem1019246 A) (@lem1019245 A add r1 mul r0)). Qed.
Lemma lem1019248 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term654 A add r1 mul r0) = (term694 A add r1 mul r0).
Proof. exact (TRANS (@lem1019193 A add r1 mul r0) (@lem1019247 A add r1 mul r0)). Qed.
Lemma lem1019250 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term276 A add r1 mul r0) = (term694 A add r1 mul r0).
Proof. exact (TRANS (@lem1019166 A add r1 mul r0) (@lem1019248 A add r1 mul r0)). Qed.
Lemma lem1019251 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term26 A add r1 mul r0) = (term694 A add r1 mul r0).
Proof. exact (TRANS (@lem1018403 A add r1 mul r0) (@lem1019250 A add r1 mul r0)). Qed.
Lemma lem1019252 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term26 A add r1 mul r0) : term694 A add r1 mul r0.
Proof. exact (EQ_MP (@lem1019251 A add r1 mul r0) (@lem1017935 A add r1 mul r0 h1)). Qed.
Lemma lem1019253 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term692 A add r1 mul m r0) : term692 A add r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019254 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term690 A add n r1 mul m r0) : term690 A add n r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019276 {A : Type'} (add : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x add y z) = (term104 A add x y z)) = ((term95 A x add y z) = (term104 A add x y z)).
Proof. exact (eq_refl ((term95 A x add y z) = (term104 A add x y z))). Qed.
Lemma lem1019277 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term137 A add x y) = (term137 A add x y).
Proof. exact (fun_ext (fun z : A => @lem1019276 A add x y z)). Qed.
Lemma lem1019278 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019279 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term138 A add x y) = (term138 A add x y).
Proof. exact (MK_COMB (@lem1019278 A) (@lem1019277 A add x y)). Qed.
Lemma lem1019280 {A : Type'} (add : type1400 A) (x : A) : (term139 A add x) = (term139 A add x).
Proof. exact (fun_ext (fun y : A => @lem1019279 A add x y)). Qed.
Lemma lem1019281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019282 {A : Type'} (add : type1400 A) (x : A) : (term140 A add x) = (term140 A add x).
Proof. exact (MK_COMB (@lem1019281 A) (@lem1019280 A add x)). Qed.
Lemma lem1019283 {A : Type'} (add : type1400 A) : (term141 A add) = (term141 A add).
Proof. exact (fun_ext (fun x : A => @lem1019282 A add x)). Qed.
Lemma lem1019284 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019285 {A : Type'} (add : type1400 A) : (term9 A add) = (term9 A add).
Proof. exact (MK_COMB (@lem1019284 A) (@lem1019283 A add)). Qed.
Lemma lem1019286 {A : Type'} (add : type1400 A) (h1 : term9 A add) : term9 A add.
Proof. exact (EQ_MP (@lem1019285 A add) (@lem1017962 A add h1)). Qed.
Lemma lem1019299 {A : Type'} (add : type1400 A) (y : A) (x : A) : ((add x y) = (add y x)) = ((add x y) = (add y x)).
Proof. exact (eq_refl ((add x y) = (add y x))). Qed.
Lemma lem1019300 {A : Type'} (add : type1400 A) (x : A) : (term113 A add x) = (term113 A add x).
Proof. exact (fun_ext (fun y : A => @lem1019299 A add y x)). Qed.
Lemma lem1019301 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019302 {A : Type'} (add : type1400 A) (x : A) : (term114 A add x) = (term114 A add x).
Proof. exact (MK_COMB (@lem1019301 A) (@lem1019300 A add x)). Qed.
Lemma lem1019303 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun x : A => @lem1019302 A add x)). Qed.
Lemma lem1019304 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019305 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1019304 A) (@lem1019303 A add)). Qed.
Lemma lem1019306 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (EQ_MP (@lem1019305 A add) (@lem1017982 A add h1)). Qed.
Lemma lem1019315 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : ((add r0 x) = x) = ((add r0 x) = x).
Proof. exact (eq_refl ((add r0 x) = x)). Qed.
Lemma lem1019316 {A : Type'} (add : type1400 A) (r0 : A) : (term136 A add r0) = (term136 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1019315 A add r0 x)). Qed.
Lemma lem1019317 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019318 {A : Type'} (add : type1400 A) (r0 : A) : (term13 A add r0) = (term13 A add r0).
Proof. exact (MK_COMB (@lem1019317 A) (@lem1019316 A add r0)). Qed.
Lemma lem1019319 {A : Type'} (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term13 A add r0.
Proof. exact (EQ_MP (@lem1019318 A add r0) (@lem1017995 A add r0 h1)). Qed.
Lemma lem1019340 {A : Type'} (mul : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x mul y z) = (term104 A mul x y z)) = ((term95 A x mul y z) = (term104 A mul x y z)).
Proof. exact (eq_refl ((term95 A x mul y z) = (term104 A mul x y z))). Qed.
Lemma lem1019341 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term137 A mul x y) = (term137 A mul x y).
Proof. exact (fun_ext (fun z : A => @lem1019340 A mul x y z)). Qed.
Lemma lem1019342 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019343 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term138 A mul x y) = (term138 A mul x y).
Proof. exact (MK_COMB (@lem1019342 A) (@lem1019341 A mul x y)). Qed.
Lemma lem1019344 {A : Type'} (mul : type1400 A) (x : A) : (term139 A mul x) = (term139 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1019343 A mul x y)). Qed.
Lemma lem1019345 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019346 {A : Type'} (mul : type1400 A) (x : A) : (term140 A mul x) = (term140 A mul x).
Proof. exact (MK_COMB (@lem1019345 A) (@lem1019344 A mul x)). Qed.
Lemma lem1019347 {A : Type'} (mul : type1400 A) : (term141 A mul) = (term141 A mul).
Proof. exact (fun_ext (fun x : A => @lem1019346 A mul x)). Qed.
Lemma lem1019348 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019349 {A : Type'} (mul : type1400 A) : (term9 A mul) = (term9 A mul).
Proof. exact (MK_COMB (@lem1019348 A) (@lem1019347 A mul)). Qed.
Lemma lem1019350 {A : Type'} (mul : type1400 A) (h1 : term9 A mul) : term9 A mul.
Proof. exact (EQ_MP (@lem1019349 A mul) (@lem1018022 A mul h1)). Qed.
Lemma lem1019363 {A : Type'} (mul : type1400 A) (y : A) (x : A) : ((mul x y) = (mul y x)) = ((mul x y) = (mul y x)).
Proof. exact (eq_refl ((mul x y) = (mul y x))). Qed.
Lemma lem1019364 {A : Type'} (mul : type1400 A) (x : A) : (term113 A mul x) = (term113 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1019363 A mul y x)). Qed.
Lemma lem1019365 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019366 {A : Type'} (mul : type1400 A) (x : A) : (term114 A mul x) = (term114 A mul x).
Proof. exact (MK_COMB (@lem1019365 A) (@lem1019364 A mul x)). Qed.
Lemma lem1019367 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun x : A => @lem1019366 A mul x)). Qed.
Lemma lem1019368 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019369 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1019368 A) (@lem1019367 A mul)). Qed.
Lemma lem1019370 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (EQ_MP (@lem1019369 A mul) (@lem1018042 A mul h1)). Qed.
Lemma lem1019379 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : ((mul r1 x) = x) = ((mul r1 x) = x).
Proof. exact (eq_refl ((mul r1 x) = x)). Qed.
Lemma lem1019380 {A : Type'} (mul : type1400 A) (r1 : A) : (term136 A mul r1) = (term136 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1019379 A mul r1 x)). Qed.
Lemma lem1019381 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019382 {A : Type'} (mul : type1400 A) (r1 : A) : (term13 A mul r1) = (term13 A mul r1).
Proof. exact (MK_COMB (@lem1019381 A) (@lem1019380 A mul r1)). Qed.
Lemma lem1019383 {A : Type'} (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term13 A mul r1.
Proof. exact (EQ_MP (@lem1019382 A mul r1) (@lem1018055 A mul r1 h1)). Qed.
Lemma lem1019392 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : ((mul r0 x) = r0) = ((mul r0 x) = r0).
Proof. exact (eq_refl ((mul r0 x) = r0)). Qed.
Lemma lem1019393 {A : Type'} (mul : type1400 A) (r0 : A) : (term135 A mul r0) = (term135 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1019392 A mul x r0)). Qed.
Lemma lem1019394 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019395 {A : Type'} (mul : type1400 A) (r0 : A) : (term18 A mul r0) = (term18 A mul r0).
Proof. exact (MK_COMB (@lem1019394 A) (@lem1019393 A mul r0)). Qed.
Lemma lem1019396 {A : Type'} (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term18 A mul r0.
Proof. exact (EQ_MP (@lem1019395 A mul r0) (@lem1018068 A mul r0 h1)). Qed.
Lemma lem1019421 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : ((term128 A mul x add y z) = (term129 A add y mul x z)) = ((term128 A mul x add y z) = (term129 A add y mul x z)).
Proof. exact (eq_refl ((term128 A mul x add y z) = (term129 A add y mul x z))). Qed.
Lemma lem1019422 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term130 A add y mul x) = (term130 A add y mul x).
Proof. exact (fun_ext (fun z : A => @lem1019421 A add y mul x z)). Qed.
Lemma lem1019423 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019424 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term131 A add y mul x) = (term131 A add y mul x).
Proof. exact (MK_COMB (@lem1019423 A) (@lem1019422 A add y mul x)). Qed.
Lemma lem1019425 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term132 A add mul x) = (term132 A add mul x).
Proof. exact (fun_ext (fun y : A => @lem1019424 A add y mul x)). Qed.
Lemma lem1019426 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019427 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term133 A add mul x) = (term133 A add mul x).
Proof. exact (MK_COMB (@lem1019426 A) (@lem1019425 A add mul x)). Qed.
Lemma lem1019428 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term134 A add mul) = (term134 A add mul).
Proof. exact (fun_ext (fun x : A => @lem1019427 A add mul x)). Qed.
Lemma lem1019429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019430 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term20 A add mul) = (term20 A add mul).
Proof. exact (MK_COMB (@lem1019429 A) (@lem1019428 A add mul)). Qed.
Lemma lem1019431 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term20 A add mul.
Proof. exact (EQ_MP (@lem1019430 A add mul) (@lem1018095 A add mul h1)). Qed.
Lemma lem1019682 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term687 A add n p r1 mul m r0) : term687 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019684 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term646 A add n p r1 mul m r0) : term646 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019686 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term605 A add n p r1 mul m r0) : term605 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019688 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term564 A add n p r1 mul m r0) : term564 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019690 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term520 A add n p r1 mul m r0) : term520 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019692 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term465 A add n p r1 mul m r0) : term465 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019694 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term406 A add n p r1 mul m r0) : term406 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019696 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term347 A add n p r1 mul m r0) : term347 A add n p r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1019713 {A : Type'} (add : type1400 A) (y : A) (x : A) : ((add x y) = (add y x)) = ((add x y) = (add y x)).
Proof. exact (eq_refl ((add x y) = (add y x))). Qed.
Lemma lem1019714 {A : Type'} (add : type1400 A) (x : A) : (term113 A add x) = (term113 A add x).
Proof. exact (fun_ext (fun y : A => @lem1019713 A add y x)). Qed.
Lemma lem1019715 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019716 {A : Type'} (add : type1400 A) (x : A) : (term114 A add x) = (term114 A add x).
Proof. exact (MK_COMB (@lem1019715 A) (@lem1019714 A add x)). Qed.
Lemma lem1019717 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun x : A => @lem1019716 A add x)). Qed.
Lemma lem1019718 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019720 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1019718 A) (@lem1019717 A add)). Qed.
Lemma lem1019721 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (EQ_MP (@lem1019720 A add) (@lem1019306 A add h1)). Qed.
Lemma lem1019799 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term148 A add n m) : term148 A add n m.
Proof. exact (h1). Qed.
Lemma lem1019801 {A : Type'} (add : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x add y z) = (term104 A add x y z)) = ((term95 A x add y z) = (term104 A add x y z)).
Proof. exact (eq_refl ((term95 A x add y z) = (term104 A add x y z))). Qed.
Lemma lem1019802 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term137 A add x y) = (term137 A add x y).
Proof. exact (fun_ext (fun z : A => @lem1019801 A add x y z)). Qed.
Lemma lem1019803 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019804 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term138 A add x y) = (term138 A add x y).
Proof. exact (MK_COMB (@lem1019803 A) (@lem1019802 A add x y)). Qed.
Lemma lem1019805 {A : Type'} (add : type1400 A) (x : A) : (term139 A add x) = (term139 A add x).
Proof. exact (fun_ext (fun y : A => @lem1019804 A add x y)). Qed.
Lemma lem1019806 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019807 {A : Type'} (add : type1400 A) (x : A) : (term140 A add x) = (term140 A add x).
Proof. exact (MK_COMB (@lem1019806 A) (@lem1019805 A add x)). Qed.
Lemma lem1019808 {A : Type'} (add : type1400 A) : (term141 A add) = (term141 A add).
Proof. exact (fun_ext (fun x : A => @lem1019807 A add x)). Qed.
Lemma lem1019809 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019811 {A : Type'} (add : type1400 A) : (term9 A add) = (term9 A add).
Proof. exact (MK_COMB (@lem1019809 A) (@lem1019808 A add)). Qed.
Lemma lem1019812 {A : Type'} (add : type1400 A) (h1 : term9 A add) : term9 A add.
Proof. exact (EQ_MP (@lem1019811 A add) (@lem1019286 A add h1)). Qed.
Lemma lem1019900 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term163 A m add n p) : term163 A m add n p.
Proof. exact (h1). Qed.
Lemma lem1019902 {A : Type'} (add : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x add y z) = (term104 A add x y z)) = ((term95 A x add y z) = (term104 A add x y z)).
Proof. exact (eq_refl ((term95 A x add y z) = (term104 A add x y z))). Qed.
Lemma lem1019903 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term137 A add x y) = (term137 A add x y).
Proof. exact (fun_ext (fun z : A => @lem1019902 A add x y z)). Qed.
Lemma lem1019904 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019905 {A : Type'} (add : type1400 A) (x : A) (y : A) : (term138 A add x y) = (term138 A add x y).
Proof. exact (MK_COMB (@lem1019904 A) (@lem1019903 A add x y)). Qed.
Lemma lem1019906 {A : Type'} (add : type1400 A) (x : A) : (term139 A add x) = (term139 A add x).
Proof. exact (fun_ext (fun y : A => @lem1019905 A add x y)). Qed.
Lemma lem1019907 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019908 {A : Type'} (add : type1400 A) (x : A) : (term140 A add x) = (term140 A add x).
Proof. exact (MK_COMB (@lem1019907 A) (@lem1019906 A add x)). Qed.
Lemma lem1019909 {A : Type'} (add : type1400 A) : (term141 A add) = (term141 A add).
Proof. exact (fun_ext (fun x : A => @lem1019908 A add x)). Qed.
Lemma lem1019910 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019912 {A : Type'} (add : type1400 A) : (term9 A add) = (term9 A add).
Proof. exact (MK_COMB (@lem1019910 A) (@lem1019909 A add)). Qed.
Lemma lem1019913 {A : Type'} (add : type1400 A) (h1 : term9 A add) : term9 A add.
Proof. exact (EQ_MP (@lem1019912 A add) (@lem1019286 A add h1)). Qed.
Lemma lem1019915 {A : Type'} (add : type1400 A) (y : A) (x : A) : ((add x y) = (add y x)) = ((add x y) = (add y x)).
Proof. exact (eq_refl ((add x y) = (add y x))). Qed.
Lemma lem1019916 {A : Type'} (add : type1400 A) (x : A) : (term113 A add x) = (term113 A add x).
Proof. exact (fun_ext (fun y : A => @lem1019915 A add y x)). Qed.
Lemma lem1019917 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019918 {A : Type'} (add : type1400 A) (x : A) : (term114 A add x) = (term114 A add x).
Proof. exact (MK_COMB (@lem1019917 A) (@lem1019916 A add x)). Qed.
Lemma lem1019919 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun x : A => @lem1019918 A add x)). Qed.
Lemma lem1019920 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1019922 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1019920 A) (@lem1019919 A add)). Qed.
Lemma lem1019923 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (EQ_MP (@lem1019922 A add) (@lem1019306 A add h1)). Qed.
Lemma lem1020001 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term185 A n add m p) : term185 A n add m p.
Proof. exact (h1). Qed.
Lemma lem1020016 {A : Type'} (add : type1400 A) (y : A) (x : A) : ((add x y) = (add y x)) = ((add x y) = (add y x)).
Proof. exact (eq_refl ((add x y) = (add y x))). Qed.
Lemma lem1020017 {A : Type'} (add : type1400 A) (x : A) : (term113 A add x) = (term113 A add x).
Proof. exact (fun_ext (fun y : A => @lem1020016 A add y x)). Qed.
Lemma lem1020018 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020019 {A : Type'} (add : type1400 A) (x : A) : (term114 A add x) = (term114 A add x).
Proof. exact (MK_COMB (@lem1020018 A) (@lem1020017 A add x)). Qed.
Lemma lem1020020 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun x : A => @lem1020019 A add x)). Qed.
Lemma lem1020021 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020023 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1020021 A) (@lem1020020 A add)). Qed.
Lemma lem1020024 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (EQ_MP (@lem1020023 A add) (@lem1019306 A add h1)). Qed.
Lemma lem1020026 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : ((add r0 x) = x) = ((add r0 x) = x).
Proof. exact (eq_refl ((add r0 x) = x)). Qed.
Lemma lem1020027 {A : Type'} (add : type1400 A) (r0 : A) : (term136 A add r0) = (term136 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1020026 A add r0 x)). Qed.
Lemma lem1020028 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020030 {A : Type'} (add : type1400 A) (r0 : A) : (term13 A add r0) = (term13 A add r0).
Proof. exact (MK_COMB (@lem1020028 A) (@lem1020027 A add r0)). Qed.
Lemma lem1020031 {A : Type'} (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term13 A add r0.
Proof. exact (EQ_MP (@lem1020030 A add r0) (@lem1019319 A add r0 h1)). Qed.
Lemma lem1020102 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term207 A add r0 m) : term207 A add r0 m.
Proof. exact (h1). Qed.
Lemma lem1020147 {A : Type'} (mul : type1400 A) (y : A) (x : A) : ((mul x y) = (mul y x)) = ((mul x y) = (mul y x)).
Proof. exact (eq_refl ((mul x y) = (mul y x))). Qed.
Lemma lem1020148 {A : Type'} (mul : type1400 A) (x : A) : (term113 A mul x) = (term113 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1020147 A mul y x)). Qed.
Lemma lem1020149 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020150 {A : Type'} (mul : type1400 A) (x : A) : (term114 A mul x) = (term114 A mul x).
Proof. exact (MK_COMB (@lem1020149 A) (@lem1020148 A mul x)). Qed.
Lemma lem1020151 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun x : A => @lem1020150 A mul x)). Qed.
Lemma lem1020152 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020154 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1020152 A) (@lem1020151 A mul)). Qed.
Lemma lem1020155 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (EQ_MP (@lem1020154 A mul) (@lem1019370 A mul h1)). Qed.
Lemma lem1020203 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term148 A mul n m) : term148 A mul n m.
Proof. exact (h1). Qed.
Lemma lem1020235 {A : Type'} (mul : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x mul y z) = (term104 A mul x y z)) = ((term95 A x mul y z) = (term104 A mul x y z)).
Proof. exact (eq_refl ((term95 A x mul y z) = (term104 A mul x y z))). Qed.
Lemma lem1020236 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term137 A mul x y) = (term137 A mul x y).
Proof. exact (fun_ext (fun z : A => @lem1020235 A mul x y z)). Qed.
Lemma lem1020237 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020238 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term138 A mul x y) = (term138 A mul x y).
Proof. exact (MK_COMB (@lem1020237 A) (@lem1020236 A mul x y)). Qed.
Lemma lem1020239 {A : Type'} (mul : type1400 A) (x : A) : (term139 A mul x) = (term139 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1020238 A mul x y)). Qed.
Lemma lem1020240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020241 {A : Type'} (mul : type1400 A) (x : A) : (term140 A mul x) = (term140 A mul x).
Proof. exact (MK_COMB (@lem1020240 A) (@lem1020239 A mul x)). Qed.
Lemma lem1020242 {A : Type'} (mul : type1400 A) : (term141 A mul) = (term141 A mul).
Proof. exact (fun_ext (fun x : A => @lem1020241 A mul x)). Qed.
Lemma lem1020243 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020245 {A : Type'} (mul : type1400 A) : (term9 A mul) = (term9 A mul).
Proof. exact (MK_COMB (@lem1020243 A) (@lem1020242 A mul)). Qed.
Lemma lem1020246 {A : Type'} (mul : type1400 A) (h1 : term9 A mul) : term9 A mul.
Proof. exact (EQ_MP (@lem1020245 A mul) (@lem1019350 A mul h1)). Qed.
Lemma lem1020304 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term163 A m mul n p) : term163 A m mul n p.
Proof. exact (h1). Qed.
Lemma lem1020336 {A : Type'} (mul : type1400 A) (x : A) (y : A) (z : A) : ((term95 A x mul y z) = (term104 A mul x y z)) = ((term95 A x mul y z) = (term104 A mul x y z)).
Proof. exact (eq_refl ((term95 A x mul y z) = (term104 A mul x y z))). Qed.
Lemma lem1020337 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term137 A mul x y) = (term137 A mul x y).
Proof. exact (fun_ext (fun z : A => @lem1020336 A mul x y z)). Qed.
Lemma lem1020338 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020339 {A : Type'} (mul : type1400 A) (x : A) (y : A) : (term138 A mul x y) = (term138 A mul x y).
Proof. exact (MK_COMB (@lem1020338 A) (@lem1020337 A mul x y)). Qed.
Lemma lem1020340 {A : Type'} (mul : type1400 A) (x : A) : (term139 A mul x) = (term139 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1020339 A mul x y)). Qed.
Lemma lem1020341 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020342 {A : Type'} (mul : type1400 A) (x : A) : (term140 A mul x) = (term140 A mul x).
Proof. exact (MK_COMB (@lem1020341 A) (@lem1020340 A mul x)). Qed.
Lemma lem1020343 {A : Type'} (mul : type1400 A) : (term141 A mul) = (term141 A mul).
Proof. exact (fun_ext (fun x : A => @lem1020342 A mul x)). Qed.
Lemma lem1020344 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020346 {A : Type'} (mul : type1400 A) : (term9 A mul) = (term9 A mul).
Proof. exact (MK_COMB (@lem1020344 A) (@lem1020343 A mul)). Qed.
Lemma lem1020347 {A : Type'} (mul : type1400 A) (h1 : term9 A mul) : term9 A mul.
Proof. exact (EQ_MP (@lem1020346 A mul) (@lem1019350 A mul h1)). Qed.
Lemma lem1020349 {A : Type'} (mul : type1400 A) (y : A) (x : A) : ((mul x y) = (mul y x)) = ((mul x y) = (mul y x)).
Proof. exact (eq_refl ((mul x y) = (mul y x))). Qed.
Lemma lem1020350 {A : Type'} (mul : type1400 A) (x : A) : (term113 A mul x) = (term113 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1020349 A mul y x)). Qed.
Lemma lem1020351 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020352 {A : Type'} (mul : type1400 A) (x : A) : (term114 A mul x) = (term114 A mul x).
Proof. exact (MK_COMB (@lem1020351 A) (@lem1020350 A mul x)). Qed.
Lemma lem1020353 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun x : A => @lem1020352 A mul x)). Qed.
Lemma lem1020354 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020356 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1020354 A) (@lem1020353 A mul)). Qed.
Lemma lem1020357 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (EQ_MP (@lem1020356 A mul) (@lem1019370 A mul h1)). Qed.
Lemma lem1020405 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term185 A n mul m p) : term185 A n mul m p.
Proof. exact (h1). Qed.
Lemma lem1020450 {A : Type'} (mul : type1400 A) (y : A) (x : A) : ((mul x y) = (mul y x)) = ((mul x y) = (mul y x)).
Proof. exact (eq_refl ((mul x y) = (mul y x))). Qed.
Lemma lem1020451 {A : Type'} (mul : type1400 A) (x : A) : (term113 A mul x) = (term113 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1020450 A mul y x)). Qed.
Lemma lem1020452 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020453 {A : Type'} (mul : type1400 A) (x : A) : (term114 A mul x) = (term114 A mul x).
Proof. exact (MK_COMB (@lem1020452 A) (@lem1020451 A mul x)). Qed.
Lemma lem1020454 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun x : A => @lem1020453 A mul x)). Qed.
Lemma lem1020455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020457 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1020455 A) (@lem1020454 A mul)). Qed.
Lemma lem1020458 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (EQ_MP (@lem1020457 A mul) (@lem1019370 A mul h1)). Qed.
Lemma lem1020474 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : ((term128 A mul x add y z) = (term129 A add y mul x z)) = ((term128 A mul x add y z) = (term129 A add y mul x z)).
Proof. exact (eq_refl ((term128 A mul x add y z) = (term129 A add y mul x z))). Qed.
Lemma lem1020475 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term130 A add y mul x) = (term130 A add y mul x).
Proof. exact (fun_ext (fun z : A => @lem1020474 A add y mul x z)). Qed.
Lemma lem1020476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020477 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term131 A add y mul x) = (term131 A add y mul x).
Proof. exact (MK_COMB (@lem1020476 A) (@lem1020475 A add y mul x)). Qed.
Lemma lem1020478 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term132 A add mul x) = (term132 A add mul x).
Proof. exact (fun_ext (fun y : A => @lem1020477 A add y mul x)). Qed.
Lemma lem1020479 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020480 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term133 A add mul x) = (term133 A add mul x).
Proof. exact (MK_COMB (@lem1020479 A) (@lem1020478 A add mul x)). Qed.
Lemma lem1020481 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term134 A add mul) = (term134 A add mul).
Proof. exact (fun_ext (fun x : A => @lem1020480 A add mul x)). Qed.
Lemma lem1020482 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020484 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term20 A add mul) = (term20 A add mul).
Proof. exact (MK_COMB (@lem1020482 A) (@lem1020481 A add mul)). Qed.
Lemma lem1020485 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term20 A add mul.
Proof. exact (EQ_MP (@lem1020484 A add mul) (@lem1019431 A add mul h1)). Qed.
Lemma lem1020506 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term215 A add m mul n p) : term215 A add m mul n p.
Proof. exact (h1). Qed.
Lemma lem1020551 {A : Type'} (mul : type1400 A) (y : A) (x : A) : ((mul x y) = (mul y x)) = ((mul x y) = (mul y x)).
Proof. exact (eq_refl ((mul x y) = (mul y x))). Qed.
Lemma lem1020552 {A : Type'} (mul : type1400 A) (x : A) : (term113 A mul x) = (term113 A mul x).
Proof. exact (fun_ext (fun y : A => @lem1020551 A mul y x)). Qed.
Lemma lem1020553 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020554 {A : Type'} (mul : type1400 A) (x : A) : (term114 A mul x) = (term114 A mul x).
Proof. exact (MK_COMB (@lem1020553 A) (@lem1020552 A mul x)). Qed.
Lemma lem1020555 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun x : A => @lem1020554 A mul x)). Qed.
Lemma lem1020556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020558 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1020556 A) (@lem1020555 A mul)). Qed.
Lemma lem1020559 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (EQ_MP (@lem1020558 A mul) (@lem1019370 A mul h1)). Qed.
Lemma lem1020561 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : ((mul r1 x) = x) = ((mul r1 x) = x).
Proof. exact (eq_refl ((mul r1 x) = x)). Qed.
Lemma lem1020562 {A : Type'} (mul : type1400 A) (r1 : A) : (term136 A mul r1) = (term136 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1020561 A mul r1 x)). Qed.
Lemma lem1020563 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020565 {A : Type'} (mul : type1400 A) (r1 : A) : (term13 A mul r1) = (term13 A mul r1).
Proof. exact (MK_COMB (@lem1020563 A) (@lem1020562 A mul r1)). Qed.
Lemma lem1020566 {A : Type'} (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term13 A mul r1.
Proof. exact (EQ_MP (@lem1020565 A mul r1) (@lem1019383 A mul r1 h1)). Qed.
Lemma lem1020568 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : ((mul r0 x) = r0) = ((mul r0 x) = r0).
Proof. exact (eq_refl ((mul r0 x) = r0)). Qed.
Lemma lem1020569 {A : Type'} (mul : type1400 A) (r0 : A) : (term135 A mul r0) = (term135 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1020568 A mul x r0)). Qed.
Lemma lem1020570 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1020572 {A : Type'} (mul : type1400 A) (r0 : A) : (term18 A mul r0) = (term18 A mul r0).
Proof. exact (MK_COMB (@lem1020570 A) (@lem1020569 A mul r0)). Qed.
Lemma lem1020573 {A : Type'} (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term18 A mul r0.
Proof. exact (EQ_MP (@lem1020572 A mul r0) (@lem1019396 A mul r0 h1)). Qed.
Lemma lem1020613 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term293 A r1 mul m r0) : term293 A r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1020623 {A : Type'} (_16580 : A) (add : type1400 A) (h1 : term11 A add) : term154 A add _16580.
Proof. exact (@lem1019721 A add h1 _16580). Qed.
Lemma lem1020624 {A : Type'} (add : type1400 A) (_16580 : A) : (term154 A add _16580) = (term114 A add _16580).
Proof. exact (eq_refl (term154 A add _16580)). Qed.
Lemma lem1020625 {A : Type'} (_16580 : A) (add : type1400 A) (h1 : term11 A add) : term114 A add _16580.
Proof. exact (EQ_MP (@lem1020624 A add _16580) (@lem1020623 A _16580 add h1)). Qed.
Lemma lem1020626 {A : Type'} (_16580 : A) (_16581 : A) (add : type1400 A) (h1 : term11 A add) : term146 A add _16580 _16581.
Proof. exact (@lem1020625 A _16580 add h1 _16581). Qed.
Lemma lem1020627 {A : Type'} (add : type1400 A) (_16581 : A) (_16580 : A) : (term146 A add _16580 _16581) = ((add _16580 _16581) = (add _16581 _16580)).
Proof. exact (eq_refl (term146 A add _16580 _16581)). Qed.
Lemma lem1020671 {A : Type'} (_16596 : A) (add : type1400 A) (h1 : term9 A add) : term695 A add _16596.
Proof. exact (@lem1019812 A add h1 _16596). Qed.
Lemma lem1020672 {A : Type'} (add : type1400 A) (_16596 : A) : (term695 A add _16596) = (term140 A add _16596).
Proof. exact (eq_refl (term695 A add _16596)). Qed.
Lemma lem1020673 {A : Type'} (_16596 : A) (add : type1400 A) (h1 : term9 A add) : term140 A add _16596.
Proof. exact (EQ_MP (@lem1020672 A add _16596) (@lem1020671 A _16596 add h1)). Qed.
Lemma lem1020674 {A : Type'} (_16596 : A) (_16597 : A) (add : type1400 A) (h1 : term9 A add) : term696 A add _16596 _16597.
Proof. exact (@lem1020673 A _16596 add h1 _16597). Qed.
Lemma lem1020675 {A : Type'} (add : type1400 A) (_16596 : A) (_16597 : A) : (term696 A add _16596 _16597) = (term138 A add _16596 _16597).
Proof. exact (eq_refl (term696 A add _16596 _16597)). Qed.
Lemma lem1020676 {A : Type'} (_16596 : A) (_16597 : A) (add : type1400 A) (h1 : term9 A add) : term138 A add _16596 _16597.
Proof. exact (EQ_MP (@lem1020675 A add _16596 _16597) (@lem1020674 A _16596 _16597 add h1)). Qed.
Lemma lem1020677 {A : Type'} (_16596 : A) (_16597 : A) (_16598 : A) (add : type1400 A) (h1 : term9 A add) : term697 A add _16596 _16597 _16598.
Proof. exact (@lem1020676 A _16596 _16597 add h1 _16598). Qed.
Lemma lem1020678 {A : Type'} (add : type1400 A) (_16596 : A) (_16597 : A) (_16598 : A) : (term697 A add _16596 _16597 _16598) = ((term95 A _16596 add _16597 _16598) = (term104 A add _16596 _16597 _16598)).
Proof. exact (eq_refl (term697 A add _16596 _16597 _16598)). Qed.
Lemma lem1020728 {A : Type'} (_16615 : A) (add : type1400 A) (h1 : term9 A add) : term695 A add _16615.
Proof. exact (@lem1019913 A add h1 _16615). Qed.
Lemma lem1020729 {A : Type'} (add : type1400 A) (_16615 : A) : (term695 A add _16615) = (term140 A add _16615).
Proof. exact (eq_refl (term695 A add _16615)). Qed.
Lemma lem1020730 {A : Type'} (_16615 : A) (add : type1400 A) (h1 : term9 A add) : term140 A add _16615.
Proof. exact (EQ_MP (@lem1020729 A add _16615) (@lem1020728 A _16615 add h1)). Qed.
Lemma lem1020731 {A : Type'} (_16615 : A) (_16616 : A) (add : type1400 A) (h1 : term9 A add) : term696 A add _16615 _16616.
Proof. exact (@lem1020730 A _16615 add h1 _16616). Qed.
Lemma lem1020732 {A : Type'} (add : type1400 A) (_16615 : A) (_16616 : A) : (term696 A add _16615 _16616) = (term138 A add _16615 _16616).
Proof. exact (eq_refl (term696 A add _16615 _16616)). Qed.
Lemma lem1020733 {A : Type'} (_16615 : A) (_16616 : A) (add : type1400 A) (h1 : term9 A add) : term138 A add _16615 _16616.
Proof. exact (EQ_MP (@lem1020732 A add _16615 _16616) (@lem1020731 A _16615 _16616 add h1)). Qed.
Lemma lem1020734 {A : Type'} (_16615 : A) (_16616 : A) (_16617 : A) (add : type1400 A) (h1 : term9 A add) : term697 A add _16615 _16616 _16617.
Proof. exact (@lem1020733 A _16615 _16616 add h1 _16617). Qed.
Lemma lem1020735 {A : Type'} (add : type1400 A) (_16615 : A) (_16616 : A) (_16617 : A) : (term697 A add _16615 _16616 _16617) = ((term95 A _16615 add _16616 _16617) = (term104 A add _16615 _16616 _16617)).
Proof. exact (eq_refl (term697 A add _16615 _16616 _16617)). Qed.
Lemma lem1020737 {A : Type'} (_16618 : A) (add : type1400 A) (h1 : term11 A add) : term154 A add _16618.
Proof. exact (@lem1019923 A add h1 _16618). Qed.
Lemma lem1020738 {A : Type'} (add : type1400 A) (_16618 : A) : (term154 A add _16618) = (term114 A add _16618).
Proof. exact (eq_refl (term154 A add _16618)). Qed.
Lemma lem1020739 {A : Type'} (_16618 : A) (add : type1400 A) (h1 : term11 A add) : term114 A add _16618.
Proof. exact (EQ_MP (@lem1020738 A add _16618) (@lem1020737 A _16618 add h1)). Qed.
Lemma lem1020740 {A : Type'} (_16618 : A) (_16619 : A) (add : type1400 A) (h1 : term11 A add) : term146 A add _16618 _16619.
Proof. exact (@lem1020739 A _16618 add h1 _16619). Qed.
Lemma lem1020741 {A : Type'} (add : type1400 A) (_16619 : A) (_16618 : A) : (term146 A add _16618 _16619) = ((add _16618 _16619) = (add _16619 _16618)).
Proof. exact (eq_refl (term146 A add _16618 _16619)). Qed.
Lemma lem1020794 {A : Type'} (_16637 : A) (add : type1400 A) (h1 : term11 A add) : term154 A add _16637.
Proof. exact (@lem1020024 A add h1 _16637). Qed.
Lemma lem1020795 {A : Type'} (add : type1400 A) (_16637 : A) : (term154 A add _16637) = (term114 A add _16637).
Proof. exact (eq_refl (term154 A add _16637)). Qed.
Lemma lem1020796 {A : Type'} (_16637 : A) (add : type1400 A) (h1 : term11 A add) : term114 A add _16637.
Proof. exact (EQ_MP (@lem1020795 A add _16637) (@lem1020794 A _16637 add h1)). Qed.
Lemma lem1020797 {A : Type'} (_16637 : A) (_16638 : A) (add : type1400 A) (h1 : term11 A add) : term146 A add _16637 _16638.
Proof. exact (@lem1020796 A _16637 add h1 _16638). Qed.
Lemma lem1020798 {A : Type'} (add : type1400 A) (_16638 : A) (_16637 : A) : (term146 A add _16637 _16638) = ((add _16637 _16638) = (add _16638 _16637)).
Proof. exact (eq_refl (term146 A add _16637 _16638)). Qed.
Lemma lem1020800 {A : Type'} (_16639 : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term698 A add r0 _16639.
Proof. exact (@lem1020031 A add r0 h1 _16639). Qed.
Lemma lem1020801 {A : Type'} (add : type1400 A) (r0 : A) (_16639 : A) : (term698 A add r0 _16639) = ((add r0 _16639) = _16639).
Proof. exact (eq_refl (term698 A add r0 _16639)). Qed.
Lemma lem1020869 {A : Type'} (_16662 : A) (mul : type1400 A) (h1 : term11 A mul) : term154 A mul _16662.
Proof. exact (@lem1020155 A mul h1 _16662). Qed.
Lemma lem1020870 {A : Type'} (mul : type1400 A) (_16662 : A) : (term154 A mul _16662) = (term114 A mul _16662).
Proof. exact (eq_refl (term154 A mul _16662)). Qed.
Lemma lem1020871 {A : Type'} (_16662 : A) (mul : type1400 A) (h1 : term11 A mul) : term114 A mul _16662.
Proof. exact (EQ_MP (@lem1020870 A mul _16662) (@lem1020869 A _16662 mul h1)). Qed.
Lemma lem1020872 {A : Type'} (_16662 : A) (_16663 : A) (mul : type1400 A) (h1 : term11 A mul) : term146 A mul _16662 _16663.
Proof. exact (@lem1020871 A _16662 mul h1 _16663). Qed.
Lemma lem1020873 {A : Type'} (mul : type1400 A) (_16663 : A) (_16662 : A) : (term146 A mul _16662 _16663) = ((mul _16662 _16663) = (mul _16663 _16662)).
Proof. exact (eq_refl (term146 A mul _16662 _16663)). Qed.
Lemma lem1020917 {A : Type'} (_16678 : A) (mul : type1400 A) (h1 : term9 A mul) : term695 A mul _16678.
Proof. exact (@lem1020246 A mul h1 _16678). Qed.
Lemma lem1020918 {A : Type'} (mul : type1400 A) (_16678 : A) : (term695 A mul _16678) = (term140 A mul _16678).
Proof. exact (eq_refl (term695 A mul _16678)). Qed.
Lemma lem1020919 {A : Type'} (_16678 : A) (mul : type1400 A) (h1 : term9 A mul) : term140 A mul _16678.
Proof. exact (EQ_MP (@lem1020918 A mul _16678) (@lem1020917 A _16678 mul h1)). Qed.
Lemma lem1020920 {A : Type'} (_16678 : A) (_16679 : A) (mul : type1400 A) (h1 : term9 A mul) : term696 A mul _16678 _16679.
Proof. exact (@lem1020919 A _16678 mul h1 _16679). Qed.
Lemma lem1020921 {A : Type'} (mul : type1400 A) (_16678 : A) (_16679 : A) : (term696 A mul _16678 _16679) = (term138 A mul _16678 _16679).
Proof. exact (eq_refl (term696 A mul _16678 _16679)). Qed.
Lemma lem1020922 {A : Type'} (_16678 : A) (_16679 : A) (mul : type1400 A) (h1 : term9 A mul) : term138 A mul _16678 _16679.
Proof. exact (EQ_MP (@lem1020921 A mul _16678 _16679) (@lem1020920 A _16678 _16679 mul h1)). Qed.
Lemma lem1020923 {A : Type'} (_16678 : A) (_16679 : A) (_16680 : A) (mul : type1400 A) (h1 : term9 A mul) : term697 A mul _16678 _16679 _16680.
Proof. exact (@lem1020922 A _16678 _16679 mul h1 _16680). Qed.
Lemma lem1020924 {A : Type'} (mul : type1400 A) (_16678 : A) (_16679 : A) (_16680 : A) : (term697 A mul _16678 _16679 _16680) = ((term95 A _16678 mul _16679 _16680) = (term104 A mul _16678 _16679 _16680)).
Proof. exact (eq_refl (term697 A mul _16678 _16679 _16680)). Qed.
Lemma lem1020974 {A : Type'} (_16697 : A) (mul : type1400 A) (h1 : term9 A mul) : term695 A mul _16697.
Proof. exact (@lem1020347 A mul h1 _16697). Qed.
Lemma lem1020975 {A : Type'} (mul : type1400 A) (_16697 : A) : (term695 A mul _16697) = (term140 A mul _16697).
Proof. exact (eq_refl (term695 A mul _16697)). Qed.
Lemma lem1020976 {A : Type'} (_16697 : A) (mul : type1400 A) (h1 : term9 A mul) : term140 A mul _16697.
Proof. exact (EQ_MP (@lem1020975 A mul _16697) (@lem1020974 A _16697 mul h1)). Qed.
Lemma lem1020977 {A : Type'} (_16697 : A) (_16698 : A) (mul : type1400 A) (h1 : term9 A mul) : term696 A mul _16697 _16698.
Proof. exact (@lem1020976 A _16697 mul h1 _16698). Qed.
Lemma lem1020978 {A : Type'} (mul : type1400 A) (_16697 : A) (_16698 : A) : (term696 A mul _16697 _16698) = (term138 A mul _16697 _16698).
Proof. exact (eq_refl (term696 A mul _16697 _16698)). Qed.
Lemma lem1020979 {A : Type'} (_16697 : A) (_16698 : A) (mul : type1400 A) (h1 : term9 A mul) : term138 A mul _16697 _16698.
Proof. exact (EQ_MP (@lem1020978 A mul _16697 _16698) (@lem1020977 A _16697 _16698 mul h1)). Qed.
Lemma lem1020980 {A : Type'} (_16697 : A) (_16698 : A) (_16699 : A) (mul : type1400 A) (h1 : term9 A mul) : term697 A mul _16697 _16698 _16699.
Proof. exact (@lem1020979 A _16697 _16698 mul h1 _16699). Qed.
Lemma lem1020981 {A : Type'} (mul : type1400 A) (_16697 : A) (_16698 : A) (_16699 : A) : (term697 A mul _16697 _16698 _16699) = ((term95 A _16697 mul _16698 _16699) = (term104 A mul _16697 _16698 _16699)).
Proof. exact (eq_refl (term697 A mul _16697 _16698 _16699)). Qed.
Lemma lem1020983 {A : Type'} (_16700 : A) (mul : type1400 A) (h1 : term11 A mul) : term154 A mul _16700.
Proof. exact (@lem1020357 A mul h1 _16700). Qed.
Lemma lem1020984 {A : Type'} (mul : type1400 A) (_16700 : A) : (term154 A mul _16700) = (term114 A mul _16700).
Proof. exact (eq_refl (term154 A mul _16700)). Qed.
Lemma lem1020985 {A : Type'} (_16700 : A) (mul : type1400 A) (h1 : term11 A mul) : term114 A mul _16700.
Proof. exact (EQ_MP (@lem1020984 A mul _16700) (@lem1020983 A _16700 mul h1)). Qed.
Lemma lem1020986 {A : Type'} (_16700 : A) (_16701 : A) (mul : type1400 A) (h1 : term11 A mul) : term146 A mul _16700 _16701.
Proof. exact (@lem1020985 A _16700 mul h1 _16701). Qed.
Lemma lem1020987 {A : Type'} (mul : type1400 A) (_16701 : A) (_16700 : A) : (term146 A mul _16700 _16701) = ((mul _16700 _16701) = (mul _16701 _16700)).
Proof. exact (eq_refl (term146 A mul _16700 _16701)). Qed.
Lemma lem1021040 {A : Type'} (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : term154 A mul _16719.
Proof. exact (@lem1020458 A mul h1 _16719). Qed.
Lemma lem1021041 {A : Type'} (mul : type1400 A) (_16719 : A) : (term154 A mul _16719) = (term114 A mul _16719).
Proof. exact (eq_refl (term154 A mul _16719)). Qed.
Lemma lem1021042 {A : Type'} (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : term114 A mul _16719.
Proof. exact (EQ_MP (@lem1021041 A mul _16719) (@lem1021040 A _16719 mul h1)). Qed.
Lemma lem1021043 {A : Type'} (_16719 : A) (_16720 : A) (mul : type1400 A) (h1 : term11 A mul) : term146 A mul _16719 _16720.
Proof. exact (@lem1021042 A _16719 mul h1 _16720). Qed.
Lemma lem1021044 {A : Type'} (mul : type1400 A) (_16720 : A) (_16719 : A) : (term146 A mul _16719 _16720) = ((mul _16719 _16720) = (mul _16720 _16719)).
Proof. exact (eq_refl (term146 A mul _16719 _16720)). Qed.
Lemma lem1021052 {A : Type'} (_16723 : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term699 A add mul _16723.
Proof. exact (@lem1020485 A add mul h1 _16723). Qed.
Lemma lem1021053 {A : Type'} (add : type1400 A) (mul : type1400 A) (_16723 : A) : (term699 A add mul _16723) = (term133 A add mul _16723).
Proof. exact (eq_refl (term699 A add mul _16723)). Qed.
Lemma lem1021054 {A : Type'} (_16723 : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term133 A add mul _16723.
Proof. exact (EQ_MP (@lem1021053 A add mul _16723) (@lem1021052 A _16723 add mul h1)). Qed.
Lemma lem1021055 {A : Type'} (_16723 : A) (_16724 : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term700 A add mul _16723 _16724.
Proof. exact (@lem1021054 A _16723 add mul h1 _16724). Qed.
Lemma lem1021056 {A : Type'} (add : type1400 A) (_16724 : A) (mul : type1400 A) (_16723 : A) : (term700 A add mul _16723 _16724) = (term131 A add _16724 mul _16723).
Proof. exact (eq_refl (term700 A add mul _16723 _16724)). Qed.
Lemma lem1021057 {A : Type'} (_16724 : A) (_16723 : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term131 A add _16724 mul _16723.
Proof. exact (EQ_MP (@lem1021056 A add _16724 mul _16723) (@lem1021055 A _16723 _16724 add mul h1)). Qed.
Lemma lem1021058 {A : Type'} (_16724 : A) (_16723 : A) (_16725 : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term701 A add _16724 mul _16723 _16725.
Proof. exact (@lem1021057 A _16724 _16723 add mul h1 _16725). Qed.
Lemma lem1021059 {A : Type'} (add : type1400 A) (_16724 : A) (mul : type1400 A) (_16723 : A) (_16725 : A) : (term701 A add _16724 mul _16723 _16725) = ((term128 A mul _16723 add _16724 _16725) = (term129 A add _16724 mul _16723 _16725)).
Proof. exact (eq_refl (term701 A add _16724 mul _16723 _16725)). Qed.
Lemma lem1021097 {A : Type'} (_16738 : A) (mul : type1400 A) (h1 : term11 A mul) : term154 A mul _16738.
Proof. exact (@lem1020559 A mul h1 _16738). Qed.
Lemma lem1021098 {A : Type'} (mul : type1400 A) (_16738 : A) : (term154 A mul _16738) = (term114 A mul _16738).
Proof. exact (eq_refl (term154 A mul _16738)). Qed.
Lemma lem1021099 {A : Type'} (_16738 : A) (mul : type1400 A) (h1 : term11 A mul) : term114 A mul _16738.
Proof. exact (EQ_MP (@lem1021098 A mul _16738) (@lem1021097 A _16738 mul h1)). Qed.
Lemma lem1021100 {A : Type'} (_16738 : A) (_16739 : A) (mul : type1400 A) (h1 : term11 A mul) : term146 A mul _16738 _16739.
Proof. exact (@lem1021099 A _16738 mul h1 _16739). Qed.
Lemma lem1021101 {A : Type'} (mul : type1400 A) (_16739 : A) (_16738 : A) : (term146 A mul _16738 _16739) = ((mul _16738 _16739) = (mul _16739 _16738)).
Proof. exact (eq_refl (term146 A mul _16738 _16739)). Qed.
Lemma lem1021103 {A : Type'} (_16740 : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term698 A mul r1 _16740.
Proof. exact (@lem1020566 A mul r1 h1 _16740). Qed.
Lemma lem1021104 {A : Type'} (mul : type1400 A) (r1 : A) (_16740 : A) : (term698 A mul r1 _16740) = ((mul r1 _16740) = _16740).
Proof. exact (eq_refl (term698 A mul r1 _16740)). Qed.
Lemma lem1021106 {A : Type'} (_16741 : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term702 A mul r0 _16741.
Proof. exact (@lem1020573 A mul r0 h1 _16741). Qed.
Lemma lem1021107 {A : Type'} (mul : type1400 A) (_16741 : A) (r0 : A) : (term702 A mul r0 _16741) = ((mul r0 _16741) = r0).
Proof. exact (eq_refl (term702 A mul r0 _16741)). Qed.
Lemma lem1021148 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term148 A add n m) : term148 A add n m.
Proof. exact (h1). Qed.
Lemma lem1021170 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term163 A m add n p) : term163 A m add n p.
Proof. exact (h1). Qed.
Lemma lem1021192 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term185 A n add m p) : term185 A n add m p.
Proof. exact (h1). Qed.
Lemma lem1021214 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term207 A add r0 m) : term207 A add r0 m.
Proof. exact (h1). Qed.
Lemma lem1021236 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term148 A mul n m) : term148 A mul n m.
Proof. exact (h1). Qed.
Lemma lem1021258 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term163 A m mul n p) : term163 A m mul n p.
Proof. exact (h1). Qed.
Lemma lem1021280 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term185 A n mul m p) : term185 A n mul m p.
Proof. exact (h1). Qed.
Lemma lem1021302 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term215 A add m mul n p) : term215 A add m mul n p.
Proof. exact (h1). Qed.
Lemma lem1021328 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term293 A r1 mul m r0) : term293 A r1 mul m r0.
Proof. exact (h1). Qed.
Lemma lem1021395 {A : Type'} (_16581 : A) (_16580 : A) (add : type1400 A) (h1 : term11 A add) : (add _16580 _16581) = (add _16581 _16580).
Proof. exact (EQ_MP (@lem1020627 A add _16581 _16580) (@lem1020626 A _16580 _16581 add h1)). Qed.
Lemma lem1021396 {A : Type'} (_16581 : A) (_16580 : A) (add : type1400 A) (h1 : term11 A add) : (add _16580 _16581) = (add _16581 _16580).
Proof. exact (@lem1021395 A _16581 _16580 add h1). Qed.
Lemma lem1021397 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (@lem1021396 A n m add h1). Qed.
Lemma lem1021398 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : term703 A add n m.
Proof. exact (fun h0 : term148 A add n m => @lem1021397 A n m add h1). Qed.
Lemma lem1021400 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021401 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term703 A add n m) = ((add m n) = (add n m)).
Proof. exact (@lem1021400 ((add m n) = (add n m))). Qed.
Lemma lem1021402 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (EQ_MP (@lem1021401 A add n m) (@lem1021398 A n m add h1)). Qed.
Lemma lem1021405 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1021407 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term148 A add n m) = (term705 A add n m).
Proof. exact (@lem1021405 ((add m n) = (add n m))). Qed.
Lemma lem1021410 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term148 A add n m) : term705 A add n m.
Proof. exact (EQ_MP (@lem1021407 A add n m) (@lem1021148 A add n m h1)). Qed.
Lemma lem1021413 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : False.
Proof. exact (@lem1021410 A add n m h2 (@lem1021402 A n m add h1)). Qed.
Lemma lem1021414 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : term706.
Proof. exact (fun h0 : ~ False => @lem1021413 A add n m h1 h2). Qed.
Lemma lem1021416 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021417 : term706 = False.
Proof. exact (@lem1021416 False). Qed.
Lemma lem1021418 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : False.
Proof. exact (EQ_MP (@lem1021417) (@lem1021414 A add n m h1 h2)). Qed.
Lemma lem1021481 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1021485 {A : Type'} (_16596 : A) (_16597 : A) (_16598 : A) (add : type1400 A) (h1 : term9 A add) : (term95 A _16596 add _16597 _16598) = (term104 A add _16596 _16597 _16598).
Proof. exact (EQ_MP (@lem1020678 A add _16596 _16597 _16598) (@lem1020677 A _16596 _16597 _16598 add h1)). Qed.
Lemma lem1021486 {A : Type'} (_16596 : A) (_16597 : A) (_16598 : A) (add : type1400 A) (h1 : term9 A add) : (term95 A _16596 add _16597 _16598) = (term104 A add _16596 _16597 _16598).
Proof. exact (@lem1021485 A _16596 _16597 _16598 add h1). Qed.
Lemma lem1021487 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : (term95 A m add n p) = (term104 A add m n p).
Proof. exact (@lem1021486 A m n p add h1). Qed.
Lemma lem1021488 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : term708 A add m n p.
Proof. exact (fun h0 : term709 A add m n p => @lem1021487 A m n p add h1). Qed.
Lemma lem1021490 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021491 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) : (term708 A add m n p) = ((term95 A m add n p) = (term104 A add m n p)).
Proof. exact (@lem1021490 ((term95 A m add n p) = (term104 A add m n p))). Qed.
Lemma lem1021492 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : (term95 A m add n p) = (term104 A add m n p).
Proof. exact (EQ_MP (@lem1021491 A add m n p) (@lem1021488 A m n p add h1)). Qed.
Lemma lem1021494 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1021495 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1021494 A x). Qed.
Lemma lem1021496 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term95 A m add n p) = (term95 A m add n p).
Proof. exact (@lem1021495 A (term95 A m add n p)). Qed.
Lemma lem1021497 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : term710 A m add n p.
Proof. exact (fun h0 : term711 A m add n p => @lem1021496 A m add n p). Qed.
Lemma lem1021499 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021500 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term710 A m add n p) = ((term95 A m add n p) = (term95 A m add n p)).
Proof. exact (@lem1021499 ((term95 A m add n p) = (term95 A m add n p))). Qed.
Lemma lem1021501 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term95 A m add n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1021500 A m add n p) (@lem1021497 A m add n p)). Qed.
Lemma lem1021519 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1021520 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1021519 (y = z) (term714 A x z)). Qed.
Lemma lem1021530 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1021531 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1021530 A x y) (@lem1021520 A y x z)). Qed.
Lemma lem1021535 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1021536 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1021535 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1021558 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1021531 A y x z) (@lem1021536 A y x z)). Qed.
Lemma lem1021559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1021560 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1021559) (@lem1021558 A y x z)). Qed.
Lemma lem1021582 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1021583 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1021560 A y x z) (@lem1021582 A y x z)). Qed.
Lemma lem1021585 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1021586 (x : Prop) : (x = x) = True.
Proof. exact (@lem1021585 Prop x). Qed.
Lemma lem1021587 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1021586 (term718 A y x z)). Qed.
Lemma lem1021588 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1021583 A y x z) (@lem1021587 A y x z)). Qed.
Lemma lem1021589 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1021588 A y x z)). Qed.
Lemma lem1021590 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1021589 A y x z) (@lem0)). Qed.
Lemma lem1021591 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1021590 A y x z) (@lem1021481 A x y z)). Qed.
Lemma lem1021593 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1021594 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1021593 (term723 A y x z) (y = z)). Qed.
Lemma lem1021596 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1021597 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1021596 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1021599 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1021600 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1021599 (x = y)). Qed.
Lemma lem1021601 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1021602 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1021601) (@lem1021600 A x y)). Qed.
Lemma lem1021604 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1021605 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1021604 (x = z)). Qed.
Lemma lem1021606 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1021602 A x y) (@lem1021605 A x z)). Qed.
Lemma lem1021607 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1021597 A y x z) (@lem1021606 A y x z)). Qed.
Lemma lem1021608 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1021609 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1021608) (@lem1021607 A y x z)). Qed.
Lemma lem1021610 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1021611 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1021609 A y x z) (@lem1021610 A y z)). Qed.
Lemma lem1021612 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1021594 A x y z) (@lem1021611 A x y z)). Qed.
Lemma lem1021614 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : term735 A m add n p.
Proof. exact (conj (@lem1021492 A m n p add h1) (@lem1021501 A m add n p)). Qed.
Lemma lem1021616 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1021612 A x y z) (@lem1021591 A y x z)). Qed.
Lemma lem1021617 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1021616 A x y z). Qed.
Lemma lem1021618 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : term736 A m add n p.
Proof. exact (@lem1021617 A (term95 A m add n p) (term104 A add m n p) (term95 A m add n p)). Qed.
Lemma lem1021621 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1021618 A m add n p (@lem1021614 A m n p add h1)). Qed.
Lemma lem1021622 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1021621 A m n p add h1). Qed.
Lemma lem1021623 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : term737 A m add n p.
Proof. exact (fun h0 : term163 A m add n p => @lem1021622 A m n p add h1). Qed.
Lemma lem1021625 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021626 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term737 A m add n p) = ((term104 A add m n p) = (term95 A m add n p)).
Proof. exact (@lem1021625 ((term104 A add m n p) = (term95 A m add n p))). Qed.
Lemma lem1021627 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term9 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1021626 A m add n p) (@lem1021623 A m n p add h1)). Qed.
Lemma lem1021630 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1021632 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term163 A m add n p) = (term738 A m add n p).
Proof. exact (@lem1021630 ((term104 A add m n p) = (term95 A m add n p))). Qed.
Lemma lem1021635 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term163 A m add n p) : term738 A m add n p.
Proof. exact (EQ_MP (@lem1021632 A m add n p) (@lem1021170 A m add n p h1)). Qed.
Lemma lem1021638 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : False.
Proof. exact (@lem1021635 A m add n p h2 (@lem1021627 A m n p add h1)). Qed.
Lemma lem1021639 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : term706.
Proof. exact (fun h0 : ~ False => @lem1021638 A m add n p h1 h2). Qed.
Lemma lem1021641 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021642 : term706 = False.
Proof. exact (@lem1021641 False). Qed.
Lemma lem1021643 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : False.
Proof. exact (EQ_MP (@lem1021642) (@lem1021639 A m add n p h1 h2)). Qed.
Lemma lem1021690 {A : Type'} (add : type1400 A) : add = add.
Proof. exact (eq_refl add). Qed.
Lemma lem1021691 {A : Type'} (_16792 : A) (_16794 : A) (h1 : _16792 = _16794) : _16792 = _16794.
Proof. exact (h1). Qed.
Lemma lem1021692 {A : Type'} (_16793 : A) (_16795 : A) (h1 : _16793 = _16795) : _16793 = _16795.
Proof. exact (h1). Qed.
Lemma lem1021693 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (h1 : _16792 = _16794) : (add _16792) = (add _16794).
Proof. exact (MK_COMB (@lem1021690 A add) (@lem1021691 A _16792 _16794 h1)). Qed.
Lemma lem1021694 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) (h1 : _16792 = _16794) (h2 : _16793 = _16795) : (add _16792 _16793) = (add _16794 _16795).
Proof. exact (MK_COMB (@lem1021693 A add _16792 _16794 h1) (@lem1021692 A _16793 _16795 h2)). Qed.
Lemma lem1021695 {A : Type'} (_16793 : A) (add : type1400 A) (_16795 : A) (_16792 : A) (_16794 : A) (h1 : _16792 = _16794) : term739 A _16792 _16793 add _16794 _16795.
Proof. exact (fun h0 : _16793 = _16795 => @lem1021694 A add _16792 _16794 _16793 _16795 h1 h0). Qed.
Lemma lem1021697 (a : Prop) (b : Prop) : (a -> b) = (term740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1021698 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : (term739 A _16792 _16793 add _16794 _16795) = (term741 A _16792 _16793 add _16794 _16795).
Proof. exact (@lem1021697 (_16793 = _16795) ((add _16792 _16793) = (add _16794 _16795))). Qed.
Lemma lem1021699 {A : Type'} (_16793 : A) (add : type1400 A) (_16795 : A) (_16792 : A) (_16794 : A) (h1 : _16792 = _16794) : term741 A _16792 _16793 add _16794 _16795.
Proof. exact (EQ_MP (@lem1021698 A _16792 _16793 add _16794 _16795) (@lem1021695 A _16793 add _16795 _16792 _16794 h1)). Qed.
Lemma lem1021700 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : term742 A _16792 _16793 add _16794 _16795.
Proof. exact (fun h0 : _16792 = _16794 => @lem1021699 A _16793 add _16795 _16792 _16794 h0). Qed.
Lemma lem1021702 (a : Prop) (b : Prop) : (a -> b) = (term740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1021703 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : (term742 A _16792 _16793 add _16794 _16795) = (term743 A _16792 _16793 add _16794 _16795).
Proof. exact (@lem1021702 (_16792 = _16794) (term741 A _16792 _16793 add _16794 _16795)). Qed.
Lemma lem1021704 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : term743 A _16792 _16793 add _16794 _16795.
Proof. exact (EQ_MP (@lem1021703 A _16792 _16793 add _16794 _16795) (@lem1021700 A _16792 _16793 add _16794 _16795)). Qed.
Lemma lem1021706 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1021710 {A : Type'} (_16619 : A) (_16618 : A) (add : type1400 A) (h1 : term11 A add) : (add _16618 _16619) = (add _16619 _16618).
Proof. exact (EQ_MP (@lem1020741 A add _16619 _16618) (@lem1020740 A _16618 _16619 add h1)). Qed.
Lemma lem1021711 {A : Type'} (_16619 : A) (_16618 : A) (add : type1400 A) (h1 : term11 A add) : (add _16618 _16619) = (add _16619 _16618).
Proof. exact (@lem1021710 A _16619 _16618 add h1). Qed.
Lemma lem1021712 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term11 A add) : (term104 A add n p m) = (term95 A m add n p).
Proof. exact (@lem1021711 A m (add n p) add h1). Qed.
Lemma lem1021713 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term11 A add) : term744 A m add n p.
Proof. exact (fun h0 : term745 A m add n p => @lem1021712 A m n p add h1). Qed.
Lemma lem1021715 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021716 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term744 A m add n p) = ((term104 A add n p m) = (term95 A m add n p)).
Proof. exact (@lem1021715 ((term104 A add n p m) = (term95 A m add n p))). Qed.
Lemma lem1021717 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term11 A add) : (term104 A add n p m) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1021716 A m add n p) (@lem1021713 A m n p add h1)). Qed.
Lemma lem1021719 {A : Type'} (_16615 : A) (_16616 : A) (_16617 : A) (add : type1400 A) (h1 : term9 A add) : (term95 A _16615 add _16616 _16617) = (term104 A add _16615 _16616 _16617).
Proof. exact (EQ_MP (@lem1020735 A add _16615 _16616 _16617) (@lem1020734 A _16615 _16616 _16617 add h1)). Qed.
Lemma lem1021720 {A : Type'} (_16615 : A) (_16616 : A) (_16617 : A) (add : type1400 A) (h1 : term9 A add) : (term95 A _16615 add _16616 _16617) = (term104 A add _16615 _16616 _16617).
Proof. exact (@lem1021719 A _16615 _16616 _16617 add h1). Qed.
Lemma lem1021721 {A : Type'} (n : A) (p : A) (m : A) (add : type1400 A) (h1 : term9 A add) : (term95 A n add p m) = (term104 A add n p m).
Proof. exact (@lem1021720 A n p m add h1). Qed.
Lemma lem1021722 {A : Type'} (n : A) (p : A) (m : A) (add : type1400 A) (h1 : term9 A add) : term708 A add n p m.
Proof. exact (fun h0 : term709 A add n p m => @lem1021721 A n p m add h1). Qed.
Lemma lem1021724 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021725 {A : Type'} (add : type1400 A) (n : A) (p : A) (m : A) : (term708 A add n p m) = ((term95 A n add p m) = (term104 A add n p m)).
Proof. exact (@lem1021724 ((term95 A n add p m) = (term104 A add n p m))). Qed.
Lemma lem1021726 {A : Type'} (n : A) (p : A) (m : A) (add : type1400 A) (h1 : term9 A add) : (term95 A n add p m) = (term104 A add n p m).
Proof. exact (EQ_MP (@lem1021725 A add n p m) (@lem1021722 A n p m add h1)). Qed.
Lemma lem1021728 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1021729 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1021728 A x). Qed.
Lemma lem1021730 {A : Type'} (n : A) : n = n.
Proof. exact (@lem1021729 A n). Qed.
Lemma lem1021731 {A : Type'} (n : A) : term746 A n.
Proof. exact (fun h0 : term747 A n => @lem1021730 A n). Qed.
Lemma lem1021733 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021734 {A : Type'} (n : A) : (term746 A n) = (n = n).
Proof. exact (@lem1021733 (n = n)). Qed.
Lemma lem1021735 {A : Type'} (n : A) : n = n.
Proof. exact (EQ_MP (@lem1021734 A n) (@lem1021731 A n)). Qed.
Lemma lem1021737 {A : Type'} (_16619 : A) (_16618 : A) (add : type1400 A) (h1 : term11 A add) : (add _16618 _16619) = (add _16619 _16618).
Proof. exact (EQ_MP (@lem1020741 A add _16619 _16618) (@lem1020740 A _16618 _16619 add h1)). Qed.
Lemma lem1021738 {A : Type'} (_16619 : A) (_16618 : A) (add : type1400 A) (h1 : term11 A add) : (add _16618 _16619) = (add _16619 _16618).
Proof. exact (@lem1021737 A _16619 _16618 add h1). Qed.
Lemma lem1021739 {A : Type'} (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : (add p m) = (add m p).
Proof. exact (@lem1021738 A m p add h1). Qed.
Lemma lem1021740 {A : Type'} (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : term703 A add m p.
Proof. exact (fun h0 : term148 A add m p => @lem1021739 A m p add h1). Qed.
Lemma lem1021742 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021743 {A : Type'} (add : type1400 A) (m : A) (p : A) : (term703 A add m p) = ((add p m) = (add m p)).
Proof. exact (@lem1021742 ((add p m) = (add m p))). Qed.
Lemma lem1021744 {A : Type'} (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : (add p m) = (add m p).
Proof. exact (EQ_MP (@lem1021743 A add m p) (@lem1021740 A m p add h1)). Qed.
Lemma lem1021762 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1021763 {A : Type'} (_16792 : A) (add : type1400 A) (_16794 : A) (_16793 : A) (_16795 : A) : (term741 A _16792 _16793 add _16794 _16795) = (term748 A _16792 add _16794 _16793 _16795).
Proof. exact (@lem1021762 ((add _16792 _16793) = (add _16794 _16795)) (term714 A _16793 _16795)). Qed.
Lemma lem1021773 {A : Type'} (_16792 : A) (_16794 : A) : (term715 A _16792 _16794) = (term715 A _16792 _16794).
Proof. exact (eq_refl (term715 A _16792 _16794)). Qed.
Lemma lem1021774 {A : Type'} (_16792 : A) (add : type1400 A) (_16794 : A) (_16793 : A) (_16795 : A) : (term743 A _16792 _16793 add _16794 _16795) = (term749 A _16792 add _16794 _16793 _16795).
Proof. exact (MK_COMB (@lem1021773 A _16792 _16794) (@lem1021763 A _16792 add _16794 _16793 _16795)). Qed.
Lemma lem1021778 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1021779 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term749 A _16792 add _16794 _16793 _16795) = (term750 A add _16792 _16794 _16793 _16795).
Proof. exact (@lem1021778 ((add _16792 _16793) = (add _16794 _16795)) (term714 A _16792 _16794) (term714 A _16793 _16795)). Qed.
Lemma lem1021801 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term743 A _16792 _16793 add _16794 _16795) = (term750 A add _16792 _16794 _16793 _16795).
Proof. exact (TRANS (@lem1021774 A _16792 add _16794 _16793 _16795) (@lem1021779 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021802 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1021803 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term751 A _16792 _16793 add _16794 _16795) = (term752 A add _16792 _16794 _16793 _16795).
Proof. exact (MK_COMB (@lem1021802) (@lem1021801 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021825 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term750 A add _16792 _16794 _16793 _16795) = (term750 A add _16792 _16794 _16793 _16795).
Proof. exact (eq_refl (term750 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021826 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : ((term743 A _16792 _16793 add _16794 _16795) = (term750 A add _16792 _16794 _16793 _16795)) = ((term750 A add _16792 _16794 _16793 _16795) = (term750 A add _16792 _16794 _16793 _16795)).
Proof. exact (MK_COMB (@lem1021803 A add _16792 _16794 _16793 _16795) (@lem1021825 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021828 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1021829 (x : Prop) : (x = x) = True.
Proof. exact (@lem1021828 Prop x). Qed.
Lemma lem1021830 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : ((term750 A add _16792 _16794 _16793 _16795) = (term750 A add _16792 _16794 _16793 _16795)) = True.
Proof. exact (@lem1021829 (term750 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021831 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : ((term743 A _16792 _16793 add _16794 _16795) = (term750 A add _16792 _16794 _16793 _16795)) = True.
Proof. exact (TRANS (@lem1021826 A add _16792 _16794 _16793 _16795) (@lem1021830 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021832 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : True = ((term743 A _16792 _16793 add _16794 _16795) = (term750 A add _16792 _16794 _16793 _16795)).
Proof. exact (SYM (@lem1021831 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021833 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term743 A _16792 _16793 add _16794 _16795) = (term750 A add _16792 _16794 _16793 _16795).
Proof. exact (EQ_MP (@lem1021832 A add _16792 _16794 _16793 _16795) (@lem0)). Qed.
Lemma lem1021834 {A : Type'} (add : type1400 A) (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : term750 A add _16792 _16794 _16793 _16795.
Proof. exact (EQ_MP (@lem1021833 A add _16792 _16794 _16793 _16795) (@lem1021704 A _16792 _16793 add _16794 _16795)). Qed.
Lemma lem1021836 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1021837 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : (term750 A add _16792 _16794 _16793 _16795) = (term753 A _16792 _16793 add _16794 _16795).
Proof. exact (@lem1021836 (term754 A _16792 _16794 _16793 _16795) ((add _16792 _16793) = (add _16794 _16795))). Qed.
Lemma lem1021839 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1021840 {A : Type'} (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term755 A _16792 _16794 _16793 _16795) = (term756 A _16792 _16794 _16793 _16795).
Proof. exact (@lem1021839 (term714 A _16792 _16794) (term714 A _16793 _16795)). Qed.
Lemma lem1021842 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1021843 {A : Type'} (_16792 : A) (_16794 : A) : (term728 A _16792 _16794) = (_16792 = _16794).
Proof. exact (@lem1021842 (_16792 = _16794)). Qed.
Lemma lem1021844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1021845 {A : Type'} (_16792 : A) (_16794 : A) : (term729 A _16792 _16794) = (term730 A _16792 _16794).
Proof. exact (MK_COMB (@lem1021844) (@lem1021843 A _16792 _16794)). Qed.
Lemma lem1021847 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1021848 {A : Type'} (_16793 : A) (_16795 : A) : (term728 A _16793 _16795) = (_16793 = _16795).
Proof. exact (@lem1021847 (_16793 = _16795)). Qed.
Lemma lem1021849 {A : Type'} (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term756 A _16792 _16794 _16793 _16795) = (term757 A _16792 _16794 _16793 _16795).
Proof. exact (MK_COMB (@lem1021845 A _16792 _16794) (@lem1021848 A _16793 _16795)). Qed.
Lemma lem1021850 {A : Type'} (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term755 A _16792 _16794 _16793 _16795) = (term757 A _16792 _16794 _16793 _16795).
Proof. exact (TRANS (@lem1021840 A _16792 _16794 _16793 _16795) (@lem1021849 A _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021851 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1021852 {A : Type'} (_16792 : A) (_16794 : A) (_16793 : A) (_16795 : A) : (term758 A _16792 _16794 _16793 _16795) = (term759 A _16792 _16794 _16793 _16795).
Proof. exact (MK_COMB (@lem1021851) (@lem1021850 A _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021853 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : ((add _16792 _16793) = (add _16794 _16795)) = ((add _16792 _16793) = (add _16794 _16795)).
Proof. exact (eq_refl ((add _16792 _16793) = (add _16794 _16795))). Qed.
Lemma lem1021854 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : (term753 A _16792 _16793 add _16794 _16795) = (term760 A _16792 _16793 add _16794 _16795).
Proof. exact (MK_COMB (@lem1021852 A _16792 _16794 _16793 _16795) (@lem1021853 A _16792 _16793 add _16794 _16795)). Qed.
Lemma lem1021855 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : (term750 A add _16792 _16794 _16793 _16795) = (term760 A _16792 _16793 add _16794 _16795).
Proof. exact (TRANS (@lem1021837 A _16792 _16793 add _16794 _16795) (@lem1021854 A _16792 _16793 add _16794 _16795)). Qed.
Lemma lem1021857 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : term761 A n add m p.
Proof. exact (conj (@lem1021735 A n) (@lem1021744 A m p add h1)). Qed.
Lemma lem1021859 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : term760 A _16792 _16793 add _16794 _16795.
Proof. exact (EQ_MP (@lem1021855 A _16792 _16793 add _16794 _16795) (@lem1021834 A add _16792 _16794 _16793 _16795)). Qed.
Lemma lem1021860 {A : Type'} (_16792 : A) (_16793 : A) (add : type1400 A) (_16794 : A) (_16795 : A) : term760 A _16792 _16793 add _16794 _16795.
Proof. exact (@lem1021859 A _16792 _16793 add _16794 _16795). Qed.
Lemma lem1021861 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : term762 A n add m p.
Proof. exact (@lem1021860 A n (add p m) add n (add m p)). Qed.
Lemma lem1021864 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : (term95 A n add p m) = (term95 A n add m p).
Proof. exact (@lem1021861 A n add m p (@lem1021857 A n m p add h1)). Qed.
Lemma lem1021865 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : (term95 A n add p m) = (term95 A n add m p).
Proof. exact (@lem1021864 A n m p add h1). Qed.
Lemma lem1021866 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : term763 A n add m p.
Proof. exact (fun h0 : term764 A n add m p => @lem1021865 A n m p add h1). Qed.
Lemma lem1021868 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021869 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term763 A n add m p) = ((term95 A n add p m) = (term95 A n add m p)).
Proof. exact (@lem1021868 ((term95 A n add p m) = (term95 A n add m p))). Qed.
Lemma lem1021870 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term11 A add) : (term95 A n add p m) = (term95 A n add m p).
Proof. exact (EQ_MP (@lem1021869 A n add m p) (@lem1021866 A n m p add h1)). Qed.
Lemma lem1021888 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1021889 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1021888 (y = z) (term714 A x z)). Qed.
Lemma lem1021899 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1021900 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1021899 A x y) (@lem1021889 A y x z)). Qed.
Lemma lem1021904 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1021905 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1021904 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1021927 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1021900 A y x z) (@lem1021905 A y x z)). Qed.
Lemma lem1021928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1021929 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1021928) (@lem1021927 A y x z)). Qed.
Lemma lem1021951 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1021952 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1021929 A y x z) (@lem1021951 A y x z)). Qed.
Lemma lem1021954 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1021955 (x : Prop) : (x = x) = True.
Proof. exact (@lem1021954 Prop x). Qed.
Lemma lem1021956 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1021955 (term718 A y x z)). Qed.
Lemma lem1021957 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1021952 A y x z) (@lem1021956 A y x z)). Qed.
Lemma lem1021958 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1021957 A y x z)). Qed.
Lemma lem1021959 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1021958 A y x z) (@lem0)). Qed.
Lemma lem1021960 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1021959 A y x z) (@lem1021706 A x y z)). Qed.
Lemma lem1021962 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1021963 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1021962 (term723 A y x z) (y = z)). Qed.
Lemma lem1021965 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1021966 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1021965 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1021968 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1021969 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1021968 (x = y)). Qed.
Lemma lem1021970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1021971 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1021970) (@lem1021969 A x y)). Qed.
Lemma lem1021973 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1021974 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1021973 (x = z)). Qed.
Lemma lem1021975 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1021971 A x y) (@lem1021974 A x z)). Qed.
Lemma lem1021976 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1021966 A y x z) (@lem1021975 A y x z)). Qed.
Lemma lem1021977 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1021978 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1021977) (@lem1021976 A y x z)). Qed.
Lemma lem1021979 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1021980 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1021978 A y x z) (@lem1021979 A y z)). Qed.
Lemma lem1021981 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1021963 A x y z) (@lem1021980 A x y z)). Qed.
Lemma lem1021983 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : term765 A n add m p.
Proof. exact (conj (@lem1021726 A n p m add h1) (@lem1021870 A n m p add h2)). Qed.
Lemma lem1021985 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1021981 A x y z) (@lem1021960 A y x z)). Qed.
Lemma lem1021986 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1021985 A x y z). Qed.
Lemma lem1021987 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : term766 A n add m p.
Proof. exact (@lem1021986 A (term95 A n add p m) (term104 A add n p m) (term95 A n add m p)). Qed.
Lemma lem1021990 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : (term104 A add n p m) = (term95 A n add m p).
Proof. exact (@lem1021987 A n add m p (@lem1021983 A n m p add h1 h2)). Qed.
Lemma lem1021991 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : (term104 A add n p m) = (term95 A n add m p).
Proof. exact (@lem1021990 A n m p add h1 h2). Qed.
Lemma lem1021992 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : term767 A n add m p.
Proof. exact (fun h0 : term768 A n add m p => @lem1021991 A n m p add h1 h2). Qed.
Lemma lem1021994 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1021995 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term767 A n add m p) = ((term104 A add n p m) = (term95 A n add m p)).
Proof. exact (@lem1021994 ((term104 A add n p m) = (term95 A n add m p))). Qed.
Lemma lem1021996 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : (term104 A add n p m) = (term95 A n add m p).
Proof. exact (EQ_MP (@lem1021995 A n add m p) (@lem1021992 A n m p add h1 h2)). Qed.
Lemma lem1021997 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : term769 A n add m p.
Proof. exact (conj (@lem1021717 A m n p add h2) (@lem1021996 A n m p add h1 h2)). Qed.
Lemma lem1021999 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1021981 A x y z) (@lem1021960 A y x z)). Qed.
Lemma lem1022000 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1021999 A x y z). Qed.
Lemma lem1022001 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : term770 A n add m p.
Proof. exact (@lem1022000 A (term104 A add n p m) (term95 A m add n p) (term95 A n add m p)). Qed.
Lemma lem1022004 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : (term95 A m add n p) = (term95 A n add m p).
Proof. exact (@lem1022001 A n add m p (@lem1021997 A n m p add h1 h2)). Qed.
Lemma lem1022005 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : (term95 A m add n p) = (term95 A n add m p).
Proof. exact (@lem1022004 A n m p add h1 h2). Qed.
Lemma lem1022006 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : term771 A n add m p.
Proof. exact (fun h0 : term185 A n add m p => @lem1022005 A n m p add h1 h2). Qed.
Lemma lem1022008 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022009 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term771 A n add m p) = ((term95 A m add n p) = (term95 A n add m p)).
Proof. exact (@lem1022008 ((term95 A m add n p) = (term95 A n add m p))). Qed.
Lemma lem1022010 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : (term95 A m add n p) = (term95 A n add m p).
Proof. exact (EQ_MP (@lem1022009 A n add m p) (@lem1022006 A n m p add h1 h2)). Qed.
Lemma lem1022013 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1022015 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term185 A n add m p) = (term772 A n add m p).
Proof. exact (@lem1022013 ((term95 A m add n p) = (term95 A n add m p))). Qed.
Lemma lem1022018 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term185 A n add m p) : term772 A n add m p.
Proof. exact (EQ_MP (@lem1022015 A n add m p) (@lem1021192 A n add m p h1)). Qed.
Lemma lem1022021 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : False.
Proof. exact (@lem1022018 A n add m p h3 (@lem1022010 A n m p add h1 h2)). Qed.
Lemma lem1022022 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : term706.
Proof. exact (fun h0 : ~ False => @lem1022021 A n add m p h1 h2 h3). Qed.
Lemma lem1022024 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022025 : term706 = False.
Proof. exact (@lem1022024 False). Qed.
Lemma lem1022026 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : False.
Proof. exact (EQ_MP (@lem1022025) (@lem1022022 A n add m p h1 h2 h3)). Qed.
Lemma lem1022089 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1022093 {A : Type'} (_16638 : A) (_16637 : A) (add : type1400 A) (h1 : term11 A add) : (add _16637 _16638) = (add _16638 _16637).
Proof. exact (EQ_MP (@lem1020798 A add _16638 _16637) (@lem1020797 A _16637 _16638 add h1)). Qed.
Lemma lem1022094 {A : Type'} (_16638 : A) (_16637 : A) (add : type1400 A) (h1 : term11 A add) : (add _16637 _16638) = (add _16638 _16637).
Proof. exact (@lem1022093 A _16638 _16637 add h1). Qed.
Lemma lem1022095 {A : Type'} (m : A) (r0 : A) (add : type1400 A) (h1 : term11 A add) : (add r0 m) = (add m r0).
Proof. exact (@lem1022094 A m r0 add h1). Qed.
Lemma lem1022096 {A : Type'} (m : A) (r0 : A) (add : type1400 A) (h1 : term11 A add) : term703 A add m r0.
Proof. exact (fun h0 : term148 A add m r0 => @lem1022095 A m r0 add h1). Qed.
Lemma lem1022098 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022099 {A : Type'} (add : type1400 A) (m : A) (r0 : A) : (term703 A add m r0) = ((add r0 m) = (add m r0)).
Proof. exact (@lem1022098 ((add r0 m) = (add m r0))). Qed.
Lemma lem1022100 {A : Type'} (m : A) (r0 : A) (add : type1400 A) (h1 : term11 A add) : (add r0 m) = (add m r0).
Proof. exact (EQ_MP (@lem1022099 A add m r0) (@lem1022096 A m r0 add h1)). Qed.
Lemma lem1022102 {A : Type'} (_16639 : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (add r0 _16639) = _16639.
Proof. exact (EQ_MP (@lem1020801 A add r0 _16639) (@lem1020800 A _16639 add r0 h1)). Qed.
Lemma lem1022103 {A : Type'} (_16639 : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (add r0 _16639) = _16639.
Proof. exact (@lem1022102 A _16639 add r0 h1). Qed.
Lemma lem1022104 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (add r0 m) = m.
Proof. exact (@lem1022103 A m add r0 h1). Qed.
Lemma lem1022105 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term773 A add r0 m.
Proof. exact (fun h0 : term237 A add r0 m => @lem1022104 A m add r0 h1). Qed.
Lemma lem1022107 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022108 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term773 A add r0 m) = ((add r0 m) = m).
Proof. exact (@lem1022107 ((add r0 m) = m)). Qed.
Lemma lem1022109 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (add r0 m) = m.
Proof. exact (EQ_MP (@lem1022108 A add r0 m) (@lem1022105 A m add r0 h1)). Qed.
Lemma lem1022127 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1022128 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1022127 (y = z) (term714 A x z)). Qed.
Lemma lem1022138 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1022139 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1022138 A x y) (@lem1022128 A y x z)). Qed.
Lemma lem1022143 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1022144 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1022143 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1022166 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1022139 A y x z) (@lem1022144 A y x z)). Qed.
Lemma lem1022167 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1022168 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1022167) (@lem1022166 A y x z)). Qed.
Lemma lem1022190 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1022191 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1022168 A y x z) (@lem1022190 A y x z)). Qed.
Lemma lem1022193 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1022194 (x : Prop) : (x = x) = True.
Proof. exact (@lem1022193 Prop x). Qed.
Lemma lem1022195 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1022194 (term718 A y x z)). Qed.
Lemma lem1022196 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1022191 A y x z) (@lem1022195 A y x z)). Qed.
Lemma lem1022197 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1022196 A y x z)). Qed.
Lemma lem1022198 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1022197 A y x z) (@lem0)). Qed.
Lemma lem1022199 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1022198 A y x z) (@lem1022089 A x y z)). Qed.
Lemma lem1022201 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1022202 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1022201 (term723 A y x z) (y = z)). Qed.
Lemma lem1022204 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1022205 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1022204 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1022207 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022208 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1022207 (x = y)). Qed.
Lemma lem1022209 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1022210 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1022209) (@lem1022208 A x y)). Qed.
Lemma lem1022212 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022213 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1022212 (x = z)). Qed.
Lemma lem1022214 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1022210 A x y) (@lem1022213 A x z)). Qed.
Lemma lem1022215 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1022205 A y x z) (@lem1022214 A y x z)). Qed.
Lemma lem1022216 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1022217 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1022216) (@lem1022215 A y x z)). Qed.
Lemma lem1022218 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1022219 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1022217 A y x z) (@lem1022218 A y z)). Qed.
Lemma lem1022220 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1022202 A x y z) (@lem1022219 A x y z)). Qed.
Lemma lem1022222 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term11 A add) (h2 : term13 A add r0) : term774 A add r0 m.
Proof. exact (conj (@lem1022100 A m r0 add h1) (@lem1022109 A m add r0 h2)). Qed.
Lemma lem1022224 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1022220 A x y z) (@lem1022199 A y x z)). Qed.
Lemma lem1022225 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1022224 A x y z). Qed.
Lemma lem1022226 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : term775 A add r0 m.
Proof. exact (@lem1022225 A (add r0 m) (add m r0) m). Qed.
Lemma lem1022229 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term11 A add) (h2 : term13 A add r0) : (add m r0) = m.
Proof. exact (@lem1022226 A add r0 m (@lem1022222 A m add r0 h1 h2)). Qed.
Lemma lem1022230 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term11 A add) (h2 : term13 A add r0) : (add m r0) = m.
Proof. exact (@lem1022229 A m add r0 h1 h2). Qed.
Lemma lem1022231 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term11 A add) (h2 : term13 A add r0) : term776 A add r0 m.
Proof. exact (fun h0 : term207 A add r0 m => @lem1022230 A m add r0 h1 h2). Qed.
Lemma lem1022233 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022234 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term776 A add r0 m) = ((add m r0) = m).
Proof. exact (@lem1022233 ((add m r0) = m)). Qed.
Lemma lem1022235 {A : Type'} (m : A) (add : type1400 A) (r0 : A) (h1 : term11 A add) (h2 : term13 A add r0) : (add m r0) = m.
Proof. exact (EQ_MP (@lem1022234 A add r0 m) (@lem1022231 A m add r0 h1 h2)). Qed.
Lemma lem1022238 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1022240 {A : Type'} (add : type1400 A) (r0 : A) (m : A) : (term207 A add r0 m) = (term777 A add r0 m).
Proof. exact (@lem1022238 ((add m r0) = m)). Qed.
Lemma lem1022243 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term207 A add r0 m) : term777 A add r0 m.
Proof. exact (EQ_MP (@lem1022240 A add r0 m) (@lem1021214 A add r0 m h1)). Qed.
Lemma lem1022246 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : False.
Proof. exact (@lem1022243 A add r0 m h3 (@lem1022235 A m add r0 h1 h2)). Qed.
Lemma lem1022247 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : term706.
Proof. exact (fun h0 : ~ False => @lem1022246 A add r0 m h1 h2 h3). Qed.
Lemma lem1022249 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022250 : term706 = False.
Proof. exact (@lem1022249 False). Qed.
Lemma lem1022251 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : False.
Proof. exact (EQ_MP (@lem1022250) (@lem1022247 A add r0 m h1 h2 h3)). Qed.
Lemma lem1022318 {A : Type'} (_16663 : A) (_16662 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16662 _16663) = (mul _16663 _16662).
Proof. exact (EQ_MP (@lem1020873 A mul _16663 _16662) (@lem1020872 A _16662 _16663 mul h1)). Qed.
Lemma lem1022319 {A : Type'} (_16663 : A) (_16662 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16662 _16663) = (mul _16663 _16662).
Proof. exact (@lem1022318 A _16663 _16662 mul h1). Qed.
Lemma lem1022320 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1022319 A n m mul h1). Qed.
Lemma lem1022321 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : term703 A mul n m.
Proof. exact (fun h0 : term148 A mul n m => @lem1022320 A n m mul h1). Qed.
Lemma lem1022323 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022324 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term703 A mul n m) = ((mul m n) = (mul n m)).
Proof. exact (@lem1022323 ((mul m n) = (mul n m))). Qed.
Lemma lem1022325 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1022324 A mul n m) (@lem1022321 A n m mul h1)). Qed.
Lemma lem1022328 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1022330 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term148 A mul n m) = (term705 A mul n m).
Proof. exact (@lem1022328 ((mul m n) = (mul n m))). Qed.
Lemma lem1022333 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term148 A mul n m) : term705 A mul n m.
Proof. exact (EQ_MP (@lem1022330 A mul n m) (@lem1021236 A mul n m h1)). Qed.
Lemma lem1022336 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : False.
Proof. exact (@lem1022333 A mul n m h2 (@lem1022325 A n m mul h1)). Qed.
Lemma lem1022337 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : term706.
Proof. exact (fun h0 : ~ False => @lem1022336 A mul n m h1 h2). Qed.
Lemma lem1022339 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022340 : term706 = False.
Proof. exact (@lem1022339 False). Qed.
Lemma lem1022341 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : False.
Proof. exact (EQ_MP (@lem1022340) (@lem1022337 A mul n m h1 h2)). Qed.
Lemma lem1022404 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1022408 {A : Type'} (_16678 : A) (_16679 : A) (_16680 : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A _16678 mul _16679 _16680) = (term104 A mul _16678 _16679 _16680).
Proof. exact (EQ_MP (@lem1020924 A mul _16678 _16679 _16680) (@lem1020923 A _16678 _16679 _16680 mul h1)). Qed.
Lemma lem1022409 {A : Type'} (_16678 : A) (_16679 : A) (_16680 : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A _16678 mul _16679 _16680) = (term104 A mul _16678 _16679 _16680).
Proof. exact (@lem1022408 A _16678 _16679 _16680 mul h1). Qed.
Lemma lem1022410 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A m mul n p) = (term104 A mul m n p).
Proof. exact (@lem1022409 A m n p mul h1). Qed.
Lemma lem1022411 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : term708 A mul m n p.
Proof. exact (fun h0 : term709 A mul m n p => @lem1022410 A m n p mul h1). Qed.
Lemma lem1022413 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022414 {A : Type'} (mul : type1400 A) (m : A) (n : A) (p : A) : (term708 A mul m n p) = ((term95 A m mul n p) = (term104 A mul m n p)).
Proof. exact (@lem1022413 ((term95 A m mul n p) = (term104 A mul m n p))). Qed.
Lemma lem1022415 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A m mul n p) = (term104 A mul m n p).
Proof. exact (EQ_MP (@lem1022414 A mul m n p) (@lem1022411 A m n p mul h1)). Qed.
Lemma lem1022417 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1022418 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1022417 A x). Qed.
Lemma lem1022419 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term95 A m mul n p) = (term95 A m mul n p).
Proof. exact (@lem1022418 A (term95 A m mul n p)). Qed.
Lemma lem1022420 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : term710 A m mul n p.
Proof. exact (fun h0 : term711 A m mul n p => @lem1022419 A m mul n p). Qed.
Lemma lem1022422 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022423 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term710 A m mul n p) = ((term95 A m mul n p) = (term95 A m mul n p)).
Proof. exact (@lem1022422 ((term95 A m mul n p) = (term95 A m mul n p))). Qed.
Lemma lem1022424 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term95 A m mul n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1022423 A m mul n p) (@lem1022420 A m mul n p)). Qed.
Lemma lem1022442 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1022443 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1022442 (y = z) (term714 A x z)). Qed.
Lemma lem1022453 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1022454 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1022453 A x y) (@lem1022443 A y x z)). Qed.
Lemma lem1022458 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1022459 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1022458 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1022481 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1022454 A y x z) (@lem1022459 A y x z)). Qed.
Lemma lem1022482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1022483 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1022482) (@lem1022481 A y x z)). Qed.
Lemma lem1022505 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1022506 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1022483 A y x z) (@lem1022505 A y x z)). Qed.
Lemma lem1022508 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1022509 (x : Prop) : (x = x) = True.
Proof. exact (@lem1022508 Prop x). Qed.
Lemma lem1022510 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1022509 (term718 A y x z)). Qed.
Lemma lem1022511 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1022506 A y x z) (@lem1022510 A y x z)). Qed.
Lemma lem1022512 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1022511 A y x z)). Qed.
Lemma lem1022513 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1022512 A y x z) (@lem0)). Qed.
Lemma lem1022514 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1022513 A y x z) (@lem1022404 A x y z)). Qed.
Lemma lem1022516 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1022517 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1022516 (term723 A y x z) (y = z)). Qed.
Lemma lem1022519 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1022520 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1022519 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1022522 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022523 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1022522 (x = y)). Qed.
Lemma lem1022524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1022525 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1022524) (@lem1022523 A x y)). Qed.
Lemma lem1022527 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022528 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1022527 (x = z)). Qed.
Lemma lem1022529 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1022525 A x y) (@lem1022528 A x z)). Qed.
Lemma lem1022530 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1022520 A y x z) (@lem1022529 A y x z)). Qed.
Lemma lem1022531 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1022532 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1022531) (@lem1022530 A y x z)). Qed.
Lemma lem1022533 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1022534 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1022532 A y x z) (@lem1022533 A y z)). Qed.
Lemma lem1022535 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1022517 A x y z) (@lem1022534 A x y z)). Qed.
Lemma lem1022537 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : term735 A m mul n p.
Proof. exact (conj (@lem1022415 A m n p mul h1) (@lem1022424 A m mul n p)). Qed.
Lemma lem1022539 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1022535 A x y z) (@lem1022514 A y x z)). Qed.
Lemma lem1022540 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1022539 A x y z). Qed.
Lemma lem1022541 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : term736 A m mul n p.
Proof. exact (@lem1022540 A (term95 A m mul n p) (term104 A mul m n p) (term95 A m mul n p)). Qed.
Lemma lem1022544 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1022541 A m mul n p (@lem1022537 A m n p mul h1)). Qed.
Lemma lem1022545 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1022544 A m n p mul h1). Qed.
Lemma lem1022546 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : term737 A m mul n p.
Proof. exact (fun h0 : term163 A m mul n p => @lem1022545 A m n p mul h1). Qed.
Lemma lem1022548 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022549 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term737 A m mul n p) = ((term104 A mul m n p) = (term95 A m mul n p)).
Proof. exact (@lem1022548 ((term104 A mul m n p) = (term95 A m mul n p))). Qed.
Lemma lem1022550 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1022549 A m mul n p) (@lem1022546 A m n p mul h1)). Qed.
Lemma lem1022553 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1022555 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term163 A m mul n p) = (term738 A m mul n p).
Proof. exact (@lem1022553 ((term104 A mul m n p) = (term95 A m mul n p))). Qed.
Lemma lem1022558 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term163 A m mul n p) : term738 A m mul n p.
Proof. exact (EQ_MP (@lem1022555 A m mul n p) (@lem1021258 A m mul n p h1)). Qed.
Lemma lem1022561 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : False.
Proof. exact (@lem1022558 A m mul n p h2 (@lem1022550 A m n p mul h1)). Qed.
Lemma lem1022562 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : term706.
Proof. exact (fun h0 : ~ False => @lem1022561 A m mul n p h1 h2). Qed.
Lemma lem1022564 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022565 : term706 = False.
Proof. exact (@lem1022564 False). Qed.
Lemma lem1022566 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : False.
Proof. exact (EQ_MP (@lem1022565) (@lem1022562 A m mul n p h1 h2)). Qed.
Lemma lem1022598 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1022599 {A : Type'} (_16852 : A) (_16854 : A) (h1 : _16852 = _16854) : _16852 = _16854.
Proof. exact (h1). Qed.
Lemma lem1022600 {A : Type'} (_16853 : A) (_16855 : A) (h1 : _16853 = _16855) : _16853 = _16855.
Proof. exact (h1). Qed.
Lemma lem1022601 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (h1 : _16852 = _16854) : (mul _16852) = (mul _16854).
Proof. exact (MK_COMB (@lem1022598 A mul) (@lem1022599 A _16852 _16854 h1)). Qed.
Lemma lem1022602 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) (h1 : _16852 = _16854) (h2 : _16853 = _16855) : (mul _16852 _16853) = (mul _16854 _16855).
Proof. exact (MK_COMB (@lem1022601 A mul _16852 _16854 h1) (@lem1022600 A _16853 _16855 h2)). Qed.
Lemma lem1022603 {A : Type'} (_16853 : A) (mul : type1400 A) (_16855 : A) (_16852 : A) (_16854 : A) (h1 : _16852 = _16854) : term739 A _16852 _16853 mul _16854 _16855.
Proof. exact (fun h0 : _16853 = _16855 => @lem1022602 A mul _16852 _16854 _16853 _16855 h1 h0). Qed.
Lemma lem1022605 (a : Prop) (b : Prop) : (a -> b) = (term740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1022606 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : (term739 A _16852 _16853 mul _16854 _16855) = (term741 A _16852 _16853 mul _16854 _16855).
Proof. exact (@lem1022605 (_16853 = _16855) ((mul _16852 _16853) = (mul _16854 _16855))). Qed.
Lemma lem1022607 {A : Type'} (_16853 : A) (mul : type1400 A) (_16855 : A) (_16852 : A) (_16854 : A) (h1 : _16852 = _16854) : term741 A _16852 _16853 mul _16854 _16855.
Proof. exact (EQ_MP (@lem1022606 A _16852 _16853 mul _16854 _16855) (@lem1022603 A _16853 mul _16855 _16852 _16854 h1)). Qed.
Lemma lem1022608 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : term742 A _16852 _16853 mul _16854 _16855.
Proof. exact (fun h0 : _16852 = _16854 => @lem1022607 A _16853 mul _16855 _16852 _16854 h0). Qed.
Lemma lem1022610 (a : Prop) (b : Prop) : (a -> b) = (term740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1022611 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : (term742 A _16852 _16853 mul _16854 _16855) = (term743 A _16852 _16853 mul _16854 _16855).
Proof. exact (@lem1022610 (_16852 = _16854) (term741 A _16852 _16853 mul _16854 _16855)). Qed.
Lemma lem1022612 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : term743 A _16852 _16853 mul _16854 _16855.
Proof. exact (EQ_MP (@lem1022611 A _16852 _16853 mul _16854 _16855) (@lem1022608 A _16852 _16853 mul _16854 _16855)). Qed.
Lemma lem1022629 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1022633 {A : Type'} (_16701 : A) (_16700 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16700 _16701) = (mul _16701 _16700).
Proof. exact (EQ_MP (@lem1020987 A mul _16701 _16700) (@lem1020986 A _16700 _16701 mul h1)). Qed.
Lemma lem1022634 {A : Type'} (_16701 : A) (_16700 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16700 _16701) = (mul _16701 _16700).
Proof. exact (@lem1022633 A _16701 _16700 mul h1). Qed.
Lemma lem1022635 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term104 A mul n p m) = (term95 A m mul n p).
Proof. exact (@lem1022634 A m (mul n p) mul h1). Qed.
Lemma lem1022636 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : term744 A m mul n p.
Proof. exact (fun h0 : term745 A m mul n p => @lem1022635 A m n p mul h1). Qed.
Lemma lem1022638 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022639 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term744 A m mul n p) = ((term104 A mul n p m) = (term95 A m mul n p)).
Proof. exact (@lem1022638 ((term104 A mul n p m) = (term95 A m mul n p))). Qed.
Lemma lem1022640 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term104 A mul n p m) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1022639 A m mul n p) (@lem1022636 A m n p mul h1)). Qed.
Lemma lem1022642 {A : Type'} (_16697 : A) (_16698 : A) (_16699 : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A _16697 mul _16698 _16699) = (term104 A mul _16697 _16698 _16699).
Proof. exact (EQ_MP (@lem1020981 A mul _16697 _16698 _16699) (@lem1020980 A _16697 _16698 _16699 mul h1)). Qed.
Lemma lem1022643 {A : Type'} (_16697 : A) (_16698 : A) (_16699 : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A _16697 mul _16698 _16699) = (term104 A mul _16697 _16698 _16699).
Proof. exact (@lem1022642 A _16697 _16698 _16699 mul h1). Qed.
Lemma lem1022644 {A : Type'} (n : A) (p : A) (m : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A n mul p m) = (term104 A mul n p m).
Proof. exact (@lem1022643 A n p m mul h1). Qed.
Lemma lem1022645 {A : Type'} (n : A) (p : A) (m : A) (mul : type1400 A) (h1 : term9 A mul) : term708 A mul n p m.
Proof. exact (fun h0 : term709 A mul n p m => @lem1022644 A n p m mul h1). Qed.
Lemma lem1022647 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022648 {A : Type'} (mul : type1400 A) (n : A) (p : A) (m : A) : (term708 A mul n p m) = ((term95 A n mul p m) = (term104 A mul n p m)).
Proof. exact (@lem1022647 ((term95 A n mul p m) = (term104 A mul n p m))). Qed.
Lemma lem1022649 {A : Type'} (n : A) (p : A) (m : A) (mul : type1400 A) (h1 : term9 A mul) : (term95 A n mul p m) = (term104 A mul n p m).
Proof. exact (EQ_MP (@lem1022648 A mul n p m) (@lem1022645 A n p m mul h1)). Qed.
Lemma lem1022651 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1022652 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1022651 A x). Qed.
Lemma lem1022653 {A : Type'} (n : A) : n = n.
Proof. exact (@lem1022652 A n). Qed.
Lemma lem1022654 {A : Type'} (n : A) : term746 A n.
Proof. exact (fun h0 : term747 A n => @lem1022653 A n). Qed.
Lemma lem1022656 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022657 {A : Type'} (n : A) : (term746 A n) = (n = n).
Proof. exact (@lem1022656 (n = n)). Qed.
Lemma lem1022658 {A : Type'} (n : A) : n = n.
Proof. exact (EQ_MP (@lem1022657 A n) (@lem1022654 A n)). Qed.
Lemma lem1022660 {A : Type'} (_16701 : A) (_16700 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16700 _16701) = (mul _16701 _16700).
Proof. exact (EQ_MP (@lem1020987 A mul _16701 _16700) (@lem1020986 A _16700 _16701 mul h1)). Qed.
Lemma lem1022661 {A : Type'} (_16701 : A) (_16700 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16700 _16701) = (mul _16701 _16700).
Proof. exact (@lem1022660 A _16701 _16700 mul h1). Qed.
Lemma lem1022662 {A : Type'} (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (mul p m) = (mul m p).
Proof. exact (@lem1022661 A m p mul h1). Qed.
Lemma lem1022663 {A : Type'} (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : term703 A mul m p.
Proof. exact (fun h0 : term148 A mul m p => @lem1022662 A m p mul h1). Qed.
Lemma lem1022665 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022666 {A : Type'} (mul : type1400 A) (m : A) (p : A) : (term703 A mul m p) = ((mul p m) = (mul m p)).
Proof. exact (@lem1022665 ((mul p m) = (mul m p))). Qed.
Lemma lem1022667 {A : Type'} (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (mul p m) = (mul m p).
Proof. exact (EQ_MP (@lem1022666 A mul m p) (@lem1022663 A m p mul h1)). Qed.
Lemma lem1022685 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1022686 {A : Type'} (_16852 : A) (mul : type1400 A) (_16854 : A) (_16853 : A) (_16855 : A) : (term741 A _16852 _16853 mul _16854 _16855) = (term748 A _16852 mul _16854 _16853 _16855).
Proof. exact (@lem1022685 ((mul _16852 _16853) = (mul _16854 _16855)) (term714 A _16853 _16855)). Qed.
Lemma lem1022696 {A : Type'} (_16852 : A) (_16854 : A) : (term715 A _16852 _16854) = (term715 A _16852 _16854).
Proof. exact (eq_refl (term715 A _16852 _16854)). Qed.
Lemma lem1022697 {A : Type'} (_16852 : A) (mul : type1400 A) (_16854 : A) (_16853 : A) (_16855 : A) : (term743 A _16852 _16853 mul _16854 _16855) = (term749 A _16852 mul _16854 _16853 _16855).
Proof. exact (MK_COMB (@lem1022696 A _16852 _16854) (@lem1022686 A _16852 mul _16854 _16853 _16855)). Qed.
Lemma lem1022701 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1022702 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term749 A _16852 mul _16854 _16853 _16855) = (term750 A mul _16852 _16854 _16853 _16855).
Proof. exact (@lem1022701 ((mul _16852 _16853) = (mul _16854 _16855)) (term714 A _16852 _16854) (term714 A _16853 _16855)). Qed.
Lemma lem1022724 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term743 A _16852 _16853 mul _16854 _16855) = (term750 A mul _16852 _16854 _16853 _16855).
Proof. exact (TRANS (@lem1022697 A _16852 mul _16854 _16853 _16855) (@lem1022702 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022725 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1022726 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term751 A _16852 _16853 mul _16854 _16855) = (term752 A mul _16852 _16854 _16853 _16855).
Proof. exact (MK_COMB (@lem1022725) (@lem1022724 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022748 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term750 A mul _16852 _16854 _16853 _16855) = (term750 A mul _16852 _16854 _16853 _16855).
Proof. exact (eq_refl (term750 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022749 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : ((term743 A _16852 _16853 mul _16854 _16855) = (term750 A mul _16852 _16854 _16853 _16855)) = ((term750 A mul _16852 _16854 _16853 _16855) = (term750 A mul _16852 _16854 _16853 _16855)).
Proof. exact (MK_COMB (@lem1022726 A mul _16852 _16854 _16853 _16855) (@lem1022748 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022751 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1022752 (x : Prop) : (x = x) = True.
Proof. exact (@lem1022751 Prop x). Qed.
Lemma lem1022753 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : ((term750 A mul _16852 _16854 _16853 _16855) = (term750 A mul _16852 _16854 _16853 _16855)) = True.
Proof. exact (@lem1022752 (term750 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022754 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : ((term743 A _16852 _16853 mul _16854 _16855) = (term750 A mul _16852 _16854 _16853 _16855)) = True.
Proof. exact (TRANS (@lem1022749 A mul _16852 _16854 _16853 _16855) (@lem1022753 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022755 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : True = ((term743 A _16852 _16853 mul _16854 _16855) = (term750 A mul _16852 _16854 _16853 _16855)).
Proof. exact (SYM (@lem1022754 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022756 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term743 A _16852 _16853 mul _16854 _16855) = (term750 A mul _16852 _16854 _16853 _16855).
Proof. exact (EQ_MP (@lem1022755 A mul _16852 _16854 _16853 _16855) (@lem0)). Qed.
Lemma lem1022757 {A : Type'} (mul : type1400 A) (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : term750 A mul _16852 _16854 _16853 _16855.
Proof. exact (EQ_MP (@lem1022756 A mul _16852 _16854 _16853 _16855) (@lem1022612 A _16852 _16853 mul _16854 _16855)). Qed.
Lemma lem1022759 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1022760 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : (term750 A mul _16852 _16854 _16853 _16855) = (term753 A _16852 _16853 mul _16854 _16855).
Proof. exact (@lem1022759 (term754 A _16852 _16854 _16853 _16855) ((mul _16852 _16853) = (mul _16854 _16855))). Qed.
Lemma lem1022762 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1022763 {A : Type'} (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term755 A _16852 _16854 _16853 _16855) = (term756 A _16852 _16854 _16853 _16855).
Proof. exact (@lem1022762 (term714 A _16852 _16854) (term714 A _16853 _16855)). Qed.
Lemma lem1022765 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022766 {A : Type'} (_16852 : A) (_16854 : A) : (term728 A _16852 _16854) = (_16852 = _16854).
Proof. exact (@lem1022765 (_16852 = _16854)). Qed.
Lemma lem1022767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1022768 {A : Type'} (_16852 : A) (_16854 : A) : (term729 A _16852 _16854) = (term730 A _16852 _16854).
Proof. exact (MK_COMB (@lem1022767) (@lem1022766 A _16852 _16854)). Qed.
Lemma lem1022770 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022771 {A : Type'} (_16853 : A) (_16855 : A) : (term728 A _16853 _16855) = (_16853 = _16855).
Proof. exact (@lem1022770 (_16853 = _16855)). Qed.
Lemma lem1022772 {A : Type'} (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term756 A _16852 _16854 _16853 _16855) = (term757 A _16852 _16854 _16853 _16855).
Proof. exact (MK_COMB (@lem1022768 A _16852 _16854) (@lem1022771 A _16853 _16855)). Qed.
Lemma lem1022773 {A : Type'} (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term755 A _16852 _16854 _16853 _16855) = (term757 A _16852 _16854 _16853 _16855).
Proof. exact (TRANS (@lem1022763 A _16852 _16854 _16853 _16855) (@lem1022772 A _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022774 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1022775 {A : Type'} (_16852 : A) (_16854 : A) (_16853 : A) (_16855 : A) : (term758 A _16852 _16854 _16853 _16855) = (term759 A _16852 _16854 _16853 _16855).
Proof. exact (MK_COMB (@lem1022774) (@lem1022773 A _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022776 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : ((mul _16852 _16853) = (mul _16854 _16855)) = ((mul _16852 _16853) = (mul _16854 _16855)).
Proof. exact (eq_refl ((mul _16852 _16853) = (mul _16854 _16855))). Qed.
Lemma lem1022777 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : (term753 A _16852 _16853 mul _16854 _16855) = (term760 A _16852 _16853 mul _16854 _16855).
Proof. exact (MK_COMB (@lem1022775 A _16852 _16854 _16853 _16855) (@lem1022776 A _16852 _16853 mul _16854 _16855)). Qed.
Lemma lem1022778 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : (term750 A mul _16852 _16854 _16853 _16855) = (term760 A _16852 _16853 mul _16854 _16855).
Proof. exact (TRANS (@lem1022760 A _16852 _16853 mul _16854 _16855) (@lem1022777 A _16852 _16853 mul _16854 _16855)). Qed.
Lemma lem1022780 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : term761 A n mul m p.
Proof. exact (conj (@lem1022658 A n) (@lem1022667 A m p mul h1)). Qed.
Lemma lem1022782 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : term760 A _16852 _16853 mul _16854 _16855.
Proof. exact (EQ_MP (@lem1022778 A _16852 _16853 mul _16854 _16855) (@lem1022757 A mul _16852 _16854 _16853 _16855)). Qed.
Lemma lem1022783 {A : Type'} (_16852 : A) (_16853 : A) (mul : type1400 A) (_16854 : A) (_16855 : A) : term760 A _16852 _16853 mul _16854 _16855.
Proof. exact (@lem1022782 A _16852 _16853 mul _16854 _16855). Qed.
Lemma lem1022784 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : term762 A n mul m p.
Proof. exact (@lem1022783 A n (mul p m) mul n (mul m p)). Qed.
Lemma lem1022787 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term95 A n mul p m) = (term95 A n mul m p).
Proof. exact (@lem1022784 A n mul m p (@lem1022780 A n m p mul h1)). Qed.
Lemma lem1022788 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term95 A n mul p m) = (term95 A n mul m p).
Proof. exact (@lem1022787 A n m p mul h1). Qed.
Lemma lem1022789 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : term763 A n mul m p.
Proof. exact (fun h0 : term764 A n mul m p => @lem1022788 A n m p mul h1). Qed.
Lemma lem1022791 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022792 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term763 A n mul m p) = ((term95 A n mul p m) = (term95 A n mul m p)).
Proof. exact (@lem1022791 ((term95 A n mul p m) = (term95 A n mul m p))). Qed.
Lemma lem1022793 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term95 A n mul p m) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1022792 A n mul m p) (@lem1022789 A n m p mul h1)). Qed.
Lemma lem1022811 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1022812 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1022811 (y = z) (term714 A x z)). Qed.
Lemma lem1022822 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1022823 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1022822 A x y) (@lem1022812 A y x z)). Qed.
Lemma lem1022827 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1022828 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1022827 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1022850 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1022823 A y x z) (@lem1022828 A y x z)). Qed.
Lemma lem1022851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1022852 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1022851) (@lem1022850 A y x z)). Qed.
Lemma lem1022874 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1022875 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1022852 A y x z) (@lem1022874 A y x z)). Qed.
Lemma lem1022877 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1022878 (x : Prop) : (x = x) = True.
Proof. exact (@lem1022877 Prop x). Qed.
Lemma lem1022879 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1022878 (term718 A y x z)). Qed.
Lemma lem1022880 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1022875 A y x z) (@lem1022879 A y x z)). Qed.
Lemma lem1022881 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1022880 A y x z)). Qed.
Lemma lem1022882 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1022881 A y x z) (@lem0)). Qed.
Lemma lem1022883 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1022882 A y x z) (@lem1022629 A x y z)). Qed.
Lemma lem1022885 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1022886 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1022885 (term723 A y x z) (y = z)). Qed.
Lemma lem1022888 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1022889 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1022888 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1022891 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022892 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1022891 (x = y)). Qed.
Lemma lem1022893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1022894 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1022893) (@lem1022892 A x y)). Qed.
Lemma lem1022896 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1022897 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1022896 (x = z)). Qed.
Lemma lem1022898 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1022894 A x y) (@lem1022897 A x z)). Qed.
Lemma lem1022899 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1022889 A y x z) (@lem1022898 A y x z)). Qed.
Lemma lem1022900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1022901 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1022900) (@lem1022899 A y x z)). Qed.
Lemma lem1022902 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1022903 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1022901 A y x z) (@lem1022902 A y z)). Qed.
Lemma lem1022904 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1022886 A x y z) (@lem1022903 A x y z)). Qed.
Lemma lem1022906 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : term765 A n mul m p.
Proof. exact (conj (@lem1022649 A n p m mul h1) (@lem1022793 A n m p mul h2)). Qed.
Lemma lem1022908 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1022904 A x y z) (@lem1022883 A y x z)). Qed.
Lemma lem1022909 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1022908 A x y z). Qed.
Lemma lem1022910 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : term766 A n mul m p.
Proof. exact (@lem1022909 A (term95 A n mul p m) (term104 A mul n p m) (term95 A n mul m p)). Qed.
Lemma lem1022913 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : (term104 A mul n p m) = (term95 A n mul m p).
Proof. exact (@lem1022910 A n mul m p (@lem1022906 A n m p mul h1 h2)). Qed.
Lemma lem1022914 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : (term104 A mul n p m) = (term95 A n mul m p).
Proof. exact (@lem1022913 A n m p mul h1 h2). Qed.
Lemma lem1022915 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : term767 A n mul m p.
Proof. exact (fun h0 : term768 A n mul m p => @lem1022914 A n m p mul h1 h2). Qed.
Lemma lem1022917 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022918 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term767 A n mul m p) = ((term104 A mul n p m) = (term95 A n mul m p)).
Proof. exact (@lem1022917 ((term104 A mul n p m) = (term95 A n mul m p))). Qed.
Lemma lem1022919 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : (term104 A mul n p m) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1022918 A n mul m p) (@lem1022915 A n m p mul h1 h2)). Qed.
Lemma lem1022920 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : term769 A n mul m p.
Proof. exact (conj (@lem1022640 A m n p mul h2) (@lem1022919 A n m p mul h1 h2)). Qed.
Lemma lem1022922 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1022904 A x y z) (@lem1022883 A y x z)). Qed.
Lemma lem1022923 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1022922 A x y z). Qed.
Lemma lem1022924 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : term770 A n mul m p.
Proof. exact (@lem1022923 A (term104 A mul n p m) (term95 A m mul n p) (term95 A n mul m p)). Qed.
Lemma lem1022927 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1022924 A n mul m p (@lem1022920 A n m p mul h1 h2)). Qed.
Lemma lem1022928 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1022927 A n m p mul h1 h2). Qed.
Lemma lem1022929 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : term771 A n mul m p.
Proof. exact (fun h0 : term185 A n mul m p => @lem1022928 A n m p mul h1 h2). Qed.
Lemma lem1022931 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022932 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term771 A n mul m p) = ((term95 A m mul n p) = (term95 A n mul m p)).
Proof. exact (@lem1022931 ((term95 A m mul n p) = (term95 A n mul m p))). Qed.
Lemma lem1022933 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term9 A mul) (h2 : term11 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1022932 A n mul m p) (@lem1022929 A n m p mul h1 h2)). Qed.
Lemma lem1022936 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1022938 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term185 A n mul m p) = (term772 A n mul m p).
Proof. exact (@lem1022936 ((term95 A m mul n p) = (term95 A n mul m p))). Qed.
Lemma lem1022941 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term185 A n mul m p) : term772 A n mul m p.
Proof. exact (EQ_MP (@lem1022938 A n mul m p) (@lem1021280 A n mul m p h1)). Qed.
Lemma lem1022944 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : False.
Proof. exact (@lem1022941 A n mul m p h3 (@lem1022933 A n m p mul h1 h2)). Qed.
Lemma lem1022945 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : term706.
Proof. exact (fun h0 : ~ False => @lem1022944 A n mul m p h1 h2 h3). Qed.
Lemma lem1022947 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1022948 : term706 = False.
Proof. exact (@lem1022947 False). Qed.
Lemma lem1022949 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : False.
Proof. exact (EQ_MP (@lem1022948) (@lem1022945 A n mul m p h1 h2 h3)). Qed.
Lemma lem1022996 {A : Type'} (add : type1400 A) : add = add.
Proof. exact (eq_refl add). Qed.
Lemma lem1022997 {A : Type'} (_16872 : A) (_16874 : A) (h1 : _16872 = _16874) : _16872 = _16874.
Proof. exact (h1). Qed.
Lemma lem1022998 {A : Type'} (_16873 : A) (_16875 : A) (h1 : _16873 = _16875) : _16873 = _16875.
Proof. exact (h1). Qed.
Lemma lem1022999 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (h1 : _16872 = _16874) : (add _16872) = (add _16874).
Proof. exact (MK_COMB (@lem1022996 A add) (@lem1022997 A _16872 _16874 h1)). Qed.
Lemma lem1023000 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) (h1 : _16872 = _16874) (h2 : _16873 = _16875) : (add _16872 _16873) = (add _16874 _16875).
Proof. exact (MK_COMB (@lem1022999 A add _16872 _16874 h1) (@lem1022998 A _16873 _16875 h2)). Qed.
Lemma lem1023001 {A : Type'} (_16873 : A) (add : type1400 A) (_16875 : A) (_16872 : A) (_16874 : A) (h1 : _16872 = _16874) : term739 A _16872 _16873 add _16874 _16875.
Proof. exact (fun h0 : _16873 = _16875 => @lem1023000 A add _16872 _16874 _16873 _16875 h1 h0). Qed.
Lemma lem1023003 (a : Prop) (b : Prop) : (a -> b) = (term740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1023004 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : (term739 A _16872 _16873 add _16874 _16875) = (term741 A _16872 _16873 add _16874 _16875).
Proof. exact (@lem1023003 (_16873 = _16875) ((add _16872 _16873) = (add _16874 _16875))). Qed.
Lemma lem1023005 {A : Type'} (_16873 : A) (add : type1400 A) (_16875 : A) (_16872 : A) (_16874 : A) (h1 : _16872 = _16874) : term741 A _16872 _16873 add _16874 _16875.
Proof. exact (EQ_MP (@lem1023004 A _16872 _16873 add _16874 _16875) (@lem1023001 A _16873 add _16875 _16872 _16874 h1)). Qed.
Lemma lem1023006 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : term742 A _16872 _16873 add _16874 _16875.
Proof. exact (fun h0 : _16872 = _16874 => @lem1023005 A _16873 add _16875 _16872 _16874 h0). Qed.
Lemma lem1023008 (a : Prop) (b : Prop) : (a -> b) = (term740 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1023009 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : (term742 A _16872 _16873 add _16874 _16875) = (term743 A _16872 _16873 add _16874 _16875).
Proof. exact (@lem1023008 (_16872 = _16874) (term741 A _16872 _16873 add _16874 _16875)). Qed.
Lemma lem1023010 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : term743 A _16872 _16873 add _16874 _16875.
Proof. exact (EQ_MP (@lem1023009 A _16872 _16873 add _16874 _16875) (@lem1023006 A _16872 _16873 add _16874 _16875)). Qed.
Lemma lem1023012 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1023016 {A : Type'} (_16724 : A) (_16723 : A) (_16725 : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term128 A mul _16723 add _16724 _16725) = (term129 A add _16724 mul _16723 _16725).
Proof. exact (EQ_MP (@lem1021059 A add _16724 mul _16723 _16725) (@lem1021058 A _16724 _16723 _16725 add mul h1)). Qed.
Lemma lem1023017 {A : Type'} (_16724 : A) (_16723 : A) (_16725 : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term128 A mul _16723 add _16724 _16725) = (term129 A add _16724 mul _16723 _16725).
Proof. exact (@lem1023016 A _16724 _16723 _16725 add mul h1). Qed.
Lemma lem1023018 {A : Type'} (m : A) (p : A) (n : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term128 A mul p add m n) = (term129 A add m mul p n).
Proof. exact (@lem1023017 A m p n add mul h1). Qed.
Lemma lem1023019 {A : Type'} (m : A) (p : A) (n : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term778 A add m mul p n.
Proof. exact (fun h0 : term779 A add m mul p n => @lem1023018 A m p n add mul h1). Qed.
Lemma lem1023021 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023022 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (p : A) (n : A) : (term778 A add m mul p n) = ((term128 A mul p add m n) = (term129 A add m mul p n)).
Proof. exact (@lem1023021 ((term128 A mul p add m n) = (term129 A add m mul p n))). Qed.
Lemma lem1023023 {A : Type'} (m : A) (p : A) (n : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term128 A mul p add m n) = (term129 A add m mul p n).
Proof. exact (EQ_MP (@lem1023022 A add m mul p n) (@lem1023019 A m p n add mul h1)). Qed.
Lemma lem1023025 {A : Type'} (_16720 : A) (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16719 _16720) = (mul _16720 _16719).
Proof. exact (EQ_MP (@lem1021044 A mul _16720 _16719) (@lem1021043 A _16719 _16720 mul h1)). Qed.
Lemma lem1023026 {A : Type'} (_16720 : A) (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16719 _16720) = (mul _16720 _16719).
Proof. exact (@lem1023025 A _16720 _16719 mul h1). Qed.
Lemma lem1023027 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term128 A mul p add m n) = (term85 A mul add m n p).
Proof. exact (@lem1023026 A (add m n) p mul h1). Qed.
Lemma lem1023028 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : term780 A mul add m n p.
Proof. exact (fun h0 : term781 A mul add m n p => @lem1023027 A add m n p mul h1). Qed.
Lemma lem1023030 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023031 {A : Type'} (mul : type1400 A) (add : type1400 A) (m : A) (n : A) (p : A) : (term780 A mul add m n p) = ((term128 A mul p add m n) = (term85 A mul add m n p)).
Proof. exact (@lem1023030 ((term128 A mul p add m n) = (term85 A mul add m n p))). Qed.
Lemma lem1023032 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term128 A mul p add m n) = (term85 A mul add m n p).
Proof. exact (EQ_MP (@lem1023031 A mul add m n p) (@lem1023028 A add m n p mul h1)). Qed.
Lemma lem1023050 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1023051 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1023050 (y = z) (term714 A x z)). Qed.
Lemma lem1023061 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1023062 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1023061 A x y) (@lem1023051 A y x z)). Qed.
Lemma lem1023066 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1023067 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1023066 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1023089 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1023062 A y x z) (@lem1023067 A y x z)). Qed.
Lemma lem1023090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1023091 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1023090) (@lem1023089 A y x z)). Qed.
Lemma lem1023113 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1023114 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1023091 A y x z) (@lem1023113 A y x z)). Qed.
Lemma lem1023116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1023117 (x : Prop) : (x = x) = True.
Proof. exact (@lem1023116 Prop x). Qed.
Lemma lem1023118 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1023117 (term718 A y x z)). Qed.
Lemma lem1023119 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1023114 A y x z) (@lem1023118 A y x z)). Qed.
Lemma lem1023120 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1023119 A y x z)). Qed.
Lemma lem1023121 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1023120 A y x z) (@lem0)). Qed.
Lemma lem1023122 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1023121 A y x z) (@lem1023012 A x y z)). Qed.
Lemma lem1023124 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1023125 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1023124 (term723 A y x z) (y = z)). Qed.
Lemma lem1023127 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1023128 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1023127 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1023130 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1023131 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1023130 (x = y)). Qed.
Lemma lem1023132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1023133 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1023132) (@lem1023131 A x y)). Qed.
Lemma lem1023135 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1023136 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1023135 (x = z)). Qed.
Lemma lem1023137 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1023133 A x y) (@lem1023136 A x z)). Qed.
Lemma lem1023138 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1023128 A y x z) (@lem1023137 A y x z)). Qed.
Lemma lem1023139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1023140 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1023139) (@lem1023138 A y x z)). Qed.
Lemma lem1023141 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1023142 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1023140 A y x z) (@lem1023141 A y z)). Qed.
Lemma lem1023143 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1023125 A x y z) (@lem1023142 A x y z)). Qed.
Lemma lem1023145 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : term782 A mul add m n p.
Proof. exact (conj (@lem1023023 A m p n add mul h1) (@lem1023032 A add m n p mul h2)). Qed.
Lemma lem1023147 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1023143 A x y z) (@lem1023122 A y x z)). Qed.
Lemma lem1023148 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1023147 A x y z). Qed.
Lemma lem1023149 {A : Type'} (mul : type1400 A) (add : type1400 A) (m : A) (n : A) (p : A) : term783 A mul add m n p.
Proof. exact (@lem1023148 A (term128 A mul p add m n) (term129 A add m mul p n) (term85 A mul add m n p)). Qed.
Lemma lem1023152 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : (term129 A add m mul p n) = (term85 A mul add m n p).
Proof. exact (@lem1023149 A mul add m n p (@lem1023145 A m n p add mul h1 h2)). Qed.
Lemma lem1023153 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : (term129 A add m mul p n) = (term85 A mul add m n p).
Proof. exact (@lem1023152 A m n p add mul h1 h2). Qed.
Lemma lem1023154 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : term784 A mul add m n p.
Proof. exact (fun h0 : term785 A mul add m n p => @lem1023153 A m n p add mul h1 h2). Qed.
Lemma lem1023156 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023157 {A : Type'} (mul : type1400 A) (add : type1400 A) (m : A) (n : A) (p : A) : (term784 A mul add m n p) = ((term129 A add m mul p n) = (term85 A mul add m n p)).
Proof. exact (@lem1023156 ((term129 A add m mul p n) = (term85 A mul add m n p))). Qed.
Lemma lem1023158 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : (term129 A add m mul p n) = (term85 A mul add m n p).
Proof. exact (EQ_MP (@lem1023157 A mul add m n p) (@lem1023154 A m n p add mul h1 h2)). Qed.
Lemma lem1023160 {A : Type'} (_16720 : A) (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16719 _16720) = (mul _16720 _16719).
Proof. exact (EQ_MP (@lem1021044 A mul _16720 _16719) (@lem1021043 A _16719 _16720 mul h1)). Qed.
Lemma lem1023161 {A : Type'} (_16720 : A) (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16719 _16720) = (mul _16720 _16719).
Proof. exact (@lem1023160 A _16720 _16719 mul h1). Qed.
Lemma lem1023162 {A : Type'} (p : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m p) = (mul p m).
Proof. exact (@lem1023161 A p m mul h1). Qed.
Lemma lem1023163 {A : Type'} (p : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : term703 A mul p m.
Proof. exact (fun h0 : term148 A mul p m => @lem1023162 A p m mul h1). Qed.
Lemma lem1023165 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023166 {A : Type'} (mul : type1400 A) (p : A) (m : A) : (term703 A mul p m) = ((mul m p) = (mul p m)).
Proof. exact (@lem1023165 ((mul m p) = (mul p m))). Qed.
Lemma lem1023167 {A : Type'} (p : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m p) = (mul p m).
Proof. exact (EQ_MP (@lem1023166 A mul p m) (@lem1023163 A p m mul h1)). Qed.
Lemma lem1023169 {A : Type'} (_16720 : A) (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16719 _16720) = (mul _16720 _16719).
Proof. exact (EQ_MP (@lem1021044 A mul _16720 _16719) (@lem1021043 A _16719 _16720 mul h1)). Qed.
Lemma lem1023170 {A : Type'} (_16720 : A) (_16719 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16719 _16720) = (mul _16720 _16719).
Proof. exact (@lem1023169 A _16720 _16719 mul h1). Qed.
Lemma lem1023171 {A : Type'} (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : (mul n p) = (mul p n).
Proof. exact (@lem1023170 A p n mul h1). Qed.
Lemma lem1023172 {A : Type'} (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : term703 A mul p n.
Proof. exact (fun h0 : term148 A mul p n => @lem1023171 A p n mul h1). Qed.
Lemma lem1023174 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023175 {A : Type'} (mul : type1400 A) (p : A) (n : A) : (term703 A mul p n) = ((mul n p) = (mul p n)).
Proof. exact (@lem1023174 ((mul n p) = (mul p n))). Qed.
Lemma lem1023176 {A : Type'} (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : (mul n p) = (mul p n).
Proof. exact (EQ_MP (@lem1023175 A mul p n) (@lem1023172 A p n mul h1)). Qed.
Lemma lem1023194 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1023195 {A : Type'} (_16872 : A) (add : type1400 A) (_16874 : A) (_16873 : A) (_16875 : A) : (term741 A _16872 _16873 add _16874 _16875) = (term748 A _16872 add _16874 _16873 _16875).
Proof. exact (@lem1023194 ((add _16872 _16873) = (add _16874 _16875)) (term714 A _16873 _16875)). Qed.
Lemma lem1023205 {A : Type'} (_16872 : A) (_16874 : A) : (term715 A _16872 _16874) = (term715 A _16872 _16874).
Proof. exact (eq_refl (term715 A _16872 _16874)). Qed.
Lemma lem1023206 {A : Type'} (_16872 : A) (add : type1400 A) (_16874 : A) (_16873 : A) (_16875 : A) : (term743 A _16872 _16873 add _16874 _16875) = (term749 A _16872 add _16874 _16873 _16875).
Proof. exact (MK_COMB (@lem1023205 A _16872 _16874) (@lem1023195 A _16872 add _16874 _16873 _16875)). Qed.
Lemma lem1023210 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1023211 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term749 A _16872 add _16874 _16873 _16875) = (term750 A add _16872 _16874 _16873 _16875).
Proof. exact (@lem1023210 ((add _16872 _16873) = (add _16874 _16875)) (term714 A _16872 _16874) (term714 A _16873 _16875)). Qed.
Lemma lem1023233 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term743 A _16872 _16873 add _16874 _16875) = (term750 A add _16872 _16874 _16873 _16875).
Proof. exact (TRANS (@lem1023206 A _16872 add _16874 _16873 _16875) (@lem1023211 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1023235 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term751 A _16872 _16873 add _16874 _16875) = (term752 A add _16872 _16874 _16873 _16875).
Proof. exact (MK_COMB (@lem1023234) (@lem1023233 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023257 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term750 A add _16872 _16874 _16873 _16875) = (term750 A add _16872 _16874 _16873 _16875).
Proof. exact (eq_refl (term750 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023258 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : ((term743 A _16872 _16873 add _16874 _16875) = (term750 A add _16872 _16874 _16873 _16875)) = ((term750 A add _16872 _16874 _16873 _16875) = (term750 A add _16872 _16874 _16873 _16875)).
Proof. exact (MK_COMB (@lem1023235 A add _16872 _16874 _16873 _16875) (@lem1023257 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023260 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1023261 (x : Prop) : (x = x) = True.
Proof. exact (@lem1023260 Prop x). Qed.
Lemma lem1023262 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : ((term750 A add _16872 _16874 _16873 _16875) = (term750 A add _16872 _16874 _16873 _16875)) = True.
Proof. exact (@lem1023261 (term750 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023263 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : ((term743 A _16872 _16873 add _16874 _16875) = (term750 A add _16872 _16874 _16873 _16875)) = True.
Proof. exact (TRANS (@lem1023258 A add _16872 _16874 _16873 _16875) (@lem1023262 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023264 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : True = ((term743 A _16872 _16873 add _16874 _16875) = (term750 A add _16872 _16874 _16873 _16875)).
Proof. exact (SYM (@lem1023263 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023265 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term743 A _16872 _16873 add _16874 _16875) = (term750 A add _16872 _16874 _16873 _16875).
Proof. exact (EQ_MP (@lem1023264 A add _16872 _16874 _16873 _16875) (@lem0)). Qed.
Lemma lem1023266 {A : Type'} (add : type1400 A) (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : term750 A add _16872 _16874 _16873 _16875.
Proof. exact (EQ_MP (@lem1023265 A add _16872 _16874 _16873 _16875) (@lem1023010 A _16872 _16873 add _16874 _16875)). Qed.
Lemma lem1023268 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1023269 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : (term750 A add _16872 _16874 _16873 _16875) = (term753 A _16872 _16873 add _16874 _16875).
Proof. exact (@lem1023268 (term754 A _16872 _16874 _16873 _16875) ((add _16872 _16873) = (add _16874 _16875))). Qed.
Lemma lem1023271 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1023272 {A : Type'} (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term755 A _16872 _16874 _16873 _16875) = (term756 A _16872 _16874 _16873 _16875).
Proof. exact (@lem1023271 (term714 A _16872 _16874) (term714 A _16873 _16875)). Qed.
Lemma lem1023274 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1023275 {A : Type'} (_16872 : A) (_16874 : A) : (term728 A _16872 _16874) = (_16872 = _16874).
Proof. exact (@lem1023274 (_16872 = _16874)). Qed.
Lemma lem1023276 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1023277 {A : Type'} (_16872 : A) (_16874 : A) : (term729 A _16872 _16874) = (term730 A _16872 _16874).
Proof. exact (MK_COMB (@lem1023276) (@lem1023275 A _16872 _16874)). Qed.
Lemma lem1023279 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1023280 {A : Type'} (_16873 : A) (_16875 : A) : (term728 A _16873 _16875) = (_16873 = _16875).
Proof. exact (@lem1023279 (_16873 = _16875)). Qed.
Lemma lem1023281 {A : Type'} (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term756 A _16872 _16874 _16873 _16875) = (term757 A _16872 _16874 _16873 _16875).
Proof. exact (MK_COMB (@lem1023277 A _16872 _16874) (@lem1023280 A _16873 _16875)). Qed.
Lemma lem1023282 {A : Type'} (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term755 A _16872 _16874 _16873 _16875) = (term757 A _16872 _16874 _16873 _16875).
Proof. exact (TRANS (@lem1023272 A _16872 _16874 _16873 _16875) (@lem1023281 A _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1023284 {A : Type'} (_16872 : A) (_16874 : A) (_16873 : A) (_16875 : A) : (term758 A _16872 _16874 _16873 _16875) = (term759 A _16872 _16874 _16873 _16875).
Proof. exact (MK_COMB (@lem1023283) (@lem1023282 A _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023285 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : ((add _16872 _16873) = (add _16874 _16875)) = ((add _16872 _16873) = (add _16874 _16875)).
Proof. exact (eq_refl ((add _16872 _16873) = (add _16874 _16875))). Qed.
Lemma lem1023286 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : (term753 A _16872 _16873 add _16874 _16875) = (term760 A _16872 _16873 add _16874 _16875).
Proof. exact (MK_COMB (@lem1023284 A _16872 _16874 _16873 _16875) (@lem1023285 A _16872 _16873 add _16874 _16875)). Qed.
Lemma lem1023287 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : (term750 A add _16872 _16874 _16873 _16875) = (term760 A _16872 _16873 add _16874 _16875).
Proof. exact (TRANS (@lem1023269 A _16872 _16873 add _16874 _16875) (@lem1023286 A _16872 _16873 add _16874 _16875)). Qed.
Lemma lem1023289 {A : Type'} (m : A) (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : term786 A m mul p n.
Proof. exact (conj (@lem1023167 A p m mul h1) (@lem1023176 A p n mul h1)). Qed.
Lemma lem1023291 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : term760 A _16872 _16873 add _16874 _16875.
Proof. exact (EQ_MP (@lem1023287 A _16872 _16873 add _16874 _16875) (@lem1023266 A add _16872 _16874 _16873 _16875)). Qed.
Lemma lem1023292 {A : Type'} (_16872 : A) (_16873 : A) (add : type1400 A) (_16874 : A) (_16875 : A) : term760 A _16872 _16873 add _16874 _16875.
Proof. exact (@lem1023291 A _16872 _16873 add _16874 _16875). Qed.
Lemma lem1023293 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (p : A) (n : A) : term787 A add m mul p n.
Proof. exact (@lem1023292 A (mul m p) (mul n p) add (mul p m) (mul p n)). Qed.
Lemma lem1023296 {A : Type'} (add : type1400 A) (m : A) (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : (term86 A add m mul n p) = (term129 A add m mul p n).
Proof. exact (@lem1023293 A add m mul p n (@lem1023289 A m p n mul h1)). Qed.
Lemma lem1023297 {A : Type'} (add : type1400 A) (m : A) (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : (term86 A add m mul n p) = (term129 A add m mul p n).
Proof. exact (@lem1023296 A add m p n mul h1). Qed.
Lemma lem1023298 {A : Type'} (add : type1400 A) (m : A) (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : term788 A add m mul p n.
Proof. exact (fun h0 : term789 A add m mul p n => @lem1023297 A add m p n mul h1). Qed.
Lemma lem1023300 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023301 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (p : A) (n : A) : (term788 A add m mul p n) = ((term86 A add m mul n p) = (term129 A add m mul p n)).
Proof. exact (@lem1023300 ((term86 A add m mul n p) = (term129 A add m mul p n))). Qed.
Lemma lem1023302 {A : Type'} (add : type1400 A) (m : A) (p : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : (term86 A add m mul n p) = (term129 A add m mul p n).
Proof. exact (EQ_MP (@lem1023301 A add m mul p n) (@lem1023298 A add m p n mul h1)). Qed.
Lemma lem1023304 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1023305 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1023304 A x). Qed.
Lemma lem1023306 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term86 A add m mul n p) = (term86 A add m mul n p).
Proof. exact (@lem1023305 A (term86 A add m mul n p)). Qed.
Lemma lem1023307 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : term790 A add m mul n p.
Proof. exact (fun h0 : term791 A add m mul n p => @lem1023306 A add m mul n p). Qed.
Lemma lem1023309 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023310 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term790 A add m mul n p) = ((term86 A add m mul n p) = (term86 A add m mul n p)).
Proof. exact (@lem1023309 ((term86 A add m mul n p) = (term86 A add m mul n p))). Qed.
Lemma lem1023311 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term86 A add m mul n p) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023310 A add m mul n p) (@lem1023307 A add m mul n p)). Qed.
Lemma lem1023312 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : term792 A add m mul n p.
Proof. exact (conj (@lem1023302 A add m p n mul h1) (@lem1023311 A add m mul n p)). Qed.
Lemma lem1023314 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1023143 A x y z) (@lem1023122 A y x z)). Qed.
Lemma lem1023315 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1023314 A x y z). Qed.
Lemma lem1023316 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : term793 A add m mul n p.
Proof. exact (@lem1023315 A (term86 A add m mul n p) (term129 A add m mul p n) (term86 A add m mul n p)). Qed.
Lemma lem1023319 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term129 A add m mul p n) = (term86 A add m mul n p).
Proof. exact (@lem1023316 A add m mul n p (@lem1023312 A add m n p mul h1)). Qed.
Lemma lem1023320 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term129 A add m mul p n) = (term86 A add m mul n p).
Proof. exact (@lem1023319 A add m n p mul h1). Qed.
Lemma lem1023321 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : term794 A add m mul n p.
Proof. exact (fun h0 : term795 A add m mul n p => @lem1023320 A add m n p mul h1). Qed.
Lemma lem1023323 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023324 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term794 A add m mul n p) = ((term129 A add m mul p n) = (term86 A add m mul n p)).
Proof. exact (@lem1023323 ((term129 A add m mul p n) = (term86 A add m mul n p))). Qed.
Lemma lem1023325 {A : Type'} (add : type1400 A) (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term11 A mul) : (term129 A add m mul p n) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023324 A add m mul n p) (@lem1023321 A add m n p mul h1)). Qed.
Lemma lem1023326 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : term796 A add m mul n p.
Proof. exact (conj (@lem1023158 A m n p add mul h1 h2) (@lem1023325 A add m n p mul h2)). Qed.
Lemma lem1023328 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1023143 A x y z) (@lem1023122 A y x z)). Qed.
Lemma lem1023329 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1023328 A x y z). Qed.
Lemma lem1023330 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : term797 A add m mul n p.
Proof. exact (@lem1023329 A (term129 A add m mul p n) (term85 A mul add m n p) (term86 A add m mul n p)). Qed.
Lemma lem1023333 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (@lem1023330 A add m mul n p (@lem1023326 A m n p add mul h1 h2)). Qed.
Lemma lem1023334 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (@lem1023333 A m n p add mul h1 h2). Qed.
Lemma lem1023335 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : term798 A add m mul n p.
Proof. exact (fun h0 : term215 A add m mul n p => @lem1023334 A m n p add mul h1 h2). Qed.
Lemma lem1023337 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023338 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term798 A add m mul n p) = ((term85 A mul add m n p) = (term86 A add m mul n p)).
Proof. exact (@lem1023337 ((term85 A mul add m n p) = (term86 A add m mul n p))). Qed.
Lemma lem1023339 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) (h2 : term11 A mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023338 A add m mul n p) (@lem1023335 A m n p add mul h1 h2)). Qed.
Lemma lem1023342 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1023344 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term215 A add m mul n p) = (term799 A add m mul n p).
Proof. exact (@lem1023342 ((term85 A mul add m n p) = (term86 A add m mul n p))). Qed.
Lemma lem1023347 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term215 A add m mul n p) : term799 A add m mul n p.
Proof. exact (EQ_MP (@lem1023344 A add m mul n p) (@lem1021302 A add m mul n p h1)). Qed.
Lemma lem1023350 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : False.
Proof. exact (@lem1023347 A add m mul n p h3 (@lem1023339 A m n p add mul h1 h2)). Qed.
Lemma lem1023351 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : term706.
Proof. exact (fun h0 : ~ False => @lem1023350 A add m mul n p h1 h2 h3). Qed.
Lemma lem1023353 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023354 : term706 = False.
Proof. exact (@lem1023353 False). Qed.
Lemma lem1023355 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : False.
Proof. exact (EQ_MP (@lem1023354) (@lem1023351 A add m mul n p h1 h2 h3)). Qed.
Lemma lem1023418 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1023422 {A : Type'} (_16739 : A) (_16738 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16738 _16739) = (mul _16739 _16738).
Proof. exact (EQ_MP (@lem1021101 A mul _16739 _16738) (@lem1021100 A _16738 _16739 mul h1)). Qed.
Lemma lem1023423 {A : Type'} (_16739 : A) (_16738 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16738 _16739) = (mul _16739 _16738).
Proof. exact (@lem1023422 A _16739 _16738 mul h1). Qed.
Lemma lem1023424 {A : Type'} (m : A) (r1 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul r1 m) = (mul m r1).
Proof. exact (@lem1023423 A m r1 mul h1). Qed.
Lemma lem1023425 {A : Type'} (m : A) (r1 : A) (mul : type1400 A) (h1 : term11 A mul) : term703 A mul m r1.
Proof. exact (fun h0 : term148 A mul m r1 => @lem1023424 A m r1 mul h1). Qed.
Lemma lem1023427 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023428 {A : Type'} (mul : type1400 A) (m : A) (r1 : A) : (term703 A mul m r1) = ((mul r1 m) = (mul m r1)).
Proof. exact (@lem1023427 ((mul r1 m) = (mul m r1))). Qed.
Lemma lem1023429 {A : Type'} (m : A) (r1 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul r1 m) = (mul m r1).
Proof. exact (EQ_MP (@lem1023428 A mul m r1) (@lem1023425 A m r1 mul h1)). Qed.
Lemma lem1023431 {A : Type'} (_16740 : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 _16740) = _16740.
Proof. exact (EQ_MP (@lem1021104 A mul r1 _16740) (@lem1021103 A _16740 mul r1 h1)). Qed.
Lemma lem1023432 {A : Type'} (_16740 : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 _16740) = _16740.
Proof. exact (@lem1023431 A _16740 mul r1 h1). Qed.
Lemma lem1023433 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 m) = m.
Proof. exact (@lem1023432 A m mul r1 h1). Qed.
Lemma lem1023434 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term773 A mul r1 m.
Proof. exact (fun h0 : term237 A mul r1 m => @lem1023433 A m mul r1 h1). Qed.
Lemma lem1023436 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023437 {A : Type'} (mul : type1400 A) (r1 : A) (m : A) : (term773 A mul r1 m) = ((mul r1 m) = m).
Proof. exact (@lem1023436 ((mul r1 m) = m)). Qed.
Lemma lem1023438 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 m) = m.
Proof. exact (EQ_MP (@lem1023437 A mul r1 m) (@lem1023434 A m mul r1 h1)). Qed.
Lemma lem1023456 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1023457 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1023456 (y = z) (term714 A x z)). Qed.
Lemma lem1023467 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1023468 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1023467 A x y) (@lem1023457 A y x z)). Qed.
Lemma lem1023472 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1023473 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1023472 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1023495 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1023468 A y x z) (@lem1023473 A y x z)). Qed.
Lemma lem1023496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1023497 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1023496) (@lem1023495 A y x z)). Qed.
Lemma lem1023519 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1023520 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1023497 A y x z) (@lem1023519 A y x z)). Qed.
Lemma lem1023522 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1023523 (x : Prop) : (x = x) = True.
Proof. exact (@lem1023522 Prop x). Qed.
Lemma lem1023524 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1023523 (term718 A y x z)). Qed.
Lemma lem1023525 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1023520 A y x z) (@lem1023524 A y x z)). Qed.
Lemma lem1023526 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1023525 A y x z)). Qed.
Lemma lem1023527 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1023526 A y x z) (@lem0)). Qed.
Lemma lem1023528 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1023527 A y x z) (@lem1023418 A x y z)). Qed.
Lemma lem1023530 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1023531 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1023530 (term723 A y x z) (y = z)). Qed.
Lemma lem1023533 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1023534 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1023533 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1023536 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1023537 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1023536 (x = y)). Qed.
Lemma lem1023538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1023539 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1023538) (@lem1023537 A x y)). Qed.
Lemma lem1023541 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1023542 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1023541 (x = z)). Qed.
Lemma lem1023543 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1023539 A x y) (@lem1023542 A x z)). Qed.
Lemma lem1023544 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1023534 A y x z) (@lem1023543 A y x z)). Qed.
Lemma lem1023545 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1023546 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1023545) (@lem1023544 A y x z)). Qed.
Lemma lem1023547 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1023548 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1023546 A y x z) (@lem1023547 A y z)). Qed.
Lemma lem1023549 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1023531 A x y z) (@lem1023548 A x y z)). Qed.
Lemma lem1023551 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term11 A mul) (h2 : term13 A mul r1) : term774 A mul r1 m.
Proof. exact (conj (@lem1023429 A m r1 mul h1) (@lem1023438 A m mul r1 h2)). Qed.
Lemma lem1023553 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1023549 A x y z) (@lem1023528 A y x z)). Qed.
Lemma lem1023554 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1023553 A x y z). Qed.
Lemma lem1023555 {A : Type'} (mul : type1400 A) (r1 : A) (m : A) : term775 A mul r1 m.
Proof. exact (@lem1023554 A (mul r1 m) (mul m r1) m). Qed.
Lemma lem1023558 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term11 A mul) (h2 : term13 A mul r1) : (mul m r1) = m.
Proof. exact (@lem1023555 A mul r1 m (@lem1023551 A m mul r1 h1 h2)). Qed.
Lemma lem1023559 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term11 A mul) (h2 : term13 A mul r1) : (mul m r1) = m.
Proof. exact (@lem1023558 A m mul r1 h1 h2). Qed.
Lemma lem1023560 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term11 A mul) (h2 : term13 A mul r1) : term776 A mul r1 m.
Proof. exact (fun h0 : term207 A mul r1 m => @lem1023559 A m mul r1 h1 h2). Qed.
Lemma lem1023562 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023563 {A : Type'} (mul : type1400 A) (r1 : A) (m : A) : (term776 A mul r1 m) = ((mul m r1) = m).
Proof. exact (@lem1023562 ((mul m r1) = m)). Qed.
Lemma lem1023564 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term11 A mul) (h2 : term13 A mul r1) : (mul m r1) = m.
Proof. exact (EQ_MP (@lem1023563 A mul r1 m) (@lem1023560 A m mul r1 h1 h2)). Qed.
Lemma lem1023566 {A : Type'} (_16739 : A) (_16738 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16738 _16739) = (mul _16739 _16738).
Proof. exact (EQ_MP (@lem1021101 A mul _16739 _16738) (@lem1021100 A _16738 _16739 mul h1)). Qed.
Lemma lem1023567 {A : Type'} (_16739 : A) (_16738 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul _16738 _16739) = (mul _16739 _16738).
Proof. exact (@lem1023566 A _16739 _16738 mul h1). Qed.
Lemma lem1023568 {A : Type'} (m : A) (r0 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul r0 m) = (mul m r0).
Proof. exact (@lem1023567 A m r0 mul h1). Qed.
Lemma lem1023569 {A : Type'} (m : A) (r0 : A) (mul : type1400 A) (h1 : term11 A mul) : term703 A mul m r0.
Proof. exact (fun h0 : term148 A mul m r0 => @lem1023568 A m r0 mul h1). Qed.
Lemma lem1023571 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023572 {A : Type'} (mul : type1400 A) (m : A) (r0 : A) : (term703 A mul m r0) = ((mul r0 m) = (mul m r0)).
Proof. exact (@lem1023571 ((mul r0 m) = (mul m r0))). Qed.
Lemma lem1023573 {A : Type'} (m : A) (r0 : A) (mul : type1400 A) (h1 : term11 A mul) : (mul r0 m) = (mul m r0).
Proof. exact (EQ_MP (@lem1023572 A mul m r0) (@lem1023569 A m r0 mul h1)). Qed.
Lemma lem1023575 {A : Type'} (_16741 : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 _16741) = r0.
Proof. exact (EQ_MP (@lem1021107 A mul _16741 r0) (@lem1021106 A _16741 mul r0 h1)). Qed.
Lemma lem1023576 {A : Type'} (_16741 : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 _16741) = r0.
Proof. exact (@lem1023575 A _16741 mul r0 h1). Qed.
Lemma lem1023577 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 m) = r0.
Proof. exact (@lem1023576 A m mul r0 h1). Qed.
Lemma lem1023578 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term776 A mul m r0.
Proof. exact (fun h0 : term207 A mul m r0 => @lem1023577 A m mul r0 h1). Qed.
Lemma lem1023580 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023581 {A : Type'} (mul : type1400 A) (m : A) (r0 : A) : (term776 A mul m r0) = ((mul r0 m) = r0).
Proof. exact (@lem1023580 ((mul r0 m) = r0)). Qed.
Lemma lem1023582 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 m) = r0.
Proof. exact (EQ_MP (@lem1023581 A mul m r0) (@lem1023578 A m mul r0 h1)). Qed.
Lemma lem1023583 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) : term800 A mul m r0.
Proof. exact (conj (@lem1023573 A m r0 mul h1) (@lem1023582 A m mul r0 h2)). Qed.
Lemma lem1023585 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1023549 A x y z) (@lem1023528 A y x z)). Qed.
Lemma lem1023586 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1023585 A x y z). Qed.
Lemma lem1023587 {A : Type'} (mul : type1400 A) (m : A) (r0 : A) : term801 A mul m r0.
Proof. exact (@lem1023586 A (mul r0 m) (mul m r0) r0). Qed.
Lemma lem1023590 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) : (mul m r0) = r0.
Proof. exact (@lem1023587 A mul m r0 (@lem1023583 A m mul r0 h1 h2)). Qed.
Lemma lem1023591 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) : (mul m r0) = r0.
Proof. exact (@lem1023590 A m mul r0 h1 h2). Qed.
Lemma lem1023592 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) : term773 A mul m r0.
Proof. exact (fun h0 : term237 A mul m r0 => @lem1023591 A m mul r0 h1 h2). Qed.
Lemma lem1023594 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023595 {A : Type'} (mul : type1400 A) (m : A) (r0 : A) : (term773 A mul m r0) = ((mul m r0) = r0).
Proof. exact (@lem1023594 ((mul m r0) = r0)). Qed.
Lemma lem1023596 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) : (mul m r0) = r0.
Proof. exact (EQ_MP (@lem1023595 A mul m r0) (@lem1023592 A m mul r0 h1 h2)). Qed.
Lemma lem1023598 (a : Prop) (b : Prop) : (term802 a b) = (term803 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1023599 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term293 A r1 mul m r0) = (term804 A r1 mul m r0).
Proof. exact (@lem1023598 ((mul m r1) = m) ((mul m r0) = r0)). Qed.
Lemma lem1023601 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1023602 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term804 A r1 mul m r0) = (term805 A r1 mul m r0).
Proof. exact (@lem1023601 (term806 A r1 mul m r0)). Qed.
Lemma lem1023603 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) : (term293 A r1 mul m r0) = (term805 A r1 mul m r0).
Proof. exact (TRANS (@lem1023599 A r1 mul m r0) (@lem1023602 A r1 mul m r0)). Qed.
Lemma lem1023605 {A : Type'} (m : A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) : term806 A r1 mul m r0.
Proof. exact (conj (@lem1023564 A m mul r1 h1 h3) (@lem1023596 A m mul r0 h1 h2)). Qed.
Lemma lem1023607 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term293 A r1 mul m r0) : term805 A r1 mul m r0.
Proof. exact (EQ_MP (@lem1023603 A r1 mul m r0) (@lem1021328 A r1 mul m r0 h1)). Qed.
Lemma lem1023610 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (@lem1023607 A r1 mul m r0 h4 (@lem1023605 A m r0 mul r1 h1 h2 h3)). Qed.
Lemma lem1023611 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : term706.
Proof. exact (fun h0 : ~ False => @lem1023610 A r1 mul m r0 h1 h2 h3 h4). Qed.
Lemma lem1023613 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1023614 : term706 = False.
Proof. exact (@lem1023613 False). Qed.
Lemma lem1023615 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023614) (@lem1023611 A r1 mul m r0 h1 h2 h3 h4)). Qed.
Lemma lem1023616 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : (term293 A r1 mul m r0) = False.
Proof. exact (prop_ext (fun h5 : term293 A r1 mul m r0 => @lem1023615 A r1 mul m r0 h1 h2 h3 h4) (fun h5 : False => @lem1021328 A r1 mul m r0 h4)). Qed.
Lemma lem1023617 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023616 A r1 mul m r0 h1 h2 h3 h4) (@lem1021328 A r1 mul m r0 h4)). Qed.
Lemma lem1023618 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : (term215 A add m mul n p) = False.
Proof. exact (prop_ext (fun h4 : term215 A add m mul n p => @lem1023355 A add m mul n p h1 h2 h3) (fun h4 : False => @lem1021302 A add m mul n p h3)). Qed.
Lemma lem1023619 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : False.
Proof. exact (EQ_MP (@lem1023618 A add m mul n p h1 h2 h3) (@lem1021302 A add m mul n p h3)). Qed.
Lemma lem1023620 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : (term185 A n mul m p) = False.
Proof. exact (prop_ext (fun h4 : term185 A n mul m p => @lem1022949 A n mul m p h1 h2 h3) (fun h4 : False => @lem1021280 A n mul m p h3)). Qed.
Lemma lem1023621 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : False.
Proof. exact (EQ_MP (@lem1023620 A n mul m p h1 h2 h3) (@lem1021280 A n mul m p h3)). Qed.
Lemma lem1023622 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : (term163 A m mul n p) = False.
Proof. exact (prop_ext (fun h3 : term163 A m mul n p => @lem1022566 A m mul n p h1 h2) (fun h3 : False => @lem1021258 A m mul n p h2)). Qed.
Lemma lem1023623 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : False.
Proof. exact (EQ_MP (@lem1023622 A m mul n p h1 h2) (@lem1021258 A m mul n p h2)). Qed.
Lemma lem1023624 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : (term148 A mul n m) = False.
Proof. exact (prop_ext (fun h3 : term148 A mul n m => @lem1022341 A mul n m h1 h2) (fun h3 : False => @lem1021236 A mul n m h2)). Qed.
Lemma lem1023625 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : False.
Proof. exact (EQ_MP (@lem1023624 A mul n m h1 h2) (@lem1021236 A mul n m h2)). Qed.
Lemma lem1023626 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : (term207 A add r0 m) = False.
Proof. exact (prop_ext (fun h4 : term207 A add r0 m => @lem1022251 A add r0 m h1 h2 h3) (fun h4 : False => @lem1021214 A add r0 m h3)). Qed.
Lemma lem1023627 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : False.
Proof. exact (EQ_MP (@lem1023626 A add r0 m h1 h2 h3) (@lem1021214 A add r0 m h3)). Qed.
Lemma lem1023628 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : (term185 A n add m p) = False.
Proof. exact (prop_ext (fun h4 : term185 A n add m p => @lem1022026 A n add m p h1 h2 h3) (fun h4 : False => @lem1021192 A n add m p h3)). Qed.
Lemma lem1023629 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : False.
Proof. exact (EQ_MP (@lem1023628 A n add m p h1 h2 h3) (@lem1021192 A n add m p h3)). Qed.
Lemma lem1023630 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : (term163 A m add n p) = False.
Proof. exact (prop_ext (fun h3 : term163 A m add n p => @lem1021643 A m add n p h1 h2) (fun h3 : False => @lem1021170 A m add n p h2)). Qed.
Lemma lem1023631 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : False.
Proof. exact (EQ_MP (@lem1023630 A m add n p h1 h2) (@lem1021170 A m add n p h2)). Qed.
Lemma lem1023632 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : (term148 A add n m) = False.
Proof. exact (prop_ext (fun h3 : term148 A add n m => @lem1021418 A add n m h1 h2) (fun h3 : False => @lem1021148 A add n m h2)). Qed.
Lemma lem1023633 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : False.
Proof. exact (EQ_MP (@lem1023632 A add n m h1 h2) (@lem1021148 A add n m h2)). Qed.
Lemma lem1023634 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : (term293 A r1 mul m r0) = False.
Proof. exact (prop_ext (fun h5 : term293 A r1 mul m r0 => @lem1023617 A r1 mul m r0 h1 h2 h3 h4) (fun h5 : False => @lem1020613 A r1 mul m r0 h4)). Qed.
Lemma lem1023635 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023634 A r1 mul m r0 h1 h2 h3 h4) (@lem1020613 A r1 mul m r0 h4)). Qed.
Lemma lem1023636 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : (term215 A add m mul n p) = False.
Proof. exact (prop_ext (fun h4 : term215 A add m mul n p => @lem1023619 A add m mul n p h1 h2 h3) (fun h4 : False => @lem1020506 A add m mul n p h3)). Qed.
Lemma lem1023637 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : False.
Proof. exact (EQ_MP (@lem1023636 A add m mul n p h1 h2 h3) (@lem1020506 A add m mul n p h3)). Qed.
Lemma lem1023638 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : (term185 A n mul m p) = False.
Proof. exact (prop_ext (fun h4 : term185 A n mul m p => @lem1023621 A n mul m p h1 h2 h3) (fun h4 : False => @lem1020405 A n mul m p h3)). Qed.
Lemma lem1023639 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : False.
Proof. exact (EQ_MP (@lem1023638 A n mul m p h1 h2 h3) (@lem1020405 A n mul m p h3)). Qed.
Lemma lem1023640 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : (term163 A m mul n p) = False.
Proof. exact (prop_ext (fun h3 : term163 A m mul n p => @lem1023623 A m mul n p h1 h2) (fun h3 : False => @lem1020304 A m mul n p h2)). Qed.
Lemma lem1023641 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : False.
Proof. exact (EQ_MP (@lem1023640 A m mul n p h1 h2) (@lem1020304 A m mul n p h2)). Qed.
Lemma lem1023642 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : (term148 A mul n m) = False.
Proof. exact (prop_ext (fun h3 : term148 A mul n m => @lem1023625 A mul n m h1 h2) (fun h3 : False => @lem1020203 A mul n m h2)). Qed.
Lemma lem1023643 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : False.
Proof. exact (EQ_MP (@lem1023642 A mul n m h1 h2) (@lem1020203 A mul n m h2)). Qed.
Lemma lem1023644 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : (term207 A add r0 m) = False.
Proof. exact (prop_ext (fun h4 : term207 A add r0 m => @lem1023627 A add r0 m h1 h2 h3) (fun h4 : False => @lem1020102 A add r0 m h3)). Qed.
Lemma lem1023645 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : False.
Proof. exact (EQ_MP (@lem1023644 A add r0 m h1 h2 h3) (@lem1020102 A add r0 m h3)). Qed.
Lemma lem1023646 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : (term185 A n add m p) = False.
Proof. exact (prop_ext (fun h4 : term185 A n add m p => @lem1023629 A n add m p h1 h2 h3) (fun h4 : False => @lem1020001 A n add m p h3)). Qed.
Lemma lem1023647 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : False.
Proof. exact (EQ_MP (@lem1023646 A n add m p h1 h2 h3) (@lem1020001 A n add m p h3)). Qed.
Lemma lem1023648 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : (term163 A m add n p) = False.
Proof. exact (prop_ext (fun h3 : term163 A m add n p => @lem1023631 A m add n p h1 h2) (fun h3 : False => @lem1019900 A m add n p h2)). Qed.
Lemma lem1023649 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : False.
Proof. exact (EQ_MP (@lem1023648 A m add n p h1 h2) (@lem1019900 A m add n p h2)). Qed.
Lemma lem1023650 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : (term148 A add n m) = False.
Proof. exact (prop_ext (fun h3 : term148 A add n m => @lem1023633 A add n m h1 h2) (fun h3 : False => @lem1019799 A add n m h2)). Qed.
Lemma lem1023651 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : False.
Proof. exact (EQ_MP (@lem1023650 A add n m h1 h2) (@lem1019799 A add n m h2)). Qed.
Lemma lem1023652 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : (term293 A r1 mul m r0) = False.
Proof. exact (prop_ext (fun h5 : term293 A r1 mul m r0 => @lem1023635 A r1 mul m r0 h1 h2 h3 h4) (fun h5 : False => @lem1020613 A r1 mul m r0 h4)). Qed.
Lemma lem1023653 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023652 A r1 mul m r0 h1 h2 h3 h4) (@lem1020613 A r1 mul m r0 h4)). Qed.
Lemma lem1023654 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : (term18 A mul r0) = False.
Proof. exact (prop_ext (fun h5 : term18 A mul r0 => @lem1023653 A r1 mul m r0 h1 h2 h3 h4) (fun h5 : False => @lem1020573 A mul r0 h2)). Qed.
Lemma lem1023655 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023654 A r1 mul m r0 h1 h2 h3 h4) (@lem1020573 A mul r0 h2)). Qed.
Lemma lem1023656 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : (term13 A mul r1) = False.
Proof. exact (prop_ext (fun h5 : term13 A mul r1 => @lem1023655 A r1 mul m r0 h1 h2 h3 h4) (fun h5 : False => @lem1020566 A mul r1 h3)). Qed.
Lemma lem1023657 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023656 A r1 mul m r0 h1 h2 h3 h4) (@lem1020566 A mul r1 h3)). Qed.
Lemma lem1023658 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : (term11 A mul) = False.
Proof. exact (prop_ext (fun h5 : term11 A mul => @lem1023657 A r1 mul m r0 h1 h2 h3 h4) (fun h5 : False => @lem1020559 A mul h1)). Qed.
Lemma lem1023659 {A : Type'} (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term11 A mul) (h2 : term18 A mul r0) (h3 : term13 A mul r1) (h4 : term293 A r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023658 A r1 mul m r0 h1 h2 h3 h4) (@lem1020559 A mul h1)). Qed.
Lemma lem1023660 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : (term215 A add m mul n p) = False.
Proof. exact (prop_ext (fun h4 : term215 A add m mul n p => @lem1023637 A add m mul n p h1 h2 h3) (fun h4 : False => @lem1020506 A add m mul n p h3)). Qed.
Lemma lem1023661 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : False.
Proof. exact (EQ_MP (@lem1023660 A add m mul n p h1 h2 h3) (@lem1020506 A add m mul n p h3)). Qed.
Lemma lem1023662 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : (term20 A add mul) = False.
Proof. exact (prop_ext (fun h4 : term20 A add mul => @lem1023661 A add m mul n p h1 h2 h3) (fun h4 : False => @lem1020485 A add mul h1)). Qed.
Lemma lem1023663 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : False.
Proof. exact (EQ_MP (@lem1023662 A add m mul n p h1 h2 h3) (@lem1020485 A add mul h1)). Qed.
Lemma lem1023664 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : (term11 A mul) = False.
Proof. exact (prop_ext (fun h4 : term11 A mul => @lem1023663 A add m mul n p h1 h2 h3) (fun h4 : False => @lem1020458 A mul h2)). Qed.
Lemma lem1023665 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term215 A add m mul n p) : False.
Proof. exact (EQ_MP (@lem1023664 A add m mul n p h1 h2 h3) (@lem1020458 A mul h2)). Qed.
Lemma lem1023666 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : (term185 A n mul m p) = False.
Proof. exact (prop_ext (fun h4 : term185 A n mul m p => @lem1023639 A n mul m p h1 h2 h3) (fun h4 : False => @lem1020405 A n mul m p h3)). Qed.
Lemma lem1023667 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : False.
Proof. exact (EQ_MP (@lem1023666 A n mul m p h1 h2 h3) (@lem1020405 A n mul m p h3)). Qed.
Lemma lem1023668 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : (term11 A mul) = False.
Proof. exact (prop_ext (fun h4 : term11 A mul => @lem1023667 A n mul m p h1 h2 h3) (fun h4 : False => @lem1020357 A mul h2)). Qed.
Lemma lem1023669 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : False.
Proof. exact (EQ_MP (@lem1023668 A n mul m p h1 h2 h3) (@lem1020357 A mul h2)). Qed.
Lemma lem1023670 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : (term9 A mul) = False.
Proof. exact (prop_ext (fun h4 : term9 A mul => @lem1023669 A n mul m p h1 h2 h3) (fun h4 : False => @lem1020347 A mul h1)). Qed.
Lemma lem1023671 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) (h1 : term9 A mul) (h2 : term11 A mul) (h3 : term185 A n mul m p) : False.
Proof. exact (EQ_MP (@lem1023670 A n mul m p h1 h2 h3) (@lem1020347 A mul h1)). Qed.
Lemma lem1023672 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : (term163 A m mul n p) = False.
Proof. exact (prop_ext (fun h3 : term163 A m mul n p => @lem1023641 A m mul n p h1 h2) (fun h3 : False => @lem1020304 A m mul n p h2)). Qed.
Lemma lem1023673 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : False.
Proof. exact (EQ_MP (@lem1023672 A m mul n p h1 h2) (@lem1020304 A m mul n p h2)). Qed.
Lemma lem1023674 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : (term9 A mul) = False.
Proof. exact (prop_ext (fun h3 : term9 A mul => @lem1023673 A m mul n p h1 h2) (fun h3 : False => @lem1020246 A mul h1)). Qed.
Lemma lem1023675 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) (h1 : term9 A mul) (h2 : term163 A m mul n p) : False.
Proof. exact (EQ_MP (@lem1023674 A m mul n p h1 h2) (@lem1020246 A mul h1)). Qed.
Lemma lem1023676 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : (term148 A mul n m) = False.
Proof. exact (prop_ext (fun h3 : term148 A mul n m => @lem1023643 A mul n m h1 h2) (fun h3 : False => @lem1020203 A mul n m h2)). Qed.
Lemma lem1023677 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : False.
Proof. exact (EQ_MP (@lem1023676 A mul n m h1 h2) (@lem1020203 A mul n m h2)). Qed.
Lemma lem1023678 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : (term11 A mul) = False.
Proof. exact (prop_ext (fun h3 : term11 A mul => @lem1023677 A mul n m h1 h2) (fun h3 : False => @lem1020155 A mul h1)). Qed.
Lemma lem1023679 {A : Type'} (mul : type1400 A) (n : A) (m : A) (h1 : term11 A mul) (h2 : term148 A mul n m) : False.
Proof. exact (EQ_MP (@lem1023678 A mul n m h1 h2) (@lem1020155 A mul h1)). Qed.
Lemma lem1023680 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : (term207 A add r0 m) = False.
Proof. exact (prop_ext (fun h4 : term207 A add r0 m => @lem1023645 A add r0 m h1 h2 h3) (fun h4 : False => @lem1020102 A add r0 m h3)). Qed.
Lemma lem1023681 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : False.
Proof. exact (EQ_MP (@lem1023680 A add r0 m h1 h2 h3) (@lem1020102 A add r0 m h3)). Qed.
Lemma lem1023682 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : (term13 A add r0) = False.
Proof. exact (prop_ext (fun h4 : term13 A add r0 => @lem1023681 A add r0 m h1 h2 h3) (fun h4 : False => @lem1020031 A add r0 h2)). Qed.
Lemma lem1023683 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : False.
Proof. exact (EQ_MP (@lem1023682 A add r0 m h1 h2 h3) (@lem1020031 A add r0 h2)). Qed.
Lemma lem1023684 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : (term11 A add) = False.
Proof. exact (prop_ext (fun h4 : term11 A add => @lem1023683 A add r0 m h1 h2 h3) (fun h4 : False => @lem1020024 A add h1)). Qed.
Lemma lem1023685 {A : Type'} (add : type1400 A) (r0 : A) (m : A) (h1 : term11 A add) (h2 : term13 A add r0) (h3 : term207 A add r0 m) : False.
Proof. exact (EQ_MP (@lem1023684 A add r0 m h1 h2 h3) (@lem1020024 A add h1)). Qed.
Lemma lem1023686 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : (term185 A n add m p) = False.
Proof. exact (prop_ext (fun h4 : term185 A n add m p => @lem1023647 A n add m p h1 h2 h3) (fun h4 : False => @lem1020001 A n add m p h3)). Qed.
Lemma lem1023687 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : False.
Proof. exact (EQ_MP (@lem1023686 A n add m p h1 h2 h3) (@lem1020001 A n add m p h3)). Qed.
Lemma lem1023688 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : (term11 A add) = False.
Proof. exact (prop_ext (fun h4 : term11 A add => @lem1023687 A n add m p h1 h2 h3) (fun h4 : False => @lem1019923 A add h2)). Qed.
Lemma lem1023689 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : False.
Proof. exact (EQ_MP (@lem1023688 A n add m p h1 h2 h3) (@lem1019923 A add h2)). Qed.
Lemma lem1023690 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : (term9 A add) = False.
Proof. exact (prop_ext (fun h4 : term9 A add => @lem1023689 A n add m p h1 h2 h3) (fun h4 : False => @lem1019913 A add h1)). Qed.
Lemma lem1023691 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term185 A n add m p) : False.
Proof. exact (EQ_MP (@lem1023690 A n add m p h1 h2 h3) (@lem1019913 A add h1)). Qed.
Lemma lem1023692 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : (term163 A m add n p) = False.
Proof. exact (prop_ext (fun h3 : term163 A m add n p => @lem1023649 A m add n p h1 h2) (fun h3 : False => @lem1019900 A m add n p h2)). Qed.
Lemma lem1023693 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : False.
Proof. exact (EQ_MP (@lem1023692 A m add n p h1 h2) (@lem1019900 A m add n p h2)). Qed.
Lemma lem1023694 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : (term9 A add) = False.
Proof. exact (prop_ext (fun h3 : term9 A add => @lem1023693 A m add n p h1 h2) (fun h3 : False => @lem1019812 A add h1)). Qed.
Lemma lem1023695 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) (h1 : term9 A add) (h2 : term163 A m add n p) : False.
Proof. exact (EQ_MP (@lem1023694 A m add n p h1 h2) (@lem1019812 A add h1)). Qed.
Lemma lem1023696 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : (term148 A add n m) = False.
Proof. exact (prop_ext (fun h3 : term148 A add n m => @lem1023651 A add n m h1 h2) (fun h3 : False => @lem1019799 A add n m h2)). Qed.
Lemma lem1023697 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : False.
Proof. exact (EQ_MP (@lem1023696 A add n m h1 h2) (@lem1019799 A add n m h2)). Qed.
Lemma lem1023698 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : (term11 A add) = False.
Proof. exact (prop_ext (fun h3 : term11 A add => @lem1023697 A add n m h1 h2) (fun h3 : False => @lem1019721 A add h1)). Qed.
Lemma lem1023699 {A : Type'} (add : type1400 A) (n : A) (m : A) (h1 : term11 A add) (h2 : term148 A add n m) : False.
Proof. exact (EQ_MP (@lem1023698 A add n m h1 h2) (@lem1019721 A add h1)). Qed.
Lemma lem1023700 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term18 A mul r0) (h4 : term13 A mul r1) (h5 : term347 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019696 A add n p r1 mul m r0 h5) (fun h0 : term215 A add m mul n p => @lem1023665 A add m mul n p h1 h2 h0) (fun h0 : term293 A r1 mul m r0 => @lem1023659 A r1 mul m r0 h2 h3 h4 h0)). Qed.
Lemma lem1023701 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term20 A add mul) (h2 : term9 A mul) (h3 : term11 A mul) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term406 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019694 A add n p r1 mul m r0 h6) (fun h0 : term185 A n mul m p => @lem1023671 A n mul m p h2 h3 h0) (fun h0 : term347 A add n p r1 mul m r0 => @lem1023700 A add n p r1 mul m r0 h1 h3 h4 h5 h0)). Qed.
Lemma lem1023702 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term20 A add mul) (h2 : term9 A mul) (h3 : term11 A mul) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term465 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019692 A add n p r1 mul m r0 h6) (fun h0 : term163 A m mul n p => @lem1023675 A m mul n p h2 h0) (fun h0 : term406 A add n p r1 mul m r0 => @lem1023701 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem1023703 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term20 A add mul) (h2 : term9 A mul) (h3 : term11 A mul) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term520 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019690 A add n p r1 mul m r0 h6) (fun h0 : term148 A mul n m => @lem1023679 A mul n m h3 h0) (fun h0 : term465 A add n p r1 mul m r0 => @lem1023702 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h0)). Qed.
Lemma lem1023704 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term20 A add mul) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term564 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019688 A add n p r1 mul m r0 h8) (fun h0 : term207 A add r0 m => @lem1023685 A add r0 m h3 h5 h0) (fun h0 : term520 A add n p r1 mul m r0 => @lem1023703 A add n p r1 mul m r0 h1 h2 h4 h6 h7 h0)). Qed.
Lemma lem1023705 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term605 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019686 A add n p r1 mul m r0 h9) (fun h0 : term185 A n add m p => @lem1023691 A n add m p h1 h4 h0) (fun h0 : term564 A add n p r1 mul m r0 => @lem1023704 A add n p r1 mul m r0 h2 h3 h4 h5 h6 h7 h8 h0)). Qed.
Lemma lem1023706 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term646 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019684 A add n p r1 mul m r0 h9) (fun h0 : term163 A m add n p => @lem1023695 A m add n p h1 h0) (fun h0 : term605 A add n p r1 mul m r0 => @lem1023705 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h0)). Qed.
Lemma lem1023707 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (or_elim (@lem1019682 A add n p r1 mul m r0 h9) (fun h0 : term148 A add n m => @lem1023699 A add n m h4 h0) (fun h0 : term646 A add n p r1 mul m r0 => @lem1023706 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h0)). Qed.
Lemma lem1023708 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term687 A add n p r1 mul m r0) = False.
Proof. exact (prop_ext (fun h10 : term687 A add n p r1 mul m r0 => @lem1023707 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019682 A add n p r1 mul m r0 h9)). Qed.
Lemma lem1023709 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023708 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019682 A add n p r1 mul m r0 h9)). Qed.
Lemma lem1023710 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term20 A add mul) = False.
Proof. exact (prop_ext (fun h10 : term20 A add mul => @lem1023709 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019431 A add mul h2)). Qed.
Lemma lem1023711 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023710 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019431 A add mul h2)). Qed.
Lemma lem1023712 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term18 A mul r0) = False.
Proof. exact (prop_ext (fun h10 : term18 A mul r0 => @lem1023711 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019396 A mul r0 h7)). Qed.
Lemma lem1023713 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023712 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019396 A mul r0 h7)). Qed.
Lemma lem1023714 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term13 A mul r1) = False.
Proof. exact (prop_ext (fun h10 : term13 A mul r1 => @lem1023713 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019383 A mul r1 h8)). Qed.
Lemma lem1023715 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023714 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019383 A mul r1 h8)). Qed.
Lemma lem1023716 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term11 A mul) = False.
Proof. exact (prop_ext (fun h10 : term11 A mul => @lem1023715 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019370 A mul h5)). Qed.
Lemma lem1023717 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023716 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019370 A mul h5)). Qed.
Lemma lem1023718 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term9 A mul) = False.
Proof. exact (prop_ext (fun h10 : term9 A mul => @lem1023717 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019350 A mul h3)). Qed.
Lemma lem1023719 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023718 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019350 A mul h3)). Qed.
Lemma lem1023720 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term13 A add r0) = False.
Proof. exact (prop_ext (fun h10 : term13 A add r0 => @lem1023719 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019319 A add r0 h6)). Qed.
Lemma lem1023721 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023720 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019319 A add r0 h6)). Qed.
Lemma lem1023722 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term11 A add) = False.
Proof. exact (prop_ext (fun h10 : term11 A add => @lem1023721 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019306 A add h4)). Qed.
Lemma lem1023723 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023722 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019306 A add h4)). Qed.
Lemma lem1023724 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : (term9 A add) = False.
Proof. exact (prop_ext (fun h10 : term9 A add => @lem1023723 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1019286 A add h1)). Qed.
Lemma lem1023725 {A : Type'} (add : type1400 A) (n : A) (p : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term687 A add n p r1 mul m r0) : False.
Proof. exact (EQ_MP (@lem1023724 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1019286 A add h1)). Qed.
Lemma lem1023726 {A : Type'} (add : type1400 A) (n : A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term690 A add n r1 mul m r0) : False.
Proof. exact (ex_elim (@lem1019254 A add n r1 mul m r0 h9) (fun p : A => fun h0 : term689 A add n r1 mul m r0 p => @lem1023725 A add n p r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h0)). Qed.
Lemma lem1023727 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (m : A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term692 A add r1 mul m r0) : False.
Proof. exact (ex_elim (@lem1019253 A add r1 mul m r0 h9) (fun n : A => fun h0 : term691 A add r1 mul m r0 n => @lem1023726 A add n r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h0)). Qed.
Lemma lem1023728 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (ex_elim (@lem1019252 A add r1 mul r0 h9) (fun m : A => fun h0 : term693 A add r1 mul r0 m => @lem1023727 A add r1 mul m r0 h1 h2 h3 h4 h5 h6 h7 h8 h0)). Qed.
Lemma lem1023729 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term20 A add mul) = False.
Proof. exact (prop_ext (fun h10 : term20 A add mul => @lem1023728 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1018095 A add mul h2)). Qed.
Lemma lem1023730 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023729 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1018095 A add mul h2)). Qed.
Lemma lem1023731 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term18 A mul r0) = False.
Proof. exact (prop_ext (fun h10 : term18 A mul r0 => @lem1023730 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1018068 A mul r0 h7)). Qed.
Lemma lem1023732 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023731 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1018068 A mul r0 h7)). Qed.
Lemma lem1023733 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term13 A mul r1) = False.
Proof. exact (prop_ext (fun h10 : term13 A mul r1 => @lem1023732 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1018055 A mul r1 h8)). Qed.
Lemma lem1023734 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023733 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1018055 A mul r1 h8)). Qed.
Lemma lem1023735 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term11 A mul) = False.
Proof. exact (prop_ext (fun h10 : term11 A mul => @lem1023734 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1018042 A mul h5)). Qed.
Lemma lem1023736 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023735 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1018042 A mul h5)). Qed.
Lemma lem1023737 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term9 A mul) = False.
Proof. exact (prop_ext (fun h10 : term9 A mul => @lem1023736 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1018022 A mul h3)). Qed.
Lemma lem1023738 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023737 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1018022 A mul h3)). Qed.
Lemma lem1023739 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term13 A add r0) = False.
Proof. exact (prop_ext (fun h10 : term13 A add r0 => @lem1023738 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1017995 A add r0 h6)). Qed.
Lemma lem1023740 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023739 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1017995 A add r0 h6)). Qed.
Lemma lem1023741 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term11 A add) = False.
Proof. exact (prop_ext (fun h10 : term11 A add => @lem1023740 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1017982 A add h4)). Qed.
Lemma lem1023742 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023741 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1017982 A add h4)). Qed.
Lemma lem1023743 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term9 A add) = False.
Proof. exact (prop_ext (fun h10 : term9 A add => @lem1023742 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1017962 A add h1)). Qed.
Lemma lem1023744 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023743 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1017962 A add h1)). Qed.
Lemma lem1023745 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : (term26 A add r1 mul r0) = False.
Proof. exact (prop_ext (fun h10 : term26 A add r1 mul r0 => @lem1023744 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : False => @lem1017935 A add r1 mul r0 h9)). Qed.
Lemma lem1023746 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023745 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1017935 A add r1 mul r0 h9)). Qed.
Lemma lem1023747 {A : Type'} (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) : term25 A add r1 mul r0.
Proof. exact (fun h0 : term26 A add r1 mul r0 => @lem1023746 A add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h0). Qed.
Lemma lem1023748 {A : Type'} (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) : term23 A add r1 mul r0.
Proof. exact (EQ_MP (@lem1017934 A add r1 mul r0) (@lem1023747 A add r0 mul r1 h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1023749 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) : term35 A pwr add r1 mul r0.
Proof. exact (fun h0 : term21 A mul pwr => @lem1023748 A add r0 mul r1 h1 h2 h3 h4 h5 h6 h7 h8). Qed.
Lemma lem1023750 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) : term38 A pwr add r1 mul r0.
Proof. exact (fun h0 : term22 A pwr r1 => @lem1023749 A pwr add r0 mul r1 h1 h2 h3 h4 h5 h6 h7 h8). Qed.
Lemma lem1023751 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) : term41 A pwr add r1 mul r0.
Proof. exact (fun h0 : term20 A add mul => @lem1023750 A pwr add r0 mul r1 h1 h0 h2 h3 h4 h5 h6 h7). Qed.
Lemma lem1023752 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) : term44 A pwr add r1 mul r0.
Proof. exact (fun h0 : term18 A mul r0 => @lem1023751 A pwr add r0 mul r1 h1 h2 h3 h4 h5 h0 h6). Qed.
Lemma lem1023753 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (add : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) : term47 A pwr add r1 mul r0.
Proof. exact (fun h0 : term13 A mul r1 => @lem1023752 A pwr add r0 mul r1 h1 h2 h3 h4 h5 h0). Qed.
Lemma lem1023754 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (add : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) : term50 A pwr add r1 mul r0.
Proof. exact (fun h0 : term11 A mul => @lem1023753 A pwr r1 mul add r0 h1 h2 h3 h0 h4). Qed.
Lemma lem1023755 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (add : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) : term53 A pwr add r1 mul r0.
Proof. exact (fun h0 : term9 A mul => @lem1023754 A pwr r1 mul add r0 h1 h0 h2 h3). Qed.
Lemma lem1023756 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : term55 A pwr add r1 mul r0.
Proof. exact (fun h0 : term13 A add r0 => @lem1023755 A pwr r1 mul add r0 h1 h2 h0). Qed.
Lemma lem1023757 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (add : type1400 A) (h1 : term9 A add) : term57 A pwr add r1 mul r0.
Proof. exact (fun h0 : term11 A add => @lem1023756 A pwr r1 mul r0 add h1 h0). Qed.
Lemma lem1023758 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term58 A pwr add r1 mul r0.
Proof. exact (fun h0 : term9 A add => @lem1023757 A pwr r1 mul r0 add h0). Qed.
Lemma lem1023763 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term62 A add r1 mul r0.
Proof. exact (fun pwr : type1423 A => @lem1023758 A pwr add r1 mul r0). Qed.
Lemma lem1023768 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : term66 A r1 mul r0.
Proof. exact (fun add : type1400 A => @lem1023763 A add r1 mul r0). Qed.
Lemma lem1023773 {A : Type'} (mul : type1400 A) (r0 : A) : term70 A mul r0.
Proof. exact (fun r1 : A => @lem1023768 A r1 mul r0). Qed.
Lemma lem1023778 {A : Type'} (r0 : A) : term74 A r0.
Proof. exact (fun mul : type1400 A => @lem1023773 A mul r0). Qed.
Lemma lem1023783 {A : Type'} : term78 A.
Proof. exact (fun r0 : A => @lem1023778 A r0). Qed.
Lemma lem1023784 {A : Type'} : term77 A.
Proof. exact (EQ_MP (@lem1017920 A) (@lem1023783 A)). Qed.
Lemma lem1023785 {A : Type'} (r0 : A) : term807 A r0.
Proof. exact (@lem1023784 A r0). Qed.
Lemma lem1023786 {A : Type'} (r0 : A) : (term807 A r0) = (term73 A r0).
Proof. exact (eq_refl (term807 A r0)). Qed.
Lemma lem1023787 {A : Type'} (r0 : A) : term73 A r0.
Proof. exact (EQ_MP (@lem1023786 A r0) (@lem1023785 A r0)). Qed.
Lemma lem1023788 {A : Type'} (r0 : A) (mul : type1400 A) : term808 A r0 mul.
Proof. exact (@lem1023787 A r0 mul). Qed.
Lemma lem1023789 {A : Type'} (mul : type1400 A) (r0 : A) : (term808 A r0 mul) = (term69 A mul r0).
Proof. exact (eq_refl (term808 A r0 mul)). Qed.
Lemma lem1023790 {A : Type'} (mul : type1400 A) (r0 : A) : term69 A mul r0.
Proof. exact (EQ_MP (@lem1023789 A mul r0) (@lem1023788 A r0 mul)). Qed.
Lemma lem1023791 {A : Type'} (mul : type1400 A) (r0 : A) (r1 : A) : term809 A mul r0 r1.
Proof. exact (@lem1023790 A mul r0 r1). Qed.
Lemma lem1023792 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : (term809 A mul r0 r1) = (term65 A r1 mul r0).
Proof. exact (eq_refl (term809 A mul r0 r1)). Qed.
Lemma lem1023793 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) : term65 A r1 mul r0.
Proof. exact (EQ_MP (@lem1023792 A r1 mul r0) (@lem1023791 A mul r0 r1)). Qed.
Lemma lem1023794 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) (add : type1400 A) : term810 A r1 mul r0 add.
Proof. exact (@lem1023793 A r1 mul r0 add). Qed.
Lemma lem1023795 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term810 A r1 mul r0 add) = (term61 A add r1 mul r0).
Proof. exact (eq_refl (term810 A r1 mul r0 add)). Qed.
Lemma lem1023796 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term61 A add r1 mul r0.
Proof. exact (EQ_MP (@lem1023795 A add r1 mul r0) (@lem1023794 A r1 mul r0 add)). Qed.
Lemma lem1023797 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (pwr : type1423 A) : term811 A add r1 mul r0 pwr.
Proof. exact (@lem1023796 A add r1 mul r0 pwr). Qed.
Lemma lem1023798 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : (term811 A add r1 mul r0 pwr) = (term27 A pwr add r1 mul r0).
Proof. exact (eq_refl (term811 A add r1 mul r0 pwr)). Qed.
Lemma lem1023799 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term27 A pwr add r1 mul r0.
Proof. exact (EQ_MP (@lem1023798 A pwr add r1 mul r0) (@lem1023797 A add r1 mul r0 pwr)). Qed.
Lemma lem1023801 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) : term27 A pwr add r1 mul r0.
Proof. exact (@lem1017079 A pwr add r1 mul r0 (@lem1023799 A pwr add r1 mul r0)). Qed.
Lemma lem1023802 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (add : type1400 A) (h1 : term9 A add) : term56 A pwr add r1 mul r0.
Proof. exact (@lem1023801 A pwr add r1 mul r0 (@lem1017041 A add h1)). Qed.
Lemma lem1023803 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (add : type1400 A) (h1 : term9 A add) (h2 : term11 A add) : term54 A pwr add r1 mul r0.
Proof. exact (@lem1023802 A pwr r1 mul r0 add h1 (@lem1017043 A add h2)). Qed.
Lemma lem1023804 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (add : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) : term52 A pwr add r1 mul r0.
Proof. exact (@lem1023803 A pwr r1 mul r0 add h1 h2 (@lem1017045 A add r0 h3)). Qed.
Lemma lem1023805 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (add : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) : term49 A pwr add r1 mul r0.
Proof. exact (@lem1023804 A pwr r1 mul add r0 h1 h3 h4 (@lem1017047 A mul h2)). Qed.
Lemma lem1023806 {A : Type'} (pwr : type1423 A) (r1 : A) (mul : type1400 A) (add : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) : term46 A pwr add r1 mul r0.
Proof. exact (@lem1023805 A pwr r1 mul add r0 h1 h2 h3 h5 (@lem1017049 A mul h4)). Qed.
Lemma lem1023807 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) : term43 A pwr add r1 mul r0.
Proof. exact (@lem1023806 A pwr r1 mul add r0 h1 h2 h3 h4 h5 (@lem1017051 A mul r1 h6)). Qed.
Lemma lem1023808 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) : term40 A pwr add r1 mul r0.
Proof. exact (@lem1023807 A pwr add r0 mul r1 h1 h2 h3 h4 h5 h7 (@lem1017053 A mul r0 h6)). Qed.
Lemma lem1023809 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) : term37 A pwr add r1 mul r0.
Proof. exact (@lem1023808 A pwr add r0 mul r1 h1 h3 h4 h5 h6 h7 h8 (@lem1017055 A add mul h2)). Qed.
Lemma lem1023810 {A : Type'} (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) : term34 A pwr add r1 mul r0.
Proof. exact (@lem1023809 A pwr add r0 mul r1 h1 h2 h3 h4 h5 h6 h7 h8 (@lem1017057 A pwr r1 h9)). Qed.
Lemma lem1023811 {A : Type'} (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : term25 A add r1 mul r0.
Proof. exact (@lem1023810 A add r0 mul pwr r1 h1 h2 h3 h4 h5 h7 h8 h9 h10 (@lem1017056 A mul pwr h6)). Qed.
Lemma lem1023812 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term26 A add r1 mul r0) : False.
Proof. exact (@lem1023811 A add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (@lem1017063 A add r1 mul r0 h11)). Qed.
Lemma lem1023813 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term26 A add r1 mul r0) : (term26 A add r1 mul r0) = False.
Proof. exact (prop_ext (fun h12 : term26 A add r1 mul r0 => @lem1023812 A pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (fun h12 : False => @lem1017063 A add r1 mul r0 h11)). Qed.
Lemma lem1023814 {A : Type'} (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term26 A add r1 mul r0) : False.
Proof. exact (EQ_MP (@lem1023813 A pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem1017063 A add r1 mul r0 h11)). Qed.
Lemma lem1023815 {A : Type'} (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : term25 A add r1 mul r0.
Proof. exact (fun h0 : term26 A add r1 mul r0 => @lem1023814 A pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h0). Qed.
Lemma lem1023816 {A : Type'} (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : term23 A add r1 mul r0.
Proof. exact (EQ_MP (@lem1017062 A add r1 mul r0) (@lem1023815 A add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1023817 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term23 A add r1 mul r0) : term23 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023818 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term120 A add r1 mul r0) : term120 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023819 {A : Type'} (add : type1400 A) (h1 : term11 A add) : term11 A add.
Proof. exact (h1). Qed.
Lemma lem1023820 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term119 A add r1 mul r0) : term119 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023821 {A : Type'} (add : type1400 A) (h1 : term110 A add) : term110 A add.
Proof. exact (h1). Qed.
Lemma lem1023822 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term118 A add r1 mul r0) : term118 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023823 {A : Type'} (add : type1400 A) (h1 : term101 A add) : term101 A add.
Proof. exact (h1). Qed.
Lemma lem1023824 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term117 A add r1 mul r0) : term117 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023825 {A : Type'} (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : term82 A add r0.
Proof. exact (h1). Qed.
Lemma lem1023826 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term112 A add r1 mul r0) : term112 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023827 {A : Type'} (mul : type1400 A) (h1 : term11 A mul) : term11 A mul.
Proof. exact (h1). Qed.
Lemma lem1023828 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term103 A add r1 mul r0) : term103 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023829 {A : Type'} (mul : type1400 A) (h1 : term110 A mul) : term110 A mul.
Proof. exact (h1). Qed.
Lemma lem1023830 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term94 A add r1 mul r0) : term94 A add r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023831 {A : Type'} (mul : type1400 A) (h1 : term101 A mul) : term101 A mul.
Proof. exact (h1). Qed.
Lemma lem1023832 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term84 A r1 mul r0) : term84 A r1 mul r0.
Proof. exact (h1). Qed.
Lemma lem1023833 {A : Type'} (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : term92 A add mul.
Proof. exact (h1). Qed.
Lemma lem1023834 {A : Type'} (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : term80 A mul r0.
Proof. exact (h1). Qed.
Lemma lem1023835 {A : Type'} (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : term82 A mul r1.
Proof. exact (h1). Qed.
Lemma lem1023836 {A : Type'} (x : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term698 A add r0 x.
Proof. exact (@lem1017045 A add r0 h1 x). Qed.
Lemma lem1023837 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : (term698 A add r0 x) = ((add r0 x) = x).
Proof. exact (eq_refl (term698 A add r0 x)). Qed.
Lemma lem1023839 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term698 A mul r1 x.
Proof. exact (@lem1017051 A mul r1 h1 x). Qed.
Lemma lem1023840 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term698 A mul r1 x) = ((mul r1 x) = x).
Proof. exact (eq_refl (term698 A mul r1 x)). Qed.
Lemma lem1023842 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : term702 A mul r0 x.
Proof. exact (@lem1017053 A mul r0 h1 x). Qed.
Lemma lem1023843 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : (term702 A mul r0 x) = ((mul r0 x) = r0).
Proof. exact (eq_refl (term702 A mul r0 x)). Qed.
Lemma lem1023845 {A : Type'} (x : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term699 A add mul x.
Proof. exact (@lem1017055 A add mul h1 x). Qed.
Lemma lem1023846 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term699 A add mul x) = (term133 A add mul x).
Proof. exact (eq_refl (term699 A add mul x)). Qed.
Lemma lem1023847 {A : Type'} (x : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term133 A add mul x.
Proof. exact (EQ_MP (@lem1023846 A add mul x) (@lem1023845 A x add mul h1)). Qed.
Lemma lem1023848 {A : Type'} (x : A) (y : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term700 A add mul x y.
Proof. exact (@lem1023847 A x add mul h1 y). Qed.
Lemma lem1023849 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term700 A add mul x y) = (term131 A add y mul x).
Proof. exact (eq_refl (term700 A add mul x y)). Qed.
Lemma lem1023850 {A : Type'} (y : A) (x : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term131 A add y mul x.
Proof. exact (EQ_MP (@lem1023849 A add y mul x) (@lem1023848 A x y add mul h1)). Qed.
Lemma lem1023851 {A : Type'} (y : A) (x : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : term701 A add y mul x z.
Proof. exact (@lem1023850 A y x add mul h1 z). Qed.
Lemma lem1023852 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : (term701 A add y mul x z) = ((term128 A mul x add y z) = (term129 A add y mul x z)).
Proof. exact (eq_refl (term701 A add y mul x z)). Qed.
Lemma lem1023854 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : term812 A pwr r1 x.
Proof. exact (@lem1017057 A pwr r1 h1 x). Qed.
Lemma lem1023855 {A : Type'} (pwr : type1423 A) (x : A) (r1 : A) : (term812 A pwr r1 x) = ((term126 A pwr x) = r1).
Proof. exact (eq_refl (term812 A pwr r1 x)). Qed.
Lemma lem1023857 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term813 A mul pwr x.
Proof. exact (@lem1017056 A mul pwr h1 x). Qed.
Lemma lem1023858 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term813 A mul pwr x) = (term124 A mul pwr x).
Proof. exact (eq_refl (term813 A mul pwr x)). Qed.
Lemma lem1023859 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term124 A mul pwr x.
Proof. exact (EQ_MP (@lem1023858 A mul pwr x) (@lem1023857 A x mul pwr h1)). Qed.
Lemma lem1023860 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term814 A mul pwr x n.
Proof. exact (@lem1023859 A x mul pwr h1 n). Qed.
Lemma lem1023861 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : (term814 A mul pwr x n) = ((term121 A pwr x n) = (term122 A mul pwr x n)).
Proof. exact (eq_refl (term814 A mul pwr x n)). Qed.
Lemma lem1023863 {A : Type'} (m : A) (add : type1400 A) (h1 : term11 A add) : term154 A add m.
Proof. exact (@lem1023819 A add h1 m). Qed.
Lemma lem1023864 {A : Type'} (add : type1400 A) (m : A) : (term154 A add m) = (term114 A add m).
Proof. exact (eq_refl (term154 A add m)). Qed.
Lemma lem1023865 {A : Type'} (m : A) (add : type1400 A) (h1 : term11 A add) : term114 A add m.
Proof. exact (EQ_MP (@lem1023864 A add m) (@lem1023863 A m add h1)). Qed.
Lemma lem1023866 {A : Type'} (m : A) (n : A) (add : type1400 A) (h1 : term11 A add) : term146 A add m n.
Proof. exact (@lem1023865 A m add h1 n). Qed.
Lemma lem1023867 {A : Type'} (add : type1400 A) (n : A) (m : A) : (term146 A add m n) = ((add m n) = (add n m)).
Proof. exact (eq_refl (term146 A add m n)). Qed.
Lemma lem1023869 {A : Type'} (m : A) (add : type1400 A) (h1 : term110 A add) : term176 A add m.
Proof. exact (@lem1023821 A add h1 m). Qed.
Lemma lem1023870 {A : Type'} (m : A) (add : type1400 A) : (term176 A add m) = (term108 A m add).
Proof. exact (eq_refl (term176 A add m)). Qed.
Lemma lem1023871 {A : Type'} (m : A) (add : type1400 A) (h1 : term110 A add) : term108 A m add.
Proof. exact (EQ_MP (@lem1023870 A m add) (@lem1023869 A m add h1)). Qed.
Lemma lem1023872 {A : Type'} (m : A) (n : A) (add : type1400 A) (h1 : term110 A add) : term169 A m add n.
Proof. exact (@lem1023871 A m add h1 n). Qed.
Lemma lem1023873 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term169 A m add n) = (term106 A m add n).
Proof. exact (eq_refl (term169 A m add n)). Qed.
Lemma lem1023874 {A : Type'} (m : A) (n : A) (add : type1400 A) (h1 : term110 A add) : term106 A m add n.
Proof. exact (EQ_MP (@lem1023873 A m add n) (@lem1023872 A m n add h1)). Qed.
Lemma lem1023875 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : term161 A m add n p.
Proof. exact (@lem1023874 A m n add h1 p). Qed.
Lemma lem1023876 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : (term161 A m add n p) = ((term104 A add m n p) = (term95 A m add n p)).
Proof. exact (eq_refl (term161 A m add n p)). Qed.
Lemma lem1023878 {A : Type'} (m : A) (add : type1400 A) (h1 : term101 A add) : term198 A add m.
Proof. exact (@lem1023823 A add h1 m). Qed.
Lemma lem1023879 {A : Type'} (add : type1400 A) (m : A) : (term198 A add m) = (term99 A add m).
Proof. exact (eq_refl (term198 A add m)). Qed.
Lemma lem1023880 {A : Type'} (m : A) (add : type1400 A) (h1 : term101 A add) : term99 A add m.
Proof. exact (EQ_MP (@lem1023879 A add m) (@lem1023878 A m add h1)). Qed.
Lemma lem1023881 {A : Type'} (m : A) (n : A) (add : type1400 A) (h1 : term101 A add) : term191 A add m n.
Proof. exact (@lem1023880 A m add h1 n). Qed.
Lemma lem1023882 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term191 A add m n) = (term97 A n add m).
Proof. exact (eq_refl (term191 A add m n)). Qed.
Lemma lem1023883 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term101 A add) : term97 A n add m.
Proof. exact (EQ_MP (@lem1023882 A n add m) (@lem1023881 A m n add h1)). Qed.
Lemma lem1023884 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term101 A add) : term183 A n add m p.
Proof. exact (@lem1023883 A n m add h1 p). Qed.
Lemma lem1023885 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : (term183 A n add m p) = ((term95 A m add n p) = (term95 A n add m p)).
Proof. exact (eq_refl (term183 A n add m p)). Qed.
Lemma lem1023887 {A : Type'} (x : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : term205 A add r0 x.
Proof. exact (@lem1023825 A add r0 h1 x). Qed.
Lemma lem1023888 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : (term205 A add r0 x) = ((add x r0) = x).
Proof. exact (eq_refl (term205 A add r0 x)). Qed.
Lemma lem1023890 {A : Type'} (m : A) (mul : type1400 A) (h1 : term11 A mul) : term154 A mul m.
Proof. exact (@lem1023827 A mul h1 m). Qed.
Lemma lem1023891 {A : Type'} (mul : type1400 A) (m : A) : (term154 A mul m) = (term114 A mul m).
Proof. exact (eq_refl (term154 A mul m)). Qed.
Lemma lem1023892 {A : Type'} (m : A) (mul : type1400 A) (h1 : term11 A mul) : term114 A mul m.
Proof. exact (EQ_MP (@lem1023891 A mul m) (@lem1023890 A m mul h1)). Qed.
Lemma lem1023893 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : term146 A mul m n.
Proof. exact (@lem1023892 A m mul h1 n). Qed.
Lemma lem1023894 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term146 A mul m n) = ((mul m n) = (mul n m)).
Proof. exact (eq_refl (term146 A mul m n)). Qed.
Lemma lem1023896 {A : Type'} (m : A) (mul : type1400 A) (h1 : term110 A mul) : term176 A mul m.
Proof. exact (@lem1023829 A mul h1 m). Qed.
Lemma lem1023897 {A : Type'} (m : A) (mul : type1400 A) : (term176 A mul m) = (term108 A m mul).
Proof. exact (eq_refl (term176 A mul m)). Qed.
Lemma lem1023898 {A : Type'} (m : A) (mul : type1400 A) (h1 : term110 A mul) : term108 A m mul.
Proof. exact (EQ_MP (@lem1023897 A m mul) (@lem1023896 A m mul h1)). Qed.
Lemma lem1023899 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term110 A mul) : term169 A m mul n.
Proof. exact (@lem1023898 A m mul h1 n). Qed.
Lemma lem1023900 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term169 A m mul n) = (term106 A m mul n).
Proof. exact (eq_refl (term169 A m mul n)). Qed.
Lemma lem1023901 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term110 A mul) : term106 A m mul n.
Proof. exact (EQ_MP (@lem1023900 A m mul n) (@lem1023899 A m n mul h1)). Qed.
Lemma lem1023902 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : term161 A m mul n p.
Proof. exact (@lem1023901 A m n mul h1 p). Qed.
Lemma lem1023903 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term161 A m mul n p) = ((term104 A mul m n p) = (term95 A m mul n p)).
Proof. exact (eq_refl (term161 A m mul n p)). Qed.
Lemma lem1023905 {A : Type'} (m : A) (mul : type1400 A) (h1 : term101 A mul) : term198 A mul m.
Proof. exact (@lem1023831 A mul h1 m). Qed.
Lemma lem1023906 {A : Type'} (mul : type1400 A) (m : A) : (term198 A mul m) = (term99 A mul m).
Proof. exact (eq_refl (term198 A mul m)). Qed.
Lemma lem1023907 {A : Type'} (m : A) (mul : type1400 A) (h1 : term101 A mul) : term99 A mul m.
Proof. exact (EQ_MP (@lem1023906 A mul m) (@lem1023905 A m mul h1)). Qed.
Lemma lem1023908 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term101 A mul) : term191 A mul m n.
Proof. exact (@lem1023907 A m mul h1 n). Qed.
Lemma lem1023909 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term191 A mul m n) = (term97 A n mul m).
Proof. exact (eq_refl (term191 A mul m n)). Qed.
Lemma lem1023910 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term101 A mul) : term97 A n mul m.
Proof. exact (EQ_MP (@lem1023909 A n mul m) (@lem1023908 A m n mul h1)). Qed.
Lemma lem1023911 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : term183 A n mul m p.
Proof. exact (@lem1023910 A n m mul h1 p). Qed.
Lemma lem1023912 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term183 A n mul m p) = ((term95 A m mul n p) = (term95 A n mul m p)).
Proof. exact (eq_refl (term183 A n mul m p)). Qed.
Lemma lem1023914 {A : Type'} (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : term228 A add mul m.
Proof. exact (@lem1023833 A add mul h1 m). Qed.
Lemma lem1023915 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term228 A add mul m) = (term90 A add m mul).
Proof. exact (eq_refl (term228 A add mul m)). Qed.
Lemma lem1023916 {A : Type'} (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : term90 A add m mul.
Proof. exact (EQ_MP (@lem1023915 A add m mul) (@lem1023914 A m add mul h1)). Qed.
Lemma lem1023917 {A : Type'} (m : A) (n : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : term221 A add m mul n.
Proof. exact (@lem1023916 A m add mul h1 n). Qed.
Lemma lem1023918 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term221 A add m mul n) = (term88 A add m mul n).
Proof. exact (eq_refl (term221 A add m mul n)). Qed.
Lemma lem1023919 {A : Type'} (m : A) (n : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : term88 A add m mul n.
Proof. exact (EQ_MP (@lem1023918 A add m mul n) (@lem1023917 A m n add mul h1)). Qed.
Lemma lem1023920 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : term213 A add m mul n p.
Proof. exact (@lem1023919 A m n add mul h1 p). Qed.
Lemma lem1023921 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : (term213 A add m mul n p) = ((term85 A mul add m n p) = (term86 A add m mul n p)).
Proof. exact (eq_refl (term213 A add m mul n p)). Qed.
Lemma lem1023923 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : term205 A mul r1 x.
Proof. exact (@lem1023835 A mul r1 h1 x). Qed.
Lemma lem1023924 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term205 A mul r1 x) = ((mul x r1) = x).
Proof. exact (eq_refl (term205 A mul r1 x)). Qed.
Lemma lem1023926 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : term235 A mul r0 x.
Proof. exact (@lem1023834 A mul r0 h1 x). Qed.
Lemma lem1023927 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : (term235 A mul r0 x) = ((mul x r0) = r0).
Proof. exact (eq_refl (term235 A mul r0 x)). Qed.
Lemma lem1023934 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1023935 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1023934 A x mul r1 h1). Qed.
Lemma lem1023936 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1023937 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term815 A mul r1 x) = (@eq A x).
Proof. exact (MK_COMB (@lem1023936 A) (@lem1023935 A x mul r1 h1)). Qed.
Lemma lem1023938 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1023939 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : ((mul r1 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1023937 A x mul r1 h1) (@lem1023938 A x)). Qed.
Lemma lem1023941 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1023942 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1023941 A x). Qed.
Lemma lem1023943 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : ((mul r1 x) = x) = True.
Proof. exact (TRANS (@lem1023939 A x mul r1 h1) (@lem1023942 A x)). Qed.
Lemma lem1023944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1023945 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term816 A mul r1 x) = (and True).
Proof. exact (MK_COMB (@lem1023944) (@lem1023943 A x mul r1 h1)). Qed.
Lemma lem1023963 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023921 A add m mul n p) (@lem1023920 A m n p add mul h1)). Qed.
Lemma lem1023964 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (@lem1023963 A m n p add mul h1). Qed.
Lemma lem1023965 {A : Type'} (a : A) (b : A) (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add a b m) = (term86 A add a mul b m).
Proof. exact (@lem1023964 A a b m add mul h1). Qed.
Lemma lem1023978 {A : Type'} (add : type1400 A) (a : A) (mul : type1400 A) (b : A) (m : A) : (term817 A add a mul b m) = (term817 A add a mul b m).
Proof. exact (eq_refl (term817 A add a mul b m)). Qed.
Lemma lem1023979 {A : Type'} (a : A) (b : A) (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : ((term86 A add a mul b m) = (term85 A mul add a b m)) = ((term86 A add a mul b m) = (term86 A add a mul b m)).
Proof. exact (MK_COMB (@lem1023978 A add a mul b m) (@lem1023965 A a b m add mul h1)). Qed.
Lemma lem1023981 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1023982 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1023981 A x). Qed.
Lemma lem1023983 {A : Type'} (add : type1400 A) (a : A) (mul : type1400 A) (b : A) (m : A) : ((term86 A add a mul b m) = (term86 A add a mul b m)) = True.
Proof. exact (@lem1023982 A (term86 A add a mul b m)). Qed.
Lemma lem1023984 {A : Type'} (a : A) (b : A) (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : ((term86 A add a mul b m) = (term85 A mul add a b m)) = True.
Proof. exact (TRANS (@lem1023979 A a b m add mul h1) (@lem1023983 A add a mul b m)). Qed.
Lemma lem1023985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1023986 {A : Type'} (a : A) (b : A) (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term818 A mul add a b m) = (and True).
Proof. exact (MK_COMB (@lem1023985) (@lem1023984 A a b m add mul h1)). Qed.
Lemma lem1023992 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (EQ_MP (@lem1023867 A add n m) (@lem1023866 A m n add h1)). Qed.
Lemma lem1023993 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (@lem1023992 A n m add h1). Qed.
Lemma lem1023994 {A : Type'} (mul : type1400 A) (a : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (term819 A add mul a m) = (term820 A add mul a m).
Proof. exact (@lem1023993 A m (mul a m) add h1). Qed.
Lemma lem1024003 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024004 {A : Type'} (mul : type1400 A) (a : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (term821 A add mul a m) = (term822 A add mul a m).
Proof. exact (MK_COMB (@lem1024003 A) (@lem1023994 A mul a m add h1)). Qed.
Lemma lem1024006 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023921 A add m mul n p) (@lem1023920 A m n p add mul h1)). Qed.
Lemma lem1024007 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (@lem1024006 A m n p add mul h1). Qed.
Lemma lem1024008 {A : Type'} (a : A) (r1 : A) (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add a r1 m) = (term86 A add a mul r1 m).
Proof. exact (@lem1024007 A a r1 m add mul h1). Qed.
Lemma lem1024018 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1024019 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1024018 A x mul r1 h1). Qed.
Lemma lem1024020 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 m) = m.
Proof. exact (@lem1024019 A m mul r1 h1). Qed.
Lemma lem1024021 {A : Type'} (add : type1400 A) (mul : type1400 A) (a : A) (m : A) : (term823 A add mul a m) = (term823 A add mul a m).
Proof. exact (eq_refl (term823 A add mul a m)). Qed.
Lemma lem1024022 {A : Type'} (add : type1400 A) (a : A) (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term86 A add a mul r1 m) = (term819 A add mul a m).
Proof. exact (MK_COMB (@lem1024021 A add mul a m) (@lem1024020 A m mul r1 h1)). Qed.
Lemma lem1024024 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (EQ_MP (@lem1023867 A add n m) (@lem1023866 A m n add h1)). Qed.
Lemma lem1024025 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (@lem1024024 A n m add h1). Qed.
Lemma lem1024026 {A : Type'} (mul : type1400 A) (a : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (term819 A add mul a m) = (term820 A add mul a m).
Proof. exact (@lem1024025 A m (mul a m) add h1). Qed.
Lemma lem1024035 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term11 A add) (h2 : term13 A mul r1) : (term86 A add a mul r1 m) = (term820 A add mul a m).
Proof. exact (TRANS (@lem1024022 A add a m mul r1 h2) (@lem1024026 A mul a m add h1)). Qed.
Lemma lem1024036 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : (term85 A mul add a r1 m) = (term820 A add mul a m).
Proof. exact (TRANS (@lem1024008 A a r1 m add mul h1) (@lem1024035 A a m add mul r1 h2 h3)). Qed.
Lemma lem1024037 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : ((term819 A add mul a m) = (term85 A mul add a r1 m)) = ((term820 A add mul a m) = (term820 A add mul a m)).
Proof. exact (MK_COMB (@lem1024004 A mul a m add h2) (@lem1024036 A a m add mul r1 h1 h2 h3)). Qed.
Lemma lem1024039 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024039 A x). Qed.
Lemma lem1024041 {A : Type'} (add : type1400 A) (mul : type1400 A) (a : A) (m : A) : ((term820 A add mul a m) = (term820 A add mul a m)) = True.
Proof. exact (@lem1024040 A (term820 A add mul a m)). Qed.
Lemma lem1024042 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : ((term819 A add mul a m) = (term85 A mul add a r1 m)) = True.
Proof. exact (TRANS (@lem1024037 A a m add mul r1 h1 h2 h3) (@lem1024041 A add mul a m)). Qed.
Lemma lem1024043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024044 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : (term824 A mul add a r1 m) = (and True).
Proof. exact (MK_COMB (@lem1024043) (@lem1024042 A a m add mul r1 h1 h2 h3)). Qed.
Lemma lem1024058 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023921 A add m mul n p) (@lem1023920 A m n p add mul h1)). Qed.
Lemma lem1024059 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (@lem1024058 A m n p add mul h1). Qed.
Lemma lem1024060 {A : Type'} (a : A) (r1 : A) (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add a r1 m) = (term86 A add a mul r1 m).
Proof. exact (@lem1024059 A a r1 m add mul h1). Qed.
Lemma lem1024070 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1024071 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1024070 A x mul r1 h1). Qed.
Lemma lem1024072 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 m) = m.
Proof. exact (@lem1024071 A m mul r1 h1). Qed.
Lemma lem1024073 {A : Type'} (add : type1400 A) (mul : type1400 A) (a : A) (m : A) : (term823 A add mul a m) = (term823 A add mul a m).
Proof. exact (eq_refl (term823 A add mul a m)). Qed.
Lemma lem1024074 {A : Type'} (add : type1400 A) (a : A) (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term86 A add a mul r1 m) = (term819 A add mul a m).
Proof. exact (MK_COMB (@lem1024073 A add mul a m) (@lem1024072 A m mul r1 h1)). Qed.
Lemma lem1024076 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (EQ_MP (@lem1023867 A add n m) (@lem1023866 A m n add h1)). Qed.
Lemma lem1024077 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (@lem1024076 A n m add h1). Qed.
Lemma lem1024078 {A : Type'} (mul : type1400 A) (a : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (term819 A add mul a m) = (term820 A add mul a m).
Proof. exact (@lem1024077 A m (mul a m) add h1). Qed.
Lemma lem1024087 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term11 A add) (h2 : term13 A mul r1) : (term86 A add a mul r1 m) = (term820 A add mul a m).
Proof. exact (TRANS (@lem1024074 A add a m mul r1 h2) (@lem1024078 A mul a m add h1)). Qed.
Lemma lem1024088 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : (term85 A mul add a r1 m) = (term820 A add mul a m).
Proof. exact (TRANS (@lem1024060 A a r1 m add mul h1) (@lem1024087 A a m add mul r1 h2 h3)). Qed.
Lemma lem1024089 {A : Type'} (add : type1400 A) (mul : type1400 A) (a : A) (m : A) : (term822 A add mul a m) = (term822 A add mul a m).
Proof. exact (eq_refl (term822 A add mul a m)). Qed.
Lemma lem1024090 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : ((term820 A add mul a m) = (term85 A mul add a r1 m)) = ((term820 A add mul a m) = (term820 A add mul a m)).
Proof. exact (MK_COMB (@lem1024089 A add mul a m) (@lem1024088 A a m add mul r1 h1 h2 h3)). Qed.
Lemma lem1024092 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024093 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024092 A x). Qed.
Lemma lem1024094 {A : Type'} (add : type1400 A) (mul : type1400 A) (a : A) (m : A) : ((term820 A add mul a m) = (term820 A add mul a m)) = True.
Proof. exact (@lem1024093 A (term820 A add mul a m)). Qed.
Lemma lem1024095 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : ((term820 A add mul a m) = (term85 A mul add a r1 m)) = True.
Proof. exact (TRANS (@lem1024090 A a m add mul r1 h1 h2 h3) (@lem1024094 A add mul a m)). Qed.
Lemma lem1024096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024097 {A : Type'} (a : A) (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term11 A add) (h3 : term13 A mul r1) : (term825 A mul add a r1 m) = (and True).
Proof. exact (MK_COMB (@lem1024096) (@lem1024095 A a m add mul r1 h1 h2 h3)). Qed.
Lemma lem1024107 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023921 A add m mul n p) (@lem1023920 A m n p add mul h1)). Qed.
Lemma lem1024108 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (@lem1024107 A m n p add mul h1). Qed.
Lemma lem1024109 {A : Type'} (r1 : A) (m : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term826 A mul add r1 m) = (term827 A add mul r1 m).
Proof. exact (@lem1024108 A r1 r1 m add mul h1). Qed.
Lemma lem1024115 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1024116 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1024115 A x mul r1 h1). Qed.
Lemma lem1024117 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 m) = m.
Proof. exact (@lem1024116 A m mul r1 h1). Qed.
Lemma lem1024118 {A : Type'} (add : type1400 A) : add = add.
Proof. exact (eq_refl add). Qed.
Lemma lem1024119 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term823 A add mul r1 m) = (add m).
Proof. exact (MK_COMB (@lem1024118 A add) (@lem1024117 A m mul r1 h1)). Qed.
Lemma lem1024121 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1024122 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1024121 A x mul r1 h1). Qed.
Lemma lem1024123 {A : Type'} (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 m) = m.
Proof. exact (@lem1024122 A m mul r1 h1). Qed.
Lemma lem1024124 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term827 A add mul r1 m) = (add m m).
Proof. exact (MK_COMB (@lem1024119 A add m mul r1 h1) (@lem1024123 A m mul r1 h1)). Qed.
Lemma lem1024129 {A : Type'} (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term13 A mul r1) : (term826 A mul add r1 m) = (add m m).
Proof. exact (TRANS (@lem1024109 A r1 m add mul h1) (@lem1024124 A add m mul r1 h2)). Qed.
Lemma lem1024130 {A : Type'} (add : type1400 A) (m : A) : (term828 A add m) = (term828 A add m).
Proof. exact (eq_refl (term828 A add m)). Qed.
Lemma lem1024131 {A : Type'} (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term13 A mul r1) : ((add m m) = (term826 A mul add r1 m)) = ((add m m) = (add m m)).
Proof. exact (MK_COMB (@lem1024130 A add m) (@lem1024129 A m add mul r1 h1 h2)). Qed.
Lemma lem1024133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024134 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024133 A x). Qed.
Lemma lem1024135 {A : Type'} (add : type1400 A) (m : A) : ((add m m) = (add m m)) = True.
Proof. exact (@lem1024134 A (add m m)). Qed.
Lemma lem1024136 {A : Type'} (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term13 A mul r1) : ((add m m) = (term826 A mul add r1 m)) = True.
Proof. exact (TRANS (@lem1024131 A m add mul r1 h1 h2) (@lem1024135 A add m)). Qed.
Lemma lem1024137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024138 {A : Type'} (m : A) (add : type1400 A) (mul : type1400 A) (r1 : A) (h1 : term92 A add mul) (h2 : term13 A mul r1) : (term829 A mul add r1 m) = (and True).
Proof. exact (MK_COMB (@lem1024137) (@lem1024136 A m add mul r1 h1 h2)). Qed.
Lemma lem1024144 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 x) = r0.
Proof. exact (EQ_MP (@lem1023843 A mul x r0) (@lem1023842 A x mul r0 h1)). Qed.
Lemma lem1024145 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 x) = r0.
Proof. exact (@lem1024144 A x mul r0 h1). Qed.
Lemma lem1024146 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 m) = r0.
Proof. exact (@lem1024145 A m mul r0 h1). Qed.
Lemma lem1024147 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024148 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (term815 A mul r0 m) = (@eq A r0).
Proof. exact (MK_COMB (@lem1024147 A) (@lem1024146 A m mul r0 h1)). Qed.
Lemma lem1024149 {A : Type'} (r0 : A) : r0 = r0.
Proof. exact (eq_refl r0). Qed.
Lemma lem1024150 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : ((mul r0 m) = r0) = (r0 = r0).
Proof. exact (MK_COMB (@lem1024148 A m mul r0 h1) (@lem1024149 A r0)). Qed.
Lemma lem1024152 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024153 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024152 A x). Qed.
Lemma lem1024154 {A : Type'} (r0 : A) : (r0 = r0) = True.
Proof. exact (@lem1024153 A r0). Qed.
Lemma lem1024155 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : ((mul r0 m) = r0) = True.
Proof. exact (TRANS (@lem1024150 A m mul r0 h1) (@lem1024154 A r0)). Qed.
Lemma lem1024156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024157 {A : Type'} (m : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (term830 A mul m r0) = (and True).
Proof. exact (MK_COMB (@lem1024156) (@lem1024155 A m mul r0 h1)). Qed.
Lemma lem1024163 {A : Type'} (x : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (add r0 x) = x.
Proof. exact (EQ_MP (@lem1023837 A add r0 x) (@lem1023836 A x add r0 h1)). Qed.
Lemma lem1024164 {A : Type'} (x : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (add r0 x) = x.
Proof. exact (@lem1024163 A x add r0 h1). Qed.
Lemma lem1024165 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (add r0 a) = a.
Proof. exact (@lem1024164 A a add r0 h1). Qed.
Lemma lem1024166 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024167 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (term815 A add r0 a) = (@eq A a).
Proof. exact (MK_COMB (@lem1024166 A) (@lem1024165 A a add r0 h1)). Qed.
Lemma lem1024168 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1024169 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : ((add r0 a) = a) = (a = a).
Proof. exact (MK_COMB (@lem1024167 A a add r0 h1) (@lem1024168 A a)). Qed.
Lemma lem1024171 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024172 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024171 A x). Qed.
Lemma lem1024173 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem1024172 A a). Qed.
Lemma lem1024174 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : ((add r0 a) = a) = True.
Proof. exact (TRANS (@lem1024169 A a add r0 h1) (@lem1024173 A a)). Qed.
Lemma lem1024175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024176 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : (term816 A add r0 a) = (and True).
Proof. exact (MK_COMB (@lem1024175) (@lem1024174 A a add r0 h1)). Qed.
Lemma lem1024182 {A : Type'} (x : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : (add x r0) = x.
Proof. exact (EQ_MP (@lem1023888 A add r0 x) (@lem1023887 A x add r0 h1)). Qed.
Lemma lem1024183 {A : Type'} (x : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : (add x r0) = x.
Proof. exact (@lem1024182 A x add r0 h1). Qed.
Lemma lem1024184 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : (add a r0) = a.
Proof. exact (@lem1024183 A a add r0 h1). Qed.
Lemma lem1024185 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024186 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : (term815 A add a r0) = (@eq A a).
Proof. exact (MK_COMB (@lem1024185 A) (@lem1024184 A a add r0 h1)). Qed.
Lemma lem1024187 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1024188 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : ((add a r0) = a) = (a = a).
Proof. exact (MK_COMB (@lem1024186 A a add r0 h1) (@lem1024187 A a)). Qed.
Lemma lem1024190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024191 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024190 A x). Qed.
Lemma lem1024192 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem1024191 A a). Qed.
Lemma lem1024193 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : ((add a r0) = a) = True.
Proof. exact (TRANS (@lem1024188 A a add r0 h1) (@lem1024192 A a)). Qed.
Lemma lem1024194 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024195 {A : Type'} (a : A) (add : type1400 A) (r0 : A) (h1 : term82 A add r0) : (term830 A add r0 a) = (and True).
Proof. exact (MK_COMB (@lem1024194) (@lem1024193 A a add r0 h1)). Qed.
Lemma lem1024205 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1024206 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1024205 A n m mul h1). Qed.
Lemma lem1024207 {A : Type'} (a : A) (b : A) (mul : type1400 A) (h1 : term11 A mul) : (mul b a) = (mul a b).
Proof. exact (@lem1024206 A a b mul h1). Qed.
Lemma lem1024212 {A : Type'} (mul : type1400 A) (a : A) (b : A) : (term815 A mul a b) = (term815 A mul a b).
Proof. exact (eq_refl (term815 A mul a b)). Qed.
Lemma lem1024213 {A : Type'} (a : A) (b : A) (mul : type1400 A) (h1 : term11 A mul) : ((mul a b) = (mul b a)) = ((mul a b) = (mul a b)).
Proof. exact (MK_COMB (@lem1024212 A mul a b) (@lem1024207 A a b mul h1)). Qed.
Lemma lem1024215 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024216 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024215 A x). Qed.
Lemma lem1024217 {A : Type'} (mul : type1400 A) (a : A) (b : A) : ((mul a b) = (mul a b)) = True.
Proof. exact (@lem1024216 A (mul a b)). Qed.
Lemma lem1024218 {A : Type'} (b : A) (a : A) (mul : type1400 A) (h1 : term11 A mul) : ((mul a b) = (mul b a)) = True.
Proof. exact (TRANS (@lem1024213 A a b mul h1) (@lem1024217 A mul a b)). Qed.
Lemma lem1024219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024220 {A : Type'} (b : A) (a : A) (mul : type1400 A) (h1 : term11 A mul) : (term831 A mul b a) = (and True).
Proof. exact (MK_COMB (@lem1024219) (@lem1024218 A b a mul h1)). Qed.
Lemma lem1024226 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (EQ_MP (@lem1023921 A add m mul n p) (@lem1023920 A m n p add mul h1)). Qed.
Lemma lem1024227 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add m n p) = (term86 A add m mul n p).
Proof. exact (@lem1024226 A m n p add mul h1). Qed.
Lemma lem1024228 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term85 A mul add a b c) = (term86 A add a mul b c).
Proof. exact (@lem1024227 A a b c add mul h1). Qed.
Lemma lem1024241 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024242 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term832 A mul add a b c) = (term817 A add a mul b c).
Proof. exact (MK_COMB (@lem1024241 A) (@lem1024228 A a b c add mul h1)). Qed.
Lemma lem1024255 {A : Type'} (add : type1400 A) (a : A) (mul : type1400 A) (b : A) (c : A) : (term86 A add a mul b c) = (term86 A add a mul b c).
Proof. exact (eq_refl (term86 A add a mul b c)). Qed.
Lemma lem1024256 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : ((term85 A mul add a b c) = (term86 A add a mul b c)) = ((term86 A add a mul b c) = (term86 A add a mul b c)).
Proof. exact (MK_COMB (@lem1024242 A a b c add mul h1) (@lem1024255 A add a mul b c)). Qed.
Lemma lem1024258 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024259 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024258 A x). Qed.
Lemma lem1024260 {A : Type'} (add : type1400 A) (a : A) (mul : type1400 A) (b : A) (c : A) : ((term86 A add a mul b c) = (term86 A add a mul b c)) = True.
Proof. exact (@lem1024259 A (term86 A add a mul b c)). Qed.
Lemma lem1024261 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : ((term85 A mul add a b c) = (term86 A add a mul b c)) = True.
Proof. exact (TRANS (@lem1024256 A a b c add mul h1) (@lem1024260 A add a mul b c)). Qed.
Lemma lem1024262 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024263 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (mul : type1400 A) (h1 : term92 A add mul) : (term833 A add a mul b c) = (and True).
Proof. exact (MK_COMB (@lem1024262) (@lem1024261 A a b c add mul h1)). Qed.
Lemma lem1024269 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 x) = r0.
Proof. exact (EQ_MP (@lem1023843 A mul x r0) (@lem1023842 A x mul r0 h1)). Qed.
Lemma lem1024270 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 x) = r0.
Proof. exact (@lem1024269 A x mul r0 h1). Qed.
Lemma lem1024271 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (mul r0 a) = r0.
Proof. exact (@lem1024270 A a mul r0 h1). Qed.
Lemma lem1024272 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024273 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (term815 A mul r0 a) = (@eq A r0).
Proof. exact (MK_COMB (@lem1024272 A) (@lem1024271 A a mul r0 h1)). Qed.
Lemma lem1024274 {A : Type'} (r0 : A) : r0 = r0.
Proof. exact (eq_refl r0). Qed.
Lemma lem1024275 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : ((mul r0 a) = r0) = (r0 = r0).
Proof. exact (MK_COMB (@lem1024273 A a mul r0 h1) (@lem1024274 A r0)). Qed.
Lemma lem1024277 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024278 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024277 A x). Qed.
Lemma lem1024279 {A : Type'} (r0 : A) : (r0 = r0) = True.
Proof. exact (@lem1024278 A r0). Qed.
Lemma lem1024280 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : ((mul r0 a) = r0) = True.
Proof. exact (TRANS (@lem1024275 A a mul r0 h1) (@lem1024279 A r0)). Qed.
Lemma lem1024281 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024282 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term18 A mul r0) : (term830 A mul a r0) = (and True).
Proof. exact (MK_COMB (@lem1024281) (@lem1024280 A a mul r0 h1)). Qed.
Lemma lem1024288 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : (mul x r0) = r0.
Proof. exact (EQ_MP (@lem1023927 A mul x r0) (@lem1023926 A x mul r0 h1)). Qed.
Lemma lem1024289 {A : Type'} (x : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : (mul x r0) = r0.
Proof. exact (@lem1024288 A x mul r0 h1). Qed.
Lemma lem1024290 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : (mul a r0) = r0.
Proof. exact (@lem1024289 A a mul r0 h1). Qed.
Lemma lem1024291 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024292 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : (term815 A mul a r0) = (@eq A r0).
Proof. exact (MK_COMB (@lem1024291 A) (@lem1024290 A a mul r0 h1)). Qed.
Lemma lem1024293 {A : Type'} (r0 : A) : r0 = r0.
Proof. exact (eq_refl r0). Qed.
Lemma lem1024294 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : ((mul a r0) = r0) = (r0 = r0).
Proof. exact (MK_COMB (@lem1024292 A a mul r0 h1) (@lem1024293 A r0)). Qed.
Lemma lem1024296 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024297 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024296 A x). Qed.
Lemma lem1024298 {A : Type'} (r0 : A) : (r0 = r0) = True.
Proof. exact (@lem1024297 A r0). Qed.
Lemma lem1024299 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : ((mul a r0) = r0) = True.
Proof. exact (TRANS (@lem1024294 A a mul r0 h1) (@lem1024298 A r0)). Qed.
Lemma lem1024300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024301 {A : Type'} (a : A) (mul : type1400 A) (r0 : A) (h1 : term80 A mul r0) : (term816 A mul a r0) = (and True).
Proof. exact (MK_COMB (@lem1024300) (@lem1024299 A a mul r0 h1)). Qed.
Lemma lem1024307 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1024308 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1024307 A x mul r1 h1). Qed.
Lemma lem1024309 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 a) = a.
Proof. exact (@lem1024308 A a mul r1 h1). Qed.
Lemma lem1024310 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024311 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term815 A mul r1 a) = (@eq A a).
Proof. exact (MK_COMB (@lem1024310 A) (@lem1024309 A a mul r1 h1)). Qed.
Lemma lem1024312 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1024313 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : ((mul r1 a) = a) = (a = a).
Proof. exact (MK_COMB (@lem1024311 A a mul r1 h1) (@lem1024312 A a)). Qed.
Lemma lem1024315 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024316 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024315 A x). Qed.
Lemma lem1024317 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem1024316 A a). Qed.
Lemma lem1024318 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : ((mul r1 a) = a) = True.
Proof. exact (TRANS (@lem1024313 A a mul r1 h1) (@lem1024317 A a)). Qed.
Lemma lem1024319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024320 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (term816 A mul r1 a) = (and True).
Proof. exact (MK_COMB (@lem1024319) (@lem1024318 A a mul r1 h1)). Qed.
Lemma lem1024326 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (mul x r1) = x.
Proof. exact (EQ_MP (@lem1023924 A mul r1 x) (@lem1023923 A x mul r1 h1)). Qed.
Lemma lem1024327 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (mul x r1) = x.
Proof. exact (@lem1024326 A x mul r1 h1). Qed.
Lemma lem1024328 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (mul a r1) = a.
Proof. exact (@lem1024327 A a mul r1 h1). Qed.
Lemma lem1024329 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024330 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (term815 A mul a r1) = (@eq A a).
Proof. exact (MK_COMB (@lem1024329 A) (@lem1024328 A a mul r1 h1)). Qed.
Lemma lem1024331 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1024332 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : ((mul a r1) = a) = (a = a).
Proof. exact (MK_COMB (@lem1024330 A a mul r1 h1) (@lem1024331 A a)). Qed.
Lemma lem1024334 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024334 A x). Qed.
Lemma lem1024336 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem1024335 A a). Qed.
Lemma lem1024337 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : ((mul a r1) = a) = True.
Proof. exact (TRANS (@lem1024332 A a mul r1 h1) (@lem1024336 A a)). Qed.
Lemma lem1024338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024339 {A : Type'} (a : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (term830 A mul r1 a) = (and True).
Proof. exact (MK_COMB (@lem1024338) (@lem1024337 A a mul r1 h1)). Qed.
Lemma lem1024345 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024346 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024345 A m n p mul h1). Qed.
Lemma lem1024347 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term834 A lx ly mul rx ry) = (term835 A lx ly mul rx ry).
Proof. exact (@lem1024346 A lx ly (mul rx ry) mul h1). Qed.
Lemma lem1024368 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024369 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term836 A lx ly mul rx ry) = (term837 A lx ly mul rx ry).
Proof. exact (MK_COMB (@lem1024368 A) (@lem1024347 A lx ly rx ry mul h1)). Qed.
Lemma lem1024371 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024372 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024371 A m n p mul h1). Qed.
Lemma lem1024373 {A : Type'} (lx : A) (rx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term834 A lx rx mul ly ry) = (term835 A lx rx mul ly ry).
Proof. exact (@lem1024372 A lx rx (mul ly ry) mul h1). Qed.
Lemma lem1024383 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1023912 A n mul m p) (@lem1023911 A n m p mul h1)). Qed.
Lemma lem1024384 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1024383 A n m p mul h1). Qed.
Lemma lem1024385 {A : Type'} (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A rx mul ly ry) = (term95 A ly mul rx ry).
Proof. exact (@lem1024384 A ly rx ry mul h1). Qed.
Lemma lem1024398 {A : Type'} (mul : type1400 A) (lx : A) : (mul lx) = (mul lx).
Proof. exact (eq_refl (mul lx)). Qed.
Lemma lem1024399 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term835 A lx rx mul ly ry) = (term835 A lx ly mul rx ry).
Proof. exact (MK_COMB (@lem1024398 A mul lx) (@lem1024385 A ly rx ry mul h1)). Qed.
Lemma lem1024408 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : (term834 A lx rx mul ly ry) = (term835 A lx ly mul rx ry).
Proof. exact (TRANS (@lem1024373 A lx rx ly ry mul h2) (@lem1024399 A lx ly rx ry mul h1)). Qed.
Lemma lem1024409 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : ((term834 A lx ly mul rx ry) = (term834 A lx rx mul ly ry)) = ((term835 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)).
Proof. exact (MK_COMB (@lem1024369 A lx ly rx ry mul h2) (@lem1024408 A lx ly rx ry mul h1 h2)). Qed.
Lemma lem1024411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024412 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024411 A x). Qed.
Lemma lem1024413 {A : Type'} (lx : A) (ly : A) (mul : type1400 A) (rx : A) (ry : A) : ((term835 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)) = True.
Proof. exact (@lem1024412 A (term835 A lx ly mul rx ry)). Qed.
Lemma lem1024414 {A : Type'} (lx : A) (rx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : ((term834 A lx ly mul rx ry) = (term834 A lx rx mul ly ry)) = True.
Proof. exact (TRANS (@lem1024409 A lx ly rx ry mul h1 h2) (@lem1024413 A lx ly mul rx ry)). Qed.
Lemma lem1024415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024416 {A : Type'} (lx : A) (rx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : (term838 A lx rx mul ly ry) = (and True).
Proof. exact (MK_COMB (@lem1024415) (@lem1024414 A lx rx ly ry mul h1 h2)). Qed.
Lemma lem1024422 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024423 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024422 A m n p mul h1). Qed.
Lemma lem1024424 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term834 A lx ly mul rx ry) = (term835 A lx ly mul rx ry).
Proof. exact (@lem1024423 A lx ly (mul rx ry) mul h1). Qed.
Lemma lem1024445 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024446 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term836 A lx ly mul rx ry) = (term837 A lx ly mul rx ry).
Proof. exact (MK_COMB (@lem1024445 A) (@lem1024424 A lx ly rx ry mul h1)). Qed.
Lemma lem1024467 {A : Type'} (lx : A) (ly : A) (mul : type1400 A) (rx : A) (ry : A) : (term835 A lx ly mul rx ry) = (term835 A lx ly mul rx ry).
Proof. exact (eq_refl (term835 A lx ly mul rx ry)). Qed.
Lemma lem1024468 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : ((term834 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)) = ((term835 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)).
Proof. exact (MK_COMB (@lem1024446 A lx ly rx ry mul h1) (@lem1024467 A lx ly mul rx ry)). Qed.
Lemma lem1024470 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024471 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024470 A x). Qed.
Lemma lem1024472 {A : Type'} (lx : A) (ly : A) (mul : type1400 A) (rx : A) (ry : A) : ((term835 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)) = True.
Proof. exact (@lem1024471 A (term835 A lx ly mul rx ry)). Qed.
Lemma lem1024473 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : ((term834 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)) = True.
Proof. exact (TRANS (@lem1024468 A lx ly rx ry mul h1) (@lem1024472 A lx ly mul rx ry)). Qed.
Lemma lem1024474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024475 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term839 A lx ly mul rx ry) = (and True).
Proof. exact (MK_COMB (@lem1024474) (@lem1024473 A lx ly rx ry mul h1)). Qed.
Lemma lem1024481 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024482 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024481 A m n p mul h1). Qed.
Lemma lem1024483 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term834 A lx ly mul rx ry) = (term835 A lx ly mul rx ry).
Proof. exact (@lem1024482 A lx ly (mul rx ry) mul h1). Qed.
Lemma lem1024504 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024505 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term836 A lx ly mul rx ry) = (term837 A lx ly mul rx ry).
Proof. exact (MK_COMB (@lem1024504 A) (@lem1024483 A lx ly rx ry mul h1)). Qed.
Lemma lem1024515 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024516 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024515 A m n p mul h1). Qed.
Lemma lem1024517 {A : Type'} (lx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul lx ly ry) = (term95 A lx mul ly ry).
Proof. exact (@lem1024516 A lx ly ry mul h1). Qed.
Lemma lem1024530 {A : Type'} (mul : type1400 A) (rx : A) : (mul rx) = (mul rx).
Proof. exact (eq_refl (mul rx)). Qed.
Lemma lem1024531 {A : Type'} (rx : A) (lx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term840 A rx mul lx ly ry) = (term835 A rx lx mul ly ry).
Proof. exact (MK_COMB (@lem1024530 A mul rx) (@lem1024517 A lx ly ry mul h1)). Qed.
Lemma lem1024533 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1023912 A n mul m p) (@lem1023911 A n m p mul h1)). Qed.
Lemma lem1024534 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1024533 A n m p mul h1). Qed.
Lemma lem1024535 {A : Type'} (lx : A) (rx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term835 A rx lx mul ly ry) = (term835 A lx rx mul ly ry).
Proof. exact (@lem1024534 A lx rx (mul ly ry) mul h1). Qed.
Lemma lem1024545 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1023912 A n mul m p) (@lem1023911 A n m p mul h1)). Qed.
Lemma lem1024546 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1024545 A n m p mul h1). Qed.
Lemma lem1024547 {A : Type'} (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A rx mul ly ry) = (term95 A ly mul rx ry).
Proof. exact (@lem1024546 A ly rx ry mul h1). Qed.
Lemma lem1024560 {A : Type'} (mul : type1400 A) (lx : A) : (mul lx) = (mul lx).
Proof. exact (eq_refl (mul lx)). Qed.
Lemma lem1024561 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term835 A lx rx mul ly ry) = (term835 A lx ly mul rx ry).
Proof. exact (MK_COMB (@lem1024560 A mul lx) (@lem1024547 A ly rx ry mul h1)). Qed.
Lemma lem1024570 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term835 A rx lx mul ly ry) = (term835 A lx ly mul rx ry).
Proof. exact (TRANS (@lem1024535 A lx rx ly ry mul h1) (@lem1024561 A lx ly rx ry mul h1)). Qed.
Lemma lem1024571 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : (term840 A rx mul lx ly ry) = (term835 A lx ly mul rx ry).
Proof. exact (TRANS (@lem1024531 A rx lx ly ry mul h2) (@lem1024570 A lx ly rx ry mul h1)). Qed.
Lemma lem1024572 {A : Type'} (lx : A) (ly : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : ((term834 A lx ly mul rx ry) = (term840 A rx mul lx ly ry)) = ((term835 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)).
Proof. exact (MK_COMB (@lem1024505 A lx ly rx ry mul h2) (@lem1024571 A lx ly rx ry mul h1 h2)). Qed.
Lemma lem1024574 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024575 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024574 A x). Qed.
Lemma lem1024576 {A : Type'} (lx : A) (ly : A) (mul : type1400 A) (rx : A) (ry : A) : ((term835 A lx ly mul rx ry) = (term835 A lx ly mul rx ry)) = True.
Proof. exact (@lem1024575 A (term835 A lx ly mul rx ry)). Qed.
Lemma lem1024577 {A : Type'} (rx : A) (lx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : ((term834 A lx ly mul rx ry) = (term840 A rx mul lx ly ry)) = True.
Proof. exact (TRANS (@lem1024572 A lx ly rx ry mul h1 h2) (@lem1024576 A lx ly mul rx ry)). Qed.
Lemma lem1024578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024579 {A : Type'} (rx : A) (lx : A) (ly : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : (term841 A rx mul lx ly ry) = (and True).
Proof. exact (MK_COMB (@lem1024578) (@lem1024577 A rx lx ly ry mul h1 h2)). Qed.
Lemma lem1024585 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024586 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024585 A m n p mul h1). Qed.
Lemma lem1024587 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul lx ly rx) = (term95 A lx mul ly rx).
Proof. exact (@lem1024586 A lx ly rx mul h1). Qed.
Lemma lem1024600 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024601 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) : (term842 A mul lx ly rx) = (term843 A lx mul ly rx).
Proof. exact (MK_COMB (@lem1024600 A) (@lem1024587 A lx ly rx mul h1)). Qed.
Lemma lem1024603 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024604 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024603 A m n p mul h1). Qed.
Lemma lem1024605 {A : Type'} (lx : A) (rx : A) (ly : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul lx rx ly) = (term95 A lx mul rx ly).
Proof. exact (@lem1024604 A lx rx ly mul h1). Qed.
Lemma lem1024615 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1024616 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1024615 A n m mul h1). Qed.
Lemma lem1024617 {A : Type'} (ly : A) (rx : A) (mul : type1400 A) (h1 : term11 A mul) : (mul rx ly) = (mul ly rx).
Proof. exact (@lem1024616 A ly rx mul h1). Qed.
Lemma lem1024622 {A : Type'} (mul : type1400 A) (lx : A) : (mul lx) = (mul lx).
Proof. exact (eq_refl (mul lx)). Qed.
Lemma lem1024623 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term11 A mul) : (term95 A lx mul rx ly) = (term95 A lx mul ly rx).
Proof. exact (MK_COMB (@lem1024622 A mul lx) (@lem1024617 A ly rx mul h1)). Qed.
Lemma lem1024632 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) (h2 : term11 A mul) : (term104 A mul lx rx ly) = (term95 A lx mul ly rx).
Proof. exact (TRANS (@lem1024605 A lx rx ly mul h1) (@lem1024623 A lx ly rx mul h2)). Qed.
Lemma lem1024633 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) (h2 : term11 A mul) : ((term104 A mul lx ly rx) = (term104 A mul lx rx ly)) = ((term95 A lx mul ly rx) = (term95 A lx mul ly rx)).
Proof. exact (MK_COMB (@lem1024601 A lx ly rx mul h1) (@lem1024632 A lx ly rx mul h1 h2)). Qed.
Lemma lem1024635 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024636 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024635 A x). Qed.
Lemma lem1024637 {A : Type'} (lx : A) (mul : type1400 A) (ly : A) (rx : A) : ((term95 A lx mul ly rx) = (term95 A lx mul ly rx)) = True.
Proof. exact (@lem1024636 A (term95 A lx mul ly rx)). Qed.
Lemma lem1024638 {A : Type'} (lx : A) (rx : A) (ly : A) (mul : type1400 A) (h1 : term110 A mul) (h2 : term11 A mul) : ((term104 A mul lx ly rx) = (term104 A mul lx rx ly)) = True.
Proof. exact (TRANS (@lem1024633 A lx ly rx mul h1 h2) (@lem1024637 A lx mul ly rx)). Qed.
Lemma lem1024639 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024640 {A : Type'} (lx : A) (rx : A) (ly : A) (mul : type1400 A) (h1 : term110 A mul) (h2 : term11 A mul) : (term844 A mul lx rx ly) = (and True).
Proof. exact (MK_COMB (@lem1024639) (@lem1024638 A lx rx ly mul h1 h2)). Qed.
Lemma lem1024646 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024647 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024646 A m n p mul h1). Qed.
Lemma lem1024648 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul lx ly rx) = (term95 A lx mul ly rx).
Proof. exact (@lem1024647 A lx ly rx mul h1). Qed.
Lemma lem1024661 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024662 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) : (term842 A mul lx ly rx) = (term843 A lx mul ly rx).
Proof. exact (MK_COMB (@lem1024661 A) (@lem1024648 A lx ly rx mul h1)). Qed.
Lemma lem1024675 {A : Type'} (lx : A) (mul : type1400 A) (ly : A) (rx : A) : (term95 A lx mul ly rx) = (term95 A lx mul ly rx).
Proof. exact (eq_refl (term95 A lx mul ly rx)). Qed.
Lemma lem1024676 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) : ((term104 A mul lx ly rx) = (term95 A lx mul ly rx)) = ((term95 A lx mul ly rx) = (term95 A lx mul ly rx)).
Proof. exact (MK_COMB (@lem1024662 A lx ly rx mul h1) (@lem1024675 A lx mul ly rx)). Qed.
Lemma lem1024678 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024679 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024678 A x). Qed.
Lemma lem1024680 {A : Type'} (lx : A) (mul : type1400 A) (ly : A) (rx : A) : ((term95 A lx mul ly rx) = (term95 A lx mul ly rx)) = True.
Proof. exact (@lem1024679 A (term95 A lx mul ly rx)). Qed.
Lemma lem1024681 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) : ((term104 A mul lx ly rx) = (term95 A lx mul ly rx)) = True.
Proof. exact (TRANS (@lem1024676 A lx ly rx mul h1) (@lem1024680 A lx mul ly rx)). Qed.
Lemma lem1024682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024683 {A : Type'} (lx : A) (ly : A) (rx : A) (mul : type1400 A) (h1 : term110 A mul) : (term845 A lx mul ly rx) = (and True).
Proof. exact (MK_COMB (@lem1024682) (@lem1024681 A lx ly rx mul h1)). Qed.
Lemma lem1024693 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1024694 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1024693 A n m mul h1). Qed.
Lemma lem1024695 {A : Type'} (lx : A) (rx : A) (mul : type1400 A) (h1 : term11 A mul) : (mul rx lx) = (mul lx rx).
Proof. exact (@lem1024694 A lx rx mul h1). Qed.
Lemma lem1024700 {A : Type'} (mul : type1400 A) (lx : A) (rx : A) : (term815 A mul lx rx) = (term815 A mul lx rx).
Proof. exact (eq_refl (term815 A mul lx rx)). Qed.
Lemma lem1024701 {A : Type'} (lx : A) (rx : A) (mul : type1400 A) (h1 : term11 A mul) : ((mul lx rx) = (mul rx lx)) = ((mul lx rx) = (mul lx rx)).
Proof. exact (MK_COMB (@lem1024700 A mul lx rx) (@lem1024695 A lx rx mul h1)). Qed.
Lemma lem1024703 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024704 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024703 A x). Qed.
Lemma lem1024705 {A : Type'} (mul : type1400 A) (lx : A) (rx : A) : ((mul lx rx) = (mul lx rx)) = True.
Proof. exact (@lem1024704 A (mul lx rx)). Qed.
Lemma lem1024706 {A : Type'} (rx : A) (lx : A) (mul : type1400 A) (h1 : term11 A mul) : ((mul lx rx) = (mul rx lx)) = True.
Proof. exact (TRANS (@lem1024701 A lx rx mul h1) (@lem1024705 A mul lx rx)). Qed.
Lemma lem1024707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024708 {A : Type'} (rx : A) (lx : A) (mul : type1400 A) (h1 : term11 A mul) : (term831 A mul rx lx) = (and True).
Proof. exact (MK_COMB (@lem1024707) (@lem1024706 A rx lx mul h1)). Qed.
Lemma lem1024726 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1023903 A m mul n p) (@lem1023902 A m n p mul h1)). Qed.
Lemma lem1024727 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1024726 A m n p mul h1). Qed.
Lemma lem1024728 {A : Type'} (lx : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul lx rx ry) = (term95 A lx mul rx ry).
Proof. exact (@lem1024727 A lx rx ry mul h1). Qed.
Lemma lem1024741 {A : Type'} (lx : A) (mul : type1400 A) (rx : A) (ry : A) : (term843 A lx mul rx ry) = (term843 A lx mul rx ry).
Proof. exact (eq_refl (term843 A lx mul rx ry)). Qed.
Lemma lem1024742 {A : Type'} (lx : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : ((term95 A lx mul rx ry) = (term104 A mul lx rx ry)) = ((term95 A lx mul rx ry) = (term95 A lx mul rx ry)).
Proof. exact (MK_COMB (@lem1024741 A lx mul rx ry) (@lem1024728 A lx rx ry mul h1)). Qed.
Lemma lem1024744 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024745 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024744 A x). Qed.
Lemma lem1024746 {A : Type'} (lx : A) (mul : type1400 A) (rx : A) (ry : A) : ((term95 A lx mul rx ry) = (term95 A lx mul rx ry)) = True.
Proof. exact (@lem1024745 A (term95 A lx mul rx ry)). Qed.
Lemma lem1024747 {A : Type'} (lx : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : ((term95 A lx mul rx ry) = (term104 A mul lx rx ry)) = True.
Proof. exact (TRANS (@lem1024742 A lx rx ry mul h1) (@lem1024746 A lx mul rx ry)). Qed.
Lemma lem1024748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024749 {A : Type'} (lx : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term110 A mul) : (term846 A mul lx rx ry) = (and True).
Proof. exact (MK_COMB (@lem1024748) (@lem1024747 A lx rx ry mul h1)). Qed.
Lemma lem1024767 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1023912 A n mul m p) (@lem1023911 A n m p mul h1)). Qed.
Lemma lem1024768 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1024767 A n m p mul h1). Qed.
Lemma lem1024769 {A : Type'} (lx : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A rx mul lx ry) = (term95 A lx mul rx ry).
Proof. exact (@lem1024768 A lx rx ry mul h1). Qed.
Lemma lem1024782 {A : Type'} (lx : A) (mul : type1400 A) (rx : A) (ry : A) : (term843 A lx mul rx ry) = (term843 A lx mul rx ry).
Proof. exact (eq_refl (term843 A lx mul rx ry)). Qed.
Lemma lem1024783 {A : Type'} (lx : A) (rx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : ((term95 A lx mul rx ry) = (term95 A rx mul lx ry)) = ((term95 A lx mul rx ry) = (term95 A lx mul rx ry)).
Proof. exact (MK_COMB (@lem1024782 A lx mul rx ry) (@lem1024769 A lx rx ry mul h1)). Qed.
Lemma lem1024785 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024786 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024785 A x). Qed.
Lemma lem1024787 {A : Type'} (lx : A) (mul : type1400 A) (rx : A) (ry : A) : ((term95 A lx mul rx ry) = (term95 A lx mul rx ry)) = True.
Proof. exact (@lem1024786 A (term95 A lx mul rx ry)). Qed.
Lemma lem1024788 {A : Type'} (rx : A) (lx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : ((term95 A lx mul rx ry) = (term95 A rx mul lx ry)) = True.
Proof. exact (TRANS (@lem1024783 A lx rx ry mul h1) (@lem1024787 A lx mul rx ry)). Qed.
Lemma lem1024789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024790 {A : Type'} (rx : A) (lx : A) (ry : A) (mul : type1400 A) (h1 : term101 A mul) : (term847 A rx mul lx ry) = (and True).
Proof. exact (MK_COMB (@lem1024789) (@lem1024788 A rx lx ry mul h1)). Qed.
Lemma lem1024796 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1023876 A m add n p) (@lem1023875 A m n p add h1)). Qed.
Lemma lem1024797 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1024796 A m n p add h1). Qed.
Lemma lem1024798 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (h1 : term110 A add) : (term834 A a b add c d) = (term835 A a b add c d).
Proof. exact (@lem1024797 A a b (add c d) add h1). Qed.
Lemma lem1024819 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024820 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (h1 : term110 A add) : (term836 A a b add c d) = (term837 A a b add c d).
Proof. exact (MK_COMB (@lem1024819 A) (@lem1024798 A a b c d add h1)). Qed.
Lemma lem1024822 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1023876 A m add n p) (@lem1023875 A m n p add h1)). Qed.
Lemma lem1024823 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1024822 A m n p add h1). Qed.
Lemma lem1024824 {A : Type'} (a : A) (c : A) (b : A) (d : A) (add : type1400 A) (h1 : term110 A add) : (term834 A a c add b d) = (term835 A a c add b d).
Proof. exact (@lem1024823 A a c (add b d) add h1). Qed.
Lemma lem1024834 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term101 A add) : (term95 A m add n p) = (term95 A n add m p).
Proof. exact (EQ_MP (@lem1023885 A n add m p) (@lem1023884 A n m p add h1)). Qed.
Lemma lem1024835 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term101 A add) : (term95 A m add n p) = (term95 A n add m p).
Proof. exact (@lem1024834 A n m p add h1). Qed.
Lemma lem1024836 {A : Type'} (b : A) (c : A) (d : A) (add : type1400 A) (h1 : term101 A add) : (term95 A c add b d) = (term95 A b add c d).
Proof. exact (@lem1024835 A b c d add h1). Qed.
Lemma lem1024849 {A : Type'} (add : type1400 A) (a : A) : (add a) = (add a).
Proof. exact (eq_refl (add a)). Qed.
Lemma lem1024850 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (h1 : term101 A add) : (term835 A a c add b d) = (term835 A a b add c d).
Proof. exact (MK_COMB (@lem1024849 A add a) (@lem1024836 A b c d add h1)). Qed.
Lemma lem1024859 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (h1 : term101 A add) (h2 : term110 A add) : (term834 A a c add b d) = (term835 A a b add c d).
Proof. exact (TRANS (@lem1024824 A a c b d add h2) (@lem1024850 A a b c d add h1)). Qed.
Lemma lem1024860 {A : Type'} (a : A) (b : A) (c : A) (d : A) (add : type1400 A) (h1 : term101 A add) (h2 : term110 A add) : ((term834 A a b add c d) = (term834 A a c add b d)) = ((term835 A a b add c d) = (term835 A a b add c d)).
Proof. exact (MK_COMB (@lem1024820 A a b c d add h2) (@lem1024859 A a b c d add h1 h2)). Qed.
Lemma lem1024862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024863 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024862 A x). Qed.
Lemma lem1024864 {A : Type'} (a : A) (b : A) (add : type1400 A) (c : A) (d : A) : ((term835 A a b add c d) = (term835 A a b add c d)) = True.
Proof. exact (@lem1024863 A (term835 A a b add c d)). Qed.
Lemma lem1024865 {A : Type'} (a : A) (c : A) (b : A) (d : A) (add : type1400 A) (h1 : term101 A add) (h2 : term110 A add) : ((term834 A a b add c d) = (term834 A a c add b d)) = True.
Proof. exact (TRANS (@lem1024860 A a b c d add h1 h2) (@lem1024864 A a b add c d)). Qed.
Lemma lem1024866 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024867 {A : Type'} (a : A) (c : A) (b : A) (d : A) (add : type1400 A) (h1 : term101 A add) (h2 : term110 A add) : (term838 A a c add b d) = (and True).
Proof. exact (MK_COMB (@lem1024866) (@lem1024865 A a c b d add h1 h2)). Qed.
Lemma lem1024873 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1023876 A m add n p) (@lem1023875 A m n p add h1)). Qed.
Lemma lem1024874 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1024873 A m n p add h1). Qed.
Lemma lem1024875 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add a b c) = (term95 A a add b c).
Proof. exact (@lem1024874 A a b c add h1). Qed.
Lemma lem1024888 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024889 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) : (term842 A add a b c) = (term843 A a add b c).
Proof. exact (MK_COMB (@lem1024888 A) (@lem1024875 A a b c add h1)). Qed.
Lemma lem1024902 {A : Type'} (a : A) (add : type1400 A) (b : A) (c : A) : (term95 A a add b c) = (term95 A a add b c).
Proof. exact (eq_refl (term95 A a add b c)). Qed.
Lemma lem1024903 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) : ((term104 A add a b c) = (term95 A a add b c)) = ((term95 A a add b c) = (term95 A a add b c)).
Proof. exact (MK_COMB (@lem1024889 A a b c add h1) (@lem1024902 A a add b c)). Qed.
Lemma lem1024905 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024906 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024905 A x). Qed.
Lemma lem1024907 {A : Type'} (a : A) (add : type1400 A) (b : A) (c : A) : ((term95 A a add b c) = (term95 A a add b c)) = True.
Proof. exact (@lem1024906 A (term95 A a add b c)). Qed.
Lemma lem1024908 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) : ((term104 A add a b c) = (term95 A a add b c)) = True.
Proof. exact (TRANS (@lem1024903 A a b c add h1) (@lem1024907 A a add b c)). Qed.
Lemma lem1024909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024910 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) : (term845 A a add b c) = (and True).
Proof. exact (MK_COMB (@lem1024909) (@lem1024908 A a b c add h1)). Qed.
Lemma lem1024928 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term101 A add) : (term95 A m add n p) = (term95 A n add m p).
Proof. exact (EQ_MP (@lem1023885 A n add m p) (@lem1023884 A n m p add h1)). Qed.
Lemma lem1024929 {A : Type'} (n : A) (m : A) (p : A) (add : type1400 A) (h1 : term101 A add) : (term95 A m add n p) = (term95 A n add m p).
Proof. exact (@lem1024928 A n m p add h1). Qed.
Lemma lem1024930 {A : Type'} (a : A) (c : A) (d : A) (add : type1400 A) (h1 : term101 A add) : (term95 A c add a d) = (term95 A a add c d).
Proof. exact (@lem1024929 A a c d add h1). Qed.
Lemma lem1024943 {A : Type'} (a : A) (add : type1400 A) (c : A) (d : A) : (term843 A a add c d) = (term843 A a add c d).
Proof. exact (eq_refl (term843 A a add c d)). Qed.
Lemma lem1024944 {A : Type'} (a : A) (c : A) (d : A) (add : type1400 A) (h1 : term101 A add) : ((term95 A a add c d) = (term95 A c add a d)) = ((term95 A a add c d) = (term95 A a add c d)).
Proof. exact (MK_COMB (@lem1024943 A a add c d) (@lem1024930 A a c d add h1)). Qed.
Lemma lem1024946 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1024947 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1024946 A x). Qed.
Lemma lem1024948 {A : Type'} (a : A) (add : type1400 A) (c : A) (d : A) : ((term95 A a add c d) = (term95 A a add c d)) = True.
Proof. exact (@lem1024947 A (term95 A a add c d)). Qed.
Lemma lem1024949 {A : Type'} (c : A) (a : A) (d : A) (add : type1400 A) (h1 : term101 A add) : ((term95 A a add c d) = (term95 A c add a d)) = True.
Proof. exact (TRANS (@lem1024944 A a c d add h1) (@lem1024948 A a add c d)). Qed.
Lemma lem1024950 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1024951 {A : Type'} (c : A) (a : A) (d : A) (add : type1400 A) (h1 : term101 A add) : (term847 A c add a d) = (and True).
Proof. exact (MK_COMB (@lem1024950) (@lem1024949 A c a d add h1)). Qed.
Lemma lem1024957 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1023876 A m add n p) (@lem1023875 A m n p add h1)). Qed.
Lemma lem1024958 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1024957 A m n p add h1). Qed.
Lemma lem1024959 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add a b c) = (term95 A a add b c).
Proof. exact (@lem1024958 A a b c add h1). Qed.
Lemma lem1024972 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1024973 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) : (term842 A add a b c) = (term843 A a add b c).
Proof. exact (MK_COMB (@lem1024972 A) (@lem1024959 A a b c add h1)). Qed.
Lemma lem1024975 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1023876 A m add n p) (@lem1023875 A m n p add h1)). Qed.
Lemma lem1024976 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1024975 A m n p add h1). Qed.
Lemma lem1024977 {A : Type'} (a : A) (c : A) (b : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add a c b) = (term95 A a add c b).
Proof. exact (@lem1024976 A a c b add h1). Qed.
Lemma lem1024987 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (EQ_MP (@lem1023867 A add n m) (@lem1023866 A m n add h1)). Qed.
Lemma lem1024988 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (@lem1024987 A n m add h1). Qed.
Lemma lem1024989 {A : Type'} (b : A) (c : A) (add : type1400 A) (h1 : term11 A add) : (add c b) = (add b c).
Proof. exact (@lem1024988 A b c add h1). Qed.
Lemma lem1024994 {A : Type'} (add : type1400 A) (a : A) : (add a) = (add a).
Proof. exact (eq_refl (add a)). Qed.
Lemma lem1024995 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term11 A add) : (term95 A a add c b) = (term95 A a add b c).
Proof. exact (MK_COMB (@lem1024994 A add a) (@lem1024989 A b c add h1)). Qed.
Lemma lem1025004 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) (h2 : term11 A add) : (term104 A add a c b) = (term95 A a add b c).
Proof. exact (TRANS (@lem1024977 A a c b add h1) (@lem1024995 A a b c add h2)). Qed.
Lemma lem1025005 {A : Type'} (a : A) (b : A) (c : A) (add : type1400 A) (h1 : term110 A add) (h2 : term11 A add) : ((term104 A add a b c) = (term104 A add a c b)) = ((term95 A a add b c) = (term95 A a add b c)).
Proof. exact (MK_COMB (@lem1024973 A a b c add h1) (@lem1025004 A a b c add h1 h2)). Qed.
Lemma lem1025007 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025008 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025007 A x). Qed.
Lemma lem1025009 {A : Type'} (a : A) (add : type1400 A) (b : A) (c : A) : ((term95 A a add b c) = (term95 A a add b c)) = True.
Proof. exact (@lem1025008 A (term95 A a add b c)). Qed.
Lemma lem1025010 {A : Type'} (a : A) (c : A) (b : A) (add : type1400 A) (h1 : term110 A add) (h2 : term11 A add) : ((term104 A add a b c) = (term104 A add a c b)) = True.
Proof. exact (TRANS (@lem1025005 A a b c add h1 h2) (@lem1025009 A a add b c)). Qed.
Lemma lem1025011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025012 {A : Type'} (a : A) (c : A) (b : A) (add : type1400 A) (h1 : term110 A add) (h2 : term11 A add) : (term844 A add a c b) = (and True).
Proof. exact (MK_COMB (@lem1025011) (@lem1025010 A a c b add h1 h2)). Qed.
Lemma lem1025022 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (EQ_MP (@lem1023867 A add n m) (@lem1023866 A m n add h1)). Qed.
Lemma lem1025023 {A : Type'} (n : A) (m : A) (add : type1400 A) (h1 : term11 A add) : (add m n) = (add n m).
Proof. exact (@lem1025022 A n m add h1). Qed.
Lemma lem1025024 {A : Type'} (a : A) (c : A) (add : type1400 A) (h1 : term11 A add) : (add c a) = (add a c).
Proof. exact (@lem1025023 A a c add h1). Qed.
Lemma lem1025029 {A : Type'} (add : type1400 A) (a : A) (c : A) : (term815 A add a c) = (term815 A add a c).
Proof. exact (eq_refl (term815 A add a c)). Qed.
Lemma lem1025030 {A : Type'} (a : A) (c : A) (add : type1400 A) (h1 : term11 A add) : ((add a c) = (add c a)) = ((add a c) = (add a c)).
Proof. exact (MK_COMB (@lem1025029 A add a c) (@lem1025024 A a c add h1)). Qed.
Lemma lem1025032 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025033 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025032 A x). Qed.
Lemma lem1025034 {A : Type'} (add : type1400 A) (a : A) (c : A) : ((add a c) = (add a c)) = True.
Proof. exact (@lem1025033 A (add a c)). Qed.
Lemma lem1025035 {A : Type'} (c : A) (a : A) (add : type1400 A) (h1 : term11 A add) : ((add a c) = (add c a)) = True.
Proof. exact (TRANS (@lem1025030 A a c add h1) (@lem1025034 A add a c)). Qed.
Lemma lem1025036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025037 {A : Type'} (c : A) (a : A) (add : type1400 A) (h1 : term11 A add) : (term831 A add c a) = (and True).
Proof. exact (MK_COMB (@lem1025036) (@lem1025035 A c a add h1)). Qed.
Lemma lem1025055 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (EQ_MP (@lem1023876 A m add n p) (@lem1023875 A m n p add h1)). Qed.
Lemma lem1025056 {A : Type'} (m : A) (n : A) (p : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add m n p) = (term95 A m add n p).
Proof. exact (@lem1025055 A m n p add h1). Qed.
Lemma lem1025057 {A : Type'} (a : A) (c : A) (d : A) (add : type1400 A) (h1 : term110 A add) : (term104 A add a c d) = (term95 A a add c d).
Proof. exact (@lem1025056 A a c d add h1). Qed.
Lemma lem1025070 {A : Type'} (a : A) (add : type1400 A) (c : A) (d : A) : (term843 A a add c d) = (term843 A a add c d).
Proof. exact (eq_refl (term843 A a add c d)). Qed.
Lemma lem1025071 {A : Type'} (a : A) (c : A) (d : A) (add : type1400 A) (h1 : term110 A add) : ((term95 A a add c d) = (term104 A add a c d)) = ((term95 A a add c d) = (term95 A a add c d)).
Proof. exact (MK_COMB (@lem1025070 A a add c d) (@lem1025057 A a c d add h1)). Qed.
Lemma lem1025073 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025073 A x). Qed.
Lemma lem1025075 {A : Type'} (a : A) (add : type1400 A) (c : A) (d : A) : ((term95 A a add c d) = (term95 A a add c d)) = True.
Proof. exact (@lem1025074 A (term95 A a add c d)). Qed.
Lemma lem1025076 {A : Type'} (a : A) (c : A) (d : A) (add : type1400 A) (h1 : term110 A add) : ((term95 A a add c d) = (term104 A add a c d)) = True.
Proof. exact (TRANS (@lem1025071 A a c d add h1) (@lem1025075 A a add c d)). Qed.
Lemma lem1025077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025078 {A : Type'} (a : A) (c : A) (d : A) (add : type1400 A) (h1 : term110 A add) : (term846 A add a c d) = (and True).
Proof. exact (MK_COMB (@lem1025077) (@lem1025076 A a c d add h1)). Qed.
Lemma lem1025092 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025093 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025092 A n m mul h1). Qed.
Lemma lem1025094 {A : Type'} (pwr : type1423 A) (q : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr x q) = (term848 A mul pwr q x).
Proof. exact (@lem1025093 A (pwr x q) x mul h1). Qed.
Lemma lem1025099 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1025100 {A : Type'} (pwr : type1423 A) (q : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term849 A mul pwr x q) = (term850 A mul pwr q x).
Proof. exact (MK_COMB (@lem1025099 A) (@lem1025094 A pwr q x mul h1)). Qed.
Lemma lem1025102 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1023861 A mul pwr x n) (@lem1023860 A x n mul pwr h1)). Qed.
Lemma lem1025103 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1025102 A x n mul pwr h1). Qed.
Lemma lem1025104 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x q) = (term122 A mul pwr x q).
Proof. exact (@lem1025103 A x q mul pwr h1). Qed.
Lemma lem1025106 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025107 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025106 A n m mul h1). Qed.
Lemma lem1025108 {A : Type'} (pwr : type1423 A) (q : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr x q) = (term848 A mul pwr q x).
Proof. exact (@lem1025107 A (pwr x q) x mul h1). Qed.
Lemma lem1025113 {A : Type'} (q : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term121 A pwr x q) = (term848 A mul pwr q x).
Proof. exact (TRANS (@lem1025104 A x q mul pwr h2) (@lem1025108 A pwr q x mul h1)). Qed.
Lemma lem1025114 {A : Type'} (q : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : ((term122 A mul pwr x q) = (term121 A pwr x q)) = ((term848 A mul pwr q x) = (term848 A mul pwr q x)).
Proof. exact (MK_COMB (@lem1025100 A pwr q x mul h1) (@lem1025113 A q x mul pwr h1 h2)). Qed.
Lemma lem1025116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025117 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025116 A x). Qed.
Lemma lem1025118 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (q : nat) (x : A) : ((term848 A mul pwr q x) = (term848 A mul pwr q x)) = True.
Proof. exact (@lem1025117 A (term848 A mul pwr q x)). Qed.
Lemma lem1025119 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : ((term122 A mul pwr x q) = (term121 A pwr x q)) = True.
Proof. exact (TRANS (@lem1025114 A q x mul pwr h1 h2) (@lem1025118 A mul pwr q x)). Qed.
Lemma lem1025120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025121 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term851 A mul pwr x q) = (and True).
Proof. exact (MK_COMB (@lem1025120) (@lem1025119 A x q mul pwr h1 h2)). Qed.
Lemma lem1025131 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1023861 A mul pwr x n) (@lem1023860 A x n mul pwr h1)). Qed.
Lemma lem1025132 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1025131 A x n mul pwr h1). Qed.
Lemma lem1025133 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x q) = (term122 A mul pwr x q).
Proof. exact (@lem1025132 A x q mul pwr h1). Qed.
Lemma lem1025135 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025136 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025135 A n m mul h1). Qed.
Lemma lem1025137 {A : Type'} (pwr : type1423 A) (q : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr x q) = (term848 A mul pwr q x).
Proof. exact (@lem1025136 A (pwr x q) x mul h1). Qed.
Lemma lem1025142 {A : Type'} (q : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term121 A pwr x q) = (term848 A mul pwr q x).
Proof. exact (TRANS (@lem1025133 A x q mul pwr h2) (@lem1025137 A pwr q x mul h1)). Qed.
Lemma lem1025143 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (q : nat) (x : A) : (term850 A mul pwr q x) = (term850 A mul pwr q x).
Proof. exact (eq_refl (term850 A mul pwr q x)). Qed.
Lemma lem1025144 {A : Type'} (q : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : ((term848 A mul pwr q x) = (term121 A pwr x q)) = ((term848 A mul pwr q x) = (term848 A mul pwr q x)).
Proof. exact (MK_COMB (@lem1025143 A mul pwr q x) (@lem1025142 A q x mul pwr h1 h2)). Qed.
Lemma lem1025146 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025147 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025146 A x). Qed.
Lemma lem1025148 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (q : nat) (x : A) : ((term848 A mul pwr q x) = (term848 A mul pwr q x)) = True.
Proof. exact (@lem1025147 A (term848 A mul pwr q x)). Qed.
Lemma lem1025149 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : ((term848 A mul pwr q x) = (term121 A pwr x q)) = True.
Proof. exact (TRANS (@lem1025144 A q x mul pwr h1 h2) (@lem1025148 A mul pwr q x)). Qed.
Lemma lem1025150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025151 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term852 A mul pwr x q) = (and True).
Proof. exact (MK_COMB (@lem1025150) (@lem1025149 A x q mul pwr h1 h2)). Qed.
Lemma lem1025161 : term6 = term5.
Proof. exact (SYM (@lem1017027)). Qed.
Lemma lem1025163 : term2 = term1.
Proof. exact (SYM (@lem1017023)). Qed.
Lemma lem1025164 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem1025165 : term5 = term853.
Proof. exact (MK_COMB (@lem1025164) (@lem1025163)). Qed.
Lemma lem1025166 : term6 = term853.
Proof. exact (TRANS (@lem1025161) (@lem1025165)). Qed.
Lemma lem1025167 {A : Type'} (pwr : type1423 A) (x : A) : (pwr x) = (pwr x).
Proof. exact (eq_refl (pwr x)). Qed.
Lemma lem1025168 {A : Type'} (pwr : type1423 A) (x : A) : (term854 A pwr x) = (term855 A pwr x).
Proof. exact (MK_COMB (@lem1025167 A pwr x) (@lem1025166)). Qed.
Lemma lem1025170 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1023861 A mul pwr x n) (@lem1023860 A x n mul pwr h1)). Qed.
Lemma lem1025171 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1025170 A x n mul pwr h1). Qed.
Lemma lem1025172 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term855 A pwr x) = (term856 A mul pwr x).
Proof. exact (@lem1025171 A x term1 mul pwr h1). Qed.
Lemma lem1025174 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025175 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025174 A n m mul h1). Qed.
Lemma lem1025176 {A : Type'} (pwr : type1423 A) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term856 A mul pwr x) = (term857 A mul pwr x).
Proof. exact (@lem1025175 A (term858 A pwr x) x mul h1). Qed.
Lemma lem1025182 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1023861 A mul pwr x n) (@lem1023860 A x n mul pwr h1)). Qed.
Lemma lem1025183 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1025182 A x n mul pwr h1). Qed.
Lemma lem1025184 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term858 A pwr x) = (term859 A mul pwr x).
Proof. exact (@lem1025183 A x (NUMERAL 0) mul pwr h1). Qed.
Lemma lem1025186 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025187 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025186 A n m mul h1). Qed.
Lemma lem1025188 {A : Type'} (pwr : type1423 A) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term859 A mul pwr x) = (term860 A mul pwr x).
Proof. exact (@lem1025187 A (term126 A pwr x) x mul h1). Qed.
Lemma lem1025193 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term858 A pwr x) = (term860 A mul pwr x).
Proof. exact (TRANS (@lem1025184 A x mul pwr h2) (@lem1025188 A pwr x mul h1)). Qed.
Lemma lem1025195 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1023855 A pwr x r1) (@lem1023854 A x pwr r1 h1)). Qed.
Lemma lem1025196 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1025195 A x pwr r1 h1). Qed.
Lemma lem1025197 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1025198 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term861 A mul pwr x) = (mul r1).
Proof. exact (MK_COMB (@lem1025197 A mul) (@lem1025196 A x pwr r1 h1)). Qed.
Lemma lem1025199 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1025200 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term860 A mul pwr x) = (mul r1 x).
Proof. exact (MK_COMB (@lem1025198 A x mul pwr r1 h1) (@lem1025199 A x)). Qed.
Lemma lem1025202 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1025203 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1025202 A x mul r1 h1). Qed.
Lemma lem1025204 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term13 A mul r1) (h2 : term22 A pwr r1) : (term860 A mul pwr x) = x.
Proof. exact (TRANS (@lem1025200 A mul x pwr r1 h2) (@lem1025203 A x mul r1 h1)). Qed.
Lemma lem1025205 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term858 A pwr x) = x.
Proof. exact (TRANS (@lem1025193 A x mul pwr h1 h2) (@lem1025204 A x mul pwr r1 h3 h4)). Qed.
Lemma lem1025206 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1025207 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term862 A mul pwr x) = (mul x).
Proof. exact (MK_COMB (@lem1025206 A mul) (@lem1025205 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025208 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1025209 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term857 A mul pwr x) = (mul x x).
Proof. exact (MK_COMB (@lem1025207 A x mul pwr r1 h1 h2 h3 h4) (@lem1025208 A x)). Qed.
Lemma lem1025214 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term856 A mul pwr x) = (mul x x).
Proof. exact (TRANS (@lem1025176 A pwr x mul h1) (@lem1025209 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025215 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term855 A pwr x) = (mul x x).
Proof. exact (TRANS (@lem1025172 A x mul pwr h2) (@lem1025214 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025216 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term854 A pwr x) = (mul x x).
Proof. exact (TRANS (@lem1025168 A pwr x) (@lem1025215 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025217 {A : Type'} (mul : type1400 A) (x : A) : (term828 A mul x) = (term828 A mul x).
Proof. exact (eq_refl (term828 A mul x)). Qed.
Lemma lem1025218 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : ((mul x x) = (term854 A pwr x)) = ((mul x x) = (mul x x)).
Proof. exact (MK_COMB (@lem1025217 A mul x) (@lem1025216 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025220 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025221 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025220 A x). Qed.
Lemma lem1025222 {A : Type'} (mul : type1400 A) (x : A) : ((mul x x) = (mul x x)) = True.
Proof. exact (@lem1025221 A (mul x x)). Qed.
Lemma lem1025223 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : ((mul x x) = (term854 A pwr x)) = True.
Proof. exact (TRANS (@lem1025218 A x mul pwr r1 h1 h2 h3 h4) (@lem1025222 A mul x)). Qed.
Lemma lem1025224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025225 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term863 A mul pwr x) = (and True).
Proof. exact (MK_COMB (@lem1025224) (@lem1025223 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025247 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1023855 A pwr x r1) (@lem1023854 A x pwr r1 h1)). Qed.
Lemma lem1025248 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1025247 A x pwr r1 h1). Qed.
Lemma lem1025249 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1025250 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term864 A pwr x) = (@eq A r1).
Proof. exact (MK_COMB (@lem1025249 A) (@lem1025248 A x pwr r1 h1)). Qed.
Lemma lem1025251 {A : Type'} (r1 : A) : r1 = r1.
Proof. exact (eq_refl r1). Qed.
Lemma lem1025252 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : ((term126 A pwr x) = r1) = (r1 = r1).
Proof. exact (MK_COMB (@lem1025250 A x pwr r1 h1) (@lem1025251 A r1)). Qed.
Lemma lem1025254 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025255 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025254 A x). Qed.
Lemma lem1025256 {A : Type'} (r1 : A) : (r1 = r1) = True.
Proof. exact (@lem1025255 A r1). Qed.
Lemma lem1025257 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : ((term126 A pwr x) = r1) = True.
Proof. exact (TRANS (@lem1025252 A x pwr r1 h1) (@lem1025256 A r1)). Qed.
Lemma lem1025258 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025259 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term865 A pwr x r1) = (and True).
Proof. exact (MK_COMB (@lem1025258) (@lem1025257 A x pwr r1 h1)). Qed.
Lemma lem1025265 : term2 = term1.
Proof. exact (SYM (@lem1017023)). Qed.
Lemma lem1025266 {A : Type'} (pwr : type1423 A) (x : A) : (pwr x) = (pwr x).
Proof. exact (eq_refl (pwr x)). Qed.
Lemma lem1025267 {A : Type'} (pwr : type1423 A) (x : A) : (term866 A pwr x) = (term858 A pwr x).
Proof. exact (MK_COMB (@lem1025266 A pwr x) (@lem1025265)). Qed.
Lemma lem1025269 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1023861 A mul pwr x n) (@lem1023860 A x n mul pwr h1)). Qed.
Lemma lem1025270 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1025269 A x n mul pwr h1). Qed.
Lemma lem1025271 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term858 A pwr x) = (term859 A mul pwr x).
Proof. exact (@lem1025270 A x (NUMERAL 0) mul pwr h1). Qed.
Lemma lem1025273 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025274 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025273 A n m mul h1). Qed.
Lemma lem1025275 {A : Type'} (pwr : type1423 A) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term859 A mul pwr x) = (term860 A mul pwr x).
Proof. exact (@lem1025274 A (term126 A pwr x) x mul h1). Qed.
Lemma lem1025281 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1023855 A pwr x r1) (@lem1023854 A x pwr r1 h1)). Qed.
Lemma lem1025282 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1025281 A x pwr r1 h1). Qed.
Lemma lem1025283 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1025284 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term861 A mul pwr x) = (mul r1).
Proof. exact (MK_COMB (@lem1025283 A mul) (@lem1025282 A x pwr r1 h1)). Qed.
Lemma lem1025285 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1025286 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term860 A mul pwr x) = (mul r1 x).
Proof. exact (MK_COMB (@lem1025284 A x mul pwr r1 h1) (@lem1025285 A x)). Qed.
Lemma lem1025288 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1023840 A mul r1 x) (@lem1023839 A x mul r1 h1)). Qed.
Lemma lem1025289 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1025288 A x mul r1 h1). Qed.
Lemma lem1025290 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term13 A mul r1) (h2 : term22 A pwr r1) : (term860 A mul pwr x) = x.
Proof. exact (TRANS (@lem1025286 A mul x pwr r1 h2) (@lem1025289 A x mul r1 h1)). Qed.
Lemma lem1025291 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term13 A mul r1) (h3 : term22 A pwr r1) : (term859 A mul pwr x) = x.
Proof. exact (TRANS (@lem1025275 A pwr x mul h1) (@lem1025290 A x mul pwr r1 h2 h3)). Qed.
Lemma lem1025292 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term858 A pwr x) = x.
Proof. exact (TRANS (@lem1025271 A x mul pwr h2) (@lem1025291 A x mul pwr r1 h1 h3 h4)). Qed.
Lemma lem1025293 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term866 A pwr x) = x.
Proof. exact (TRANS (@lem1025267 A pwr x) (@lem1025292 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025294 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1025295 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term867 A pwr x) = (@eq A x).
Proof. exact (MK_COMB (@lem1025294 A) (@lem1025293 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025296 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1025297 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : ((term866 A pwr x) = x) = (x = x).
Proof. exact (MK_COMB (@lem1025295 A x mul pwr r1 h1 h2 h3 h4) (@lem1025296 A x)). Qed.
Lemma lem1025299 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025300 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025299 A x). Qed.
Lemma lem1025301 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : ((term866 A pwr x) = x) = True.
Proof. exact (TRANS (@lem1025297 A x mul pwr r1 h1 h2 h3 h4) (@lem1025300 A x)). Qed.
Lemma lem1025302 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025303 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term11 A mul) (h2 : term21 A mul pwr) (h3 : term13 A mul r1) (h4 : term22 A pwr r1) : (term868 A pwr x) = (and True).
Proof. exact (MK_COMB (@lem1025302) (@lem1025301 A x mul pwr r1 h1 h2 h3 h4)). Qed.
Lemma lem1025309 {A : Type'} (y : A) (x : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term128 A mul x add y z) = (term129 A add y mul x z).
Proof. exact (EQ_MP (@lem1023852 A add y mul x z) (@lem1023851 A y x z add mul h1)). Qed.
Lemma lem1025310 {A : Type'} (y : A) (x : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term128 A mul x add y z) = (term129 A add y mul x z).
Proof. exact (@lem1025309 A y x z add mul h1). Qed.
Lemma lem1025323 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1025324 {A : Type'} (y : A) (x : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term869 A mul x add y z) = (term870 A add y mul x z).
Proof. exact (MK_COMB (@lem1025323 A) (@lem1025310 A y x z add mul h1)). Qed.
Lemma lem1025337 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : (term129 A add y mul x z) = (term129 A add y mul x z).
Proof. exact (eq_refl (term129 A add y mul x z)). Qed.
Lemma lem1025338 {A : Type'} (y : A) (x : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : ((term128 A mul x add y z) = (term129 A add y mul x z)) = ((term129 A add y mul x z) = (term129 A add y mul x z)).
Proof. exact (MK_COMB (@lem1025324 A y x z add mul h1) (@lem1025337 A add y mul x z)). Qed.
Lemma lem1025340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025341 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025340 A x). Qed.
Lemma lem1025342 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : ((term129 A add y mul x z) = (term129 A add y mul x z)) = True.
Proof. exact (@lem1025341 A (term129 A add y mul x z)). Qed.
Lemma lem1025343 {A : Type'} (y : A) (x : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : ((term128 A mul x add y z) = (term129 A add y mul x z)) = True.
Proof. exact (TRANS (@lem1025338 A y x z add mul h1) (@lem1025342 A add y mul x z)). Qed.
Lemma lem1025344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1025345 {A : Type'} (y : A) (x : A) (z : A) (add : type1400 A) (mul : type1400 A) (h1 : term20 A add mul) : (term871 A add y mul x z) = (and True).
Proof. exact (MK_COMB (@lem1025344) (@lem1025343 A y x z add mul h1)). Qed.
Lemma lem1025349 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1023861 A mul pwr x n) (@lem1023860 A x n mul pwr h1)). Qed.
Lemma lem1025350 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1025349 A x n mul pwr h1). Qed.
Lemma lem1025351 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x q) = (term122 A mul pwr x q).
Proof. exact (@lem1025350 A x q mul pwr h1). Qed.
Lemma lem1025353 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025354 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025353 A n m mul h1). Qed.
Lemma lem1025355 {A : Type'} (pwr : type1423 A) (q : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr x q) = (term848 A mul pwr q x).
Proof. exact (@lem1025354 A (pwr x q) x mul h1). Qed.
Lemma lem1025360 {A : Type'} (q : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term121 A pwr x q) = (term848 A mul pwr q x).
Proof. exact (TRANS (@lem1025351 A x q mul pwr h2) (@lem1025355 A pwr q x mul h1)). Qed.
Lemma lem1025361 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1025362 {A : Type'} (q : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term872 A pwr x q) = (term850 A mul pwr q x).
Proof. exact (MK_COMB (@lem1025361 A) (@lem1025360 A q x mul pwr h1 h2)). Qed.
Lemma lem1025364 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1023894 A mul n m) (@lem1023893 A m n mul h1)). Qed.
Lemma lem1025365 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1025364 A n m mul h1). Qed.
Lemma lem1025366 {A : Type'} (pwr : type1423 A) (q : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr x q) = (term848 A mul pwr q x).
Proof. exact (@lem1025365 A (pwr x q) x mul h1). Qed.
Lemma lem1025371 {A : Type'} (q : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : ((term121 A pwr x q) = (term122 A mul pwr x q)) = ((term848 A mul pwr q x) = (term848 A mul pwr q x)).
Proof. exact (MK_COMB (@lem1025362 A q x mul pwr h1 h2) (@lem1025366 A pwr q x mul h1)). Qed.
Lemma lem1025373 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1025374 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1025373 A x). Qed.
Lemma lem1025375 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (q : nat) (x : A) : ((term848 A mul pwr q x) = (term848 A mul pwr q x)) = True.
Proof. exact (@lem1025374 A (term848 A mul pwr q x)). Qed.
Lemma lem1025376 {A : Type'} (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : ((term121 A pwr x q) = (term122 A mul pwr x q)) = True.
Proof. exact (TRANS (@lem1025371 A q x mul pwr h1 h2) (@lem1025375 A mul pwr q x)). Qed.
Lemma lem1025377 {A : Type'} (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) : (term873 A add y z mul pwr x q) = (True /\ True).
Proof. exact (MK_COMB (@lem1025345 A y x z add mul h1) (@lem1025376 A x q mul pwr h2 h3)). Qed.
Lemma lem1025379 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025380 : (True /\ True) = True.
Proof. exact (@lem1025379 True). Qed.
Lemma lem1025381 {A : Type'} (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) : (term873 A add y z mul pwr x q) = True.
Proof. exact (TRANS (@lem1025377 A y z x q add mul pwr h1 h2 h3) (@lem1025380)). Qed.
Lemma lem1025382 {A : Type'} (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term874 A add y z mul pwr x q) = (True /\ True).
Proof. exact (MK_COMB (@lem1025303 A x mul pwr r1 h2 h3 h4 h5) (@lem1025381 A y z x q add mul pwr h1 h2 h3)). Qed.
Lemma lem1025384 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025385 : (True /\ True) = True.
Proof. exact (@lem1025384 True). Qed.
Lemma lem1025386 {A : Type'} (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term874 A add y z mul pwr x q) = True.
Proof. exact (TRANS (@lem1025382 A y z x q add mul pwr r1 h1 h2 h3 h4 h5) (@lem1025385)). Qed.
Lemma lem1025387 {A : Type'} (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term875 A r1 add y z mul pwr x q) = (True /\ True).
Proof. exact (MK_COMB (@lem1025259 A x pwr r1 h5) (@lem1025386 A y z x q add mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1025389 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025390 : (True /\ True) = True.
Proof. exact (@lem1025389 True). Qed.
Lemma lem1025391 {A : Type'} (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term875 A r1 add y z mul pwr x q) = True.
Proof. exact (TRANS (@lem1025387 A y z x q add mul pwr r1 h1 h2 h3 h4 h5) (@lem1025390)). Qed.
Lemma lem1025392 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term876 A pwr x p q) = (term876 A pwr x p q).
Proof. exact (eq_refl (term876 A pwr x p q)). Qed.
Lemma lem1025393 {A : Type'} (y : A) (z : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term877 A p r1 add y z mul pwr x q) = (term878 A pwr x p q).
Proof. exact (MK_COMB (@lem1025392 A pwr x p q) (@lem1025391 A y z x q add mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1025395 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1025396 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term878 A pwr x p q) = ((term879 A pwr x p q) = (term880 A pwr x p q)).
Proof. exact (@lem1025395 ((term879 A pwr x p q) = (term880 A pwr x p q))). Qed.
Lemma lem1025399 {A : Type'} (y : A) (z : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term877 A p r1 add y z mul pwr x q) = ((term879 A pwr x p q) = (term880 A pwr x p q)).
Proof. exact (TRANS (@lem1025393 A y z x p q add mul pwr r1 h1 h2 h3 h4 h5) (@lem1025396 A pwr x p q)). Qed.
Lemma lem1025400 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) : (term881 A mul x pwr y q) = (term881 A mul x pwr y q).
Proof. exact (eq_refl (term881 A mul x pwr y q)). Qed.
Lemma lem1025401 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term882 A p r1 add y z mul pwr x q) = (term883 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025400 A mul x pwr y q) (@lem1025399 A y z x p q add mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1025404 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term884 A p r1 add y z mul pwr x q) = (term885 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025225 A x mul pwr r1 h2 h3 h4 h5) (@lem1025401 A z y x p q add mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1025406 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025407 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term885 A mul y pwr x p q) = (term883 A mul y pwr x p q).
Proof. exact (@lem1025406 (term883 A mul y pwr x p q)). Qed.
Lemma lem1025422 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term884 A p r1 add y z mul pwr x q) = (term883 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025404 A z y x p q add mul pwr r1 h1 h2 h3 h4 h5) (@lem1025407 A mul y pwr x p q)). Qed.
Lemma lem1025423 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term886 A p r1 add y z mul pwr x q) = (term885 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025151 A x q mul pwr h2 h3) (@lem1025422 A z y x p q add mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1025425 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025426 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term885 A mul y pwr x p q) = (term883 A mul y pwr x p q).
Proof. exact (@lem1025425 (term883 A mul y pwr x p q)). Qed.
Lemma lem1025441 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term886 A p r1 add y z mul pwr x q) = (term883 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025423 A z y x p q add mul pwr r1 h1 h2 h3 h4 h5) (@lem1025426 A mul y pwr x p q)). Qed.
Lemma lem1025442 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term887 A p r1 add y z mul pwr x q) = (term885 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025121 A x q mul pwr h2 h3) (@lem1025441 A z y x p q add mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1025444 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025445 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term885 A mul y pwr x p q) = (term883 A mul y pwr x p q).
Proof. exact (@lem1025444 (term883 A mul y pwr x p q)). Qed.
Lemma lem1025460 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term887 A p r1 add y z mul pwr x q) = (term883 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025442 A z y x p q add mul pwr r1 h1 h2 h3 h4 h5) (@lem1025445 A mul y pwr x p q)). Qed.
Lemma lem1025461 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term888 A mul pwr x p q) = (term888 A mul pwr x p q).
Proof. exact (eq_refl (term888 A mul pwr x p q)). Qed.
Lemma lem1025462 {A : Type'} (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : (term889 A p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025461 A mul pwr x p q) (@lem1025460 A z y x p q add mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1025465 {A : Type'} (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : (term891 A a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025078 A a c d add h1) (@lem1025462 A z y x p q add mul pwr r1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1025467 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025468 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025467 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025491 {A : Type'} (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : (term891 A a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025465 A a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6) (@lem1025468 A mul y pwr x p q)). Qed.
Lemma lem1025492 {A : Type'} (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term21 A mul pwr) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) : (term893 A a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025037 A c a add h3) (@lem1025491 A a c d z y x p q add mul pwr r1 h1 h2 h4 h5 h6 h7)). Qed.
Lemma lem1025494 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025495 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025494 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025518 {A : Type'} (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term21 A mul pwr) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) : (term893 A a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025492 A a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7) (@lem1025495 A mul y pwr x p q)). Qed.
Lemma lem1025519 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term21 A mul pwr) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) : (term894 A b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1025012 A a c b add h1 h3) (@lem1025518 A a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7)). Qed.
Lemma lem1025521 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025522 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025521 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025545 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term21 A mul pwr) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) : (term894 A b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025519 A b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7) (@lem1025522 A mul y pwr x p q)). Qed.
Lemma lem1025546 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) : (term895 A b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024951 A c a d add h1) (@lem1025545 A b a c d z y x p q add mul pwr r1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1025548 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025549 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025548 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025572 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) : (term895 A b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025546 A b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1025549 A mul y pwr x p q)). Qed.
Lemma lem1025573 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) : (term896 A b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024910 A a b c add h2) (@lem1025572 A b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1025575 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025576 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025575 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025599 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) : (term896 A b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025573 A b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1025576 A mul y pwr x p q)). Qed.
Lemma lem1025600 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) : (term897 A b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024867 A a c b d add h1 h2) (@lem1025599 A b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8)). Qed.
Lemma lem1025602 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025603 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025602 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025626 {A : Type'} (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) : (term897 A b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025600 A b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1025603 A mul y pwr x p q)). Qed.
Lemma lem1025627 {A : Type'} (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) : (term898 A rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024790 A rx lx ry mul h4) (@lem1025626 A b a c d z y x p q add mul pwr r1 h1 h2 h3 h5 h6 h7 h8 h9)). Qed.
Lemma lem1025629 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025630 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025629 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025653 {A : Type'} (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) : (term898 A rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025627 A rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1025630 A mul y pwr x p q)). Qed.
Lemma lem1025654 {A : Type'} (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term899 A rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024749 A lx rx ry mul h5) (@lem1025653 A rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h6 h7 h8 h9 h10)). Qed.
Lemma lem1025656 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025657 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025656 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025680 {A : Type'} (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term899 A rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025654 A rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1025657 A mul y pwr x p q)). Qed.
Lemma lem1025681 {A : Type'} (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term900 A rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024708 A rx lx mul h7) (@lem1025680 A rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1025683 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025684 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025683 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025707 {A : Type'} (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term900 A rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025681 A rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1025684 A mul y pwr x p q)). Qed.
Lemma lem1025708 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term901 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024683 A lx ly rx mul h5) (@lem1025707 A rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1025710 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025711 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025710 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025734 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term901 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025708 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1025711 A mul y pwr x p q)). Qed.
Lemma lem1025735 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term902 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024640 A lx rx ly mul h5 h7) (@lem1025734 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1025737 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025738 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025737 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025761 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term902 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025735 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1025738 A mul y pwr x p q)). Qed.
Lemma lem1025762 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term903 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024579 A rx lx ly ry mul h4 h5) (@lem1025761 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1025764 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025765 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025764 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025788 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term903 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025762 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1025765 A mul y pwr x p q)). Qed.
Lemma lem1025789 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term904 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024475 A lx ly rx ry mul h5) (@lem1025788 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1025791 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025792 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025791 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025815 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term904 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025789 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1025792 A mul y pwr x p q)). Qed.
Lemma lem1025816 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term905 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024416 A lx rx ly ry mul h4 h5) (@lem1025815 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1025818 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025819 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025818 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025842 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term905 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025816 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1025819 A mul y pwr x p q)). Qed.
Lemma lem1025843 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A mul r1) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) : (term906 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024339 A a mul r1 h9) (@lem1025842 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h10 h11)). Qed.
Lemma lem1025845 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025846 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025845 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025869 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A mul r1) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) : (term906 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025843 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem1025846 A mul y pwr x p q)). Qed.
Lemma lem1025870 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A mul r1) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) : (term907 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024320 A a mul r1 h10) (@lem1025869 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11)). Qed.
Lemma lem1025872 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025873 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025872 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025896 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A mul r1) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) : (term907 A ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025870 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem1025873 A mul y pwr x p q)). Qed.
Lemma lem1025897 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term80 A mul r0) (h10 : term82 A mul r1) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) : (term908 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024301 A a mul r0 h9) (@lem1025896 A ly rx lx ry b a c d z y x p q add mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h10 h11 h12)). Qed.
Lemma lem1025899 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025900 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025899 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025923 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term80 A mul r0) (h10 : term82 A mul r1) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) : (term908 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025897 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) (@lem1025900 A mul y pwr x p q)). Qed.
Lemma lem1025924 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term80 A mul r0) (h10 : term82 A mul r1) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) : (term909 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024282 A a mul r0 h11) (@lem1025923 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13)). Qed.
Lemma lem1025926 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025927 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025926 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025950 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term80 A mul r0) (h10 : term82 A mul r1) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) : (term909 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025924 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) (@lem1025927 A mul y pwr x p q)). Qed.
Lemma lem1025951 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term80 A mul r0) (h11 : term82 A mul r1) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) : (term910 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024263 A a b c add mul h5) (@lem1025950 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h6 h7 h8 h9 h10 h11 h12 h13 h14)). Qed.
Lemma lem1025953 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025954 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025953 (term890 A mul y pwr x p q)). Qed.
Lemma lem1025977 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term80 A mul r0) (h11 : term82 A mul r1) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) : (term910 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025951 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14) (@lem1025954 A mul y pwr x p q)). Qed.
Lemma lem1025978 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term80 A mul r0) (h11 : term82 A mul r1) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) : (term911 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024220 A b a mul h8) (@lem1025977 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14)). Qed.
Lemma lem1025980 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1025981 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1025980 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026004 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term80 A mul r0) (h11 : term82 A mul r1) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) : (term911 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1025978 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14) (@lem1025981 A mul y pwr x p q)). Qed.
Lemma lem1026005 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term80 A mul r0) (h12 : term82 A mul r1) (h13 : term18 A mul r0) (h14 : term13 A mul r1) (h15 : term22 A pwr r1) : (term912 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024195 A a add r0 h10) (@lem1026004 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14 h15)). Qed.
Lemma lem1026007 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026008 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026007 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026031 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term80 A mul r0) (h12 : term82 A mul r1) (h13 : term18 A mul r0) (h14 : term13 A mul r1) (h15 : term22 A pwr r1) : (term912 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026005 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15) (@lem1026008 A mul y pwr x p q)). Qed.
Lemma lem1026032 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term913 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024176 A a add r0 h11) (@lem1026031 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026034 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026035 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026034 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026058 {A : Type'} (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term913 A r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026032 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026035 A mul y pwr x p q)). Qed.
Lemma lem1026059 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term914 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024157 A m mul r0 h14) (@lem1026058 A ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026061 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026062 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026061 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026085 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term914 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026059 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026062 A mul y pwr x p q)). Qed.
Lemma lem1026086 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term915 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024138 A m add mul r1 h5 h15) (@lem1026085 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026088 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026089 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026088 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026112 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term915 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026086 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026089 A mul y pwr x p q)). Qed.
Lemma lem1026113 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term916 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024097 A a m add mul r1 h5 h7 h15) (@lem1026112 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026115 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026116 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026115 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026139 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term916 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026113 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026116 A mul y pwr x p q)). Qed.
Lemma lem1026140 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term917 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1024044 A a m add mul r1 h5 h7 h15) (@lem1026139 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026142 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026143 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026142 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026166 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term917 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026140 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026143 A mul y pwr x p q)). Qed.
Lemma lem1026167 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term918 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1023986 A a b m add mul h5) (@lem1026166 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026169 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026170 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026169 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026193 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term918 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026167 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026170 A mul y pwr x p q)). Qed.
Lemma lem1026194 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term892 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1023945 A x mul r1 h15) (@lem1026193 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026196 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1026197 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term892 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (@lem1026196 (term890 A mul y pwr x p q)). Qed.
Lemma lem1026220 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (z : A) (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q) = (term890 A mul y pwr x p q).
Proof. exact (TRANS (@lem1026194 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026197 A mul y pwr x p q)). Qed.
Lemma lem1026221 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term890 A mul y pwr x p q) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (SYM (@lem1026220 A m ly rx lx ry b a c d z y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1026222 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term920 A mul pwr.
Proof. exact (h1). Qed.
Lemma lem1026224 (P : nat -> Prop) : term921 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1026225 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : term922 A mul m pwr.
Proof. exact (@lem1026224 (term923 A mul m pwr)). Qed.
Lemma lem1026226 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term924 A mul m pwr) = (term925 A mul m pwr).
Proof. exact (eq_refl (term924 A mul m pwr)). Qed.
Lemma lem1026227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1026228 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term926 A mul m pwr) = (term927 A mul m pwr).
Proof. exact (MK_COMB (@lem1026227) (@lem1026226 A mul m pwr)). Qed.
Lemma lem1026229 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term928 A mul m pwr n) = (term929 A mul m pwr n).
Proof. exact (eq_refl (term928 A mul m pwr n)). Qed.
Lemma lem1026230 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1026231 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term930 A mul m pwr n) = (term931 A mul m pwr n).
Proof. exact (MK_COMB (@lem1026230) (@lem1026229 A mul m pwr n)). Qed.
Lemma lem1026232 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term932 A mul m pwr n) = (term933 A mul m pwr n).
Proof. exact (eq_refl (term932 A mul m pwr n)). Qed.
Lemma lem1026233 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term934 A mul m pwr n) = (term935 A mul m pwr n).
Proof. exact (MK_COMB (@lem1026231 A mul m pwr n) (@lem1026232 A mul m pwr n)). Qed.
Lemma lem1026234 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term936 A mul m pwr) = (term937 A mul m pwr).
Proof. exact (fun_ext (fun n : nat => @lem1026233 A mul m pwr n)). Qed.
Lemma lem1026235 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1026236 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term938 A mul m pwr) = (term939 A mul m pwr).
Proof. exact (MK_COMB (@lem1026235) (@lem1026234 A mul m pwr)). Qed.
Lemma lem1026237 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term940 A mul m pwr) = (term941 A mul m pwr).
Proof. exact (MK_COMB (@lem1026228 A mul m pwr) (@lem1026236 A mul m pwr)). Qed.
Lemma lem1026238 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1026239 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term942 A mul m pwr) = (term943 A mul m pwr).
Proof. exact (MK_COMB (@lem1026238) (@lem1026237 A mul m pwr)). Qed.
Lemma lem1026240 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term928 A mul m pwr n) = (term929 A mul m pwr n).
Proof. exact (eq_refl (term928 A mul m pwr n)). Qed.
Lemma lem1026241 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term944 A mul m pwr) = (term923 A mul m pwr).
Proof. exact (fun_ext (fun n : nat => @lem1026240 A mul m pwr n)). Qed.
Lemma lem1026242 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1026243 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term945 A mul m pwr) = (term946 A mul m pwr).
Proof. exact (MK_COMB (@lem1026242) (@lem1026241 A mul m pwr)). Qed.
Lemma lem1026244 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term922 A mul m pwr) = (term947 A mul m pwr).
Proof. exact (MK_COMB (@lem1026239 A mul m pwr) (@lem1026243 A mul m pwr)). Qed.
Lemma lem1026245 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : term947 A mul m pwr.
Proof. exact (EQ_MP (@lem1026244 A mul m pwr) (@lem1026225 A mul m pwr)). Qed.
Lemma lem1026246 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term929 A mul m pwr n) : term929 A mul m pwr n.
Proof. exact (h1). Qed.
Lemma lem1026247 : term948.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1026263 : term949.
Proof. exact (proj1 (@lem1026247)). Qed.
Lemma lem1026264 (m : nat) : term950 m.
Proof. exact (@lem1026263 m). Qed.
Lemma lem1026265 (m : nat) : (term950 m) = ((term951 m) = m).
Proof. exact (eq_refl (term950 m)). Qed.
Lemma lem1026289 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : term812 A pwr r1 x.
Proof. exact (@lem1017057 A pwr r1 h1 x). Qed.
Lemma lem1026290 {A : Type'} (pwr : type1423 A) (x : A) (r1 : A) : (term812 A pwr r1 x) = ((term126 A pwr x) = r1).
Proof. exact (eq_refl (term812 A pwr r1 x)). Qed.
Lemma lem1026358 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : term205 A mul r1 x.
Proof. exact (@lem1023835 A mul r1 h1 x). Qed.
Lemma lem1026359 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term205 A mul r1 x) = ((mul x r1) = x).
Proof. exact (eq_refl (term205 A mul r1 x)). Qed.
Lemma lem1026371 (m : nat) : (term951 m) = m.
Proof. exact (EQ_MP (@lem1026265 m) (@lem1026264 m)). Qed.
Lemma lem1026372 {A : Type'} (pwr : type1423 A) (x : A) : (pwr x) = (pwr x).
Proof. exact (eq_refl (pwr x)). Qed.
Lemma lem1026373 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term952 A pwr x m) = (pwr x m).
Proof. exact (MK_COMB (@lem1026372 A pwr x) (@lem1026371 m)). Qed.
Lemma lem1026374 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1026375 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term953 A pwr x m) = (term954 A pwr x m).
Proof. exact (MK_COMB (@lem1026374 A) (@lem1026373 A pwr x m)). Qed.
Lemma lem1026381 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1026290 A pwr x r1) (@lem1026289 A x pwr r1 h1)). Qed.
Lemma lem1026382 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1026381 A x pwr r1 h1). Qed.
Lemma lem1026383 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) : (term955 A mul pwr x m) = (term955 A mul pwr x m).
Proof. exact (eq_refl (term955 A mul pwr x m)). Qed.
Lemma lem1026384 {A : Type'} (mul : type1400 A) (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term956 A mul m pwr x) = (term957 A mul pwr x m r1).
Proof. exact (MK_COMB (@lem1026383 A mul pwr x m) (@lem1026382 A x pwr r1 h1)). Qed.
Lemma lem1026386 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (mul x r1) = x.
Proof. exact (EQ_MP (@lem1026359 A mul r1 x) (@lem1026358 A x mul r1 h1)). Qed.
Lemma lem1026387 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (mul x r1) = x.
Proof. exact (@lem1026386 A x mul r1 h1). Qed.
Lemma lem1026388 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (mul : type1400 A) (r1 : A) (h1 : term82 A mul r1) : (term957 A mul pwr x m r1) = (pwr x m).
Proof. exact (@lem1026387 A (pwr x m) mul r1 h1). Qed.
Lemma lem1026389 {A : Type'} (x : A) (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : (term956 A mul m pwr x) = (pwr x m).
Proof. exact (TRANS (@lem1026384 A mul x m pwr r1 h2) (@lem1026388 A pwr x m mul r1 h1)). Qed.
Lemma lem1026390 {A : Type'} (x : A) (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : ((term952 A pwr x m) = (term956 A mul m pwr x)) = ((pwr x m) = (pwr x m)).
Proof. exact (MK_COMB (@lem1026375 A pwr x m) (@lem1026389 A x m mul pwr r1 h1 h2)). Qed.
Lemma lem1026392 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1026393 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1026392 A x). Qed.
Lemma lem1026394 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : ((pwr x m) = (pwr x m)) = True.
Proof. exact (@lem1026393 A (pwr x m)). Qed.
Lemma lem1026395 {A : Type'} (m : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : ((term952 A pwr x m) = (term956 A mul m pwr x)) = True.
Proof. exact (TRANS (@lem1026390 A x m mul pwr r1 h1 h2) (@lem1026394 A pwr x m)). Qed.
Lemma lem1026396 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : (term958 A mul m pwr) = (term959 A).
Proof. exact (fun_ext (fun x : A => @lem1026395 A m x mul pwr r1 h1 h2)). Qed.
Lemma lem1026397 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1026398 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : (term925 A mul m pwr) = (term960 A).
Proof. exact (MK_COMB (@lem1026397 A) (@lem1026396 A m mul pwr r1 h1 h2)). Qed.
Lemma lem1026400 {A : Type'} (t : Prop) : (term961 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1026401 {A : Type'} (t : Prop) : (term961 A t) = t.
Proof. exact (@lem1026400 A t). Qed.
Lemma lem1026402 {A : Type'} : (term960 A) = True.
Proof. exact (@lem1026401 A True). Qed.
Lemma lem1026403 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : (term925 A mul m pwr) = True.
Proof. exact (TRANS (@lem1026398 A m mul pwr r1 h1 h2) (@lem1026402 A)). Qed.
Lemma lem1026404 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : True = (term925 A mul m pwr).
Proof. exact (SYM (@lem1026403 A m mul pwr r1 h1 h2)). Qed.
Lemma lem1026405 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term82 A mul r1) (h2 : term22 A pwr r1) : term925 A mul m pwr.
Proof. exact (EQ_MP (@lem1026404 A m mul pwr r1 h1 h2) (@lem0)). Qed.
Lemma lem1026406 : term948.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem1026407 : term962.
Proof. exact (proj2 (@lem1026406)). Qed.
Lemma lem1026408 : term963.
Proof. exact (proj2 (@lem1026407)). Qed.
Lemma lem1026409 (m : nat) : term964 m.
Proof. exact (@lem1026408 m). Qed.
Lemma lem1026410 (m : nat) : (term964 m) = (term965 m).
Proof. exact (eq_refl (term964 m)). Qed.
Lemma lem1026411 (m : nat) : term965 m.
Proof. exact (EQ_MP (@lem1026410 m) (@lem1026409 m)). Qed.
Lemma lem1026412 (m : nat) (n : nat) : term966 m n.
Proof. exact (@lem1026411 m n). Qed.
Lemma lem1026413 (m : nat) (n : nat) : (term966 m n) = ((term967 m n) = (term968 m n)).
Proof. exact (eq_refl (term966 m n)). Qed.
Lemma lem1026451 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term813 A mul pwr x.
Proof. exact (@lem1017056 A mul pwr h1 x). Qed.
Lemma lem1026452 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term813 A mul pwr x) = (term124 A mul pwr x).
Proof. exact (eq_refl (term813 A mul pwr x)). Qed.
Lemma lem1026453 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term124 A mul pwr x.
Proof. exact (EQ_MP (@lem1026452 A mul pwr x) (@lem1026451 A x mul pwr h1)). Qed.
Lemma lem1026454 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term814 A mul pwr x n.
Proof. exact (@lem1026453 A x mul pwr h1 n). Qed.
Lemma lem1026455 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : (term814 A mul pwr x n) = ((term121 A pwr x n) = (term122 A mul pwr x n)).
Proof. exact (eq_refl (term814 A mul pwr x n)). Qed.
Lemma lem1026484 {A : Type'} (m : A) (mul : type1400 A) (h1 : term11 A mul) : term154 A mul m.
Proof. exact (@lem1023827 A mul h1 m). Qed.
Lemma lem1026485 {A : Type'} (mul : type1400 A) (m : A) : (term154 A mul m) = (term114 A mul m).
Proof. exact (eq_refl (term154 A mul m)). Qed.
Lemma lem1026486 {A : Type'} (m : A) (mul : type1400 A) (h1 : term11 A mul) : term114 A mul m.
Proof. exact (EQ_MP (@lem1026485 A mul m) (@lem1026484 A m mul h1)). Qed.
Lemma lem1026487 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : term146 A mul m n.
Proof. exact (@lem1026486 A m mul h1 n). Qed.
Lemma lem1026488 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term146 A mul m n) = ((mul m n) = (mul n m)).
Proof. exact (eq_refl (term146 A mul m n)). Qed.
Lemma lem1026490 {A : Type'} (m : A) (mul : type1400 A) (h1 : term110 A mul) : term176 A mul m.
Proof. exact (@lem1023829 A mul h1 m). Qed.
Lemma lem1026491 {A : Type'} (m : A) (mul : type1400 A) : (term176 A mul m) = (term108 A m mul).
Proof. exact (eq_refl (term176 A mul m)). Qed.
Lemma lem1026492 {A : Type'} (m : A) (mul : type1400 A) (h1 : term110 A mul) : term108 A m mul.
Proof. exact (EQ_MP (@lem1026491 A m mul) (@lem1026490 A m mul h1)). Qed.
Lemma lem1026493 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term110 A mul) : term169 A m mul n.
Proof. exact (@lem1026492 A m mul h1 n). Qed.
Lemma lem1026494 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term169 A m mul n) = (term106 A m mul n).
Proof. exact (eq_refl (term169 A m mul n)). Qed.
Lemma lem1026495 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term110 A mul) : term106 A m mul n.
Proof. exact (EQ_MP (@lem1026494 A m mul n) (@lem1026493 A m n mul h1)). Qed.
Lemma lem1026496 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : term161 A m mul n p.
Proof. exact (@lem1026495 A m n mul h1 p). Qed.
Lemma lem1026497 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term161 A m mul n p) = ((term104 A mul m n p) = (term95 A m mul n p)).
Proof. exact (eq_refl (term161 A m mul n p)). Qed.
Lemma lem1026523 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term929 A mul m pwr n) : term969 A mul m pwr n x.
Proof. exact (@lem1026246 A mul m pwr n h1 x). Qed.
Lemma lem1026524 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (x : A) (n : nat) : (term969 A mul m pwr n x) = ((term970 A pwr x m n) = (term971 A mul m pwr x n)).
Proof. exact (eq_refl (term969 A mul m pwr n x)). Qed.
Lemma lem1026533 (m : nat) (n : nat) : (term967 m n) = (term968 m n).
Proof. exact (EQ_MP (@lem1026413 m n) (@lem1026412 m n)). Qed.
Lemma lem1026534 {A : Type'} (pwr : type1423 A) (x : A) : (pwr x) = (pwr x).
Proof. exact (eq_refl (pwr x)). Qed.
Lemma lem1026535 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : (term972 A pwr x m n) = (term973 A pwr x m n).
Proof. exact (MK_COMB (@lem1026534 A pwr x) (@lem1026533 m n)). Qed.
Lemma lem1026537 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1026455 A mul pwr x n) (@lem1026454 A x n mul pwr h1)). Qed.
Lemma lem1026538 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1026537 A x n mul pwr h1). Qed.
Lemma lem1026539 {A : Type'} (x : A) (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term973 A pwr x m n) = (term974 A mul pwr x m n).
Proof. exact (@lem1026538 A x (Nat.add m n) mul pwr h1). Qed.
Lemma lem1026541 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1026488 A mul n m) (@lem1026487 A m n mul h1)). Qed.
Lemma lem1026542 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1026541 A n m mul h1). Qed.
Lemma lem1026543 {A : Type'} (pwr : type1423 A) (m : nat) (n : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term974 A mul pwr x m n) = (term975 A mul pwr m n x).
Proof. exact (@lem1026542 A (term970 A pwr x m n) x mul h1). Qed.
Lemma lem1026549 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term929 A mul m pwr n) : (term970 A pwr x m n) = (term971 A mul m pwr x n).
Proof. exact (EQ_MP (@lem1026524 A mul m pwr x n) (@lem1026523 A x mul m pwr n h1)). Qed.
Lemma lem1026550 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term929 A mul m pwr n) : (term970 A pwr x m n) = (term971 A mul m pwr x n).
Proof. exact (@lem1026549 A x mul m pwr n h1). Qed.
Lemma lem1026555 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1026556 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term929 A mul m pwr n) : (term976 A mul pwr x m n) = (term977 A mul m pwr x n).
Proof. exact (MK_COMB (@lem1026555 A mul) (@lem1026550 A x mul m pwr n h1)). Qed.
Lemma lem1026557 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1026558 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term929 A mul m pwr n) : (term975 A mul pwr m n x) = (term978 A mul m pwr n x).
Proof. exact (MK_COMB (@lem1026556 A x mul m pwr n h1) (@lem1026557 A x)). Qed.
Lemma lem1026560 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1026497 A m mul n p) (@lem1026496 A m n p mul h1)). Qed.
Lemma lem1026561 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1026560 A m n p mul h1). Qed.
Lemma lem1026562 {A : Type'} (m : nat) (pwr : type1423 A) (n : nat) (x : A) (mul : type1400 A) (h1 : term110 A mul) : (term978 A mul m pwr n x) = (term979 A m mul pwr n x).
Proof. exact (@lem1026561 A (pwr x m) (pwr x n) x mul h1). Qed.
Lemma lem1026575 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term929 A mul m pwr n) : (term975 A mul pwr m n x) = (term979 A m mul pwr n x).
Proof. exact (TRANS (@lem1026558 A x mul m pwr n h2) (@lem1026562 A m pwr n x mul h1)). Qed.
Lemma lem1026576 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term929 A mul m pwr n) : (term974 A mul pwr x m n) = (term979 A m mul pwr n x).
Proof. exact (TRANS (@lem1026543 A pwr m n x mul h2) (@lem1026575 A x mul m pwr n h1 h3)). Qed.
Lemma lem1026577 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : (term973 A pwr x m n) = (term979 A m mul pwr n x).
Proof. exact (TRANS (@lem1026539 A x m n mul pwr h3) (@lem1026576 A x mul m pwr n h1 h2 h4)). Qed.
Lemma lem1026578 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : (term972 A pwr x m n) = (term979 A m mul pwr n x).
Proof. exact (TRANS (@lem1026535 A pwr x m n) (@lem1026577 A x mul m pwr n h1 h2 h3 h4)). Qed.
Lemma lem1026579 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1026580 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : (term980 A pwr x m n) = (term981 A m mul pwr n x).
Proof. exact (MK_COMB (@lem1026579 A) (@lem1026578 A x mul m pwr n h1 h2 h3 h4)). Qed.
Lemma lem1026586 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1026455 A mul pwr x n) (@lem1026454 A x n mul pwr h1)). Qed.
Lemma lem1026587 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1026586 A x n mul pwr h1). Qed.
Lemma lem1026589 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1026488 A mul n m) (@lem1026487 A m n mul h1)). Qed.
Lemma lem1026590 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1026589 A n m mul h1). Qed.
Lemma lem1026591 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr x n) = (term848 A mul pwr n x).
Proof. exact (@lem1026590 A (pwr x n) x mul h1). Qed.
Lemma lem1026596 {A : Type'} (n : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term121 A pwr x n) = (term848 A mul pwr n x).
Proof. exact (TRANS (@lem1026587 A x n mul pwr h2) (@lem1026591 A pwr n x mul h1)). Qed.
Lemma lem1026597 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) : (term955 A mul pwr x m) = (term955 A mul pwr x m).
Proof. exact (eq_refl (term955 A mul pwr x m)). Qed.
Lemma lem1026598 {A : Type'} (m : nat) (n : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term982 A mul m pwr x n) = (term979 A m mul pwr n x).
Proof. exact (MK_COMB (@lem1026597 A mul pwr x m) (@lem1026596 A n x mul pwr h1 h2)). Qed.
Lemma lem1026607 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : ((term972 A pwr x m n) = (term982 A mul m pwr x n)) = ((term979 A m mul pwr n x) = (term979 A m mul pwr n x)).
Proof. exact (MK_COMB (@lem1026580 A x mul m pwr n h1 h2 h3 h4) (@lem1026598 A m n x mul pwr h2 h3)). Qed.
Lemma lem1026609 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1026610 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1026609 A x). Qed.
Lemma lem1026611 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (n : nat) (x : A) : ((term979 A m mul pwr n x) = (term979 A m mul pwr n x)) = True.
Proof. exact (@lem1026610 A (term979 A m mul pwr n x)). Qed.
Lemma lem1026612 {A : Type'} (x : A) (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : ((term972 A pwr x m n) = (term982 A mul m pwr x n)) = True.
Proof. exact (TRANS (@lem1026607 A x mul m pwr n h1 h2 h3 h4) (@lem1026611 A m mul pwr n x)). Qed.
Lemma lem1026613 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : (term983 A mul m pwr n) = (term959 A).
Proof. exact (fun_ext (fun x : A => @lem1026612 A x mul m pwr n h1 h2 h3 h4)). Qed.
Lemma lem1026614 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1026615 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : (term933 A mul m pwr n) = (term960 A).
Proof. exact (MK_COMB (@lem1026614 A) (@lem1026613 A mul m pwr n h1 h2 h3 h4)). Qed.
Lemma lem1026617 {A : Type'} (t : Prop) : (term961 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1026618 {A : Type'} (t : Prop) : (term961 A t) = t.
Proof. exact (@lem1026617 A t). Qed.
Lemma lem1026619 {A : Type'} : (term960 A) = True.
Proof. exact (@lem1026618 A True). Qed.
Lemma lem1026620 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : (term933 A mul m pwr n) = True.
Proof. exact (TRANS (@lem1026615 A mul m pwr n h1 h2 h3 h4) (@lem1026619 A)). Qed.
Lemma lem1026621 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : True = (term933 A mul m pwr n).
Proof. exact (SYM (@lem1026620 A mul m pwr n h1 h2 h3 h4)). Qed.
Lemma lem1026622 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term929 A mul m pwr n) : term933 A mul m pwr n.
Proof. exact (EQ_MP (@lem1026621 A mul m pwr n h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem1026623 {A : Type'} (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) : term935 A mul m pwr n.
Proof. exact (fun h0 : term929 A mul m pwr n => @lem1026622 A mul m pwr n h1 h2 h3 h0). Qed.
Lemma lem1026628 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) : term939 A mul m pwr.
Proof. exact (fun n : nat => @lem1026623 A m n mul pwr h1 h2 h3). Qed.
Lemma lem1026629 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term82 A mul r1) (h5 : term22 A pwr r1) : term941 A mul m pwr.
Proof. exact (conj (@lem1026405 A m mul pwr r1 h4 h5) (@lem1026628 A m mul pwr h1 h2 h3)). Qed.
Lemma lem1026630 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term82 A mul r1) (h5 : term22 A pwr r1) : term946 A mul m pwr.
Proof. exact (@lem1026245 A mul m pwr (@lem1026629 A m mul pwr r1 h1 h2 h3 h4 h5)). Qed.
Lemma lem1026635 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : term21 A mul pwr) (h4 : term82 A mul r1) (h5 : term22 A pwr r1) : term920 A mul pwr.
Proof. exact (fun m : nat => @lem1026630 A m mul pwr r1 h1 h2 h3 h4 h5). Qed.
Lemma lem1026636 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term984 A mul pwr.
Proof. exact (h1). Qed.
Lemma lem1026638 (P : nat -> Prop) : term921 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1026639 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : term985 A mul x pwr y.
Proof. exact (@lem1026638 (term986 A mul x pwr y)). Qed.
Lemma lem1026640 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term987 A mul x pwr y) = ((term988 A pwr mul x y) = (term989 A mul x pwr y)).
Proof. exact (eq_refl (term987 A mul x pwr y)). Qed.
Lemma lem1026641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1026642 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term990 A mul x pwr y) = (term991 A mul x pwr y).
Proof. exact (MK_COMB (@lem1026641) (@lem1026640 A mul x pwr y)). Qed.
Lemma lem1026643 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : (term992 A mul x pwr y n) = ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)).
Proof. exact (eq_refl (term992 A mul x pwr y n)). Qed.
Lemma lem1026644 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1026645 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : (term995 A mul x pwr y n) = (term996 A mul x pwr y n).
Proof. exact (MK_COMB (@lem1026644) (@lem1026643 A mul x pwr y n)). Qed.
Lemma lem1026646 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : (term997 A mul x pwr y n) = ((term998 A pwr mul x y n) = (term999 A mul x pwr y n)).
Proof. exact (eq_refl (term997 A mul x pwr y n)). Qed.
Lemma lem1026647 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : (term1000 A mul x pwr y n) = (term1001 A mul x pwr y n).
Proof. exact (MK_COMB (@lem1026645 A mul x pwr y n) (@lem1026646 A mul x pwr y n)). Qed.
Lemma lem1026648 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1002 A mul x pwr y) = (term1003 A mul x pwr y).
Proof. exact (fun_ext (fun n : nat => @lem1026647 A mul x pwr y n)). Qed.
Lemma lem1026649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1026650 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1004 A mul x pwr y) = (term1005 A mul x pwr y).
Proof. exact (MK_COMB (@lem1026649) (@lem1026648 A mul x pwr y)). Qed.
Lemma lem1026651 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1006 A mul x pwr y) = (term1007 A mul x pwr y).
Proof. exact (MK_COMB (@lem1026642 A mul x pwr y) (@lem1026650 A mul x pwr y)). Qed.
Lemma lem1026652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1026653 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1008 A mul x pwr y) = (term1009 A mul x pwr y).
Proof. exact (MK_COMB (@lem1026652) (@lem1026651 A mul x pwr y)). Qed.
Lemma lem1026654 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : (term992 A mul x pwr y n) = ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)).
Proof. exact (eq_refl (term992 A mul x pwr y n)). Qed.
Lemma lem1026655 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1010 A mul x pwr y) = (term986 A mul x pwr y).
Proof. exact (fun_ext (fun n : nat => @lem1026654 A mul x pwr y n)). Qed.
Lemma lem1026656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1026657 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1011 A mul x pwr y) = (term1012 A mul x pwr y).
Proof. exact (MK_COMB (@lem1026656) (@lem1026655 A mul x pwr y)). Qed.
Lemma lem1026658 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term985 A mul x pwr y) = (term1013 A mul x pwr y).
Proof. exact (MK_COMB (@lem1026653 A mul x pwr y) (@lem1026657 A mul x pwr y)). Qed.
Lemma lem1026659 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : term1013 A mul x pwr y.
Proof. exact (EQ_MP (@lem1026658 A mul x pwr y) (@lem1026639 A mul x pwr y)). Qed.
Lemma lem1026664 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : term698 A mul r1 x.
Proof. exact (@lem1017051 A mul r1 h1 x). Qed.
Lemma lem1026665 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : (term698 A mul r1 x) = ((mul r1 x) = x).
Proof. exact (eq_refl (term698 A mul r1 x)). Qed.
Lemma lem1026679 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : term812 A pwr r1 x.
Proof. exact (@lem1017057 A pwr r1 h1 x). Qed.
Lemma lem1026680 {A : Type'} (pwr : type1423 A) (x : A) (r1 : A) : (term812 A pwr r1 x) = ((term126 A pwr x) = r1).
Proof. exact (eq_refl (term812 A pwr r1 x)). Qed.
Lemma lem1026766 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1026680 A pwr x r1) (@lem1026679 A x pwr r1 h1)). Qed.
Lemma lem1026767 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1026766 A x pwr r1 h1). Qed.
Lemma lem1026768 {A : Type'} (mul : type1400 A) (x : A) (y : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term988 A pwr mul x y) = r1.
Proof. exact (@lem1026767 A (mul x y) pwr r1 h1). Qed.
Lemma lem1026769 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1026770 {A : Type'} (mul : type1400 A) (x : A) (y : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term1014 A pwr mul x y) = (@eq A r1).
Proof. exact (MK_COMB (@lem1026769 A) (@lem1026768 A mul x y pwr r1 h1)). Qed.
Lemma lem1026776 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1026680 A pwr x r1) (@lem1026679 A x pwr r1 h1)). Qed.
Lemma lem1026777 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1026776 A x pwr r1 h1). Qed.
Lemma lem1026778 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1026779 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term861 A mul pwr x) = (mul r1).
Proof. exact (MK_COMB (@lem1026778 A mul) (@lem1026777 A x pwr r1 h1)). Qed.
Lemma lem1026781 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1026680 A pwr x r1) (@lem1026679 A x pwr r1 h1)). Qed.
Lemma lem1026782 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1026781 A x pwr r1 h1). Qed.
Lemma lem1026783 {A : Type'} (y : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr y) = r1.
Proof. exact (@lem1026782 A y pwr r1 h1). Qed.
Lemma lem1026784 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term989 A mul x pwr y) = (mul r1 r1).
Proof. exact (MK_COMB (@lem1026779 A x mul pwr r1 h1) (@lem1026783 A y pwr r1 h1)). Qed.
Lemma lem1026786 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (EQ_MP (@lem1026665 A mul r1 x) (@lem1026664 A x mul r1 h1)). Qed.
Lemma lem1026787 {A : Type'} (x : A) (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 x) = x.
Proof. exact (@lem1026786 A x mul r1 h1). Qed.
Lemma lem1026788 {A : Type'} (mul : type1400 A) (r1 : A) (h1 : term13 A mul r1) : (mul r1 r1) = r1.
Proof. exact (@lem1026787 A r1 mul r1 h1). Qed.
Lemma lem1026789 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term13 A mul r1) (h2 : term22 A pwr r1) : (term989 A mul x pwr y) = r1.
Proof. exact (TRANS (@lem1026784 A x y mul pwr r1 h2) (@lem1026788 A mul r1 h1)). Qed.
Lemma lem1026790 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term13 A mul r1) (h2 : term22 A pwr r1) : ((term988 A pwr mul x y) = (term989 A mul x pwr y)) = (r1 = r1).
Proof. exact (MK_COMB (@lem1026770 A mul x y pwr r1 h2) (@lem1026789 A x y mul pwr r1 h1 h2)). Qed.
Lemma lem1026792 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1026793 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1026792 A x). Qed.
Lemma lem1026794 {A : Type'} (r1 : A) : (r1 = r1) = True.
Proof. exact (@lem1026793 A r1). Qed.
Lemma lem1026795 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term13 A mul r1) (h2 : term22 A pwr r1) : ((term988 A pwr mul x y) = (term989 A mul x pwr y)) = True.
Proof. exact (TRANS (@lem1026790 A x y mul pwr r1 h1 h2) (@lem1026794 A r1)). Qed.
Lemma lem1026796 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term13 A mul r1) (h2 : term22 A pwr r1) : True = ((term988 A pwr mul x y) = (term989 A mul x pwr y)).
Proof. exact (SYM (@lem1026795 A x y mul pwr r1 h1 h2)). Qed.
Lemma lem1026797 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term13 A mul r1) (h2 : term22 A pwr r1) : (term988 A pwr mul x y) = (term989 A mul x pwr y).
Proof. exact (EQ_MP (@lem1026796 A x y mul pwr r1 h1 h2) (@lem0)). Qed.
Lemma lem1026819 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term813 A mul pwr x.
Proof. exact (@lem1017056 A mul pwr h1 x). Qed.
Lemma lem1026820 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term813 A mul pwr x) = (term124 A mul pwr x).
Proof. exact (eq_refl (term813 A mul pwr x)). Qed.
Lemma lem1026821 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term124 A mul pwr x.
Proof. exact (EQ_MP (@lem1026820 A mul pwr x) (@lem1026819 A x mul pwr h1)). Qed.
Lemma lem1026822 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term814 A mul pwr x n.
Proof. exact (@lem1026821 A x mul pwr h1 n). Qed.
Lemma lem1026823 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : (term814 A mul pwr x n) = ((term121 A pwr x n) = (term122 A mul pwr x n)).
Proof. exact (eq_refl (term814 A mul pwr x n)). Qed.
Lemma lem1026852 {A : Type'} (m : A) (mul : type1400 A) (h1 : term11 A mul) : term154 A mul m.
Proof. exact (@lem1023827 A mul h1 m). Qed.
Lemma lem1026853 {A : Type'} (mul : type1400 A) (m : A) : (term154 A mul m) = (term114 A mul m).
Proof. exact (eq_refl (term154 A mul m)). Qed.
Lemma lem1026854 {A : Type'} (m : A) (mul : type1400 A) (h1 : term11 A mul) : term114 A mul m.
Proof. exact (EQ_MP (@lem1026853 A mul m) (@lem1026852 A m mul h1)). Qed.
Lemma lem1026855 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term11 A mul) : term146 A mul m n.
Proof. exact (@lem1026854 A m mul h1 n). Qed.
Lemma lem1026856 {A : Type'} (mul : type1400 A) (n : A) (m : A) : (term146 A mul m n) = ((mul m n) = (mul n m)).
Proof. exact (eq_refl (term146 A mul m n)). Qed.
Lemma lem1026858 {A : Type'} (m : A) (mul : type1400 A) (h1 : term110 A mul) : term176 A mul m.
Proof. exact (@lem1023829 A mul h1 m). Qed.
Lemma lem1026859 {A : Type'} (m : A) (mul : type1400 A) : (term176 A mul m) = (term108 A m mul).
Proof. exact (eq_refl (term176 A mul m)). Qed.
Lemma lem1026860 {A : Type'} (m : A) (mul : type1400 A) (h1 : term110 A mul) : term108 A m mul.
Proof. exact (EQ_MP (@lem1026859 A m mul) (@lem1026858 A m mul h1)). Qed.
Lemma lem1026861 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term110 A mul) : term169 A m mul n.
Proof. exact (@lem1026860 A m mul h1 n). Qed.
Lemma lem1026862 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term169 A m mul n) = (term106 A m mul n).
Proof. exact (eq_refl (term169 A m mul n)). Qed.
Lemma lem1026863 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term110 A mul) : term106 A m mul n.
Proof. exact (EQ_MP (@lem1026862 A m mul n) (@lem1026861 A m n mul h1)). Qed.
Lemma lem1026864 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : term161 A m mul n p.
Proof. exact (@lem1026863 A m n mul h1 p). Qed.
Lemma lem1026865 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : (term161 A m mul n p) = ((term104 A mul m n p) = (term95 A m mul n p)).
Proof. exact (eq_refl (term161 A m mul n p)). Qed.
Lemma lem1026867 {A : Type'} (m : A) (mul : type1400 A) (h1 : term101 A mul) : term198 A mul m.
Proof. exact (@lem1023831 A mul h1 m). Qed.
Lemma lem1026868 {A : Type'} (mul : type1400 A) (m : A) : (term198 A mul m) = (term99 A mul m).
Proof. exact (eq_refl (term198 A mul m)). Qed.
Lemma lem1026869 {A : Type'} (m : A) (mul : type1400 A) (h1 : term101 A mul) : term99 A mul m.
Proof. exact (EQ_MP (@lem1026868 A mul m) (@lem1026867 A m mul h1)). Qed.
Lemma lem1026870 {A : Type'} (m : A) (n : A) (mul : type1400 A) (h1 : term101 A mul) : term191 A mul m n.
Proof. exact (@lem1026869 A m mul h1 n). Qed.
Lemma lem1026871 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term191 A mul m n) = (term97 A n mul m).
Proof. exact (eq_refl (term191 A mul m n)). Qed.
Lemma lem1026872 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term101 A mul) : term97 A n mul m.
Proof. exact (EQ_MP (@lem1026871 A n mul m) (@lem1026870 A m n mul h1)). Qed.
Lemma lem1026873 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : term183 A n mul m p.
Proof. exact (@lem1026872 A n m mul h1 p). Qed.
Lemma lem1026874 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : (term183 A n mul m p) = ((term95 A m mul n p) = (term95 A n mul m p)).
Proof. exact (eq_refl (term183 A n mul m p)). Qed.
Lemma lem1026903 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1026823 A mul pwr x n) (@lem1026822 A x n mul pwr h1)). Qed.
Lemma lem1026904 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1026903 A x n mul pwr h1). Qed.
Lemma lem1026905 {A : Type'} (x : A) (y : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term998 A pwr mul x y n) = (term1015 A pwr mul x y n).
Proof. exact (@lem1026904 A (mul x y) n mul pwr h1). Qed.
Lemma lem1026907 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1026865 A m mul n p) (@lem1026864 A m n p mul h1)). Qed.
Lemma lem1026908 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1026907 A m n p mul h1). Qed.
Lemma lem1026909 {A : Type'} (pwr : type1423 A) (x : A) (y : A) (n : nat) (mul : type1400 A) (h1 : term110 A mul) : (term1015 A pwr mul x y n) = (term1016 A pwr mul x y n).
Proof. exact (@lem1026908 A x y (term993 A pwr mul x y n) mul h1). Qed.
Lemma lem1026918 {A : Type'} (x : A) (y : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term110 A mul) (h2 : term21 A mul pwr) : (term998 A pwr mul x y n) = (term1016 A pwr mul x y n).
Proof. exact (TRANS (@lem1026905 A x y n mul pwr h2) (@lem1026909 A pwr x y n mul h1)). Qed.
Lemma lem1026920 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1026856 A mul n m) (@lem1026855 A m n mul h1)). Qed.
Lemma lem1026921 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1026920 A n m mul h1). Qed.
Lemma lem1026922 {A : Type'} (pwr : type1423 A) (x : A) (n : nat) (y : A) (mul : type1400 A) (h1 : term11 A mul) : (term1017 A pwr mul x y n) = (term1018 A pwr mul x n y).
Proof. exact (@lem1026921 A (term993 A pwr mul x y n) y mul h1). Qed.
Lemma lem1026928 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term993 A pwr mul x y n) = (term994 A mul x pwr y n).
Proof. exact (h1). Qed.
Lemma lem1026933 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1026934 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term1019 A pwr mul x y n) = (term1020 A mul x pwr y n).
Proof. exact (MK_COMB (@lem1026933 A mul) (@lem1026928 A mul x pwr y n h1)). Qed.
Lemma lem1026935 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1026936 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term1018 A pwr mul x n y) = (term1021 A mul x pwr n y).
Proof. exact (MK_COMB (@lem1026934 A mul x pwr y n h1) (@lem1026935 A y)). Qed.
Lemma lem1026938 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1026865 A m mul n p) (@lem1026864 A m n p mul h1)). Qed.
Lemma lem1026939 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1026938 A m n p mul h1). Qed.
Lemma lem1026940 {A : Type'} (x : A) (pwr : type1423 A) (n : nat) (y : A) (mul : type1400 A) (h1 : term110 A mul) : (term1021 A mul x pwr n y) = (term1022 A x mul pwr n y).
Proof. exact (@lem1026939 A (pwr x n) (pwr y n) y mul h1). Qed.
Lemma lem1026953 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term110 A mul) (h2 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term1018 A pwr mul x n y) = (term1022 A x mul pwr n y).
Proof. exact (TRANS (@lem1026936 A mul x pwr y n h2) (@lem1026940 A x pwr n y mul h1)). Qed.
Lemma lem1026954 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term1017 A pwr mul x y n) = (term1022 A x mul pwr n y).
Proof. exact (TRANS (@lem1026922 A pwr x n y mul h2) (@lem1026953 A mul x pwr y n h1 h3)). Qed.
Lemma lem1026955 {A : Type'} (mul : type1400 A) (x : A) : (mul x) = (mul x).
Proof. exact (eq_refl (mul x)). Qed.
Lemma lem1026956 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term110 A mul) (h2 : term11 A mul) (h3 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term1016 A pwr mul x y n) = (term1023 A x mul pwr n y).
Proof. exact (MK_COMB (@lem1026955 A mul x) (@lem1026954 A mul x pwr y n h1 h2 h3)). Qed.
Lemma lem1026958 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1026874 A n mul m p) (@lem1026873 A n m p mul h1)). Qed.
Lemma lem1026959 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1026958 A n m p mul h1). Qed.
Lemma lem1026960 {A : Type'} (x : A) (pwr : type1423 A) (n : nat) (y : A) (mul : type1400 A) (h1 : term101 A mul) : (term1023 A x mul pwr n y) = (term1024 A x mul pwr n y).
Proof. exact (@lem1026959 A (pwr x n) x (term848 A mul pwr n y) mul h1). Qed.
Lemma lem1026970 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1026874 A n mul m p) (@lem1026873 A n m p mul h1)). Qed.
Lemma lem1026971 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1026970 A n m p mul h1). Qed.
Lemma lem1026972 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (y : A) (mul : type1400 A) (h1 : term101 A mul) : (term1025 A x mul pwr n y) = (term1026 A pwr n mul x y).
Proof. exact (@lem1026971 A (pwr y n) x y mul h1). Qed.
Lemma lem1026985 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : (term955 A mul pwr x n) = (term955 A mul pwr x n).
Proof. exact (eq_refl (term955 A mul pwr x n)). Qed.
Lemma lem1026986 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (y : A) (mul : type1400 A) (h1 : term101 A mul) : (term1024 A x mul pwr n y) = (term1027 A pwr n mul x y).
Proof. exact (MK_COMB (@lem1026985 A mul pwr x n) (@lem1026972 A pwr n x y mul h1)). Qed.
Lemma lem1026995 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (y : A) (mul : type1400 A) (h1 : term101 A mul) : (term1023 A x mul pwr n y) = (term1027 A pwr n mul x y).
Proof. exact (TRANS (@lem1026960 A x pwr n y mul h1) (@lem1026986 A pwr n x y mul h1)). Qed.
Lemma lem1026996 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term1016 A pwr mul x y n) = (term1027 A pwr n mul x y).
Proof. exact (TRANS (@lem1026956 A mul x pwr y n h2 h3 h4) (@lem1026995 A pwr n x y mul h1)). Qed.
Lemma lem1026997 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term998 A pwr mul x y n) = (term1027 A pwr n mul x y).
Proof. exact (TRANS (@lem1026918 A x y n mul pwr h2 h4) (@lem1026996 A mul x pwr y n h1 h2 h3 h5)). Qed.
Lemma lem1026998 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1026999 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term1028 A pwr mul x y n) = (term1029 A pwr n mul x y).
Proof. exact (MK_COMB (@lem1026998 A) (@lem1026997 A mul x pwr y n h1 h2 h3 h4 h5)). Qed.
Lemma lem1027005 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1026823 A mul pwr x n) (@lem1026822 A x n mul pwr h1)). Qed.
Lemma lem1027006 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1027005 A x n mul pwr h1). Qed.
Lemma lem1027008 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1026856 A mul n m) (@lem1026855 A m n mul h1)). Qed.
Lemma lem1027009 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1027008 A n m mul h1). Qed.
Lemma lem1027010 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr x n) = (term848 A mul pwr n x).
Proof. exact (@lem1027009 A (pwr x n) x mul h1). Qed.
Lemma lem1027015 {A : Type'} (n : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term121 A pwr x n) = (term848 A mul pwr n x).
Proof. exact (TRANS (@lem1027006 A x n mul pwr h2) (@lem1027010 A pwr n x mul h1)). Qed.
Lemma lem1027016 {A : Type'} (mul : type1400 A) : mul = mul.
Proof. exact (eq_refl mul). Qed.
Lemma lem1027017 {A : Type'} (n : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term1030 A mul pwr x n) = (term1031 A mul pwr n x).
Proof. exact (MK_COMB (@lem1027016 A mul) (@lem1027015 A n x mul pwr h1 h2)). Qed.
Lemma lem1027019 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1026823 A mul pwr x n) (@lem1026822 A x n mul pwr h1)). Qed.
Lemma lem1027020 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1027019 A x n mul pwr h1). Qed.
Lemma lem1027021 {A : Type'} (y : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr y n) = (term122 A mul pwr y n).
Proof. exact (@lem1027020 A y n mul pwr h1). Qed.
Lemma lem1027023 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (EQ_MP (@lem1026856 A mul n m) (@lem1026855 A m n mul h1)). Qed.
Lemma lem1027024 {A : Type'} (n : A) (m : A) (mul : type1400 A) (h1 : term11 A mul) : (mul m n) = (mul n m).
Proof. exact (@lem1027023 A n m mul h1). Qed.
Lemma lem1027025 {A : Type'} (pwr : type1423 A) (n : nat) (y : A) (mul : type1400 A) (h1 : term11 A mul) : (term122 A mul pwr y n) = (term848 A mul pwr n y).
Proof. exact (@lem1027024 A (pwr y n) y mul h1). Qed.
Lemma lem1027030 {A : Type'} (n : nat) (y : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term121 A pwr y n) = (term848 A mul pwr n y).
Proof. exact (TRANS (@lem1027021 A y n mul pwr h2) (@lem1027025 A pwr n y mul h1)). Qed.
Lemma lem1027031 {A : Type'} (x : A) (n : nat) (y : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term11 A mul) (h2 : term21 A mul pwr) : (term999 A mul x pwr y n) = (term1032 A x mul pwr n y).
Proof. exact (MK_COMB (@lem1027017 A n x mul pwr h1 h2) (@lem1027030 A n y mul pwr h1 h2)). Qed.
Lemma lem1027033 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (EQ_MP (@lem1026865 A m mul n p) (@lem1026864 A m n p mul h1)). Qed.
Lemma lem1027034 {A : Type'} (m : A) (n : A) (p : A) (mul : type1400 A) (h1 : term110 A mul) : (term104 A mul m n p) = (term95 A m mul n p).
Proof. exact (@lem1027033 A m n p mul h1). Qed.
Lemma lem1027035 {A : Type'} (x : A) (pwr : type1423 A) (n : nat) (y : A) (mul : type1400 A) (h1 : term110 A mul) : (term1032 A x mul pwr n y) = (term1024 A x mul pwr n y).
Proof. exact (@lem1027034 A (pwr x n) x (term848 A mul pwr n y) mul h1). Qed.
Lemma lem1027045 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (EQ_MP (@lem1026874 A n mul m p) (@lem1026873 A n m p mul h1)). Qed.
Lemma lem1027046 {A : Type'} (n : A) (m : A) (p : A) (mul : type1400 A) (h1 : term101 A mul) : (term95 A m mul n p) = (term95 A n mul m p).
Proof. exact (@lem1027045 A n m p mul h1). Qed.
Lemma lem1027047 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (y : A) (mul : type1400 A) (h1 : term101 A mul) : (term1025 A x mul pwr n y) = (term1026 A pwr n mul x y).
Proof. exact (@lem1027046 A (pwr y n) x y mul h1). Qed.
Lemma lem1027060 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : (term955 A mul pwr x n) = (term955 A mul pwr x n).
Proof. exact (eq_refl (term955 A mul pwr x n)). Qed.
Lemma lem1027061 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (y : A) (mul : type1400 A) (h1 : term101 A mul) : (term1024 A x mul pwr n y) = (term1027 A pwr n mul x y).
Proof. exact (MK_COMB (@lem1027060 A mul pwr x n) (@lem1027047 A pwr n x y mul h1)). Qed.
Lemma lem1027070 {A : Type'} (pwr : type1423 A) (n : nat) (x : A) (y : A) (mul : type1400 A) (h1 : term101 A mul) (h2 : term110 A mul) : (term1032 A x mul pwr n y) = (term1027 A pwr n mul x y).
Proof. exact (TRANS (@lem1027035 A x pwr n y mul h2) (@lem1027061 A pwr n x y mul h1)). Qed.
Lemma lem1027071 {A : Type'} (n : nat) (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) : (term999 A mul x pwr y n) = (term1027 A pwr n mul x y).
Proof. exact (TRANS (@lem1027031 A x n y mul pwr h3 h4) (@lem1027070 A pwr n x y mul h1 h2)). Qed.
Lemma lem1027072 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : ((term998 A pwr mul x y n) = (term999 A mul x pwr y n)) = ((term1027 A pwr n mul x y) = (term1027 A pwr n mul x y)).
Proof. exact (MK_COMB (@lem1026999 A mul x pwr y n h1 h2 h3 h4 h5) (@lem1027071 A n x y mul pwr h1 h2 h3 h4)). Qed.
Lemma lem1027074 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1027075 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1027074 A x). Qed.
Lemma lem1027076 {A : Type'} (pwr : type1423 A) (n : nat) (mul : type1400 A) (x : A) (y : A) : ((term1027 A pwr n mul x y) = (term1027 A pwr n mul x y)) = True.
Proof. exact (@lem1027075 A (term1027 A pwr n mul x y)). Qed.
Lemma lem1027077 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : ((term998 A pwr mul x y n) = (term999 A mul x pwr y n)) = True.
Proof. exact (TRANS (@lem1027072 A mul x pwr y n h1 h2 h3 h4 h5) (@lem1027076 A pwr n mul x y)). Qed.
Lemma lem1027078 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : True = ((term998 A pwr mul x y n) = (term999 A mul x pwr y n)).
Proof. exact (SYM (@lem1027077 A mul x pwr y n h1 h2 h3 h4 h5)). Qed.
Lemma lem1027079 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n)) : (term998 A pwr mul x y n) = (term999 A mul x pwr y n).
Proof. exact (EQ_MP (@lem1027078 A mul x pwr y n h1 h2 h3 h4 h5) (@lem0)). Qed.
Lemma lem1027080 {A : Type'} (x : A) (y : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) : term1001 A mul x pwr y n.
Proof. exact (fun h0 : (term993 A pwr mul x y n) = (term994 A mul x pwr y n) => @lem1027079 A mul x pwr y n h1 h2 h3 h4 h0). Qed.
Lemma lem1027085 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) : term1005 A mul x pwr y.
Proof. exact (fun n : nat => @lem1027080 A x y n mul pwr h1 h2 h3 h4). Qed.
Lemma lem1027086 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : term1007 A mul x pwr y.
Proof. exact (conj (@lem1026797 A x y mul pwr r1 h5 h6) (@lem1027085 A x y mul pwr h1 h2 h3 h4)). Qed.
Lemma lem1027087 {A : Type'} (x : A) (y : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : term1012 A mul x pwr y.
Proof. exact (@lem1026659 A mul x pwr y (@lem1027086 A x y mul pwr r1 h1 h2 h3 h4 h5 h6)). Qed.
Lemma lem1027092 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : term1033 A mul x pwr.
Proof. exact (fun y : A => @lem1027087 A x y mul pwr r1 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1027097 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A mul) (h2 : term110 A mul) (h3 : term11 A mul) (h4 : term21 A mul pwr) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : term984 A mul pwr.
Proof. exact (fun x : A => @lem1027092 A x mul pwr r1 h1 h2 h3 h4 h5 h6). Qed.
Lemma lem1027098 {A : Type'} (pwr : type1423 A) (h1 : term1034 A pwr) : term1034 A pwr.
Proof. exact (h1). Qed.
Lemma lem1027110 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1027111 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term890 A mul y pwr x p q) = (term1035 A mul y pwr x p q).
Proof. exact (@lem1027110 (term890 A mul y pwr x p q)). Qed.
Lemma lem1027112 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1035 A mul y pwr x p q) = (term890 A mul y pwr x p q).
Proof. exact (SYM (@lem1027111 A mul y pwr x p q)). Qed.
Lemma lem1027113 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1036 A mul y pwr x p q) : term1036 A mul y pwr x p q.
Proof. exact (h1). Qed.
Lemma lem1027116 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1037 A add r1 r0 mul y x p q pwr) : term1037 A add r1 r0 mul y x p q pwr.
Proof. exact (h1). Qed.
Lemma lem1027117 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1038 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term1037 A add r1 r0 mul y x p q pwr => @lem1027116 A add r1 r0 mul y x p q pwr h0). Qed.
Lemma lem1027118 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1038 A add r1 r0 mul y x p q pwr) : term1038 A add r1 r0 mul y x p q pwr.
Proof. exact (h1). Qed.
Lemma lem1027119 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1037 A add r1 r0 mul y x p q pwr) : term1037 A add r1 r0 mul y x p q pwr.
Proof. exact (h1). Qed.
Lemma lem1027120 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1037 A add r1 r0 mul y x p q pwr) (h2 : term1038 A add r1 r0 mul y x p q pwr) : term1037 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1027118 A add r1 r0 mul y x p q pwr h2 (@lem1027119 A add r1 r0 mul y x p q pwr h1)). Qed.
Lemma lem1027121 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1037 A add r1 r0 mul y x p q pwr) : term1039 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term1038 A add r1 r0 mul y x p q pwr => @lem1027120 A add r1 r0 mul y x p q pwr h1 h0). Qed.
Lemma lem1027122 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1038 A add r1 r0 mul y x p q pwr) : term1038 A add r1 r0 mul y x p q pwr.
Proof. exact (h1). Qed.
Lemma lem1027123 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1037 A add r1 r0 mul y x p q pwr) (h2 : term1038 A add r1 r0 mul y x p q pwr) : term1037 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1027121 A add r1 r0 mul y x p q pwr h1 (@lem1027122 A add r1 r0 mul y x p q pwr h2)). Qed.
Lemma lem1027124 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1038 A add r1 r0 mul y x p q pwr) : term1038 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term1037 A add r1 r0 mul y x p q pwr => @lem1027123 A add r1 r0 mul y x p q pwr h0 h1). Qed.
Lemma lem1027125 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1040 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term1038 A add r1 r0 mul y x p q pwr => @lem1027124 A add r1 r0 mul y x p q pwr h0). Qed.
Lemma lem1027128 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1038 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1027125 A add r1 r0 mul y x p q pwr (@lem1027117 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027129 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1038 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1027128 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1027357 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1027358 {A : Type'} (pwr : type1423 A) : (term1041 A pwr) = (term1042 A pwr).
Proof. exact (@lem1027357 (term1034 A pwr)). Qed.
Lemma lem1027371 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1043 A mul y pwr x p q) = (term1043 A mul y pwr x p q).
Proof. exact (eq_refl (term1043 A mul y pwr x p q)). Qed.
Lemma lem1027372 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1044 A mul y x p q pwr) = (term1045 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027371 A mul y pwr x p q) (@lem1027358 A pwr)). Qed.
Lemma lem1027375 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1046 A mul pwr) = (term1046 A mul pwr).
Proof. exact (eq_refl (term1046 A mul pwr)). Qed.
Lemma lem1027376 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1047 A mul y x p q pwr) = (term1048 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027375 A mul pwr) (@lem1027372 A mul y x p q pwr)). Qed.
Lemma lem1027379 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1049 A mul pwr) = (term1049 A mul pwr).
Proof. exact (eq_refl (term1049 A mul pwr)). Qed.
Lemma lem1027380 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1050 A mul y x p q pwr) = (term1051 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027379 A mul pwr) (@lem1027376 A mul y x p q pwr)). Qed.
Lemma lem1027383 {A : Type'} (mul : type1400 A) (r0 : A) : (term1052 A mul r0) = (term1052 A mul r0).
Proof. exact (eq_refl (term1052 A mul r0)). Qed.
Lemma lem1027384 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1053 A r0 mul y x p q pwr) = (term1054 A r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027383 A mul r0) (@lem1027380 A mul y x p q pwr)). Qed.
Lemma lem1027387 {A : Type'} (mul : type1400 A) (r1 : A) : (term1055 A mul r1) = (term1055 A mul r1).
Proof. exact (eq_refl (term1055 A mul r1)). Qed.
Lemma lem1027388 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1056 A r1 r0 mul y x p q pwr) = (term1057 A r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027387 A mul r1) (@lem1027384 A r0 mul y x p q pwr)). Qed.
Lemma lem1027391 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term1058 A add mul) = (term1058 A add mul).
Proof. exact (eq_refl (term1058 A add mul)). Qed.
Lemma lem1027392 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1059 A add r1 r0 mul y x p q pwr) = (term1060 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027391 A add mul) (@lem1027388 A r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027395 {A : Type'} (mul : type1400 A) : (term1061 A mul) = (term1061 A mul).
Proof. exact (eq_refl (term1061 A mul)). Qed.
Lemma lem1027396 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1062 A add r1 r0 mul y x p q pwr) = (term1063 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027395 A mul) (@lem1027392 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027399 {A : Type'} (mul : type1400 A) : (term1064 A mul) = (term1064 A mul).
Proof. exact (eq_refl (term1064 A mul)). Qed.
Lemma lem1027400 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1065 A add r1 r0 mul y x p q pwr) = (term1066 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027399 A mul) (@lem1027396 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027403 {A : Type'} (mul : type1400 A) : (term48 A mul) = (term48 A mul).
Proof. exact (eq_refl (term48 A mul)). Qed.
Lemma lem1027404 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1067 A add r1 r0 mul y x p q pwr) = (term1068 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027403 A mul) (@lem1027400 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027407 {A : Type'} (add : type1400 A) (r0 : A) : (term1055 A add r0) = (term1055 A add r0).
Proof. exact (eq_refl (term1055 A add r0)). Qed.
Lemma lem1027408 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1069 A add r1 r0 mul y x p q pwr) = (term1070 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027407 A add r0) (@lem1027404 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027411 {A : Type'} (add : type1400 A) : (term1061 A add) = (term1061 A add).
Proof. exact (eq_refl (term1061 A add)). Qed.
Lemma lem1027412 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1071 A add r1 r0 mul y x p q pwr) = (term1072 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027411 A add) (@lem1027408 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027415 {A : Type'} (add : type1400 A) : (term1064 A add) = (term1064 A add).
Proof. exact (eq_refl (term1064 A add)). Qed.
Lemma lem1027416 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1073 A add r1 r0 mul y x p q pwr) = (term1074 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027415 A add) (@lem1027412 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027419 {A : Type'} (add : type1400 A) : (term48 A add) = (term48 A add).
Proof. exact (eq_refl (term48 A add)). Qed.
Lemma lem1027420 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1075 A add r1 r0 mul y x p q pwr) = (term1076 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027419 A add) (@lem1027416 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027423 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term33 A mul pwr) = (term33 A mul pwr).
Proof. exact (eq_refl (term33 A mul pwr)). Qed.
Lemma lem1027424 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1077 A add r1 r0 mul y x p q pwr) = (term1078 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027423 A mul pwr) (@lem1027420 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027427 {A : Type'} (pwr : type1423 A) (r1 : A) : (term36 A pwr r1) = (term36 A pwr r1).
Proof. exact (eq_refl (term36 A pwr r1)). Qed.
Lemma lem1027428 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1079 A add r1 r0 mul y x p q pwr) = (term1080 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027427 A pwr r1) (@lem1027424 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027431 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term39 A add mul) = (term39 A add mul).
Proof. exact (eq_refl (term39 A add mul)). Qed.
Lemma lem1027432 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1081 A add r1 r0 mul y x p q pwr) = (term1082 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027431 A add mul) (@lem1027428 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027435 {A : Type'} (mul : type1400 A) (r0 : A) : (term42 A mul r0) = (term42 A mul r0).
Proof. exact (eq_refl (term42 A mul r0)). Qed.
Lemma lem1027436 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1083 A add r1 r0 mul y x p q pwr) = (term1084 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027435 A mul r0) (@lem1027432 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027439 {A : Type'} (mul : type1400 A) (r1 : A) : (term45 A mul r1) = (term45 A mul r1).
Proof. exact (eq_refl (term45 A mul r1)). Qed.
Lemma lem1027440 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1085 A add r1 r0 mul y x p q pwr) = (term1086 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027439 A mul r1) (@lem1027436 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027443 {A : Type'} (add : type1400 A) (r0 : A) : (term45 A add r0) = (term45 A add r0).
Proof. exact (eq_refl (term45 A add r0)). Qed.
Lemma lem1027444 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1037 A add r1 r0 mul y x p q pwr) = (term1087 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027443 A add r0) (@lem1027440 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027447 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1088 A r1 r0 mul y x p q pwr) = (term1089 A r1 r0 mul y x p q pwr).
Proof. exact (fun_ext (fun add : type1400 A => @lem1027444 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027448 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1027449 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1090 A r1 r0 mul y x p q pwr) = (term1091 A r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027448 A) (@lem1027447 A r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027454 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1092 A r0 mul y x p q pwr) = (term1093 A r0 mul y x p q pwr).
Proof. exact (fun_ext (fun r1 : A => @lem1027449 A r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027456 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1094 A r0 mul y x p q pwr) = (term1095 A r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027455 A) (@lem1027454 A r0 mul y x p q pwr)). Qed.
Lemma lem1027461 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1096 A mul y x p q pwr) = (term1097 A mul y x p q pwr).
Proof. exact (fun_ext (fun r0 : A => @lem1027456 A r0 mul y x p q pwr)). Qed.
Lemma lem1027462 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027463 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1098 A mul y x p q pwr) = (term1099 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027462 A) (@lem1027461 A mul y x p q pwr)). Qed.
Lemma lem1027468 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1100 A y x p q pwr) = (term1101 A y x p q pwr).
Proof. exact (fun_ext (fun mul : type1400 A => @lem1027463 A mul y x p q pwr)). Qed.
Lemma lem1027469 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1027470 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1102 A y x p q pwr) = (term1103 A y x p q pwr).
Proof. exact (MK_COMB (@lem1027469 A) (@lem1027468 A y x p q pwr)). Qed.
Lemma lem1027475 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1104 A x p q pwr) = (term1105 A x p q pwr).
Proof. exact (fun_ext (fun y : A => @lem1027470 A y x p q pwr)). Qed.
Lemma lem1027476 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027477 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1106 A x p q pwr) = (term1107 A x p q pwr).
Proof. exact (MK_COMB (@lem1027476 A) (@lem1027475 A x p q pwr)). Qed.
Lemma lem1027482 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) : (term1108 A p q pwr) = (term1109 A p q pwr).
Proof. exact (fun_ext (fun x : A => @lem1027477 A x p q pwr)). Qed.
Lemma lem1027483 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027484 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) : (term1110 A p q pwr) = (term1111 A p q pwr).
Proof. exact (MK_COMB (@lem1027483 A) (@lem1027482 A p q pwr)). Qed.
Lemma lem1027489 {A : Type'} (q : nat) (pwr : type1423 A) : (term1112 A q pwr) = (term1113 A q pwr).
Proof. exact (fun_ext (fun p : nat => @lem1027484 A p q pwr)). Qed.
Lemma lem1027490 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027491 {A : Type'} (q : nat) (pwr : type1423 A) : (term1114 A q pwr) = (term1115 A q pwr).
Proof. exact (MK_COMB (@lem1027490) (@lem1027489 A q pwr)). Qed.
Lemma lem1027496 {A : Type'} (pwr : type1423 A) : (term1116 A pwr) = (term1117 A pwr).
Proof. exact (fun_ext (fun q : nat => @lem1027491 A q pwr)). Qed.
Lemma lem1027497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027498 {A : Type'} (pwr : type1423 A) : (term1118 A pwr) = (term1119 A pwr).
Proof. exact (MK_COMB (@lem1027497) (@lem1027496 A pwr)). Qed.
Lemma lem1027503 {A : Type'} : (term1120 A) = (term1121 A).
Proof. exact (fun_ext (fun pwr : type1423 A => @lem1027498 A pwr)). Qed.
Lemma lem1027504 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem1027513 {A : Type'} : (term1122 A) = (term1123 A).
Proof. exact (MK_COMB (@lem1027504 A) (@lem1027503 A)). Qed.
Lemma lem1027514 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : ((term879 A pwr x m n) = (term880 A pwr x m n)) = ((term879 A pwr x m n) = (term880 A pwr x m n)).
Proof. exact (eq_refl ((term879 A pwr x m n) = (term880 A pwr x m n))). Qed.
Lemma lem1027515 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1124 A pwr x m) = (term1124 A pwr x m).
Proof. exact (fun_ext (fun n : nat => @lem1027514 A pwr x m n)). Qed.
Lemma lem1027516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027517 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1125 A pwr x m) = (term1125 A pwr x m).
Proof. exact (MK_COMB (@lem1027516) (@lem1027515 A pwr x m)). Qed.
Lemma lem1027518 {A : Type'} (pwr : type1423 A) (x : A) : (term1126 A pwr x) = (term1126 A pwr x).
Proof. exact (fun_ext (fun m : nat => @lem1027517 A pwr x m)). Qed.
Lemma lem1027519 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027520 {A : Type'} (pwr : type1423 A) (x : A) : (term1127 A pwr x) = (term1127 A pwr x).
Proof. exact (MK_COMB (@lem1027519) (@lem1027518 A pwr x)). Qed.
Lemma lem1027521 {A : Type'} (pwr : type1423 A) : (term1128 A pwr) = (term1128 A pwr).
Proof. exact (fun_ext (fun x : A => @lem1027520 A pwr x)). Qed.
Lemma lem1027522 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027523 {A : Type'} (pwr : type1423 A) : (term1034 A pwr) = (term1034 A pwr).
Proof. exact (MK_COMB (@lem1027522 A) (@lem1027521 A pwr)). Qed.
Lemma lem1027524 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1027525 {A : Type'} (pwr : type1423 A) : (term1042 A pwr) = (term1042 A pwr).
Proof. exact (MK_COMB (@lem1027524) (@lem1027523 A pwr)). Qed.
Lemma lem1027538 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1043 A mul y pwr x p q) = (term1043 A mul y pwr x p q).
Proof. exact (eq_refl (term1043 A mul y pwr x p q)). Qed.
Lemma lem1027539 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1045 A mul y x p q pwr) = (term1045 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027538 A mul y pwr x p q) (@lem1027525 A pwr)). Qed.
Lemma lem1027540 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)) = ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)).
Proof. exact (eq_refl ((term993 A pwr mul x y n) = (term994 A mul x pwr y n))). Qed.
Lemma lem1027541 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term986 A mul x pwr y) = (term986 A mul x pwr y).
Proof. exact (fun_ext (fun n : nat => @lem1027540 A mul x pwr y n)). Qed.
Lemma lem1027542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027543 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1012 A mul x pwr y) = (term1012 A mul x pwr y).
Proof. exact (MK_COMB (@lem1027542) (@lem1027541 A mul x pwr y)). Qed.
Lemma lem1027544 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1129 A mul x pwr) = (term1129 A mul x pwr).
Proof. exact (fun_ext (fun y : A => @lem1027543 A mul x pwr y)). Qed.
Lemma lem1027545 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027546 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1033 A mul x pwr) = (term1033 A mul x pwr).
Proof. exact (MK_COMB (@lem1027545 A) (@lem1027544 A mul x pwr)). Qed.
Lemma lem1027547 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1130 A mul pwr) = (term1130 A mul pwr).
Proof. exact (fun_ext (fun x : A => @lem1027546 A mul x pwr)). Qed.
Lemma lem1027548 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027549 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term984 A mul pwr) = (term984 A mul pwr).
Proof. exact (MK_COMB (@lem1027548 A) (@lem1027547 A mul pwr)). Qed.
Lemma lem1027550 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027551 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1046 A mul pwr) = (term1046 A mul pwr).
Proof. exact (MK_COMB (@lem1027550) (@lem1027549 A mul pwr)). Qed.
Lemma lem1027552 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1048 A mul y x p q pwr) = (term1048 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027551 A mul pwr) (@lem1027539 A mul y x p q pwr)). Qed.
Lemma lem1027553 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (x : A) (n : nat) : ((term970 A pwr x m n) = (term971 A mul m pwr x n)) = ((term970 A pwr x m n) = (term971 A mul m pwr x n)).
Proof. exact (eq_refl ((term970 A pwr x m n) = (term971 A mul m pwr x n))). Qed.
Lemma lem1027554 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term1131 A mul m pwr n) = (term1131 A mul m pwr n).
Proof. exact (fun_ext (fun x : A => @lem1027553 A mul m pwr x n)). Qed.
Lemma lem1027555 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027556 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term929 A mul m pwr n) = (term929 A mul m pwr n).
Proof. exact (MK_COMB (@lem1027555 A) (@lem1027554 A mul m pwr n)). Qed.
Lemma lem1027557 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term923 A mul m pwr) = (term923 A mul m pwr).
Proof. exact (fun_ext (fun n : nat => @lem1027556 A mul m pwr n)). Qed.
Lemma lem1027558 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027559 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term946 A mul m pwr) = (term946 A mul m pwr).
Proof. exact (MK_COMB (@lem1027558) (@lem1027557 A mul m pwr)). Qed.
Lemma lem1027560 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1132 A mul pwr) = (term1132 A mul pwr).
Proof. exact (fun_ext (fun m : nat => @lem1027559 A mul m pwr)). Qed.
Lemma lem1027561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027562 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term920 A mul pwr) = (term920 A mul pwr).
Proof. exact (MK_COMB (@lem1027561) (@lem1027560 A mul pwr)). Qed.
Lemma lem1027563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027564 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1049 A mul pwr) = (term1049 A mul pwr).
Proof. exact (MK_COMB (@lem1027563) (@lem1027562 A mul pwr)). Qed.
Lemma lem1027565 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1051 A mul y x p q pwr) = (term1051 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027564 A mul pwr) (@lem1027552 A mul y x p q pwr)). Qed.
Lemma lem1027566 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : ((mul x r0) = r0) = ((mul x r0) = r0).
Proof. exact (eq_refl ((mul x r0) = r0)). Qed.
Lemma lem1027567 {A : Type'} (mul : type1400 A) (r0 : A) : (term79 A mul r0) = (term79 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1027566 A mul x r0)). Qed.
Lemma lem1027568 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027569 {A : Type'} (mul : type1400 A) (r0 : A) : (term80 A mul r0) = (term80 A mul r0).
Proof. exact (MK_COMB (@lem1027568 A) (@lem1027567 A mul r0)). Qed.
Lemma lem1027570 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027571 {A : Type'} (mul : type1400 A) (r0 : A) : (term1052 A mul r0) = (term1052 A mul r0).
Proof. exact (MK_COMB (@lem1027570) (@lem1027569 A mul r0)). Qed.
Lemma lem1027572 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1054 A r0 mul y x p q pwr) = (term1054 A r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027571 A mul r0) (@lem1027565 A mul y x p q pwr)). Qed.
Lemma lem1027573 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : ((mul x r1) = x) = ((mul x r1) = x).
Proof. exact (eq_refl ((mul x r1) = x)). Qed.
Lemma lem1027574 {A : Type'} (mul : type1400 A) (r1 : A) : (term81 A mul r1) = (term81 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1027573 A mul r1 x)). Qed.
Lemma lem1027575 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027576 {A : Type'} (mul : type1400 A) (r1 : A) : (term82 A mul r1) = (term82 A mul r1).
Proof. exact (MK_COMB (@lem1027575 A) (@lem1027574 A mul r1)). Qed.
Lemma lem1027577 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027578 {A : Type'} (mul : type1400 A) (r1 : A) : (term1055 A mul r1) = (term1055 A mul r1).
Proof. exact (MK_COMB (@lem1027577) (@lem1027576 A mul r1)). Qed.
Lemma lem1027579 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1057 A r1 r0 mul y x p q pwr) = (term1057 A r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027578 A mul r1) (@lem1027572 A r0 mul y x p q pwr)). Qed.
Lemma lem1027580 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) (p : A) : ((term85 A mul add m n p) = (term86 A add m mul n p)) = ((term85 A mul add m n p) = (term86 A add m mul n p)).
Proof. exact (eq_refl ((term85 A mul add m n p) = (term86 A add m mul n p))). Qed.
Lemma lem1027581 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term87 A add m mul n) = (term87 A add m mul n).
Proof. exact (fun_ext (fun p : A => @lem1027580 A add m mul n p)). Qed.
Lemma lem1027582 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027583 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) (n : A) : (term88 A add m mul n) = (term88 A add m mul n).
Proof. exact (MK_COMB (@lem1027582 A) (@lem1027581 A add m mul n)). Qed.
Lemma lem1027584 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term89 A add m mul) = (term89 A add m mul).
Proof. exact (fun_ext (fun n : A => @lem1027583 A add m mul n)). Qed.
Lemma lem1027585 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027586 {A : Type'} (add : type1400 A) (m : A) (mul : type1400 A) : (term90 A add m mul) = (term90 A add m mul).
Proof. exact (MK_COMB (@lem1027585 A) (@lem1027584 A add m mul)). Qed.
Lemma lem1027587 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term91 A add mul) = (term91 A add mul).
Proof. exact (fun_ext (fun m : A => @lem1027586 A add m mul)). Qed.
Lemma lem1027588 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027589 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term92 A add mul) = (term92 A add mul).
Proof. exact (MK_COMB (@lem1027588 A) (@lem1027587 A add mul)). Qed.
Lemma lem1027590 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027591 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term1058 A add mul) = (term1058 A add mul).
Proof. exact (MK_COMB (@lem1027590) (@lem1027589 A add mul)). Qed.
Lemma lem1027592 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1060 A add r1 r0 mul y x p q pwr) = (term1060 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027591 A add mul) (@lem1027579 A r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027593 {A : Type'} (n : A) (mul : type1400 A) (m : A) (p : A) : ((term95 A m mul n p) = (term95 A n mul m p)) = ((term95 A m mul n p) = (term95 A n mul m p)).
Proof. exact (eq_refl ((term95 A m mul n p) = (term95 A n mul m p))). Qed.
Lemma lem1027594 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term96 A n mul m) = (term96 A n mul m).
Proof. exact (fun_ext (fun p : A => @lem1027593 A n mul m p)). Qed.
Lemma lem1027595 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027596 {A : Type'} (n : A) (mul : type1400 A) (m : A) : (term97 A n mul m) = (term97 A n mul m).
Proof. exact (MK_COMB (@lem1027595 A) (@lem1027594 A n mul m)). Qed.
Lemma lem1027597 {A : Type'} (mul : type1400 A) (m : A) : (term98 A mul m) = (term98 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1027596 A n mul m)). Qed.
Lemma lem1027598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027599 {A : Type'} (mul : type1400 A) (m : A) : (term99 A mul m) = (term99 A mul m).
Proof. exact (MK_COMB (@lem1027598 A) (@lem1027597 A mul m)). Qed.
Lemma lem1027600 {A : Type'} (mul : type1400 A) : (term100 A mul) = (term100 A mul).
Proof. exact (fun_ext (fun m : A => @lem1027599 A mul m)). Qed.
Lemma lem1027601 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027602 {A : Type'} (mul : type1400 A) : (term101 A mul) = (term101 A mul).
Proof. exact (MK_COMB (@lem1027601 A) (@lem1027600 A mul)). Qed.
Lemma lem1027603 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027604 {A : Type'} (mul : type1400 A) : (term1061 A mul) = (term1061 A mul).
Proof. exact (MK_COMB (@lem1027603) (@lem1027602 A mul)). Qed.
Lemma lem1027605 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1063 A add r1 r0 mul y x p q pwr) = (term1063 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027604 A mul) (@lem1027592 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027606 {A : Type'} (m : A) (mul : type1400 A) (n : A) (p : A) : ((term104 A mul m n p) = (term95 A m mul n p)) = ((term104 A mul m n p) = (term95 A m mul n p)).
Proof. exact (eq_refl ((term104 A mul m n p) = (term95 A m mul n p))). Qed.
Lemma lem1027607 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term105 A m mul n) = (term105 A m mul n).
Proof. exact (fun_ext (fun p : A => @lem1027606 A m mul n p)). Qed.
Lemma lem1027608 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027609 {A : Type'} (m : A) (mul : type1400 A) (n : A) : (term106 A m mul n) = (term106 A m mul n).
Proof. exact (MK_COMB (@lem1027608 A) (@lem1027607 A m mul n)). Qed.
Lemma lem1027610 {A : Type'} (m : A) (mul : type1400 A) : (term107 A m mul) = (term107 A m mul).
Proof. exact (fun_ext (fun n : A => @lem1027609 A m mul n)). Qed.
Lemma lem1027611 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027612 {A : Type'} (m : A) (mul : type1400 A) : (term108 A m mul) = (term108 A m mul).
Proof. exact (MK_COMB (@lem1027611 A) (@lem1027610 A m mul)). Qed.
Lemma lem1027613 {A : Type'} (mul : type1400 A) : (term109 A mul) = (term109 A mul).
Proof. exact (fun_ext (fun m : A => @lem1027612 A m mul)). Qed.
Lemma lem1027614 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027615 {A : Type'} (mul : type1400 A) : (term110 A mul) = (term110 A mul).
Proof. exact (MK_COMB (@lem1027614 A) (@lem1027613 A mul)). Qed.
Lemma lem1027616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027617 {A : Type'} (mul : type1400 A) : (term1064 A mul) = (term1064 A mul).
Proof. exact (MK_COMB (@lem1027616) (@lem1027615 A mul)). Qed.
Lemma lem1027618 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1066 A add r1 r0 mul y x p q pwr) = (term1066 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027617 A mul) (@lem1027605 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027619 {A : Type'} (mul : type1400 A) (n : A) (m : A) : ((mul m n) = (mul n m)) = ((mul m n) = (mul n m)).
Proof. exact (eq_refl ((mul m n) = (mul n m))). Qed.
Lemma lem1027620 {A : Type'} (mul : type1400 A) (m : A) : (term113 A mul m) = (term113 A mul m).
Proof. exact (fun_ext (fun n : A => @lem1027619 A mul n m)). Qed.
Lemma lem1027621 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027622 {A : Type'} (mul : type1400 A) (m : A) : (term114 A mul m) = (term114 A mul m).
Proof. exact (MK_COMB (@lem1027621 A) (@lem1027620 A mul m)). Qed.
Lemma lem1027623 {A : Type'} (mul : type1400 A) : (term115 A mul) = (term115 A mul).
Proof. exact (fun_ext (fun m : A => @lem1027622 A mul m)). Qed.
Lemma lem1027624 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027625 {A : Type'} (mul : type1400 A) : (term11 A mul) = (term11 A mul).
Proof. exact (MK_COMB (@lem1027624 A) (@lem1027623 A mul)). Qed.
Lemma lem1027626 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027627 {A : Type'} (mul : type1400 A) : (term48 A mul) = (term48 A mul).
Proof. exact (MK_COMB (@lem1027626) (@lem1027625 A mul)). Qed.
Lemma lem1027628 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1068 A add r1 r0 mul y x p q pwr) = (term1068 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027627 A mul) (@lem1027618 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027629 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : ((add x r0) = x) = ((add x r0) = x).
Proof. exact (eq_refl ((add x r0) = x)). Qed.
Lemma lem1027630 {A : Type'} (add : type1400 A) (r0 : A) : (term81 A add r0) = (term81 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1027629 A add r0 x)). Qed.
Lemma lem1027631 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027632 {A : Type'} (add : type1400 A) (r0 : A) : (term82 A add r0) = (term82 A add r0).
Proof. exact (MK_COMB (@lem1027631 A) (@lem1027630 A add r0)). Qed.
Lemma lem1027633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027634 {A : Type'} (add : type1400 A) (r0 : A) : (term1055 A add r0) = (term1055 A add r0).
Proof. exact (MK_COMB (@lem1027633) (@lem1027632 A add r0)). Qed.
Lemma lem1027635 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1070 A add r1 r0 mul y x p q pwr) = (term1070 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027634 A add r0) (@lem1027628 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027636 {A : Type'} (n : A) (add : type1400 A) (m : A) (p : A) : ((term95 A m add n p) = (term95 A n add m p)) = ((term95 A m add n p) = (term95 A n add m p)).
Proof. exact (eq_refl ((term95 A m add n p) = (term95 A n add m p))). Qed.
Lemma lem1027637 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term96 A n add m) = (term96 A n add m).
Proof. exact (fun_ext (fun p : A => @lem1027636 A n add m p)). Qed.
Lemma lem1027638 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027639 {A : Type'} (n : A) (add : type1400 A) (m : A) : (term97 A n add m) = (term97 A n add m).
Proof. exact (MK_COMB (@lem1027638 A) (@lem1027637 A n add m)). Qed.
Lemma lem1027640 {A : Type'} (add : type1400 A) (m : A) : (term98 A add m) = (term98 A add m).
Proof. exact (fun_ext (fun n : A => @lem1027639 A n add m)). Qed.
Lemma lem1027641 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027642 {A : Type'} (add : type1400 A) (m : A) : (term99 A add m) = (term99 A add m).
Proof. exact (MK_COMB (@lem1027641 A) (@lem1027640 A add m)). Qed.
Lemma lem1027643 {A : Type'} (add : type1400 A) : (term100 A add) = (term100 A add).
Proof. exact (fun_ext (fun m : A => @lem1027642 A add m)). Qed.
Lemma lem1027644 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027645 {A : Type'} (add : type1400 A) : (term101 A add) = (term101 A add).
Proof. exact (MK_COMB (@lem1027644 A) (@lem1027643 A add)). Qed.
Lemma lem1027646 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027647 {A : Type'} (add : type1400 A) : (term1061 A add) = (term1061 A add).
Proof. exact (MK_COMB (@lem1027646) (@lem1027645 A add)). Qed.
Lemma lem1027648 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1072 A add r1 r0 mul y x p q pwr) = (term1072 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027647 A add) (@lem1027635 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027649 {A : Type'} (m : A) (add : type1400 A) (n : A) (p : A) : ((term104 A add m n p) = (term95 A m add n p)) = ((term104 A add m n p) = (term95 A m add n p)).
Proof. exact (eq_refl ((term104 A add m n p) = (term95 A m add n p))). Qed.
Lemma lem1027650 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term105 A m add n) = (term105 A m add n).
Proof. exact (fun_ext (fun p : A => @lem1027649 A m add n p)). Qed.
Lemma lem1027651 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027652 {A : Type'} (m : A) (add : type1400 A) (n : A) : (term106 A m add n) = (term106 A m add n).
Proof. exact (MK_COMB (@lem1027651 A) (@lem1027650 A m add n)). Qed.
Lemma lem1027653 {A : Type'} (m : A) (add : type1400 A) : (term107 A m add) = (term107 A m add).
Proof. exact (fun_ext (fun n : A => @lem1027652 A m add n)). Qed.
Lemma lem1027654 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027655 {A : Type'} (m : A) (add : type1400 A) : (term108 A m add) = (term108 A m add).
Proof. exact (MK_COMB (@lem1027654 A) (@lem1027653 A m add)). Qed.
Lemma lem1027656 {A : Type'} (add : type1400 A) : (term109 A add) = (term109 A add).
Proof. exact (fun_ext (fun m : A => @lem1027655 A m add)). Qed.
Lemma lem1027657 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027658 {A : Type'} (add : type1400 A) : (term110 A add) = (term110 A add).
Proof. exact (MK_COMB (@lem1027657 A) (@lem1027656 A add)). Qed.
Lemma lem1027659 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027660 {A : Type'} (add : type1400 A) : (term1064 A add) = (term1064 A add).
Proof. exact (MK_COMB (@lem1027659) (@lem1027658 A add)). Qed.
Lemma lem1027661 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1074 A add r1 r0 mul y x p q pwr) = (term1074 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027660 A add) (@lem1027648 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027662 {A : Type'} (add : type1400 A) (n : A) (m : A) : ((add m n) = (add n m)) = ((add m n) = (add n m)).
Proof. exact (eq_refl ((add m n) = (add n m))). Qed.
Lemma lem1027663 {A : Type'} (add : type1400 A) (m : A) : (term113 A add m) = (term113 A add m).
Proof. exact (fun_ext (fun n : A => @lem1027662 A add n m)). Qed.
Lemma lem1027664 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027665 {A : Type'} (add : type1400 A) (m : A) : (term114 A add m) = (term114 A add m).
Proof. exact (MK_COMB (@lem1027664 A) (@lem1027663 A add m)). Qed.
Lemma lem1027666 {A : Type'} (add : type1400 A) : (term115 A add) = (term115 A add).
Proof. exact (fun_ext (fun m : A => @lem1027665 A add m)). Qed.
Lemma lem1027667 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027668 {A : Type'} (add : type1400 A) : (term11 A add) = (term11 A add).
Proof. exact (MK_COMB (@lem1027667 A) (@lem1027666 A add)). Qed.
Lemma lem1027669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027670 {A : Type'} (add : type1400 A) : (term48 A add) = (term48 A add).
Proof. exact (MK_COMB (@lem1027669) (@lem1027668 A add)). Qed.
Lemma lem1027671 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1076 A add r1 r0 mul y x p q pwr) = (term1076 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027670 A add) (@lem1027661 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027672 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : ((term121 A pwr x n) = (term122 A mul pwr x n)) = ((term121 A pwr x n) = (term122 A mul pwr x n)).
Proof. exact (eq_refl ((term121 A pwr x n) = (term122 A mul pwr x n))). Qed.
Lemma lem1027673 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term123 A mul pwr x) = (term123 A mul pwr x).
Proof. exact (fun_ext (fun n : nat => @lem1027672 A mul pwr x n)). Qed.
Lemma lem1027674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027675 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term124 A mul pwr x) = (term124 A mul pwr x).
Proof. exact (MK_COMB (@lem1027674) (@lem1027673 A mul pwr x)). Qed.
Lemma lem1027676 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term125 A mul pwr) = (term125 A mul pwr).
Proof. exact (fun_ext (fun x : A => @lem1027675 A mul pwr x)). Qed.
Lemma lem1027677 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027678 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term21 A mul pwr) = (term21 A mul pwr).
Proof. exact (MK_COMB (@lem1027677 A) (@lem1027676 A mul pwr)). Qed.
Lemma lem1027679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027680 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term33 A mul pwr) = (term33 A mul pwr).
Proof. exact (MK_COMB (@lem1027679) (@lem1027678 A mul pwr)). Qed.
Lemma lem1027681 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1078 A add r1 r0 mul y x p q pwr) = (term1078 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027680 A mul pwr) (@lem1027671 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027682 {A : Type'} (pwr : type1423 A) (x : A) (r1 : A) : ((term126 A pwr x) = r1) = ((term126 A pwr x) = r1).
Proof. exact (eq_refl ((term126 A pwr x) = r1)). Qed.
Lemma lem1027683 {A : Type'} (pwr : type1423 A) (r1 : A) : (term127 A pwr r1) = (term127 A pwr r1).
Proof. exact (fun_ext (fun x : A => @lem1027682 A pwr x r1)). Qed.
Lemma lem1027684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027685 {A : Type'} (pwr : type1423 A) (r1 : A) : (term22 A pwr r1) = (term22 A pwr r1).
Proof. exact (MK_COMB (@lem1027684 A) (@lem1027683 A pwr r1)). Qed.
Lemma lem1027686 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027687 {A : Type'} (pwr : type1423 A) (r1 : A) : (term36 A pwr r1) = (term36 A pwr r1).
Proof. exact (MK_COMB (@lem1027686) (@lem1027685 A pwr r1)). Qed.
Lemma lem1027688 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1080 A add r1 r0 mul y x p q pwr) = (term1080 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027687 A pwr r1) (@lem1027681 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027689 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) (z : A) : ((term128 A mul x add y z) = (term129 A add y mul x z)) = ((term128 A mul x add y z) = (term129 A add y mul x z)).
Proof. exact (eq_refl ((term128 A mul x add y z) = (term129 A add y mul x z))). Qed.
Lemma lem1027690 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term130 A add y mul x) = (term130 A add y mul x).
Proof. exact (fun_ext (fun z : A => @lem1027689 A add y mul x z)). Qed.
Lemma lem1027691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027692 {A : Type'} (add : type1400 A) (y : A) (mul : type1400 A) (x : A) : (term131 A add y mul x) = (term131 A add y mul x).
Proof. exact (MK_COMB (@lem1027691 A) (@lem1027690 A add y mul x)). Qed.
Lemma lem1027693 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term132 A add mul x) = (term132 A add mul x).
Proof. exact (fun_ext (fun y : A => @lem1027692 A add y mul x)). Qed.
Lemma lem1027694 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027695 {A : Type'} (add : type1400 A) (mul : type1400 A) (x : A) : (term133 A add mul x) = (term133 A add mul x).
Proof. exact (MK_COMB (@lem1027694 A) (@lem1027693 A add mul x)). Qed.
Lemma lem1027696 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term134 A add mul) = (term134 A add mul).
Proof. exact (fun_ext (fun x : A => @lem1027695 A add mul x)). Qed.
Lemma lem1027697 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027698 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term20 A add mul) = (term20 A add mul).
Proof. exact (MK_COMB (@lem1027697 A) (@lem1027696 A add mul)). Qed.
Lemma lem1027699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027700 {A : Type'} (add : type1400 A) (mul : type1400 A) : (term39 A add mul) = (term39 A add mul).
Proof. exact (MK_COMB (@lem1027699) (@lem1027698 A add mul)). Qed.
Lemma lem1027701 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1082 A add r1 r0 mul y x p q pwr) = (term1082 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027700 A add mul) (@lem1027688 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027702 {A : Type'} (mul : type1400 A) (x : A) (r0 : A) : ((mul r0 x) = r0) = ((mul r0 x) = r0).
Proof. exact (eq_refl ((mul r0 x) = r0)). Qed.
Lemma lem1027703 {A : Type'} (mul : type1400 A) (r0 : A) : (term135 A mul r0) = (term135 A mul r0).
Proof. exact (fun_ext (fun x : A => @lem1027702 A mul x r0)). Qed.
Lemma lem1027704 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027705 {A : Type'} (mul : type1400 A) (r0 : A) : (term18 A mul r0) = (term18 A mul r0).
Proof. exact (MK_COMB (@lem1027704 A) (@lem1027703 A mul r0)). Qed.
Lemma lem1027706 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027707 {A : Type'} (mul : type1400 A) (r0 : A) : (term42 A mul r0) = (term42 A mul r0).
Proof. exact (MK_COMB (@lem1027706) (@lem1027705 A mul r0)). Qed.
Lemma lem1027708 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1084 A add r1 r0 mul y x p q pwr) = (term1084 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027707 A mul r0) (@lem1027701 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027709 {A : Type'} (mul : type1400 A) (r1 : A) (x : A) : ((mul r1 x) = x) = ((mul r1 x) = x).
Proof. exact (eq_refl ((mul r1 x) = x)). Qed.
Lemma lem1027710 {A : Type'} (mul : type1400 A) (r1 : A) : (term136 A mul r1) = (term136 A mul r1).
Proof. exact (fun_ext (fun x : A => @lem1027709 A mul r1 x)). Qed.
Lemma lem1027711 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027712 {A : Type'} (mul : type1400 A) (r1 : A) : (term13 A mul r1) = (term13 A mul r1).
Proof. exact (MK_COMB (@lem1027711 A) (@lem1027710 A mul r1)). Qed.
Lemma lem1027713 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027714 {A : Type'} (mul : type1400 A) (r1 : A) : (term45 A mul r1) = (term45 A mul r1).
Proof. exact (MK_COMB (@lem1027713) (@lem1027712 A mul r1)). Qed.
Lemma lem1027715 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1086 A add r1 r0 mul y x p q pwr) = (term1086 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027714 A mul r1) (@lem1027708 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027716 {A : Type'} (add : type1400 A) (r0 : A) (x : A) : ((add r0 x) = x) = ((add r0 x) = x).
Proof. exact (eq_refl ((add r0 x) = x)). Qed.
Lemma lem1027717 {A : Type'} (add : type1400 A) (r0 : A) : (term136 A add r0) = (term136 A add r0).
Proof. exact (fun_ext (fun x : A => @lem1027716 A add r0 x)). Qed.
Lemma lem1027718 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027719 {A : Type'} (add : type1400 A) (r0 : A) : (term13 A add r0) = (term13 A add r0).
Proof. exact (MK_COMB (@lem1027718 A) (@lem1027717 A add r0)). Qed.
Lemma lem1027720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1027721 {A : Type'} (add : type1400 A) (r0 : A) : (term45 A add r0) = (term45 A add r0).
Proof. exact (MK_COMB (@lem1027720) (@lem1027719 A add r0)). Qed.
Lemma lem1027722 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1087 A add r1 r0 mul y x p q pwr) = (term1087 A add r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027721 A add r0) (@lem1027715 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027723 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1089 A r1 r0 mul y x p q pwr) = (term1089 A r1 r0 mul y x p q pwr).
Proof. exact (fun_ext (fun add : type1400 A => @lem1027722 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027724 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1027725 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1091 A r1 r0 mul y x p q pwr) = (term1091 A r1 r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027724 A) (@lem1027723 A r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027726 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1093 A r0 mul y x p q pwr) = (term1093 A r0 mul y x p q pwr).
Proof. exact (fun_ext (fun r1 : A => @lem1027725 A r1 r0 mul y x p q pwr)). Qed.
Lemma lem1027727 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027728 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1095 A r0 mul y x p q pwr) = (term1095 A r0 mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027727 A) (@lem1027726 A r0 mul y x p q pwr)). Qed.
Lemma lem1027729 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1097 A mul y x p q pwr) = (term1097 A mul y x p q pwr).
Proof. exact (fun_ext (fun r0 : A => @lem1027728 A r0 mul y x p q pwr)). Qed.
Lemma lem1027730 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027731 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1099 A mul y x p q pwr) = (term1099 A mul y x p q pwr).
Proof. exact (MK_COMB (@lem1027730 A) (@lem1027729 A mul y x p q pwr)). Qed.
Lemma lem1027732 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1101 A y x p q pwr) = (term1101 A y x p q pwr).
Proof. exact (fun_ext (fun mul : type1400 A => @lem1027731 A mul y x p q pwr)). Qed.
Lemma lem1027733 {A : Type'} : (@all (A -> A -> A)) = (@all (A -> A -> A)).
Proof. exact (eq_refl (@all (A -> A -> A))). Qed.
Lemma lem1027734 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1103 A y x p q pwr) = (term1103 A y x p q pwr).
Proof. exact (MK_COMB (@lem1027733 A) (@lem1027732 A y x p q pwr)). Qed.
Lemma lem1027735 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1105 A x p q pwr) = (term1105 A x p q pwr).
Proof. exact (fun_ext (fun y : A => @lem1027734 A y x p q pwr)). Qed.
Lemma lem1027736 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027737 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1107 A x p q pwr) = (term1107 A x p q pwr).
Proof. exact (MK_COMB (@lem1027736 A) (@lem1027735 A x p q pwr)). Qed.
Lemma lem1027738 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) : (term1109 A p q pwr) = (term1109 A p q pwr).
Proof. exact (fun_ext (fun x : A => @lem1027737 A x p q pwr)). Qed.
Lemma lem1027739 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1027740 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) : (term1111 A p q pwr) = (term1111 A p q pwr).
Proof. exact (MK_COMB (@lem1027739 A) (@lem1027738 A p q pwr)). Qed.
Lemma lem1027741 {A : Type'} (q : nat) (pwr : type1423 A) : (term1113 A q pwr) = (term1113 A q pwr).
Proof. exact (fun_ext (fun p : nat => @lem1027740 A p q pwr)). Qed.
Lemma lem1027742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027743 {A : Type'} (q : nat) (pwr : type1423 A) : (term1115 A q pwr) = (term1115 A q pwr).
Proof. exact (MK_COMB (@lem1027742) (@lem1027741 A q pwr)). Qed.
Lemma lem1027744 {A : Type'} (pwr : type1423 A) : (term1117 A pwr) = (term1117 A pwr).
Proof. exact (fun_ext (fun q : nat => @lem1027743 A q pwr)). Qed.
Lemma lem1027745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1027746 {A : Type'} (pwr : type1423 A) : (term1119 A pwr) = (term1119 A pwr).
Proof. exact (MK_COMB (@lem1027745) (@lem1027744 A pwr)). Qed.
Lemma lem1027747 {A : Type'} : (term1121 A) = (term1121 A).
Proof. exact (fun_ext (fun pwr : type1423 A => @lem1027746 A pwr)). Qed.
Lemma lem1027748 {A : Type'} : (@all (A -> nat -> A)) = (@all (A -> nat -> A)).
Proof. exact (eq_refl (@all (A -> nat -> A))). Qed.
Lemma lem1027749 {A : Type'} : (term1123 A) = (term1123 A).
Proof. exact (MK_COMB (@lem1027748 A) (@lem1027747 A)). Qed.
Lemma lem1028088 {A : Type'} : (term1122 A) = (term1123 A).
Proof. exact (TRANS (@lem1027513 A) (@lem1027749 A)). Qed.
Lemma lem1028089 {A : Type'} : (term1123 A) = (term1122 A).
Proof. exact (SYM (@lem1028088 A)). Qed.
Lemma lem1028106 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term920 A mul pwr.
Proof. exact (h1). Qed.
Lemma lem1028107 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term984 A mul pwr.
Proof. exact (h1). Qed.
Lemma lem1028108 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1036 A mul y pwr x p q) : term1036 A mul y pwr x p q.
Proof. exact (h1). Qed.
Lemma lem1028109 {A : Type'} (pwr : type1423 A) (h1 : term1034 A pwr) : term1034 A pwr.
Proof. exact (h1). Qed.
Lemma lem1028423 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (x : A) (n : nat) : ((term970 A pwr x m n) = (term971 A mul m pwr x n)) = ((term970 A pwr x m n) = (term971 A mul m pwr x n)).
Proof. exact (eq_refl ((term970 A pwr x m n) = (term971 A mul m pwr x n))). Qed.
Lemma lem1028424 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term1131 A mul m pwr n) = (term1131 A mul m pwr n).
Proof. exact (fun_ext (fun x : A => @lem1028423 A mul m pwr x n)). Qed.
Lemma lem1028425 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1028426 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term929 A mul m pwr n) = (term929 A mul m pwr n).
Proof. exact (MK_COMB (@lem1028425 A) (@lem1028424 A mul m pwr n)). Qed.
Lemma lem1028427 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term923 A mul m pwr) = (term923 A mul m pwr).
Proof. exact (fun_ext (fun n : nat => @lem1028426 A mul m pwr n)). Qed.
Lemma lem1028428 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028429 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term946 A mul m pwr) = (term946 A mul m pwr).
Proof. exact (MK_COMB (@lem1028428) (@lem1028427 A mul m pwr)). Qed.
Lemma lem1028430 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1132 A mul pwr) = (term1132 A mul pwr).
Proof. exact (fun_ext (fun m : nat => @lem1028429 A mul m pwr)). Qed.
Lemma lem1028431 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028448 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term920 A mul pwr) = (term920 A mul pwr).
Proof. exact (MK_COMB (@lem1028431) (@lem1028430 A mul pwr)). Qed.
Lemma lem1028449 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term920 A mul pwr.
Proof. exact (EQ_MP (@lem1028448 A mul pwr) (@lem1028106 A mul pwr h1)). Qed.
Lemma lem1028450 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)) = ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)).
Proof. exact (eq_refl ((term993 A pwr mul x y n) = (term994 A mul x pwr y n))). Qed.
Lemma lem1028451 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term986 A mul x pwr y) = (term986 A mul x pwr y).
Proof. exact (fun_ext (fun n : nat => @lem1028450 A mul x pwr y n)). Qed.
Lemma lem1028452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028453 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1012 A mul x pwr y) = (term1012 A mul x pwr y).
Proof. exact (MK_COMB (@lem1028452) (@lem1028451 A mul x pwr y)). Qed.
Lemma lem1028454 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1129 A mul x pwr) = (term1129 A mul x pwr).
Proof. exact (fun_ext (fun y : A => @lem1028453 A mul x pwr y)). Qed.
Lemma lem1028455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1028456 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1033 A mul x pwr) = (term1033 A mul x pwr).
Proof. exact (MK_COMB (@lem1028455 A) (@lem1028454 A mul x pwr)). Qed.
Lemma lem1028457 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1130 A mul pwr) = (term1130 A mul pwr).
Proof. exact (fun_ext (fun x : A => @lem1028456 A mul x pwr)). Qed.
Lemma lem1028458 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1028475 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term984 A mul pwr) = (term984 A mul pwr).
Proof. exact (MK_COMB (@lem1028458 A) (@lem1028457 A mul pwr)). Qed.
Lemma lem1028476 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term984 A mul pwr.
Proof. exact (EQ_MP (@lem1028475 A mul pwr) (@lem1028107 A mul pwr h1)). Qed.
Lemma lem1028484 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1133 A mul y pwr x p q) = (term1134 A mul y pwr x p q).
Proof. exact (@lem17045 ((term993 A pwr mul x y q) = (term994 A mul x pwr y q)) ((term879 A pwr x p q) = (term880 A pwr x p q))). Qed.
Lemma lem1028486 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1135 A mul pwr x p q) = (term1135 A mul pwr x p q).
Proof. exact (eq_refl (term1135 A mul pwr x p q)). Qed.
Lemma lem1028487 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1136 A mul y pwr x p q) = (term1137 A mul y pwr x p q).
Proof. exact (MK_COMB (@lem1028486 A mul pwr x p q) (@lem1028484 A mul y pwr x p q)). Qed.
Lemma lem1028488 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1036 A mul y pwr x p q) = (term1136 A mul y pwr x p q).
Proof. exact (@lem17045 ((term971 A mul p pwr x q) = (term970 A pwr x p q)) (term883 A mul y pwr x p q)). Qed.
Lemma lem1028493 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1036 A mul y pwr x p q) = (term1137 A mul y pwr x p q).
Proof. exact (TRANS (@lem1028488 A mul y pwr x p q) (@lem1028487 A mul y pwr x p q)). Qed.
Lemma lem1028495 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : ((term879 A pwr x m n) = (term880 A pwr x m n)) = ((term879 A pwr x m n) = (term880 A pwr x m n)).
Proof. exact (eq_refl ((term879 A pwr x m n) = (term880 A pwr x m n))). Qed.
Lemma lem1028496 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1124 A pwr x m) = (term1124 A pwr x m).
Proof. exact (fun_ext (fun n : nat => @lem1028495 A pwr x m n)). Qed.
Lemma lem1028497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028498 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1125 A pwr x m) = (term1125 A pwr x m).
Proof. exact (MK_COMB (@lem1028497) (@lem1028496 A pwr x m)). Qed.
Lemma lem1028499 {A : Type'} (pwr : type1423 A) (x : A) : (term1126 A pwr x) = (term1126 A pwr x).
Proof. exact (fun_ext (fun m : nat => @lem1028498 A pwr x m)). Qed.
Lemma lem1028500 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028501 {A : Type'} (pwr : type1423 A) (x : A) : (term1127 A pwr x) = (term1127 A pwr x).
Proof. exact (MK_COMB (@lem1028500) (@lem1028499 A pwr x)). Qed.
Lemma lem1028502 {A : Type'} (pwr : type1423 A) : (term1128 A pwr) = (term1128 A pwr).
Proof. exact (fun_ext (fun x : A => @lem1028501 A pwr x)). Qed.
Lemma lem1028503 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1028520 {A : Type'} (pwr : type1423 A) : (term1034 A pwr) = (term1034 A pwr).
Proof. exact (MK_COMB (@lem1028503 A) (@lem1028502 A pwr)). Qed.
Lemma lem1028521 {A : Type'} (pwr : type1423 A) (h1 : term1034 A pwr) : term1034 A pwr.
Proof. exact (EQ_MP (@lem1028520 A pwr) (@lem1028109 A pwr h1)). Qed.
Lemma lem1028899 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (x : A) (n : nat) : ((term970 A pwr x m n) = (term971 A mul m pwr x n)) = ((term970 A pwr x m n) = (term971 A mul m pwr x n)).
Proof. exact (eq_refl ((term970 A pwr x m n) = (term971 A mul m pwr x n))). Qed.
Lemma lem1028900 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term1131 A mul m pwr n) = (term1131 A mul m pwr n).
Proof. exact (fun_ext (fun x : A => @lem1028899 A mul m pwr x n)). Qed.
Lemma lem1028901 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1028902 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term929 A mul m pwr n) = (term929 A mul m pwr n).
Proof. exact (MK_COMB (@lem1028901 A) (@lem1028900 A mul m pwr n)). Qed.
Lemma lem1028903 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term923 A mul m pwr) = (term923 A mul m pwr).
Proof. exact (fun_ext (fun n : nat => @lem1028902 A mul m pwr n)). Qed.
Lemma lem1028904 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028905 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term946 A mul m pwr) = (term946 A mul m pwr).
Proof. exact (MK_COMB (@lem1028904) (@lem1028903 A mul m pwr)). Qed.
Lemma lem1028906 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1132 A mul pwr) = (term1132 A mul pwr).
Proof. exact (fun_ext (fun m : nat => @lem1028905 A mul m pwr)). Qed.
Lemma lem1028907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028908 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term920 A mul pwr) = (term920 A mul pwr).
Proof. exact (MK_COMB (@lem1028907) (@lem1028906 A mul pwr)). Qed.
Lemma lem1028909 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term920 A mul pwr.
Proof. exact (EQ_MP (@lem1028908 A mul pwr) (@lem1028449 A mul pwr h1)). Qed.
Lemma lem1028934 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)) = ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)).
Proof. exact (eq_refl ((term993 A pwr mul x y n) = (term994 A mul x pwr y n))). Qed.
Lemma lem1028935 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term986 A mul x pwr y) = (term986 A mul x pwr y).
Proof. exact (fun_ext (fun n : nat => @lem1028934 A mul x pwr y n)). Qed.
Lemma lem1028936 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1028937 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1012 A mul x pwr y) = (term1012 A mul x pwr y).
Proof. exact (MK_COMB (@lem1028936) (@lem1028935 A mul x pwr y)). Qed.
Lemma lem1028938 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1129 A mul x pwr) = (term1129 A mul x pwr).
Proof. exact (fun_ext (fun y : A => @lem1028937 A mul x pwr y)). Qed.
Lemma lem1028939 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1028940 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1033 A mul x pwr) = (term1033 A mul x pwr).
Proof. exact (MK_COMB (@lem1028939 A) (@lem1028938 A mul x pwr)). Qed.
Lemma lem1028941 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1130 A mul pwr) = (term1130 A mul pwr).
Proof. exact (fun_ext (fun x : A => @lem1028940 A mul x pwr)). Qed.
Lemma lem1028942 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1028943 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term984 A mul pwr) = (term984 A mul pwr).
Proof. exact (MK_COMB (@lem1028942 A) (@lem1028941 A mul pwr)). Qed.
Lemma lem1028944 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term984 A mul pwr.
Proof. exact (EQ_MP (@lem1028943 A mul pwr) (@lem1028476 A mul pwr h1)). Qed.
Lemma lem1029028 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1036 A mul y pwr x p q) : term1137 A mul y pwr x p q.
Proof. exact (EQ_MP (@lem1028493 A mul y pwr x p q) (@lem1028108 A mul y pwr x p q h1)). Qed.
Lemma lem1029049 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : ((term879 A pwr x m n) = (term880 A pwr x m n)) = ((term879 A pwr x m n) = (term880 A pwr x m n)).
Proof. exact (eq_refl ((term879 A pwr x m n) = (term880 A pwr x m n))). Qed.
Lemma lem1029050 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1124 A pwr x m) = (term1124 A pwr x m).
Proof. exact (fun_ext (fun n : nat => @lem1029049 A pwr x m n)). Qed.
Lemma lem1029051 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1029052 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1125 A pwr x m) = (term1125 A pwr x m).
Proof. exact (MK_COMB (@lem1029051) (@lem1029050 A pwr x m)). Qed.
Lemma lem1029053 {A : Type'} (pwr : type1423 A) (x : A) : (term1126 A pwr x) = (term1126 A pwr x).
Proof. exact (fun_ext (fun m : nat => @lem1029052 A pwr x m)). Qed.
Lemma lem1029054 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1029055 {A : Type'} (pwr : type1423 A) (x : A) : (term1127 A pwr x) = (term1127 A pwr x).
Proof. exact (MK_COMB (@lem1029054) (@lem1029053 A pwr x)). Qed.
Lemma lem1029056 {A : Type'} (pwr : type1423 A) : (term1128 A pwr) = (term1128 A pwr).
Proof. exact (fun_ext (fun x : A => @lem1029055 A pwr x)). Qed.
Lemma lem1029057 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1029058 {A : Type'} (pwr : type1423 A) : (term1034 A pwr) = (term1034 A pwr).
Proof. exact (MK_COMB (@lem1029057 A) (@lem1029056 A pwr)). Qed.
Lemma lem1029059 {A : Type'} (pwr : type1423 A) (h1 : term1034 A pwr) : term1034 A pwr.
Proof. exact (EQ_MP (@lem1029058 A pwr) (@lem1028521 A pwr h1)). Qed.
Lemma lem1029061 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1134 A mul y pwr x p q) : term1134 A mul y pwr x p q.
Proof. exact (h1). Qed.
Lemma lem1029222 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (x : A) (n : nat) : ((term970 A pwr x m n) = (term971 A mul m pwr x n)) = ((term970 A pwr x m n) = (term971 A mul m pwr x n)).
Proof. exact (eq_refl ((term970 A pwr x m n) = (term971 A mul m pwr x n))). Qed.
Lemma lem1029223 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term1131 A mul m pwr n) = (term1131 A mul m pwr n).
Proof. exact (fun_ext (fun x : A => @lem1029222 A mul m pwr x n)). Qed.
Lemma lem1029224 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1029225 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term929 A mul m pwr n) = (term929 A mul m pwr n).
Proof. exact (MK_COMB (@lem1029224 A) (@lem1029223 A mul m pwr n)). Qed.
Lemma lem1029226 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term923 A mul m pwr) = (term923 A mul m pwr).
Proof. exact (fun_ext (fun n : nat => @lem1029225 A mul m pwr n)). Qed.
Lemma lem1029227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1029228 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term946 A mul m pwr) = (term946 A mul m pwr).
Proof. exact (MK_COMB (@lem1029227) (@lem1029226 A mul m pwr)). Qed.
Lemma lem1029229 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1132 A mul pwr) = (term1132 A mul pwr).
Proof. exact (fun_ext (fun m : nat => @lem1029228 A mul m pwr)). Qed.
Lemma lem1029230 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1029232 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term920 A mul pwr) = (term920 A mul pwr).
Proof. exact (MK_COMB (@lem1029230) (@lem1029229 A mul pwr)). Qed.
Lemma lem1029233 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term920 A mul pwr.
Proof. exact (EQ_MP (@lem1029232 A mul pwr) (@lem1028909 A mul pwr h1)). Qed.
Lemma lem1029263 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1138 A mul pwr x p q) : term1138 A mul pwr x p q.
Proof. exact (h1). Qed.
Lemma lem1029435 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (n : nat) : ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)) = ((term993 A pwr mul x y n) = (term994 A mul x pwr y n)).
Proof. exact (eq_refl ((term993 A pwr mul x y n) = (term994 A mul x pwr y n))). Qed.
Lemma lem1029436 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term986 A mul x pwr y) = (term986 A mul x pwr y).
Proof. exact (fun_ext (fun n : nat => @lem1029435 A mul x pwr y n)). Qed.
Lemma lem1029437 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1029438 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) : (term1012 A mul x pwr y) = (term1012 A mul x pwr y).
Proof. exact (MK_COMB (@lem1029437) (@lem1029436 A mul x pwr y)). Qed.
Lemma lem1029439 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1129 A mul x pwr) = (term1129 A mul x pwr).
Proof. exact (fun_ext (fun y : A => @lem1029438 A mul x pwr y)). Qed.
Lemma lem1029440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1029441 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) : (term1033 A mul x pwr) = (term1033 A mul x pwr).
Proof. exact (MK_COMB (@lem1029440 A) (@lem1029439 A mul x pwr)). Qed.
Lemma lem1029442 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term1130 A mul pwr) = (term1130 A mul pwr).
Proof. exact (fun_ext (fun x : A => @lem1029441 A mul x pwr)). Qed.
Lemma lem1029443 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1029445 {A : Type'} (mul : type1400 A) (pwr : type1423 A) : (term984 A mul pwr) = (term984 A mul pwr).
Proof. exact (MK_COMB (@lem1029443 A) (@lem1029442 A mul pwr)). Qed.
Lemma lem1029446 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term984 A mul pwr.
Proof. exact (EQ_MP (@lem1029445 A mul pwr) (@lem1028944 A mul pwr h1)). Qed.
Lemma lem1029463 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term1139 A mul x pwr y q) : term1139 A mul x pwr y q.
Proof. exact (h1). Qed.
Lemma lem1029648 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : ((term879 A pwr x m n) = (term880 A pwr x m n)) = ((term879 A pwr x m n) = (term880 A pwr x m n)).
Proof. exact (eq_refl ((term879 A pwr x m n) = (term880 A pwr x m n))). Qed.
Lemma lem1029649 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1124 A pwr x m) = (term1124 A pwr x m).
Proof. exact (fun_ext (fun n : nat => @lem1029648 A pwr x m n)). Qed.
Lemma lem1029650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1029651 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1125 A pwr x m) = (term1125 A pwr x m).
Proof. exact (MK_COMB (@lem1029650) (@lem1029649 A pwr x m)). Qed.
Lemma lem1029652 {A : Type'} (pwr : type1423 A) (x : A) : (term1126 A pwr x) = (term1126 A pwr x).
Proof. exact (fun_ext (fun m : nat => @lem1029651 A pwr x m)). Qed.
Lemma lem1029653 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1029654 {A : Type'} (pwr : type1423 A) (x : A) : (term1127 A pwr x) = (term1127 A pwr x).
Proof. exact (MK_COMB (@lem1029653) (@lem1029652 A pwr x)). Qed.
Lemma lem1029655 {A : Type'} (pwr : type1423 A) : (term1128 A pwr) = (term1128 A pwr).
Proof. exact (fun_ext (fun x : A => @lem1029654 A pwr x)). Qed.
Lemma lem1029656 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1029658 {A : Type'} (pwr : type1423 A) : (term1034 A pwr) = (term1034 A pwr).
Proof. exact (MK_COMB (@lem1029656 A) (@lem1029655 A pwr)). Qed.
Lemma lem1029659 {A : Type'} (pwr : type1423 A) (h1 : term1034 A pwr) : term1034 A pwr.
Proof. exact (EQ_MP (@lem1029658 A pwr) (@lem1029059 A pwr h1)). Qed.
Lemma lem1029663 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1140 A pwr x p q) : term1140 A pwr x p q.
Proof. exact (h1). Qed.
Lemma lem1029757 {A : Type'} (_16923 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term1141 A mul pwr _16923.
Proof. exact (@lem1029233 A mul pwr h1 _16923). Qed.
Lemma lem1029758 {A : Type'} (mul : type1400 A) (_16923 : nat) (pwr : type1423 A) : (term1141 A mul pwr _16923) = (term946 A mul _16923 pwr).
Proof. exact (eq_refl (term1141 A mul pwr _16923)). Qed.
Lemma lem1029759 {A : Type'} (_16923 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term946 A mul _16923 pwr.
Proof. exact (EQ_MP (@lem1029758 A mul _16923 pwr) (@lem1029757 A _16923 mul pwr h1)). Qed.
Lemma lem1029760 {A : Type'} (_16923 : nat) (_16924 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term928 A mul _16923 pwr _16924.
Proof. exact (@lem1029759 A _16923 mul pwr h1 _16924). Qed.
Lemma lem1029761 {A : Type'} (mul : type1400 A) (_16923 : nat) (pwr : type1423 A) (_16924 : nat) : (term928 A mul _16923 pwr _16924) = (term929 A mul _16923 pwr _16924).
Proof. exact (eq_refl (term928 A mul _16923 pwr _16924)). Qed.
Lemma lem1029762 {A : Type'} (_16923 : nat) (_16924 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term929 A mul _16923 pwr _16924.
Proof. exact (EQ_MP (@lem1029761 A mul _16923 pwr _16924) (@lem1029760 A _16923 _16924 mul pwr h1)). Qed.
Lemma lem1029763 {A : Type'} (_16923 : nat) (_16924 : nat) (_16925 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term969 A mul _16923 pwr _16924 _16925.
Proof. exact (@lem1029762 A _16923 _16924 mul pwr h1 _16925). Qed.
Lemma lem1029764 {A : Type'} (mul : type1400 A) (_16923 : nat) (pwr : type1423 A) (_16925 : A) (_16924 : nat) : (term969 A mul _16923 pwr _16924 _16925) = ((term970 A pwr _16925 _16923 _16924) = (term971 A mul _16923 pwr _16925 _16924)).
Proof. exact (eq_refl (term969 A mul _16923 pwr _16924 _16925)). Qed.
Lemma lem1029886 {A : Type'} (_16966 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term1142 A mul pwr _16966.
Proof. exact (@lem1029446 A mul pwr h1 _16966). Qed.
Lemma lem1029887 {A : Type'} (mul : type1400 A) (_16966 : A) (pwr : type1423 A) : (term1142 A mul pwr _16966) = (term1033 A mul _16966 pwr).
Proof. exact (eq_refl (term1142 A mul pwr _16966)). Qed.
Lemma lem1029888 {A : Type'} (_16966 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term1033 A mul _16966 pwr.
Proof. exact (EQ_MP (@lem1029887 A mul _16966 pwr) (@lem1029886 A _16966 mul pwr h1)). Qed.
Lemma lem1029889 {A : Type'} (_16966 : A) (_16967 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term1143 A mul _16966 pwr _16967.
Proof. exact (@lem1029888 A _16966 mul pwr h1 _16967). Qed.
Lemma lem1029890 {A : Type'} (mul : type1400 A) (_16966 : A) (pwr : type1423 A) (_16967 : A) : (term1143 A mul _16966 pwr _16967) = (term1012 A mul _16966 pwr _16967).
Proof. exact (eq_refl (term1143 A mul _16966 pwr _16967)). Qed.
Lemma lem1029891 {A : Type'} (_16966 : A) (_16967 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term1012 A mul _16966 pwr _16967.
Proof. exact (EQ_MP (@lem1029890 A mul _16966 pwr _16967) (@lem1029889 A _16966 _16967 mul pwr h1)). Qed.
Lemma lem1029892 {A : Type'} (_16966 : A) (_16967 : A) (_16968 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term992 A mul _16966 pwr _16967 _16968.
Proof. exact (@lem1029891 A _16966 _16967 mul pwr h1 _16968). Qed.
Lemma lem1029893 {A : Type'} (mul : type1400 A) (_16966 : A) (pwr : type1423 A) (_16967 : A) (_16968 : nat) : (term992 A mul _16966 pwr _16967 _16968) = ((term993 A pwr mul _16966 _16967 _16968) = (term994 A mul _16966 pwr _16967 _16968)).
Proof. exact (eq_refl (term992 A mul _16966 pwr _16967 _16968)). Qed.
Lemma lem1030015 {A : Type'} (_17009 : A) (pwr : type1423 A) (h1 : term1034 A pwr) : term1144 A pwr _17009.
Proof. exact (@lem1029659 A pwr h1 _17009). Qed.
Lemma lem1030016 {A : Type'} (pwr : type1423 A) (_17009 : A) : (term1144 A pwr _17009) = (term1127 A pwr _17009).
Proof. exact (eq_refl (term1144 A pwr _17009)). Qed.
Lemma lem1030017 {A : Type'} (_17009 : A) (pwr : type1423 A) (h1 : term1034 A pwr) : term1127 A pwr _17009.
Proof. exact (EQ_MP (@lem1030016 A pwr _17009) (@lem1030015 A _17009 pwr h1)). Qed.
Lemma lem1030018 {A : Type'} (_17009 : A) (_17010 : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : term1145 A pwr _17009 _17010.
Proof. exact (@lem1030017 A _17009 pwr h1 _17010). Qed.
Lemma lem1030019 {A : Type'} (pwr : type1423 A) (_17009 : A) (_17010 : nat) : (term1145 A pwr _17009 _17010) = (term1125 A pwr _17009 _17010).
Proof. exact (eq_refl (term1145 A pwr _17009 _17010)). Qed.
Lemma lem1030020 {A : Type'} (_17009 : A) (_17010 : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : term1125 A pwr _17009 _17010.
Proof. exact (EQ_MP (@lem1030019 A pwr _17009 _17010) (@lem1030018 A _17009 _17010 pwr h1)). Qed.
Lemma lem1030021 {A : Type'} (_17009 : A) (_17010 : nat) (_17011 : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : term1146 A pwr _17009 _17010 _17011.
Proof. exact (@lem1030020 A _17009 _17010 pwr h1 _17011). Qed.
Lemma lem1030022 {A : Type'} (pwr : type1423 A) (_17009 : A) (_17010 : nat) (_17011 : nat) : (term1146 A pwr _17009 _17010 _17011) = ((term879 A pwr _17009 _17010 _17011) = (term880 A pwr _17009 _17010 _17011)).
Proof. exact (eq_refl (term1146 A pwr _17009 _17010 _17011)). Qed.
Lemma lem1030063 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1138 A mul pwr x p q) : term1138 A mul pwr x p q.
Proof. exact (h1). Qed.
Lemma lem1030103 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term1139 A mul x pwr y q) : term1139 A mul x pwr y q.
Proof. exact (h1). Qed.
Lemma lem1030143 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1140 A pwr x p q) : term1140 A pwr x p q.
Proof. exact (h1). Qed.
Lemma lem1030236 {A : Type'} (x : A) (y : A) (z : A) : term707 A x y z.
Proof. exact (@lem21385 A x y z). Qed.
Lemma lem1030240 {A : Type'} (_16923 : nat) (_16925 : A) (_16924 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term970 A pwr _16925 _16923 _16924) = (term971 A mul _16923 pwr _16925 _16924).
Proof. exact (EQ_MP (@lem1029764 A mul _16923 pwr _16925 _16924) (@lem1029763 A _16923 _16924 _16925 mul pwr h1)). Qed.
Lemma lem1030241 {A : Type'} (_16923 : nat) (_16925 : A) (_16924 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term970 A pwr _16925 _16923 _16924) = (term971 A mul _16923 pwr _16925 _16924).
Proof. exact (@lem1030240 A _16923 _16925 _16924 mul pwr h1). Qed.
Lemma lem1030242 {A : Type'} (p : nat) (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term970 A pwr x p q) = (term971 A mul p pwr x q).
Proof. exact (@lem1030241 A p x q mul pwr h1). Qed.
Lemma lem1030243 {A : Type'} (p : nat) (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term1147 A mul p pwr x q.
Proof. exact (fun h0 : term1148 A mul p pwr x q => @lem1030242 A p x q mul pwr h1). Qed.
Lemma lem1030245 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030246 {A : Type'} (mul : type1400 A) (p : nat) (pwr : type1423 A) (x : A) (q : nat) : (term1147 A mul p pwr x q) = ((term970 A pwr x p q) = (term971 A mul p pwr x q)).
Proof. exact (@lem1030245 ((term970 A pwr x p q) = (term971 A mul p pwr x q))). Qed.
Lemma lem1030247 {A : Type'} (p : nat) (x : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term970 A pwr x p q) = (term971 A mul p pwr x q).
Proof. exact (EQ_MP (@lem1030246 A mul p pwr x q) (@lem1030243 A p x q mul pwr h1)). Qed.
Lemma lem1030249 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1030250 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1030249 A x). Qed.
Lemma lem1030251 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term970 A pwr x p q) = (term970 A pwr x p q).
Proof. exact (@lem1030250 A (term970 A pwr x p q)). Qed.
Lemma lem1030252 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : term1149 A pwr x p q.
Proof. exact (fun h0 : term1150 A pwr x p q => @lem1030251 A pwr x p q). Qed.
Lemma lem1030254 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030255 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1149 A pwr x p q) = ((term970 A pwr x p q) = (term970 A pwr x p q)).
Proof. exact (@lem1030254 ((term970 A pwr x p q) = (term970 A pwr x p q))). Qed.
Lemma lem1030256 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term970 A pwr x p q) = (term970 A pwr x p q).
Proof. exact (EQ_MP (@lem1030255 A pwr x p q) (@lem1030252 A pwr x p q)). Qed.
Lemma lem1030274 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1030275 {A : Type'} (y : A) (x : A) (z : A) : (term712 A x y z) = (term713 A y x z).
Proof. exact (@lem1030274 (y = z) (term714 A x z)). Qed.
Lemma lem1030285 {A : Type'} (x : A) (y : A) : (term715 A x y) = (term715 A x y).
Proof. exact (eq_refl (term715 A x y)). Qed.
Lemma lem1030286 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term716 A y x z).
Proof. exact (MK_COMB (@lem1030285 A x y) (@lem1030275 A y x z)). Qed.
Lemma lem1030290 (q : Prop) (p : Prop) (r : Prop) : (term717 p q r) = (term717 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1030291 {A : Type'} (y : A) (x : A) (z : A) : (term716 A y x z) = (term718 A y x z).
Proof. exact (@lem1030290 (y = z) (term714 A x y) (term714 A x z)). Qed.
Lemma lem1030313 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (TRANS (@lem1030286 A y x z) (@lem1030291 A y x z)). Qed.
Lemma lem1030314 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1030315 {A : Type'} (y : A) (x : A) (z : A) : (term719 A x y z) = (term720 A y x z).
Proof. exact (MK_COMB (@lem1030314) (@lem1030313 A y x z)). Qed.
Lemma lem1030337 {A : Type'} (y : A) (x : A) (z : A) : (term718 A y x z) = (term718 A y x z).
Proof. exact (eq_refl (term718 A y x z)). Qed.
Lemma lem1030338 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = ((term718 A y x z) = (term718 A y x z)).
Proof. exact (MK_COMB (@lem1030315 A y x z) (@lem1030337 A y x z)). Qed.
Lemma lem1030340 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1030341 (x : Prop) : (x = x) = True.
Proof. exact (@lem1030340 Prop x). Qed.
Lemma lem1030342 {A : Type'} (y : A) (x : A) (z : A) : ((term718 A y x z) = (term718 A y x z)) = True.
Proof. exact (@lem1030341 (term718 A y x z)). Qed.
Lemma lem1030343 {A : Type'} (y : A) (x : A) (z : A) : ((term707 A x y z) = (term718 A y x z)) = True.
Proof. exact (TRANS (@lem1030338 A y x z) (@lem1030342 A y x z)). Qed.
Lemma lem1030344 {A : Type'} (y : A) (x : A) (z : A) : True = ((term707 A x y z) = (term718 A y x z)).
Proof. exact (SYM (@lem1030343 A y x z)). Qed.
Lemma lem1030345 {A : Type'} (y : A) (x : A) (z : A) : (term707 A x y z) = (term718 A y x z).
Proof. exact (EQ_MP (@lem1030344 A y x z) (@lem0)). Qed.
Lemma lem1030346 {A : Type'} (y : A) (x : A) (z : A) : term718 A y x z.
Proof. exact (EQ_MP (@lem1030345 A y x z) (@lem1030236 A x y z)). Qed.
Lemma lem1030348 (b : Prop) (a : Prop) : (a \/ b) = (term721 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1030349 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term722 A x y z).
Proof. exact (@lem1030348 (term723 A y x z) (y = z)). Qed.
Lemma lem1030351 (a : Prop) (b : Prop) : (term724 a b) = (term725 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1030352 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term727 A y x z).
Proof. exact (@lem1030351 (term714 A x y) (term714 A x z)). Qed.
Lemma lem1030354 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1030355 {A : Type'} (x : A) (y : A) : (term728 A x y) = (x = y).
Proof. exact (@lem1030354 (x = y)). Qed.
Lemma lem1030356 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1030357 {A : Type'} (x : A) (y : A) : (term729 A x y) = (term730 A x y).
Proof. exact (MK_COMB (@lem1030356) (@lem1030355 A x y)). Qed.
Lemma lem1030359 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1030360 {A : Type'} (x : A) (z : A) : (term728 A x z) = (x = z).
Proof. exact (@lem1030359 (x = z)). Qed.
Lemma lem1030361 {A : Type'} (y : A) (x : A) (z : A) : (term727 A y x z) = (term731 A y x z).
Proof. exact (MK_COMB (@lem1030357 A x y) (@lem1030360 A x z)). Qed.
Lemma lem1030362 {A : Type'} (y : A) (x : A) (z : A) : (term726 A y x z) = (term731 A y x z).
Proof. exact (TRANS (@lem1030352 A y x z) (@lem1030361 A y x z)). Qed.
Lemma lem1030363 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1030364 {A : Type'} (y : A) (x : A) (z : A) : (term732 A y x z) = (term733 A y x z).
Proof. exact (MK_COMB (@lem1030363) (@lem1030362 A y x z)). Qed.
Lemma lem1030365 {A : Type'} (y : A) (z : A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1030366 {A : Type'} (x : A) (y : A) (z : A) : (term722 A x y z) = (term734 A x y z).
Proof. exact (MK_COMB (@lem1030364 A y x z) (@lem1030365 A y z)). Qed.
Lemma lem1030367 {A : Type'} (x : A) (y : A) (z : A) : (term718 A y x z) = (term734 A x y z).
Proof. exact (TRANS (@lem1030349 A x y z) (@lem1030366 A x y z)). Qed.
Lemma lem1030369 {A : Type'} (x : A) (p : nat) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term1151 A mul pwr x p q.
Proof. exact (conj (@lem1030247 A p x q mul pwr h1) (@lem1030256 A pwr x p q)). Qed.
Lemma lem1030371 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (EQ_MP (@lem1030367 A x y z) (@lem1030346 A y x z)). Qed.
Lemma lem1030372 {A : Type'} (x : A) (y : A) (z : A) : term734 A x y z.
Proof. exact (@lem1030371 A x y z). Qed.
Lemma lem1030373 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : term1152 A mul pwr x p q.
Proof. exact (@lem1030372 A (term970 A pwr x p q) (term971 A mul p pwr x q) (term970 A pwr x p q)). Qed.
Lemma lem1030376 {A : Type'} (x : A) (p : nat) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term971 A mul p pwr x q) = (term970 A pwr x p q).
Proof. exact (@lem1030373 A mul pwr x p q (@lem1030369 A x p q mul pwr h1)). Qed.
Lemma lem1030377 {A : Type'} (x : A) (p : nat) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term971 A mul p pwr x q) = (term970 A pwr x p q).
Proof. exact (@lem1030376 A x p q mul pwr h1). Qed.
Lemma lem1030378 {A : Type'} (x : A) (p : nat) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term1153 A mul pwr x p q.
Proof. exact (fun h0 : term1138 A mul pwr x p q => @lem1030377 A x p q mul pwr h1). Qed.
Lemma lem1030380 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030381 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1153 A mul pwr x p q) = ((term971 A mul p pwr x q) = (term970 A pwr x p q)).
Proof. exact (@lem1030380 ((term971 A mul p pwr x q) = (term970 A pwr x p q))). Qed.
Lemma lem1030382 {A : Type'} (x : A) (p : nat) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term971 A mul p pwr x q) = (term970 A pwr x p q).
Proof. exact (EQ_MP (@lem1030381 A mul pwr x p q) (@lem1030378 A x p q mul pwr h1)). Qed.
Lemma lem1030385 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1030387 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1138 A mul pwr x p q) = (term1154 A mul pwr x p q).
Proof. exact (@lem1030385 ((term971 A mul p pwr x q) = (term970 A pwr x p q))). Qed.
Lemma lem1030390 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1138 A mul pwr x p q) : term1154 A mul pwr x p q.
Proof. exact (EQ_MP (@lem1030387 A mul pwr x p q) (@lem1030063 A mul pwr x p q h1)). Qed.
Lemma lem1030393 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : False.
Proof. exact (@lem1030390 A mul pwr x p q h2 (@lem1030382 A x p q mul pwr h1)). Qed.
Lemma lem1030394 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : term706.
Proof. exact (fun h0 : ~ False => @lem1030393 A mul pwr x p q h1 h2). Qed.
Lemma lem1030396 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030397 : term706 = False.
Proof. exact (@lem1030396 False). Qed.
Lemma lem1030398 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030397) (@lem1030394 A mul pwr x p q h1 h2)). Qed.
Lemma lem1030495 {A : Type'} (_16966 : A) (_16967 : A) (_16968 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : (term993 A pwr mul _16966 _16967 _16968) = (term994 A mul _16966 pwr _16967 _16968).
Proof. exact (EQ_MP (@lem1029893 A mul _16966 pwr _16967 _16968) (@lem1029892 A _16966 _16967 _16968 mul pwr h1)). Qed.
Lemma lem1030496 {A : Type'} (_16966 : A) (_16967 : A) (_16968 : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : (term993 A pwr mul _16966 _16967 _16968) = (term994 A mul _16966 pwr _16967 _16968).
Proof. exact (@lem1030495 A _16966 _16967 _16968 mul pwr h1). Qed.
Lemma lem1030497 {A : Type'} (x : A) (y : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : (term993 A pwr mul x y q) = (term994 A mul x pwr y q).
Proof. exact (@lem1030496 A x y q mul pwr h1). Qed.
Lemma lem1030498 {A : Type'} (x : A) (y : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : term1155 A mul x pwr y q.
Proof. exact (fun h0 : term1139 A mul x pwr y q => @lem1030497 A x y q mul pwr h1). Qed.
Lemma lem1030500 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030501 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) : (term1155 A mul x pwr y q) = ((term993 A pwr mul x y q) = (term994 A mul x pwr y q)).
Proof. exact (@lem1030500 ((term993 A pwr mul x y q) = (term994 A mul x pwr y q))). Qed.
Lemma lem1030502 {A : Type'} (x : A) (y : A) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) : (term993 A pwr mul x y q) = (term994 A mul x pwr y q).
Proof. exact (EQ_MP (@lem1030501 A mul x pwr y q) (@lem1030498 A x y q mul pwr h1)). Qed.
Lemma lem1030505 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1030507 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) : (term1139 A mul x pwr y q) = (term1156 A mul x pwr y q).
Proof. exact (@lem1030505 ((term993 A pwr mul x y q) = (term994 A mul x pwr y q))). Qed.
Lemma lem1030510 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term1139 A mul x pwr y q) : term1156 A mul x pwr y q.
Proof. exact (EQ_MP (@lem1030507 A mul x pwr y q) (@lem1030103 A mul x pwr y q h1)). Qed.
Lemma lem1030513 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : False.
Proof. exact (@lem1030510 A mul x pwr y q h2 (@lem1030502 A x y q mul pwr h1)). Qed.
Lemma lem1030514 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : term706.
Proof. exact (fun h0 : ~ False => @lem1030513 A mul x pwr y q h1 h2). Qed.
Lemma lem1030516 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030517 : term706 = False.
Proof. exact (@lem1030516 False). Qed.
Lemma lem1030518 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : False.
Proof. exact (EQ_MP (@lem1030517) (@lem1030514 A mul x pwr y q h1 h2)). Qed.
Lemma lem1030615 {A : Type'} (_17009 : A) (_17010 : nat) (_17011 : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : (term879 A pwr _17009 _17010 _17011) = (term880 A pwr _17009 _17010 _17011).
Proof. exact (EQ_MP (@lem1030022 A pwr _17009 _17010 _17011) (@lem1030021 A _17009 _17010 _17011 pwr h1)). Qed.
Lemma lem1030616 {A : Type'} (_17009 : A) (_17010 : nat) (_17011 : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : (term879 A pwr _17009 _17010 _17011) = (term880 A pwr _17009 _17010 _17011).
Proof. exact (@lem1030615 A _17009 _17010 _17011 pwr h1). Qed.
Lemma lem1030617 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : (term879 A pwr x p q) = (term880 A pwr x p q).
Proof. exact (@lem1030616 A x p q pwr h1). Qed.
Lemma lem1030618 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : term1157 A pwr x p q.
Proof. exact (fun h0 : term1140 A pwr x p q => @lem1030617 A x p q pwr h1). Qed.
Lemma lem1030620 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030621 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1157 A pwr x p q) = ((term879 A pwr x p q) = (term880 A pwr x p q)).
Proof. exact (@lem1030620 ((term879 A pwr x p q) = (term880 A pwr x p q))). Qed.
Lemma lem1030622 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) (h1 : term1034 A pwr) : (term879 A pwr x p q) = (term880 A pwr x p q).
Proof. exact (EQ_MP (@lem1030621 A pwr x p q) (@lem1030618 A x p q pwr h1)). Qed.
Lemma lem1030625 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1030627 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) : (term1140 A pwr x p q) = (term1158 A pwr x p q).
Proof. exact (@lem1030625 ((term879 A pwr x p q) = (term880 A pwr x p q))). Qed.
Lemma lem1030630 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1140 A pwr x p q) : term1158 A pwr x p q.
Proof. exact (EQ_MP (@lem1030627 A pwr x p q) (@lem1030143 A pwr x p q h1)). Qed.
Lemma lem1030633 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : False.
Proof. exact (@lem1030630 A pwr x p q h2 (@lem1030622 A x p q pwr h1)). Qed.
Lemma lem1030634 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : term706.
Proof. exact (fun h0 : ~ False => @lem1030633 A pwr x p q h1 h2). Qed.
Lemma lem1030636 (p : Prop) : (term704 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1030637 : term706 = False.
Proof. exact (@lem1030636 False). Qed.
Lemma lem1030638 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030637) (@lem1030634 A pwr x p q h1 h2)). Qed.
Lemma lem1030639 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : (term1140 A pwr x p q) = False.
Proof. exact (prop_ext (fun h3 : term1140 A pwr x p q => @lem1030638 A pwr x p q h1 h2) (fun h3 : False => @lem1030143 A pwr x p q h2)). Qed.
Lemma lem1030640 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030639 A pwr x p q h1 h2) (@lem1030143 A pwr x p q h2)). Qed.
Lemma lem1030641 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : (term1139 A mul x pwr y q) = False.
Proof. exact (prop_ext (fun h3 : term1139 A mul x pwr y q => @lem1030518 A mul x pwr y q h1 h2) (fun h3 : False => @lem1030103 A mul x pwr y q h2)). Qed.
Lemma lem1030642 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : False.
Proof. exact (EQ_MP (@lem1030641 A mul x pwr y q h1 h2) (@lem1030103 A mul x pwr y q h2)). Qed.
Lemma lem1030643 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : (term1138 A mul pwr x p q) = False.
Proof. exact (prop_ext (fun h3 : term1138 A mul pwr x p q => @lem1030398 A mul pwr x p q h1 h2) (fun h3 : False => @lem1030063 A mul pwr x p q h2)). Qed.
Lemma lem1030644 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030643 A mul pwr x p q h1 h2) (@lem1030063 A mul pwr x p q h2)). Qed.
Lemma lem1030645 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : (term1140 A pwr x p q) = False.
Proof. exact (prop_ext (fun h3 : term1140 A pwr x p q => @lem1030640 A pwr x p q h1 h2) (fun h3 : False => @lem1029663 A pwr x p q h2)). Qed.
Lemma lem1030646 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030645 A pwr x p q h1 h2) (@lem1029663 A pwr x p q h2)). Qed.
Lemma lem1030647 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : (term1139 A mul x pwr y q) = False.
Proof. exact (prop_ext (fun h3 : term1139 A mul x pwr y q => @lem1030642 A mul x pwr y q h1 h2) (fun h3 : False => @lem1029463 A mul x pwr y q h2)). Qed.
Lemma lem1030648 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : False.
Proof. exact (EQ_MP (@lem1030647 A mul x pwr y q h1 h2) (@lem1029463 A mul x pwr y q h2)). Qed.
Lemma lem1030649 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : (term1138 A mul pwr x p q) = False.
Proof. exact (prop_ext (fun h3 : term1138 A mul pwr x p q => @lem1030644 A mul pwr x p q h1 h2) (fun h3 : False => @lem1029263 A mul pwr x p q h2)). Qed.
Lemma lem1030650 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030649 A mul pwr x p q h1 h2) (@lem1029263 A mul pwr x p q h2)). Qed.
Lemma lem1030651 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : (term1140 A pwr x p q) = False.
Proof. exact (prop_ext (fun h3 : term1140 A pwr x p q => @lem1030646 A pwr x p q h1 h2) (fun h3 : False => @lem1029663 A pwr x p q h2)). Qed.
Lemma lem1030652 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030651 A pwr x p q h1 h2) (@lem1029663 A pwr x p q h2)). Qed.
Lemma lem1030653 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : (term1034 A pwr) = False.
Proof. exact (prop_ext (fun h3 : term1034 A pwr => @lem1030652 A pwr x p q h1 h2) (fun h3 : False => @lem1029659 A pwr h1)). Qed.
Lemma lem1030654 {A : Type'} (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term1034 A pwr) (h2 : term1140 A pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030653 A pwr x p q h1 h2) (@lem1029659 A pwr h1)). Qed.
Lemma lem1030655 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : (term1139 A mul x pwr y q) = False.
Proof. exact (prop_ext (fun h3 : term1139 A mul x pwr y q => @lem1030648 A mul x pwr y q h1 h2) (fun h3 : False => @lem1029463 A mul x pwr y q h2)). Qed.
Lemma lem1030656 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : False.
Proof. exact (EQ_MP (@lem1030655 A mul x pwr y q h1 h2) (@lem1029463 A mul x pwr y q h2)). Qed.
Lemma lem1030657 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : (term984 A mul pwr) = False.
Proof. exact (prop_ext (fun h3 : term984 A mul pwr => @lem1030656 A mul x pwr y q h1 h2) (fun h3 : False => @lem1029446 A mul pwr h1)). Qed.
Lemma lem1030658 {A : Type'} (mul : type1400 A) (x : A) (pwr : type1423 A) (y : A) (q : nat) (h1 : term984 A mul pwr) (h2 : term1139 A mul x pwr y q) : False.
Proof. exact (EQ_MP (@lem1030657 A mul x pwr y q h1 h2) (@lem1029446 A mul pwr h1)). Qed.
Lemma lem1030659 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : (term1138 A mul pwr x p q) = False.
Proof. exact (prop_ext (fun h3 : term1138 A mul pwr x p q => @lem1030650 A mul pwr x p q h1 h2) (fun h3 : False => @lem1029263 A mul pwr x p q h2)). Qed.
Lemma lem1030660 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030659 A mul pwr x p q h1 h2) (@lem1029263 A mul pwr x p q h2)). Qed.
Lemma lem1030661 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : (term920 A mul pwr) = False.
Proof. exact (prop_ext (fun h3 : term920 A mul pwr => @lem1030660 A mul pwr x p q h1 h2) (fun h3 : False => @lem1029233 A mul pwr h1)). Qed.
Lemma lem1030662 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term920 A mul pwr) (h2 : term1138 A mul pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030661 A mul pwr x p q h1 h2) (@lem1029233 A mul pwr h1)). Qed.
Lemma lem1030663 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term1134 A mul y pwr x p q) : False.
Proof. exact (or_elim (@lem1029061 A mul y pwr x p q h3) (fun h0 : term1139 A mul x pwr y q => @lem1030658 A mul x pwr y q h1 h0) (fun h0 : term1140 A pwr x p q => @lem1030654 A pwr x p q h2 h0)). Qed.
Lemma lem1030664 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : False.
Proof. exact (or_elim (@lem1029028 A mul y pwr x p q h4) (fun h0 : term1138 A mul pwr x p q => @lem1030662 A mul pwr x p q h3 h0) (fun h0 : term1134 A mul y pwr x p q => @lem1030663 A mul y pwr x p q h1 h2 h0)). Qed.
Lemma lem1030665 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : (term1034 A pwr) = False.
Proof. exact (prop_ext (fun h5 : term1034 A pwr => @lem1030664 A mul y pwr x p q h1 h2 h3 h4) (fun h5 : False => @lem1029059 A pwr h2)). Qed.
Lemma lem1030666 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030665 A mul y pwr x p q h1 h2 h3 h4) (@lem1029059 A pwr h2)). Qed.
Lemma lem1030667 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : (term984 A mul pwr) = False.
Proof. exact (prop_ext (fun h5 : term984 A mul pwr => @lem1030666 A mul y pwr x p q h1 h2 h3 h4) (fun h5 : False => @lem1028944 A mul pwr h1)). Qed.
Lemma lem1030668 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030667 A mul y pwr x p q h1 h2 h3 h4) (@lem1028944 A mul pwr h1)). Qed.
Lemma lem1030669 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : (term920 A mul pwr) = False.
Proof. exact (prop_ext (fun h5 : term920 A mul pwr => @lem1030668 A mul y pwr x p q h1 h2 h3 h4) (fun h5 : False => @lem1028909 A mul pwr h3)). Qed.
Lemma lem1030670 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030669 A mul y pwr x p q h1 h2 h3 h4) (@lem1028909 A mul pwr h3)). Qed.
Lemma lem1030671 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : (term1034 A pwr) = False.
Proof. exact (prop_ext (fun h5 : term1034 A pwr => @lem1030670 A mul y pwr x p q h1 h2 h3 h4) (fun h5 : False => @lem1028521 A pwr h2)). Qed.
Lemma lem1030672 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030671 A mul y pwr x p q h1 h2 h3 h4) (@lem1028521 A pwr h2)). Qed.
Lemma lem1030673 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : (term984 A mul pwr) = False.
Proof. exact (prop_ext (fun h5 : term984 A mul pwr => @lem1030672 A mul y pwr x p q h1 h2 h3 h4) (fun h5 : False => @lem1028476 A mul pwr h1)). Qed.
Lemma lem1030674 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030673 A mul y pwr x p q h1 h2 h3 h4) (@lem1028476 A mul pwr h1)). Qed.
Lemma lem1030675 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : (term920 A mul pwr) = False.
Proof. exact (prop_ext (fun h5 : term920 A mul pwr => @lem1030674 A mul y pwr x p q h1 h2 h3 h4) (fun h5 : False => @lem1028449 A mul pwr h3)). Qed.
Lemma lem1030676 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term1034 A pwr) (h3 : term920 A mul pwr) (h4 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030675 A mul y pwr x p q h1 h2 h3 h4) (@lem1028449 A mul pwr h3)). Qed.
Lemma lem1030677 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term920 A mul pwr) (h3 : term1036 A mul y pwr x p q) : term1041 A pwr.
Proof. exact (fun h0 : term1034 A pwr => @lem1030676 A mul y pwr x p q h1 h0 h2 h3). Qed.
Lemma lem1030678 {A : Type'} (pwr : type1423 A) : (term1041 A pwr) = (term1042 A pwr).
Proof. exact (@lem69 (term1034 A pwr)). Qed.
Lemma lem1030679 {A : Type'} (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term984 A mul pwr) (h2 : term920 A mul pwr) (h3 : term1036 A mul y pwr x p q) : term1042 A pwr.
Proof. exact (EQ_MP (@lem1030678 A pwr) (@lem1030677 A mul y pwr x p q h1 h2 h3)). Qed.
Lemma lem1030680 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term984 A mul pwr) (h2 : term920 A mul pwr) : term1045 A mul y x p q pwr.
Proof. exact (fun h0 : term1036 A mul y pwr x p q => @lem1030679 A mul y pwr x p q h1 h2 h0). Qed.
Lemma lem1030681 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term1048 A mul y x p q pwr.
Proof. exact (fun h0 : term984 A mul pwr => @lem1030680 A y x p q mul pwr h0 h1). Qed.
Lemma lem1030682 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1051 A mul y x p q pwr.
Proof. exact (fun h0 : term920 A mul pwr => @lem1030681 A y x p q mul pwr h0). Qed.
Lemma lem1030683 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1054 A r0 mul y x p q pwr.
Proof. exact (fun h0 : term80 A mul r0 => @lem1030682 A mul y x p q pwr). Qed.
Lemma lem1030684 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1057 A r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term82 A mul r1 => @lem1030683 A r0 mul y x p q pwr). Qed.
Lemma lem1030685 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1060 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term92 A add mul => @lem1030684 A r1 r0 mul y x p q pwr). Qed.
Lemma lem1030686 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1063 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term101 A mul => @lem1030685 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030687 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1066 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term110 A mul => @lem1030686 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030688 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1068 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term11 A mul => @lem1030687 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030689 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1070 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term82 A add r0 => @lem1030688 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030690 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1072 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term101 A add => @lem1030689 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030691 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1074 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term110 A add => @lem1030690 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030692 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1076 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term11 A add => @lem1030691 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030693 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1078 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term21 A mul pwr => @lem1030692 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030694 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1080 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term22 A pwr r1 => @lem1030693 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030695 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1082 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term20 A add mul => @lem1030694 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030696 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1084 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term18 A mul r0 => @lem1030695 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030697 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1086 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term13 A mul r1 => @lem1030696 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030698 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1087 A add r1 r0 mul y x p q pwr.
Proof. exact (fun h0 : term13 A add r0 => @lem1030697 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030703 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1091 A r1 r0 mul y x p q pwr.
Proof. exact (fun add : type1400 A => @lem1030698 A add r1 r0 mul y x p q pwr). Qed.
Lemma lem1030708 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1095 A r0 mul y x p q pwr.
Proof. exact (fun r1 : A => @lem1030703 A r1 r0 mul y x p q pwr). Qed.
Lemma lem1030713 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1099 A mul y x p q pwr.
Proof. exact (fun r0 : A => @lem1030708 A r0 mul y x p q pwr). Qed.
Lemma lem1030718 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1103 A y x p q pwr.
Proof. exact (fun mul : type1400 A => @lem1030713 A mul y x p q pwr). Qed.
Lemma lem1030723 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1107 A x p q pwr.
Proof. exact (fun y : A => @lem1030718 A y x p q pwr). Qed.
Lemma lem1030728 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) : term1111 A p q pwr.
Proof. exact (fun x : A => @lem1030723 A x p q pwr). Qed.
Lemma lem1030733 {A : Type'} (q : nat) (pwr : type1423 A) : term1115 A q pwr.
Proof. exact (fun p : nat => @lem1030728 A p q pwr). Qed.
Lemma lem1030738 {A : Type'} (pwr : type1423 A) : term1119 A pwr.
Proof. exact (fun q : nat => @lem1030733 A q pwr). Qed.
Lemma lem1030743 {A : Type'} : term1123 A.
Proof. exact (fun pwr : type1423 A => @lem1030738 A pwr). Qed.
Lemma lem1030744 {A : Type'} : term1122 A.
Proof. exact (EQ_MP (@lem1028089 A) (@lem1030743 A)). Qed.
Lemma lem1030745 {A : Type'} (pwr : type1423 A) : term1159 A pwr.
Proof. exact (@lem1030744 A pwr). Qed.
Lemma lem1030746 {A : Type'} (pwr : type1423 A) : (term1159 A pwr) = (term1118 A pwr).
Proof. exact (eq_refl (term1159 A pwr)). Qed.
Lemma lem1030747 {A : Type'} (pwr : type1423 A) : term1118 A pwr.
Proof. exact (EQ_MP (@lem1030746 A pwr) (@lem1030745 A pwr)). Qed.
Lemma lem1030748 {A : Type'} (pwr : type1423 A) (q : nat) : term1160 A pwr q.
Proof. exact (@lem1030747 A pwr q). Qed.
Lemma lem1030749 {A : Type'} (q : nat) (pwr : type1423 A) : (term1160 A pwr q) = (term1114 A q pwr).
Proof. exact (eq_refl (term1160 A pwr q)). Qed.
Lemma lem1030750 {A : Type'} (q : nat) (pwr : type1423 A) : term1114 A q pwr.
Proof. exact (EQ_MP (@lem1030749 A q pwr) (@lem1030748 A pwr q)). Qed.
Lemma lem1030751 {A : Type'} (q : nat) (pwr : type1423 A) (p : nat) : term1161 A q pwr p.
Proof. exact (@lem1030750 A q pwr p). Qed.
Lemma lem1030752 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) : (term1161 A q pwr p) = (term1110 A p q pwr).
Proof. exact (eq_refl (term1161 A q pwr p)). Qed.
Lemma lem1030753 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) : term1110 A p q pwr.
Proof. exact (EQ_MP (@lem1030752 A p q pwr) (@lem1030751 A q pwr p)). Qed.
Lemma lem1030754 {A : Type'} (p : nat) (q : nat) (pwr : type1423 A) (x : A) : term1162 A p q pwr x.
Proof. exact (@lem1030753 A p q pwr x). Qed.
Lemma lem1030755 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1162 A p q pwr x) = (term1106 A x p q pwr).
Proof. exact (eq_refl (term1162 A p q pwr x)). Qed.
Lemma lem1030756 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1106 A x p q pwr.
Proof. exact (EQ_MP (@lem1030755 A x p q pwr) (@lem1030754 A p q pwr x)). Qed.
Lemma lem1030757 {A : Type'} (x : A) (p : nat) (q : nat) (pwr : type1423 A) (y : A) : term1163 A x p q pwr y.
Proof. exact (@lem1030756 A x p q pwr y). Qed.
Lemma lem1030758 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1163 A x p q pwr y) = (term1102 A y x p q pwr).
Proof. exact (eq_refl (term1163 A x p q pwr y)). Qed.
Lemma lem1030759 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1102 A y x p q pwr.
Proof. exact (EQ_MP (@lem1030758 A y x p q pwr) (@lem1030757 A x p q pwr y)). Qed.
Lemma lem1030760 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (mul : type1400 A) : term1164 A y x p q pwr mul.
Proof. exact (@lem1030759 A y x p q pwr mul). Qed.
Lemma lem1030761 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1164 A y x p q pwr mul) = (term1098 A mul y x p q pwr).
Proof. exact (eq_refl (term1164 A y x p q pwr mul)). Qed.
Lemma lem1030762 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1098 A mul y x p q pwr.
Proof. exact (EQ_MP (@lem1030761 A mul y x p q pwr) (@lem1030760 A y x p q pwr mul)). Qed.
Lemma lem1030763 {A : Type'} (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (r0 : A) : term1165 A mul y x p q pwr r0.
Proof. exact (@lem1030762 A mul y x p q pwr r0). Qed.
Lemma lem1030764 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1165 A mul y x p q pwr r0) = (term1094 A r0 mul y x p q pwr).
Proof. exact (eq_refl (term1165 A mul y x p q pwr r0)). Qed.
Lemma lem1030765 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1094 A r0 mul y x p q pwr.
Proof. exact (EQ_MP (@lem1030764 A r0 mul y x p q pwr) (@lem1030763 A mul y x p q pwr r0)). Qed.
Lemma lem1030766 {A : Type'} (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (r1 : A) : term1166 A r0 mul y x p q pwr r1.
Proof. exact (@lem1030765 A r0 mul y x p q pwr r1). Qed.
Lemma lem1030767 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1166 A r0 mul y x p q pwr r1) = (term1090 A r1 r0 mul y x p q pwr).
Proof. exact (eq_refl (term1166 A r0 mul y x p q pwr r1)). Qed.
Lemma lem1030768 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1090 A r1 r0 mul y x p q pwr.
Proof. exact (EQ_MP (@lem1030767 A r1 r0 mul y x p q pwr) (@lem1030766 A r0 mul y x p q pwr r1)). Qed.
Lemma lem1030769 {A : Type'} (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (add : type1400 A) : term1167 A r1 r0 mul y x p q pwr add.
Proof. exact (@lem1030768 A r1 r0 mul y x p q pwr add). Qed.
Lemma lem1030770 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : (term1167 A r1 r0 mul y x p q pwr add) = (term1037 A add r1 r0 mul y x p q pwr).
Proof. exact (eq_refl (term1167 A r1 r0 mul y x p q pwr add)). Qed.
Lemma lem1030771 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1037 A add r1 r0 mul y x p q pwr.
Proof. exact (EQ_MP (@lem1030770 A add r1 r0 mul y x p q pwr) (@lem1030769 A r1 r0 mul y x p q pwr add)). Qed.
Lemma lem1030773 {A : Type'} (add : type1400 A) (r1 : A) (r0 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) : term1037 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1027129 A add r1 r0 mul y x p q pwr (@lem1030771 A add r1 r0 mul y x p q pwr)). Qed.
Lemma lem1030774 {A : Type'} (r1 : A) (mul : type1400 A) (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (add : type1400 A) (r0 : A) (h1 : term13 A add r0) : term1085 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030773 A add r1 r0 mul y x p q pwr (@lem1017045 A add r0 h1)). Qed.
Lemma lem1030775 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term13 A add r0) (h2 : term13 A mul r1) : term1083 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030774 A r1 mul y x p q pwr add r0 h1 (@lem1017051 A mul r1 h2)). Qed.
Lemma lem1030776 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term13 A add r0) (h2 : term18 A mul r0) (h3 : term13 A mul r1) : term1081 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030775 A y x p q pwr add r0 mul r1 h1 h3 (@lem1017053 A mul r0 h2)). Qed.
Lemma lem1030777 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (pwr : type1423 A) (add : type1400 A) (r0 : A) (mul : type1400 A) (r1 : A) (h1 : term20 A add mul) (h2 : term13 A add r0) (h3 : term18 A mul r0) (h4 : term13 A mul r1) : term1079 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030776 A y x p q pwr add r0 mul r1 h2 h3 h4 (@lem1017055 A add mul h1)). Qed.
Lemma lem1030778 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term13 A add r0) (h3 : term18 A mul r0) (h4 : term13 A mul r1) (h5 : term22 A pwr r1) : term1077 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030777 A y x p q pwr add r0 mul r1 h1 h2 h3 h4 (@lem1017057 A pwr r1 h5)). Qed.
Lemma lem1030779 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term21 A mul pwr) (h3 : term13 A add r0) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : term1075 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030778 A y x p q add r0 mul pwr r1 h1 h3 h4 h5 h6 (@lem1017056 A mul pwr h2)). Qed.
Lemma lem1030780 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term11 A add) (h3 : term21 A mul pwr) (h4 : term13 A add r0) (h5 : term18 A mul r0) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) : term1073 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030779 A y x p q add r0 mul pwr r1 h1 h3 h4 h5 h6 h7 (@lem1023819 A add h2)). Qed.
Lemma lem1030781 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term21 A mul pwr) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) : term1071 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030780 A y x p q add r0 mul pwr r1 h2 h3 h4 h5 h6 h7 h8 (@lem1023821 A add h1)). Qed.
Lemma lem1030782 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) : term1069 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030781 A y x p q add r0 mul pwr r1 h2 h3 h4 h5 h6 h7 h8 h9 (@lem1023823 A add h1)). Qed.
Lemma lem1030783 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term82 A add r0) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : term1067 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030782 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h7 h8 h9 h10 (@lem1023825 A add r0 h6)). Qed.
Lemma lem1030784 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term82 A add r0) (h8 : term13 A add r0) (h9 : term18 A mul r0) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) : term1065 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030783 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h6 h7 h8 h9 h10 h11 (@lem1023827 A mul h5)). Qed.
Lemma lem1030785 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term110 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term82 A add r0) (h9 : term13 A add r0) (h10 : term18 A mul r0) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) : term1062 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030784 A y x p q add r0 mul pwr r1 h1 h2 h3 h5 h6 h7 h8 h9 h10 h11 h12 (@lem1023829 A mul h4)). Qed.
Lemma lem1030786 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A add r0) (h10 : term13 A add r0) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) : term1059 A add r1 r0 mul y x p q pwr.
Proof. exact (@lem1030785 A y x p q add r0 mul pwr r1 h1 h2 h3 h5 h6 h7 h8 h9 h10 h11 h12 h13 (@lem1023831 A mul h4)). Qed.
Lemma lem1030787 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) : term1056 A r1 r0 mul y x p q pwr.
Proof. exact (@lem1030786 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h6 h7 h8 h9 h10 h11 h12 h13 h14 (@lem1023833 A add mul h5)). Qed.
Lemma lem1030788 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term82 A mul r1) (h13 : term18 A mul r0) (h14 : term13 A mul r1) (h15 : term22 A pwr r1) : term1053 A r0 mul y x p q pwr.
Proof. exact (@lem1030787 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h13 h14 h15 (@lem1023835 A mul r1 h12)). Qed.
Lemma lem1030789 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : term1050 A mul y x p q pwr.
Proof. exact (@lem1030788 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h13 h14 h15 h16 (@lem1023834 A mul r0 h12)). Qed.
Lemma lem1030790 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) (h17 : term920 A mul pwr) : term1047 A mul y x p q pwr.
Proof. exact (@lem1030789 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 (@lem1026222 A mul pwr h17)). Qed.
Lemma lem1030791 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term21 A mul pwr) (h11 : term82 A add r0) (h12 : term13 A add r0) (h13 : term80 A mul r0) (h14 : term82 A mul r1) (h15 : term18 A mul r0) (h16 : term13 A mul r1) (h17 : term22 A pwr r1) (h18 : term920 A mul pwr) : term1044 A mul y x p q pwr.
Proof. exact (@lem1030790 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 (@lem1026636 A mul pwr h7)). Qed.
Lemma lem1030792 {A : Type'} (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term21 A mul pwr) (h11 : term82 A add r0) (h12 : term13 A add r0) (h13 : term80 A mul r0) (h14 : term82 A mul r1) (h15 : term18 A mul r0) (h16 : term13 A mul r1) (h17 : term22 A pwr r1) (h18 : term920 A mul pwr) (h19 : term1036 A mul y pwr x p q) : term1041 A pwr.
Proof. exact (@lem1030791 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 (@lem1027113 A mul y pwr x p q h19)). Qed.
Lemma lem1030793 {A : Type'} (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term1034 A pwr) (h11 : term21 A mul pwr) (h12 : term82 A add r0) (h13 : term13 A add r0) (h14 : term80 A mul r0) (h15 : term82 A mul r1) (h16 : term18 A mul r0) (h17 : term13 A mul r1) (h18 : term22 A pwr r1) (h19 : term920 A mul pwr) (h20 : term1036 A mul y pwr x p q) : False.
Proof. exact (@lem1030792 A add r0 r1 mul y pwr x p q h1 h2 h3 h4 h5 h6 h7 h8 h9 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 (@lem1027098 A pwr h10)). Qed.
Lemma lem1030794 {A : Type'} (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term1034 A pwr) (h11 : term21 A mul pwr) (h12 : term82 A add r0) (h13 : term13 A add r0) (h14 : term80 A mul r0) (h15 : term82 A mul r1) (h16 : term18 A mul r0) (h17 : term13 A mul r1) (h18 : term22 A pwr r1) (h19 : term920 A mul pwr) (h20 : term1036 A mul y pwr x p q) : (term1034 A pwr) = False.
Proof. exact (prop_ext (fun h21 : term1034 A pwr => @lem1030793 A add r0 r1 mul y pwr x p q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20) (fun h21 : False => @lem1027098 A pwr h10)). Qed.
Lemma lem1030795 {A : Type'} (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term1034 A pwr) (h11 : term21 A mul pwr) (h12 : term82 A add r0) (h13 : term13 A add r0) (h14 : term80 A mul r0) (h15 : term82 A mul r1) (h16 : term18 A mul r0) (h17 : term13 A mul r1) (h18 : term22 A pwr r1) (h19 : term920 A mul pwr) (h20 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030794 A add r0 r1 mul y pwr x p q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20) (@lem1027098 A pwr h10)). Qed.
Lemma lem1030796 {A : Type'} (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term1034 A pwr) (h11 : term21 A mul pwr) (h12 : term82 A add r0) (h13 : term13 A add r0) (h14 : term80 A mul r0) (h15 : term82 A mul r1) (h16 : term18 A mul r0) (h17 : term13 A mul r1) (h18 : term22 A pwr r1) (h19 : term920 A mul pwr) (h20 : term1036 A mul y pwr x p q) : (term1036 A mul y pwr x p q) = False.
Proof. exact (prop_ext (fun h21 : term1036 A mul y pwr x p q => @lem1030795 A add r0 r1 mul y pwr x p q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20) (fun h21 : False => @lem1027113 A mul y pwr x p q h20)). Qed.
Lemma lem1030797 {A : Type'} (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (y : A) (pwr : type1423 A) (x : A) (p : nat) (q : nat) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term1034 A pwr) (h11 : term21 A mul pwr) (h12 : term82 A add r0) (h13 : term13 A add r0) (h14 : term80 A mul r0) (h15 : term82 A mul r1) (h16 : term18 A mul r0) (h17 : term13 A mul r1) (h18 : term22 A pwr r1) (h19 : term920 A mul pwr) (h20 : term1036 A mul y pwr x p q) : False.
Proof. exact (EQ_MP (@lem1030796 A add r0 r1 mul y pwr x p q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20) (@lem1027113 A mul y pwr x p q h20)). Qed.
Lemma lem1030798 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term1034 A pwr) (h11 : term21 A mul pwr) (h12 : term82 A add r0) (h13 : term13 A add r0) (h14 : term80 A mul r0) (h15 : term82 A mul r1) (h16 : term18 A mul r0) (h17 : term13 A mul r1) (h18 : term22 A pwr r1) (h19 : term920 A mul pwr) : term1035 A mul y pwr x p q.
Proof. exact (fun h0 : term1036 A mul y pwr x p q => @lem1030797 A add r0 r1 mul y pwr x p q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h0). Qed.
Lemma lem1030799 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term1034 A pwr) (h11 : term21 A mul pwr) (h12 : term82 A add r0) (h13 : term13 A add r0) (h14 : term80 A mul r0) (h15 : term82 A mul r1) (h16 : term18 A mul r0) (h17 : term13 A mul r1) (h18 : term22 A pwr r1) (h19 : term920 A mul pwr) : term890 A mul y pwr x p q.
Proof. exact (EQ_MP (@lem1027112 A mul y pwr x p q) (@lem1030798 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19)). Qed.
Lemma lem1030801 (P : nat -> Prop) : term921 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1030802 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : term1168 A pwr x m.
Proof. exact (@lem1030801 (term1124 A pwr x m)). Qed.
Lemma lem1030803 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1169 A pwr x m) = ((term1170 A pwr x m) = (term1171 A pwr x m)).
Proof. exact (eq_refl (term1169 A pwr x m)). Qed.
Lemma lem1030804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1030805 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1172 A pwr x m) = (term1173 A pwr x m).
Proof. exact (MK_COMB (@lem1030804) (@lem1030803 A pwr x m)). Qed.
Lemma lem1030806 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : (term1146 A pwr x m n) = ((term879 A pwr x m n) = (term880 A pwr x m n)).
Proof. exact (eq_refl (term1146 A pwr x m n)). Qed.
Lemma lem1030807 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1030808 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : (term1174 A pwr x m n) = (term1175 A pwr x m n).
Proof. exact (MK_COMB (@lem1030807) (@lem1030806 A pwr x m n)). Qed.
Lemma lem1030809 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : (term1176 A pwr x m n) = ((term1177 A pwr x m n) = (term1178 A pwr x m n)).
Proof. exact (eq_refl (term1176 A pwr x m n)). Qed.
Lemma lem1030810 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : (term1179 A pwr x m n) = (term1180 A pwr x m n).
Proof. exact (MK_COMB (@lem1030808 A pwr x m n) (@lem1030809 A pwr x m n)). Qed.
Lemma lem1030811 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1181 A pwr x m) = (term1182 A pwr x m).
Proof. exact (fun_ext (fun n : nat => @lem1030810 A pwr x m n)). Qed.
Lemma lem1030812 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1030813 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1183 A pwr x m) = (term1184 A pwr x m).
Proof. exact (MK_COMB (@lem1030812) (@lem1030811 A pwr x m)). Qed.
Lemma lem1030814 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1185 A pwr x m) = (term1186 A pwr x m).
Proof. exact (MK_COMB (@lem1030805 A pwr x m) (@lem1030813 A pwr x m)). Qed.
Lemma lem1030815 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1030816 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1187 A pwr x m) = (term1188 A pwr x m).
Proof. exact (MK_COMB (@lem1030815) (@lem1030814 A pwr x m)). Qed.
Lemma lem1030817 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : (term1146 A pwr x m n) = ((term879 A pwr x m n) = (term880 A pwr x m n)).
Proof. exact (eq_refl (term1146 A pwr x m n)). Qed.
Lemma lem1030818 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1189 A pwr x m) = (term1124 A pwr x m).
Proof. exact (fun_ext (fun n : nat => @lem1030817 A pwr x m n)). Qed.
Lemma lem1030819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1030820 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1190 A pwr x m) = (term1125 A pwr x m).
Proof. exact (MK_COMB (@lem1030819) (@lem1030818 A pwr x m)). Qed.
Lemma lem1030821 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : (term1168 A pwr x m) = (term1191 A pwr x m).
Proof. exact (MK_COMB (@lem1030816 A pwr x m) (@lem1030820 A pwr x m)). Qed.
Lemma lem1030822 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) : term1191 A pwr x m.
Proof. exact (EQ_MP (@lem1030821 A pwr x m) (@lem1030802 A pwr x m)). Qed.
Lemma lem1030824 : term1192.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1030850 : term1193.
Proof. exact (proj1 (@lem1030824)). Qed.
Lemma lem1030851 (m : nat) : term1194 m.
Proof. exact (@lem1030850 m). Qed.
Lemma lem1030852 (m : nat) : (term1194 m) = ((term1195 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term1194 m)). Qed.
Lemma lem1030876 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : term812 A pwr r1 x.
Proof. exact (@lem1017057 A pwr r1 h1 x). Qed.
Lemma lem1030877 {A : Type'} (pwr : type1423 A) (x : A) (r1 : A) : (term812 A pwr r1 x) = ((term126 A pwr x) = r1).
Proof. exact (eq_refl (term812 A pwr r1 x)). Qed.
Lemma lem1030972 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1030877 A pwr x r1) (@lem1030876 A x pwr r1 h1)). Qed.
Lemma lem1030973 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1030972 A x pwr r1 h1). Qed.
Lemma lem1030974 {A : Type'} (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term1170 A pwr x m) = r1.
Proof. exact (@lem1030973 A (pwr x m) pwr r1 h1). Qed.
Lemma lem1030975 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1030976 {A : Type'} (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term1196 A pwr x m) = (@eq A r1).
Proof. exact (MK_COMB (@lem1030975 A) (@lem1030974 A x m pwr r1 h1)). Qed.
Lemma lem1030978 (m : nat) : (term1195 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1030852 m) (@lem1030851 m)). Qed.
Lemma lem1030979 {A : Type'} (pwr : type1423 A) (x : A) : (pwr x) = (pwr x).
Proof. exact (eq_refl (pwr x)). Qed.
Lemma lem1030980 {A : Type'} (m : nat) (pwr : type1423 A) (x : A) : (term1171 A pwr x m) = (term126 A pwr x).
Proof. exact (MK_COMB (@lem1030979 A pwr x) (@lem1030978 m)). Qed.
Lemma lem1030982 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (EQ_MP (@lem1030877 A pwr x r1) (@lem1030876 A x pwr r1 h1)). Qed.
Lemma lem1030983 {A : Type'} (x : A) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term126 A pwr x) = r1.
Proof. exact (@lem1030982 A x pwr r1 h1). Qed.
Lemma lem1030984 {A : Type'} (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term1171 A pwr x m) = r1.
Proof. exact (TRANS (@lem1030980 A m pwr x) (@lem1030983 A x pwr r1 h1)). Qed.
Lemma lem1030985 {A : Type'} (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : ((term1170 A pwr x m) = (term1171 A pwr x m)) = (r1 = r1).
Proof. exact (MK_COMB (@lem1030976 A x m pwr r1 h1) (@lem1030984 A x m pwr r1 h1)). Qed.
Lemma lem1030987 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1030988 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1030987 A x). Qed.
Lemma lem1030989 {A : Type'} (r1 : A) : (r1 = r1) = True.
Proof. exact (@lem1030988 A r1). Qed.
Lemma lem1030990 {A : Type'} (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : ((term1170 A pwr x m) = (term1171 A pwr x m)) = True.
Proof. exact (TRANS (@lem1030985 A x m pwr r1 h1) (@lem1030989 A r1)). Qed.
Lemma lem1030991 {A : Type'} (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : True = ((term1170 A pwr x m) = (term1171 A pwr x m)).
Proof. exact (SYM (@lem1030990 A x m pwr r1 h1)). Qed.
Lemma lem1030992 {A : Type'} (x : A) (m : nat) (pwr : type1423 A) (r1 : A) (h1 : term22 A pwr r1) : (term1170 A pwr x m) = (term1171 A pwr x m).
Proof. exact (EQ_MP (@lem1030991 A x m pwr r1 h1) (@lem0)). Qed.
Lemma lem1030993 : term1192.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1030994 : term1197.
Proof. exact (proj2 (@lem1030993)). Qed.
Lemma lem1030995 : term1198.
Proof. exact (proj2 (@lem1030994)). Qed.
Lemma lem1030996 : term1199.
Proof. exact (proj2 (@lem1030995)). Qed.
Lemma lem1030997 : term1200.
Proof. exact (proj2 (@lem1030996)). Qed.
Lemma lem1030998 (m : nat) : term1201 m.
Proof. exact (@lem1030997 m). Qed.
Lemma lem1030999 (m : nat) : (term1201 m) = (term1202 m).
Proof. exact (eq_refl (term1201 m)). Qed.
Lemma lem1031000 (m : nat) : term1202 m.
Proof. exact (EQ_MP (@lem1030999 m) (@lem1030998 m)). Qed.
Lemma lem1031001 (m : nat) (n : nat) : term1203 m n.
Proof. exact (@lem1031000 m n). Qed.
Lemma lem1031002 (m : nat) (n : nat) : (term1203 m n) = ((term1204 m n) = (term1205 m n)).
Proof. exact (eq_refl (term1203 m n)). Qed.
Lemma lem1031048 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term813 A mul pwr x.
Proof. exact (@lem1017056 A mul pwr h1 x). Qed.
Lemma lem1031049 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) : (term813 A mul pwr x) = (term124 A mul pwr x).
Proof. exact (eq_refl (term813 A mul pwr x)). Qed.
Lemma lem1031050 {A : Type'} (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term124 A mul pwr x.
Proof. exact (EQ_MP (@lem1031049 A mul pwr x) (@lem1031048 A x mul pwr h1)). Qed.
Lemma lem1031051 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : term814 A mul pwr x n.
Proof. exact (@lem1031050 A x mul pwr h1 n). Qed.
Lemma lem1031052 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (n : nat) : (term814 A mul pwr x n) = ((term121 A pwr x n) = (term122 A mul pwr x n)).
Proof. exact (eq_refl (term814 A mul pwr x n)). Qed.
Lemma lem1031120 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term1141 A mul pwr m.
Proof. exact (@lem1026222 A mul pwr h1 m). Qed.
Lemma lem1031121 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) : (term1141 A mul pwr m) = (term946 A mul m pwr).
Proof. exact (eq_refl (term1141 A mul pwr m)). Qed.
Lemma lem1031122 {A : Type'} (m : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term946 A mul m pwr.
Proof. exact (EQ_MP (@lem1031121 A mul m pwr) (@lem1031120 A m mul pwr h1)). Qed.
Lemma lem1031123 {A : Type'} (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term928 A mul m pwr n.
Proof. exact (@lem1031122 A m mul pwr h1 n). Qed.
Lemma lem1031124 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (n : nat) : (term928 A mul m pwr n) = (term929 A mul m pwr n).
Proof. exact (eq_refl (term928 A mul m pwr n)). Qed.
Lemma lem1031125 {A : Type'} (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term929 A mul m pwr n.
Proof. exact (EQ_MP (@lem1031124 A mul m pwr n) (@lem1031123 A m n mul pwr h1)). Qed.
Lemma lem1031126 {A : Type'} (m : nat) (n : nat) (x : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : term969 A mul m pwr n x.
Proof. exact (@lem1031125 A m n mul pwr h1 x). Qed.
Lemma lem1031127 {A : Type'} (mul : type1400 A) (m : nat) (pwr : type1423 A) (x : A) (n : nat) : (term969 A mul m pwr n x) = ((term970 A pwr x m n) = (term971 A mul m pwr x n)).
Proof. exact (eq_refl (term969 A mul m pwr n x)). Qed.
Lemma lem1031141 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (EQ_MP (@lem1031052 A mul pwr x n) (@lem1031051 A x n mul pwr h1)). Qed.
Lemma lem1031142 {A : Type'} (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term121 A pwr x n) = (term122 A mul pwr x n).
Proof. exact (@lem1031141 A x n mul pwr h1). Qed.
Lemma lem1031143 {A : Type'} (x : A) (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) : (term1177 A pwr x m n) = (term1206 A mul pwr x m n).
Proof. exact (@lem1031142 A (pwr x m) n mul pwr h1). Qed.
Lemma lem1031149 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : (term879 A pwr x m n) = (term880 A pwr x m n)) : (term879 A pwr x m n) = (term880 A pwr x m n).
Proof. exact (h1). Qed.
Lemma lem1031150 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) : (term955 A mul pwr x m) = (term955 A mul pwr x m).
Proof. exact (eq_refl (term955 A mul pwr x m)). Qed.
Lemma lem1031151 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : (term879 A pwr x m n) = (term880 A pwr x m n)) : (term1206 A mul pwr x m n) = (term1207 A mul pwr x m n).
Proof. exact (MK_COMB (@lem1031150 A mul pwr x m) (@lem1031149 A pwr x m n h1)). Qed.
Lemma lem1031156 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : term21 A mul pwr) (h2 : (term879 A pwr x m n) = (term880 A pwr x m n)) : (term1177 A pwr x m n) = (term1207 A mul pwr x m n).
Proof. exact (TRANS (@lem1031143 A x m n mul pwr h1) (@lem1031151 A mul pwr x m n h2)). Qed.
Lemma lem1031157 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem1031158 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : term21 A mul pwr) (h2 : (term879 A pwr x m n) = (term880 A pwr x m n)) : (term1208 A pwr x m n) = (term1209 A mul pwr x m n).
Proof. exact (MK_COMB (@lem1031157 A) (@lem1031156 A mul pwr x m n h1 h2)). Qed.
Lemma lem1031160 (m : nat) (n : nat) : (term1204 m n) = (term1205 m n).
Proof. exact (EQ_MP (@lem1031002 m n) (@lem1031001 m n)). Qed.
Lemma lem1031161 {A : Type'} (pwr : type1423 A) (x : A) : (pwr x) = (pwr x).
Proof. exact (eq_refl (pwr x)). Qed.
Lemma lem1031162 {A : Type'} (pwr : type1423 A) (x : A) (m : nat) (n : nat) : (term1178 A pwr x m n) = (term1210 A pwr x m n).
Proof. exact (MK_COMB (@lem1031161 A pwr x) (@lem1031160 m n)). Qed.
Lemma lem1031164 {A : Type'} (m : nat) (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term970 A pwr x m n) = (term971 A mul m pwr x n).
Proof. exact (EQ_MP (@lem1031127 A mul m pwr x n) (@lem1031126 A m n x mul pwr h1)). Qed.
Lemma lem1031165 {A : Type'} (m : nat) (x : A) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term970 A pwr x m n) = (term971 A mul m pwr x n).
Proof. exact (@lem1031164 A m x n mul pwr h1). Qed.
Lemma lem1031166 {A : Type'} (x : A) (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term1210 A pwr x m n) = (term1207 A mul pwr x m n).
Proof. exact (@lem1031165 A m x (Nat.mul m n) mul pwr h1). Qed.
Lemma lem1031171 {A : Type'} (x : A) (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term920 A mul pwr) : (term1178 A pwr x m n) = (term1207 A mul pwr x m n).
Proof. exact (TRANS (@lem1031162 A pwr x m n) (@lem1031166 A x m n mul pwr h1)). Qed.
Lemma lem1031172 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : term21 A mul pwr) (h2 : term920 A mul pwr) (h3 : (term879 A pwr x m n) = (term880 A pwr x m n)) : ((term1177 A pwr x m n) = (term1178 A pwr x m n)) = ((term1207 A mul pwr x m n) = (term1207 A mul pwr x m n)).
Proof. exact (MK_COMB (@lem1031158 A mul pwr x m n h1 h3) (@lem1031171 A x m n mul pwr h2)). Qed.
Lemma lem1031174 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1031175 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1031174 A x). Qed.
Lemma lem1031176 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) : ((term1207 A mul pwr x m n) = (term1207 A mul pwr x m n)) = True.
Proof. exact (@lem1031175 A (term1207 A mul pwr x m n)). Qed.
Lemma lem1031177 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : term21 A mul pwr) (h2 : term920 A mul pwr) (h3 : (term879 A pwr x m n) = (term880 A pwr x m n)) : ((term1177 A pwr x m n) = (term1178 A pwr x m n)) = True.
Proof. exact (TRANS (@lem1031172 A mul pwr x m n h1 h2 h3) (@lem1031176 A mul pwr x m n)). Qed.
Lemma lem1031178 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : term21 A mul pwr) (h2 : term920 A mul pwr) (h3 : (term879 A pwr x m n) = (term880 A pwr x m n)) : True = ((term1177 A pwr x m n) = (term1178 A pwr x m n)).
Proof. exact (SYM (@lem1031177 A mul pwr x m n h1 h2 h3)). Qed.
Lemma lem1031179 {A : Type'} (mul : type1400 A) (pwr : type1423 A) (x : A) (m : nat) (n : nat) (h1 : term21 A mul pwr) (h2 : term920 A mul pwr) (h3 : (term879 A pwr x m n) = (term880 A pwr x m n)) : (term1177 A pwr x m n) = (term1178 A pwr x m n).
Proof. exact (EQ_MP (@lem1031178 A mul pwr x m n h1 h2 h3) (@lem0)). Qed.
Lemma lem1031180 {A : Type'} (x : A) (m : nat) (n : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) (h2 : term920 A mul pwr) : term1180 A pwr x m n.
Proof. exact (fun h0 : (term879 A pwr x m n) = (term880 A pwr x m n) => @lem1031179 A mul pwr x m n h1 h2 h0). Qed.
Lemma lem1031185 {A : Type'} (x : A) (m : nat) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) (h2 : term920 A mul pwr) : term1184 A pwr x m.
Proof. exact (fun n : nat => @lem1031180 A x m n mul pwr h1 h2). Qed.
Lemma lem1031186 {A : Type'} (x : A) (m : nat) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) (h2 : term22 A pwr r1) (h3 : term920 A mul pwr) : term1186 A pwr x m.
Proof. exact (conj (@lem1030992 A x m pwr r1 h2) (@lem1031185 A x m mul pwr h1 h3)). Qed.
Lemma lem1031187 {A : Type'} (x : A) (m : nat) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) (h2 : term22 A pwr r1) (h3 : term920 A mul pwr) : term1125 A pwr x m.
Proof. exact (@lem1030822 A pwr x m (@lem1031186 A x m r1 mul pwr h1 h2 h3)). Qed.
Lemma lem1031192 {A : Type'} (x : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) (h2 : term22 A pwr r1) (h3 : term920 A mul pwr) : term1127 A pwr x.
Proof. exact (fun m : nat => @lem1031187 A x m r1 mul pwr h1 h2 h3). Qed.
Lemma lem1031197 {A : Type'} (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term21 A mul pwr) (h2 : term22 A pwr r1) (h3 : term920 A mul pwr) : term1034 A pwr.
Proof. exact (fun x : A => @lem1031192 A x r1 mul pwr h1 h2 h3). Qed.
Lemma lem1031198 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term21 A mul pwr) (h11 : term82 A add r0) (h12 : term13 A add r0) (h13 : term80 A mul r0) (h14 : term82 A mul r1) (h15 : term18 A mul r0) (h16 : term13 A mul r1) (h17 : term22 A pwr r1) (h18 : term920 A mul pwr) : (term1034 A pwr) = (term890 A mul y pwr x p q).
Proof. exact (prop_ext (fun h19 : term1034 A pwr => @lem1030799 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h19 h10 h11 h12 h13 h14 h15 h16 h17 h18) (fun h19 : term890 A mul y pwr x p q => @lem1031197 A r1 mul pwr h10 h17 h18)). Qed.
Lemma lem1031199 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term21 A mul pwr) (h11 : term82 A add r0) (h12 : term13 A add r0) (h13 : term80 A mul r0) (h14 : term82 A mul r1) (h15 : term18 A mul r0) (h16 : term13 A mul r1) (h17 : term22 A pwr r1) (h18 : term920 A mul pwr) : term890 A mul y pwr x p q.
Proof. exact (EQ_MP (@lem1031198 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18) (@lem1031197 A r1 mul pwr h10 h17 h18)). Qed.
Lemma lem1031200 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term21 A mul pwr) (h11 : term82 A add r0) (h12 : term13 A add r0) (h13 : term80 A mul r0) (h14 : term82 A mul r1) (h15 : term18 A mul r0) (h16 : term13 A mul r1) (h17 : term22 A pwr r1) (h18 : term920 A mul pwr) : (term984 A mul pwr) = (term890 A mul y pwr x p q).
Proof. exact (prop_ext (fun h19 : term984 A mul pwr => @lem1031199 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18) (fun h19 : term890 A mul y pwr x p q => @lem1026636 A mul pwr h7)). Qed.
Lemma lem1031201 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term984 A mul pwr) (h8 : term11 A add) (h9 : term11 A mul) (h10 : term21 A mul pwr) (h11 : term82 A add r0) (h12 : term13 A add r0) (h13 : term80 A mul r0) (h14 : term82 A mul r1) (h15 : term18 A mul r0) (h16 : term13 A mul r1) (h17 : term22 A pwr r1) (h18 : term920 A mul pwr) : term890 A mul y pwr x p q.
Proof. exact (EQ_MP (@lem1031200 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18) (@lem1026636 A mul pwr h7)). Qed.
Lemma lem1031202 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) (h17 : term920 A mul pwr) : (term984 A mul pwr) = (term890 A mul y pwr x p q).
Proof. exact (prop_ext (fun h18 : term984 A mul pwr => @lem1031201 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h18 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17) (fun h18 : term890 A mul y pwr x p q => @lem1027097 A mul pwr r1 h4 h6 h8 h9 h15 h16)). Qed.
Lemma lem1031203 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) (h17 : term920 A mul pwr) : term890 A mul y pwr x p q.
Proof. exact (EQ_MP (@lem1031202 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17) (@lem1027097 A mul pwr r1 h4 h6 h8 h9 h15 h16)). Qed.
Lemma lem1031204 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) (h17 : term920 A mul pwr) : (term920 A mul pwr) = (term890 A mul y pwr x p q).
Proof. exact (prop_ext (fun h18 : term920 A mul pwr => @lem1031203 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17) (fun h18 : term890 A mul y pwr x p q => @lem1026222 A mul pwr h17)). Qed.
Lemma lem1031205 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) (h17 : term920 A mul pwr) : term890 A mul y pwr x p q.
Proof. exact (EQ_MP (@lem1031204 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17) (@lem1026222 A mul pwr h17)). Qed.
Lemma lem1031206 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term920 A mul pwr) = (term890 A mul y pwr x p q).
Proof. exact (prop_ext (fun h17 : term920 A mul pwr => @lem1031205 A y x p q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17) (fun h17 : term890 A mul y pwr x p q => @lem1026635 A mul pwr r1 h6 h8 h9 h13 h16)). Qed.
Lemma lem1031207 {A : Type'} (y : A) (x : A) (p : nat) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : term890 A mul y pwr x p q.
Proof. exact (EQ_MP (@lem1031206 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1026635 A mul pwr r1 h6 h8 h9 h13 h16)). Qed.
Lemma lem1031208 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1026221 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1031207 A y x p q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16)). Qed.
Lemma lem1031209 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term23 A add r1 mul r0) : term120 A add r1 mul r0.
Proof. exact (proj2 (@lem1023817 A add r1 mul r0 h1)). Qed.
Lemma lem1031210 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term23 A add r1 mul r0) : term11 A add.
Proof. exact (proj1 (@lem1023817 A add r1 mul r0 h1)). Qed.
Lemma lem1031211 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term120 A add r1 mul r0) : term119 A add r1 mul r0.
Proof. exact (proj2 (@lem1023818 A add r1 mul r0 h1)). Qed.
Lemma lem1031212 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term120 A add r1 mul r0) : term110 A add.
Proof. exact (proj1 (@lem1023818 A add r1 mul r0 h1)). Qed.
Lemma lem1031213 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term119 A add r1 mul r0) : term118 A add r1 mul r0.
Proof. exact (proj2 (@lem1023820 A add r1 mul r0 h1)). Qed.
Lemma lem1031214 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term119 A add r1 mul r0) : term101 A add.
Proof. exact (proj1 (@lem1023820 A add r1 mul r0 h1)). Qed.
Lemma lem1031215 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term118 A add r1 mul r0) : term117 A add r1 mul r0.
Proof. exact (proj2 (@lem1023822 A add r1 mul r0 h1)). Qed.
Lemma lem1031216 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term118 A add r1 mul r0) : term82 A add r0.
Proof. exact (proj1 (@lem1023822 A add r1 mul r0 h1)). Qed.
Lemma lem1031217 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term117 A add r1 mul r0) : term112 A add r1 mul r0.
Proof. exact (proj2 (@lem1023824 A add r1 mul r0 h1)). Qed.
Lemma lem1031218 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term117 A add r1 mul r0) : term11 A mul.
Proof. exact (proj1 (@lem1023824 A add r1 mul r0 h1)). Qed.
Lemma lem1031219 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term112 A add r1 mul r0) : term103 A add r1 mul r0.
Proof. exact (proj2 (@lem1023826 A add r1 mul r0 h1)). Qed.
Lemma lem1031220 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term112 A add r1 mul r0) : term110 A mul.
Proof. exact (proj1 (@lem1023826 A add r1 mul r0 h1)). Qed.
Lemma lem1031221 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term103 A add r1 mul r0) : term94 A add r1 mul r0.
Proof. exact (proj2 (@lem1023828 A add r1 mul r0 h1)). Qed.
Lemma lem1031222 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term103 A add r1 mul r0) : term101 A mul.
Proof. exact (proj1 (@lem1023828 A add r1 mul r0 h1)). Qed.
Lemma lem1031223 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term94 A add r1 mul r0) : term84 A r1 mul r0.
Proof. exact (proj2 (@lem1023830 A add r1 mul r0 h1)). Qed.
Lemma lem1031224 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term94 A add r1 mul r0) : term92 A add mul.
Proof. exact (proj1 (@lem1023830 A add r1 mul r0 h1)). Qed.
Lemma lem1031225 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term84 A r1 mul r0) : term80 A mul r0.
Proof. exact (proj2 (@lem1023832 A r1 mul r0 h1)). Qed.
Lemma lem1031226 {A : Type'} (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term84 A r1 mul r0) : term82 A mul r1.
Proof. exact (proj1 (@lem1023832 A r1 mul r0 h1)). Qed.
Lemma lem1031227 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term80 A mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h17 : term80 A mul r0 => @lem1031208 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (fun h17 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023834 A mul r0 h12)). Qed.
Lemma lem1031228 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031227 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1023834 A mul r0 h12)). Qed.
Lemma lem1031229 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : (term82 A mul r1) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h17 : term82 A mul r1 => @lem1031228 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (fun h17 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023835 A mul r1 h13)). Qed.
Lemma lem1031230 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term80 A mul r0) (h13 : term82 A mul r1) (h14 : term18 A mul r0) (h15 : term13 A mul r1) (h16 : term22 A pwr r1) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031229 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1023835 A mul r1 h13)). Qed.
Lemma lem1031231 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term82 A mul r1) (h13 : term18 A mul r0) (h14 : term13 A mul r1) (h15 : term22 A pwr r1) (h16 : term84 A r1 mul r0) : (term80 A mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h17 : term80 A mul r0 => @lem1031230 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h17 h12 h13 h14 h15) (fun h17 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031225 A r1 mul r0 h16)). Qed.
Lemma lem1031232 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term82 A mul r1) (h13 : term18 A mul r0) (h14 : term13 A mul r1) (h15 : term22 A pwr r1) (h16 : term84 A r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031231 A m ly rx lx ry b a c d p y z x q add pwr r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16) (@lem1031225 A r1 mul r0 h16)). Qed.
Lemma lem1031233 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) (h15 : term84 A r1 mul r0) : (term82 A mul r1) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h16 : term82 A mul r1 => @lem1031232 A m ly rx lx ry b a c d p y z x q add pwr r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h16 h12 h13 h14 h15) (fun h16 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031226 A r1 mul r0 h15)). Qed.
Lemma lem1031234 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) (h15 : term84 A r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031233 A m ly rx lx ry b a c d p y z x q add pwr r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15) (@lem1031226 A r1 mul r0 h15)). Qed.
Lemma lem1031235 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) (h15 : term84 A r1 mul r0) : (term92 A add mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h16 : term92 A add mul => @lem1031234 A m ly rx lx ry b a c d p y z x q add pwr r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15) (fun h16 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023833 A add mul h5)). Qed.
Lemma lem1031236 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (pwr : type1423 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) (h15 : term84 A r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031235 A m ly rx lx ry b a c d p y z x q add pwr r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15) (@lem1023833 A add mul h5)). Qed.
Lemma lem1031237 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) (h15 : term94 A add r1 mul r0) : (term84 A r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h16 : term84 A r1 mul r0 => @lem1031236 A m ly rx lx ry b a c d p y z x q add pwr r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h16) (fun h16 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031223 A add r1 mul r0 h15)). Qed.
Lemma lem1031238 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term92 A add mul) (h6 : term110 A mul) (h7 : term11 A add) (h8 : term11 A mul) (h9 : term21 A mul pwr) (h10 : term82 A add r0) (h11 : term13 A add r0) (h12 : term18 A mul r0) (h13 : term13 A mul r1) (h14 : term22 A pwr r1) (h15 : term94 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031237 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15) (@lem1031223 A add r1 mul r0 h15)). Qed.
Lemma lem1031239 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A add r0) (h10 : term13 A add r0) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) (h14 : term94 A add r1 mul r0) : (term92 A add mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h15 : term92 A add mul => @lem1031238 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h15 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14) (fun h15 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031224 A add r1 mul r0 h14)). Qed.
Lemma lem1031240 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A add r0) (h10 : term13 A add r0) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) (h14 : term94 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031239 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14) (@lem1031224 A add r1 mul r0 h14)). Qed.
Lemma lem1031241 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A add r0) (h10 : term13 A add r0) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) (h14 : term94 A add r1 mul r0) : (term101 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h15 : term101 A mul => @lem1031240 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14) (fun h15 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023831 A mul h4)). Qed.
Lemma lem1031242 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A add r0) (h10 : term13 A add r0) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) (h14 : term94 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031241 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14) (@lem1023831 A mul h4)). Qed.
Lemma lem1031243 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A add r0) (h10 : term13 A add r0) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) (h14 : term103 A add r1 mul r0) : (term94 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h15 : term94 A add r1 mul r0 => @lem1031242 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h15) (fun h15 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031221 A add r1 mul r0 h14)). Qed.
Lemma lem1031244 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term101 A mul) (h5 : term110 A mul) (h6 : term11 A add) (h7 : term11 A mul) (h8 : term21 A mul pwr) (h9 : term82 A add r0) (h10 : term13 A add r0) (h11 : term18 A mul r0) (h12 : term13 A mul r1) (h13 : term22 A pwr r1) (h14 : term103 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031243 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14) (@lem1031221 A add r1 mul r0 h14)). Qed.
Lemma lem1031245 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term110 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term82 A add r0) (h9 : term13 A add r0) (h10 : term18 A mul r0) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) (h13 : term103 A add r1 mul r0) : (term101 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h14 : term101 A mul => @lem1031244 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h14 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) (fun h14 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031222 A add r1 mul r0 h13)). Qed.
Lemma lem1031246 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term110 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term82 A add r0) (h9 : term13 A add r0) (h10 : term18 A mul r0) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) (h13 : term103 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031245 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) (@lem1031222 A add r1 mul r0 h13)). Qed.
Lemma lem1031247 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term110 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term82 A add r0) (h9 : term13 A add r0) (h10 : term18 A mul r0) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) (h13 : term103 A add r1 mul r0) : (term110 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h14 : term110 A mul => @lem1031246 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) (fun h14 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023829 A mul h4)). Qed.
Lemma lem1031248 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term110 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term82 A add r0) (h9 : term13 A add r0) (h10 : term18 A mul r0) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) (h13 : term103 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031247 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) (@lem1023829 A mul h4)). Qed.
Lemma lem1031249 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term110 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term82 A add r0) (h9 : term13 A add r0) (h10 : term18 A mul r0) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) (h13 : term112 A add r1 mul r0) : (term103 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h14 : term103 A add r1 mul r0 => @lem1031248 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h14) (fun h14 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031219 A add r1 mul r0 h13)). Qed.
Lemma lem1031250 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term110 A mul) (h5 : term11 A add) (h6 : term11 A mul) (h7 : term21 A mul pwr) (h8 : term82 A add r0) (h9 : term13 A add r0) (h10 : term18 A mul r0) (h11 : term13 A mul r1) (h12 : term22 A pwr r1) (h13 : term112 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031249 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13) (@lem1031219 A add r1 mul r0 h13)). Qed.
Lemma lem1031251 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term82 A add r0) (h8 : term13 A add r0) (h9 : term18 A mul r0) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) (h12 : term112 A add r1 mul r0) : (term110 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h13 : term110 A mul => @lem1031250 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h13 h4 h5 h6 h7 h8 h9 h10 h11 h12) (fun h13 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031220 A add r1 mul r0 h12)). Qed.
Lemma lem1031252 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term82 A add r0) (h8 : term13 A add r0) (h9 : term18 A mul r0) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) (h12 : term112 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031251 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) (@lem1031220 A add r1 mul r0 h12)). Qed.
Lemma lem1031253 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term82 A add r0) (h8 : term13 A add r0) (h9 : term18 A mul r0) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) (h12 : term112 A add r1 mul r0) : (term11 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h13 : term11 A mul => @lem1031252 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) (fun h13 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023827 A mul h5)). Qed.
Lemma lem1031254 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term82 A add r0) (h8 : term13 A add r0) (h9 : term18 A mul r0) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) (h12 : term112 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031253 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) (@lem1023827 A mul h5)). Qed.
Lemma lem1031255 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term82 A add r0) (h8 : term13 A add r0) (h9 : term18 A mul r0) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) (h12 : term117 A add r1 mul r0) : (term112 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h13 : term112 A add r1 mul r0 => @lem1031254 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h13) (fun h13 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031217 A add r1 mul r0 h12)). Qed.
Lemma lem1031256 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term82 A add r0) (h8 : term13 A add r0) (h9 : term18 A mul r0) (h10 : term13 A mul r1) (h11 : term22 A pwr r1) (h12 : term117 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031255 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12) (@lem1031217 A add r1 mul r0 h12)). Qed.
Lemma lem1031257 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term82 A add r0) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term117 A add r1 mul r0) : (term11 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h12 : term11 A mul => @lem1031256 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h12 h5 h6 h7 h8 h9 h10 h11) (fun h12 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031218 A add r1 mul r0 h11)). Qed.
Lemma lem1031258 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term82 A add r0) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term117 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031257 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem1031218 A add r1 mul r0 h11)). Qed.
Lemma lem1031259 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term82 A add r0) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term117 A add r1 mul r0) : (term82 A add r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h12 : term82 A add r0 => @lem1031258 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (fun h12 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023825 A add r0 h6)). Qed.
Lemma lem1031260 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term82 A add r0) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term117 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031259 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem1023825 A add r0 h6)). Qed.
Lemma lem1031261 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term82 A add r0) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term118 A add r1 mul r0) : (term117 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h12 : term117 A add r1 mul r0 => @lem1031260 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h12) (fun h12 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031215 A add r1 mul r0 h11)). Qed.
Lemma lem1031262 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term82 A add r0) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) (h11 : term118 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031261 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11) (@lem1031215 A add r1 mul r0 h11)). Qed.
Lemma lem1031263 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term118 A add r1 mul r0) : (term82 A add r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h11 : term82 A add r0 => @lem1031262 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h11 h6 h7 h8 h9 h10) (fun h11 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031216 A add r1 mul r0 h10)). Qed.
Lemma lem1031264 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term118 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031263 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1031216 A add r1 mul r0 h10)). Qed.
Lemma lem1031265 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term118 A add r1 mul r0) : (term101 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h11 : term101 A add => @lem1031264 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023823 A add h1)). Qed.
Lemma lem1031266 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term118 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031265 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1023823 A add h1)). Qed.
Lemma lem1031267 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term119 A add r1 mul r0) : (term118 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h11 : term118 A add r1 mul r0 => @lem1031266 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h11) (fun h11 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031213 A add r1 mul r0 h10)). Qed.
Lemma lem1031268 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term101 A add) (h2 : term110 A add) (h3 : term20 A add mul) (h4 : term11 A add) (h5 : term21 A mul pwr) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term119 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031267 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1031213 A add r1 mul r0 h10)). Qed.
Lemma lem1031269 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term21 A mul pwr) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) (h9 : term119 A add r1 mul r0) : (term101 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h10 : term101 A add => @lem1031268 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h10 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031214 A add r1 mul r0 h9)). Qed.
Lemma lem1031270 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term21 A mul pwr) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) (h9 : term119 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031269 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1031214 A add r1 mul r0 h9)). Qed.
Lemma lem1031271 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term21 A mul pwr) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) (h9 : term119 A add r1 mul r0) : (term110 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h10 : term110 A add => @lem1031270 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023821 A add h1)). Qed.
Lemma lem1031272 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term21 A mul pwr) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) (h9 : term119 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031271 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1023821 A add h1)). Qed.
Lemma lem1031273 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term21 A mul pwr) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) (h9 : term120 A add r1 mul r0) : (term119 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h10 : term119 A add r1 mul r0 => @lem1031272 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h10) (fun h10 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031211 A add r1 mul r0 h9)). Qed.
Lemma lem1031274 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term110 A add) (h2 : term20 A add mul) (h3 : term11 A add) (h4 : term21 A mul pwr) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term22 A pwr r1) (h9 : term120 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031273 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1031211 A add r1 mul r0 h9)). Qed.
Lemma lem1031275 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term11 A add) (h3 : term21 A mul pwr) (h4 : term13 A add r0) (h5 : term18 A mul r0) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) (h8 : term120 A add r1 mul r0) : (term110 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h9 : term110 A add => @lem1031274 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h9 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031212 A add r1 mul r0 h8)). Qed.
Lemma lem1031276 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term11 A add) (h3 : term21 A mul pwr) (h4 : term13 A add r0) (h5 : term18 A mul r0) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) (h8 : term120 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031275 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1031212 A add r1 mul r0 h8)). Qed.
Lemma lem1031277 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term11 A add) (h3 : term21 A mul pwr) (h4 : term13 A add r0) (h5 : term18 A mul r0) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) (h8 : term120 A add r1 mul r0) : (term11 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h9 : term11 A add => @lem1031276 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023819 A add h2)). Qed.
Lemma lem1031278 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term11 A add) (h3 : term21 A mul pwr) (h4 : term13 A add r0) (h5 : term18 A mul r0) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) (h8 : term120 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031277 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1023819 A add h2)). Qed.
Lemma lem1031279 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term11 A add) (h3 : term21 A mul pwr) (h4 : term13 A add r0) (h5 : term18 A mul r0) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) (h8 : term23 A add r1 mul r0) : (term120 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h9 : term120 A add r1 mul r0 => @lem1031278 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h9) (fun h9 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031209 A add r1 mul r0 h8)). Qed.
Lemma lem1031280 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term11 A add) (h3 : term21 A mul pwr) (h4 : term13 A add r0) (h5 : term18 A mul r0) (h6 : term13 A mul r1) (h7 : term22 A pwr r1) (h8 : term23 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031279 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7 h8) (@lem1031209 A add r1 mul r0 h8)). Qed.
Lemma lem1031281 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term21 A mul pwr) (h3 : term13 A add r0) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) (h7 : term23 A add r1 mul r0) : (term11 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h8 : term11 A add => @lem1031280 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h8 h2 h3 h4 h5 h6 h7) (fun h8 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031210 A add r1 mul r0 h7)). Qed.
Lemma lem1031282 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term21 A mul pwr) (h3 : term13 A add r0) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) (h7 : term23 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031281 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h7) (@lem1031210 A add r1 mul r0 h7)). Qed.
Lemma lem1031283 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term20 A add mul) (h2 : term21 A mul pwr) (h3 : term13 A add r0) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) : term1211 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (fun h0 : term23 A add r1 mul r0 => @lem1031282 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h1 h2 h3 h4 h5 h6 h0). Qed.
Lemma lem1031284 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (pwr : type1423 A) (add : type1400 A) (r1 : A) (mul : type1400 A) (r0 : A) (h1 : term20 A add mul) (h2 : term21 A mul pwr) (h3 : term13 A add r0) (h4 : term18 A mul r0) (h5 : term13 A mul r1) (h6 : term22 A pwr r1) (h7 : term23 A add r1 mul r0) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (@lem1031283 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 (@lem1017058 A add r1 mul r0 h7)). Qed.
Lemma lem1031285 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term23 A add r1 mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h11 : term23 A add r1 mul r0 => @lem1031284 A m ly rx lx ry b a c d p y z x q pwr add r1 mul r0 h2 h6 h7 h8 h9 h10 h11) (fun h11 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1023816 A add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1031286 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031285 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1023816 A add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)). Qed.
Lemma lem1031287 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term7 A r0 add r1 mul pwr) : term8 A r0 add r1 mul pwr.
Proof. exact (proj2 (@lem1017039 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031288 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term7 A r0 add r1 mul pwr) : term9 A add.
Proof. exact (proj1 (@lem1017039 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031289 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term8 A r0 add r1 mul pwr) : term10 A r0 add r1 mul pwr.
Proof. exact (proj2 (@lem1017040 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031290 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term8 A r0 add r1 mul pwr) : term11 A add.
Proof. exact (proj1 (@lem1017040 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031291 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term10 A r0 add r1 mul pwr) : term12 A r0 add r1 mul pwr.
Proof. exact (proj2 (@lem1017042 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031292 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term10 A r0 add r1 mul pwr) : term13 A add r0.
Proof. exact (proj1 (@lem1017042 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031293 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term12 A r0 add r1 mul pwr) : term14 A r0 add r1 mul pwr.
Proof. exact (proj2 (@lem1017044 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031294 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term12 A r0 add r1 mul pwr) : term9 A mul.
Proof. exact (proj1 (@lem1017044 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031295 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term14 A r0 add r1 mul pwr) : term15 A r0 add r1 mul pwr.
Proof. exact (proj2 (@lem1017046 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031296 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term14 A r0 add r1 mul pwr) : term11 A mul.
Proof. exact (proj1 (@lem1017046 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031297 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term15 A r0 add r1 mul pwr) : term16 A r0 add r1 mul pwr.
Proof. exact (proj2 (@lem1017048 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031298 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term15 A r0 add r1 mul pwr) : term13 A mul r1.
Proof. exact (proj1 (@lem1017048 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031299 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term16 A r0 add r1 mul pwr) : term17 A add r1 mul pwr.
Proof. exact (proj2 (@lem1017050 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031300 {A : Type'} (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term16 A r0 add r1 mul pwr) : term18 A mul r0.
Proof. exact (proj1 (@lem1017050 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031301 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term17 A add r1 mul pwr) : term19 A r1 mul pwr.
Proof. exact (proj2 (@lem1017052 A add r1 mul pwr h1)). Qed.
Lemma lem1031302 {A : Type'} (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term17 A add r1 mul pwr) : term20 A add mul.
Proof. exact (proj1 (@lem1017052 A add r1 mul pwr h1)). Qed.
Lemma lem1031303 {A : Type'} (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term19 A r1 mul pwr) : term21 A mul pwr.
Proof. exact (proj2 (@lem1017054 A r1 mul pwr h1)). Qed.
Lemma lem1031304 {A : Type'} (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term19 A r1 mul pwr) : term22 A pwr r1.
Proof. exact (proj1 (@lem1017054 A r1 mul pwr h1)). Qed.
Lemma lem1031305 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term21 A mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h11 : term21 A mul pwr => @lem1031286 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017056 A mul pwr h6)). Qed.
Lemma lem1031306 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031305 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1017056 A mul pwr h6)). Qed.
Lemma lem1031307 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : (term22 A pwr r1) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h11 : term22 A pwr r1 => @lem1031306 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (fun h11 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017057 A pwr r1 h10)). Qed.
Lemma lem1031308 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (mul : type1400 A) (pwr : type1423 A) (r1 : A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term21 A mul pwr) (h7 : term13 A add r0) (h8 : term18 A mul r0) (h9 : term13 A mul r1) (h10 : term22 A pwr r1) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031307 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1017057 A pwr r1 h10)). Qed.
Lemma lem1031309 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term19 A r1 mul pwr) : (term21 A mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h11 : term21 A mul pwr => @lem1031308 A m ly rx lx ry b a c d p y z x q add r0 mul pwr r1 h1 h2 h3 h4 h5 h11 h6 h7 h8 h9) (fun h11 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031303 A r1 mul pwr h10)). Qed.
Lemma lem1031310 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term22 A pwr r1) (h10 : term19 A r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031309 A m ly rx lx ry b a c d p y z x q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9 h10) (@lem1031303 A r1 mul pwr h10)). Qed.
Lemma lem1031311 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term19 A r1 mul pwr) : (term22 A pwr r1) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h10 : term22 A pwr r1 => @lem1031310 A m ly rx lx ry b a c d p y z x q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h10 h9) (fun h10 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031304 A r1 mul pwr h9)). Qed.
Lemma lem1031312 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term19 A r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031311 A m ly rx lx ry b a c d p y z x q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1031304 A r1 mul pwr h9)). Qed.
Lemma lem1031313 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term19 A r1 mul pwr) : (term20 A add mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h10 : term20 A add mul => @lem1031312 A m ly rx lx ry b a c d p y z x q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9) (fun h10 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017055 A add mul h2)). Qed.
Lemma lem1031314 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (add : type1400 A) (r0 : A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term19 A r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031313 A m ly rx lx ry b a c d p y z x q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1017055 A add mul h2)). Qed.
Lemma lem1031315 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term17 A add r1 mul pwr) : (term19 A r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h10 : term19 A r1 mul pwr => @lem1031314 A m ly rx lx ry b a c d p y z x q add r0 r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h10) (fun h10 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031301 A add r1 mul pwr h9)). Qed.
Lemma lem1031316 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term20 A add mul) (h3 : term9 A mul) (h4 : term11 A add) (h5 : term11 A mul) (h6 : term13 A add r0) (h7 : term18 A mul r0) (h8 : term13 A mul r1) (h9 : term17 A add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031315 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8 h9) (@lem1031301 A add r1 mul pwr h9)). Qed.
Lemma lem1031317 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term17 A add r1 mul pwr) : (term20 A add mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h9 : term20 A add mul => @lem1031316 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h9 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031302 A add r1 mul pwr h8)). Qed.
Lemma lem1031318 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term17 A add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031317 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8) (@lem1031302 A add r1 mul pwr h8)). Qed.
Lemma lem1031319 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term17 A add r1 mul pwr) : (term18 A mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h9 : term18 A mul r0 => @lem1031318 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8) (fun h9 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017053 A mul r0 h6)). Qed.
Lemma lem1031320 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term17 A add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031319 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8) (@lem1017053 A mul r0 h6)). Qed.
Lemma lem1031321 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term16 A r0 add r1 mul pwr) : (term17 A add r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h9 : term17 A add r1 mul pwr => @lem1031320 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h9) (fun h9 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031299 A r0 add r1 mul pwr h8)). Qed.
Lemma lem1031322 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term18 A mul r0) (h7 : term13 A mul r1) (h8 : term16 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031321 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7 h8) (@lem1031299 A r0 add r1 mul pwr h8)). Qed.
Lemma lem1031323 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) (h7 : term16 A r0 add r1 mul pwr) : (term18 A mul r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h8 : term18 A mul r0 => @lem1031322 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h8 h6 h7) (fun h8 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031300 A r0 add r1 mul pwr h7)). Qed.
Lemma lem1031324 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) (h7 : term16 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031323 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7) (@lem1031300 A r0 add r1 mul pwr h7)). Qed.
Lemma lem1031325 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) (h7 : term16 A r0 add r1 mul pwr) : (term13 A mul r1) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h8 : term13 A mul r1 => @lem1031324 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7) (fun h8 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017051 A mul r1 h6)). Qed.
Lemma lem1031326 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) (h7 : term16 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031325 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7) (@lem1017051 A mul r1 h6)). Qed.
Lemma lem1031327 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) (h7 : term15 A r0 add r1 mul pwr) : (term16 A r0 add r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h8 : term16 A r0 add r1 mul pwr => @lem1031326 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h8) (fun h8 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031297 A r0 add r1 mul pwr h7)). Qed.
Lemma lem1031328 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term13 A mul r1) (h7 : term15 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031327 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6 h7) (@lem1031297 A r0 add r1 mul pwr h7)). Qed.
Lemma lem1031329 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term15 A r0 add r1 mul pwr) : (term13 A mul r1) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h7 : term13 A mul r1 => @lem1031328 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h7 h6) (fun h7 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031298 A r0 add r1 mul pwr h6)). Qed.
Lemma lem1031330 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term15 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031329 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6) (@lem1031298 A r0 add r1 mul pwr h6)). Qed.
Lemma lem1031331 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term15 A r0 add r1 mul pwr) : (term11 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h7 : term11 A mul => @lem1031330 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6) (fun h7 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017049 A mul h4)). Qed.
Lemma lem1031332 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term15 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031331 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6) (@lem1017049 A mul h4)). Qed.
Lemma lem1031333 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term14 A r0 add r1 mul pwr) : (term15 A r0 add r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h7 : term15 A r0 add r1 mul pwr => @lem1031332 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h7) (fun h7 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031295 A r0 add r1 mul pwr h6)). Qed.
Lemma lem1031334 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term11 A mul) (h5 : term13 A add r0) (h6 : term14 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031333 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5 h6) (@lem1031295 A r0 add r1 mul pwr h6)). Qed.
Lemma lem1031335 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) (h5 : term14 A r0 add r1 mul pwr) : (term11 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h6 : term11 A mul => @lem1031334 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h6 h4 h5) (fun h6 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031296 A r0 add r1 mul pwr h5)). Qed.
Lemma lem1031336 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) (h5 : term14 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031335 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5) (@lem1031296 A r0 add r1 mul pwr h5)). Qed.
Lemma lem1031337 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) (h5 : term14 A r0 add r1 mul pwr) : (term9 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h6 : term9 A mul => @lem1031336 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5) (fun h6 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017047 A mul h2)). Qed.
Lemma lem1031338 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) (h5 : term14 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031337 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5) (@lem1017047 A mul h2)). Qed.
Lemma lem1031339 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) (h5 : term12 A r0 add r1 mul pwr) : (term14 A r0 add r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h6 : term14 A r0 add r1 mul pwr => @lem1031338 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h6) (fun h6 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031293 A r0 add r1 mul pwr h5)). Qed.
Lemma lem1031340 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term9 A mul) (h3 : term11 A add) (h4 : term13 A add r0) (h5 : term12 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031339 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4 h5) (@lem1031293 A r0 add r1 mul pwr h5)). Qed.
Lemma lem1031341 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) (h4 : term12 A r0 add r1 mul pwr) : (term9 A mul) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h5 : term9 A mul => @lem1031340 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h5 h2 h3 h4) (fun h5 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031294 A r0 add r1 mul pwr h4)). Qed.
Lemma lem1031342 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) (h4 : term12 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031341 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4) (@lem1031294 A r0 add r1 mul pwr h4)). Qed.
Lemma lem1031343 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) (h4 : term12 A r0 add r1 mul pwr) : (term13 A add r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h5 : term13 A add r0 => @lem1031342 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4) (fun h5 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017045 A add r0 h3)). Qed.
Lemma lem1031344 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) (h4 : term12 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031343 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4) (@lem1017045 A add r0 h3)). Qed.
Lemma lem1031345 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) (h4 : term10 A r0 add r1 mul pwr) : (term12 A r0 add r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h5 : term12 A r0 add r1 mul pwr => @lem1031344 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h5) (fun h5 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031291 A r0 add r1 mul pwr h4)). Qed.
Lemma lem1031346 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term13 A add r0) (h4 : term10 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031345 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3 h4) (@lem1031291 A r0 add r1 mul pwr h4)). Qed.
Lemma lem1031347 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term10 A r0 add r1 mul pwr) : (term13 A add r0) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h4 : term13 A add r0 => @lem1031346 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h4 h3) (fun h4 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031292 A r0 add r1 mul pwr h3)). Qed.
Lemma lem1031348 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term10 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031347 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3) (@lem1031292 A r0 add r1 mul pwr h3)). Qed.
Lemma lem1031349 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term10 A r0 add r1 mul pwr) : (term11 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h4 : term11 A add => @lem1031348 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3) (fun h4 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017043 A add h2)). Qed.
Lemma lem1031350 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term10 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031349 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3) (@lem1017043 A add h2)). Qed.
Lemma lem1031351 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term8 A r0 add r1 mul pwr) : (term10 A r0 add r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h4 : term10 A r0 add r1 mul pwr => @lem1031350 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h4) (fun h4 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031289 A r0 add r1 mul pwr h3)). Qed.
Lemma lem1031352 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term11 A add) (h3 : term8 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031351 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2 h3) (@lem1031289 A r0 add r1 mul pwr h3)). Qed.
Lemma lem1031353 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term8 A r0 add r1 mul pwr) : (term11 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h3 : term11 A add => @lem1031352 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h3 h2) (fun h3 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031290 A r0 add r1 mul pwr h2)). Qed.
Lemma lem1031354 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term8 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031353 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2) (@lem1031290 A r0 add r1 mul pwr h2)). Qed.
Lemma lem1031355 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term8 A r0 add r1 mul pwr) : (term9 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h3 : term9 A add => @lem1031354 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2) (fun h3 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1017041 A add h1)). Qed.
Lemma lem1031356 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term8 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031355 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2) (@lem1017041 A add h1)). Qed.
Lemma lem1031357 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term7 A r0 add r1 mul pwr) : (term8 A r0 add r1 mul pwr) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h3 : term8 A r0 add r1 mul pwr => @lem1031356 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h3) (fun h3 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031287 A r0 add r1 mul pwr h2)). Qed.
Lemma lem1031358 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term9 A add) (h2 : term7 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031357 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1 h2) (@lem1031287 A r0 add r1 mul pwr h2)). Qed.
Lemma lem1031359 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term7 A r0 add r1 mul pwr) : (term9 A add) = (term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q).
Proof. exact (prop_ext (fun h2 : term9 A add => @lem1031358 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h2 h1) (fun h2 : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q => @lem1031288 A r0 add r1 mul pwr h1)). Qed.
Lemma lem1031360 {A : Type'} (m : A) (ly : A) (rx : A) (lx : A) (ry : A) (b : A) (a : A) (c : A) (d : A) (p : nat) (y : A) (z : A) (x : A) (q : nat) (r0 : A) (add : type1400 A) (r1 : A) (mul : type1400 A) (pwr : type1423 A) (h1 : term7 A r0 add r1 mul pwr) : term919 A m r0 ly rx lx ry b a c d p r1 add y z mul pwr x q.
Proof. exact (EQ_MP (@lem1031359 A m ly rx lx ry b a c d p y z x q r0 add r1 mul pwr h1) (@lem1031288 A r0 add r1 mul pwr h1)). Qed.
