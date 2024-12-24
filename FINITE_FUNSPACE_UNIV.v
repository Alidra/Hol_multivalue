Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_FUNSPACE_UNIV_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_FUNSPACE_UNIV_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem4588127 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4588128 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4588129 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4588128 t1) (@lem4588127 t1)). Qed.
Lemma lem4588130 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4588129 t1 t2). Qed.
Lemma lem4588131 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4588132 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4588131 t1 t2) (@lem4588130 t1 t2)). Qed.
Lemma lem4588133 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4588132 t1 t2 t3). Qed.
Lemma lem4588134 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4588135 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4588134 t1 t2 t3) (@lem4588133 t1 t2 t3)). Qed.
Lemma lem4588136 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4588135 t1 t2 t3)). Qed.
Lemma lem4588138 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4588139 {A B : Type'} : (term8 A B) = (term9 A B).
Proof. exact (@lem4588138 (term8 A B)). Qed.
Lemma lem4588140 {A B : Type'} : (term9 A B) = (term8 A B).
Proof. exact (SYM (@lem4588139 A B)). Qed.
Lemma lem4588141 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem4588142 {A B : Type'} : term11 A B.
Proof. exact (@lem4582295 A B). Qed.
Lemma lem4588143 {B : Type'} : term12 B.
Proof. exact (@lem4582295 B B). Qed.
Lemma lem4588144 {A B : Type'} : term13 A B.
Proof. exact (@lem4582295 (A -> B) B). Qed.
Lemma lem4588145 {A : Type'} : term12 A.
Proof. exact (@lem4582295 A A). Qed.
Lemma lem4588147 {A B : Type'} : term14 A B.
Proof. exact (@lem4582295 A (A -> B)). Qed.
Lemma lem4588149 {A B : Type'} : term15 A B.
Proof. exact (@lem3863773 (A -> B)). Qed.
Lemma lem4588150 {B : Type'} : term16 B.
Proof. exact (@lem3863773 B). Qed.
Lemma lem4588151 {A B : Type'} : term17 A B.
Proof. exact (@lem3863773 (type570 A B)). Qed.
Lemma lem4588152 {B : Type'} : term18 B.
Proof. exact (@lem3863773 (B -> B)). Qed.
Lemma lem4588153 {A : Type'} : term16 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem4588154 {A B : Type'} : term19 A B.
Proof. exact (@lem3863773 (type1401 A B)). Qed.
Lemma lem4588155 {A : Type'} : term18 A.
Proof. exact (@lem3863773 (A -> A)). Qed.
Lemma lem4588161 {A B : Type'} (h1 : term20 A B) : term20 A B.
Proof. exact (h1). Qed.
Lemma lem4588162 {A B : Type'} : term21 A B.
Proof. exact (fun h0 : term20 A B => @lem4588161 A B h0). Qed.
Lemma lem4588163 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (h1). Qed.
Lemma lem4588164 {A B : Type'} (h1 : term20 A B) : term20 A B.
Proof. exact (h1). Qed.
Lemma lem4588165 {A B : Type'} (h1 : term20 A B) (h2 : term21 A B) : term20 A B.
Proof. exact (@lem4588163 A B h2 (@lem4588164 A B h1)). Qed.
Lemma lem4588166 {A B : Type'} (h1 : term20 A B) : term22 A B.
Proof. exact (fun h0 : term21 A B => @lem4588165 A B h1 h0). Qed.
Lemma lem4588167 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (h1). Qed.
Lemma lem4588168 {A B : Type'} (h1 : term20 A B) (h2 : term21 A B) : term20 A B.
Proof. exact (@lem4588166 A B h1 (@lem4588167 A B h2)). Qed.
Lemma lem4588169 {A B : Type'} (h1 : term21 A B) : term21 A B.
Proof. exact (fun h0 : term20 A B => @lem4588168 A B h0 h1). Qed.
Lemma lem4588170 {A B : Type'} : term23 A B.
Proof. exact (fun h0 : term21 A B => @lem4588169 A B h0). Qed.
Lemma lem4588173 {A B : Type'} : term21 A B.
Proof. exact (@lem4588170 A B (@lem4588162 A B)). Qed.
Lemma lem4588174 {A B : Type'} : term21 A B.
Proof. exact (@lem4588173 A B). Qed.
Lemma lem4588322 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4588323 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (@lem4588322 (term13 A B)). Qed.
Lemma lem4588336 {B : Type'} : (term26 B) = (term26 B).
Proof. exact (eq_refl (term26 B)). Qed.
Lemma lem4588337 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (MK_COMB (@lem4588336 B) (@lem4588323 A B)). Qed.
Lemma lem4588340 {A B : Type'} : (term29 A B) = (term29 A B).
Proof. exact (eq_refl (term29 A B)). Qed.
Lemma lem4588341 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem4588340 A B) (@lem4588337 A B)). Qed.
Lemma lem4588344 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (eq_refl (term32 A B)). Qed.
Lemma lem4588345 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem4588344 A B) (@lem4588341 A B)). Qed.
Lemma lem4588348 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (eq_refl (term26 A)). Qed.
Lemma lem4588349 {A B : Type'} : (term35 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem4588348 A) (@lem4588345 A B)). Qed.
Lemma lem4588352 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (eq_refl (term37 A B)). Qed.
Lemma lem4588353 {A B : Type'} : (term38 A B) = (term39 A B).
Proof. exact (MK_COMB (@lem4588352 A B) (@lem4588349 A B)). Qed.
Lemma lem4588356 {B : Type'} : (term40 B) = (term40 B).
Proof. exact (eq_refl (term40 B)). Qed.
Lemma lem4588357 {A B : Type'} : (term41 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem4588356 B) (@lem4588353 A B)). Qed.
Lemma lem4588360 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (eq_refl (term43 A B)). Qed.
Lemma lem4588361 {A B : Type'} : (term44 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem4588360 A B) (@lem4588357 A B)). Qed.
Lemma lem4588364 {A B : Type'} : (term46 A B) = (term46 A B).
Proof. exact (eq_refl (term46 A B)). Qed.
Lemma lem4588365 {A B : Type'} : (term47 A B) = (term48 A B).
Proof. exact (MK_COMB (@lem4588364 A B) (@lem4588361 A B)). Qed.
Lemma lem4588368 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (eq_refl (term40 A)). Qed.
Lemma lem4588369 {A B : Type'} : (term49 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem4588368 A) (@lem4588365 A B)). Qed.
Lemma lem4588372 {B : Type'} : (term51 B) = (term51 B).
Proof. exact (eq_refl (term51 B)). Qed.
Lemma lem4588373 {A B : Type'} : (term52 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem4588372 B) (@lem4588369 A B)). Qed.
Lemma lem4588376 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (eq_refl (term51 A)). Qed.
Lemma lem4588377 {A B : Type'} : (term54 A B) = (term55 A B).
Proof. exact (MK_COMB (@lem4588376 A) (@lem4588373 A B)). Qed.
Lemma lem4588380 {A B : Type'} : (term56 A B) = (term56 A B).
Proof. exact (eq_refl (term56 A B)). Qed.
Lemma lem4588387 {A B : Type'} : (term20 A B) = (term57 A B).
Proof. exact (MK_COMB (@lem4588380 A B) (@lem4588377 A B)). Qed.
Lemma lem4588396 {A B : Type'} (n : nat) (m : nat) : (term58 A B n m) = (term58 A B n m).
Proof. exact (eq_refl (term58 A B n m)). Qed.
Lemma lem4588397 {A B : Type'} (m : nat) : (term59 A B m) = (term59 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4588396 A B n m)). Qed.
Lemma lem4588398 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588399 {A B : Type'} (m : nat) : (term60 A B m) = (term60 A B m).
Proof. exact (MK_COMB (@lem4588398) (@lem4588397 A B m)). Qed.
Lemma lem4588400 {A B : Type'} : (term61 A B) = (term61 A B).
Proof. exact (fun_ext (fun m : nat => @lem4588399 A B m)). Qed.
Lemma lem4588401 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588402 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (MK_COMB (@lem4588401) (@lem4588400 A B)). Qed.
Lemma lem4588403 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4588404 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem4588403) (@lem4588402 A B)). Qed.
Lemma lem4588413 {B : Type'} (n : nat) (m : nat) : (term62 B n m) = (term62 B n m).
Proof. exact (eq_refl (term62 B n m)). Qed.
Lemma lem4588414 {B : Type'} (m : nat) : (term63 B m) = (term63 B m).
Proof. exact (fun_ext (fun n : nat => @lem4588413 B n m)). Qed.
Lemma lem4588415 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588416 {B : Type'} (m : nat) : (term64 B m) = (term64 B m).
Proof. exact (MK_COMB (@lem4588415) (@lem4588414 B m)). Qed.
Lemma lem4588417 {B : Type'} : (term65 B) = (term65 B).
Proof. exact (fun_ext (fun m : nat => @lem4588416 B m)). Qed.
Lemma lem4588418 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588419 {B : Type'} : (term12 B) = (term12 B).
Proof. exact (MK_COMB (@lem4588418) (@lem4588417 B)). Qed.
Lemma lem4588420 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588421 {B : Type'} : (term26 B) = (term26 B).
Proof. exact (MK_COMB (@lem4588420) (@lem4588419 B)). Qed.
Lemma lem4588422 {A B : Type'} : (term28 A B) = (term28 A B).
Proof. exact (MK_COMB (@lem4588421 B) (@lem4588404 A B)). Qed.
Lemma lem4588431 {A B : Type'} (n : nat) (m : nat) : (term66 A B n m) = (term66 A B n m).
Proof. exact (eq_refl (term66 A B n m)). Qed.
Lemma lem4588432 {A B : Type'} (m : nat) : (term67 A B m) = (term67 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4588431 A B n m)). Qed.
Lemma lem4588433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588434 {A B : Type'} (m : nat) : (term68 A B m) = (term68 A B m).
Proof. exact (MK_COMB (@lem4588433) (@lem4588432 A B m)). Qed.
Lemma lem4588435 {A B : Type'} : (term69 A B) = (term69 A B).
Proof. exact (fun_ext (fun m : nat => @lem4588434 A B m)). Qed.
Lemma lem4588436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588437 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem4588436) (@lem4588435 A B)). Qed.
Lemma lem4588438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588439 {A B : Type'} : (term29 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem4588438) (@lem4588437 A B)). Qed.
Lemma lem4588440 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem4588439 A B) (@lem4588422 A B)). Qed.
Lemma lem4588449 {A B : Type'} (n : nat) (m : nat) : (term70 A B n m) = (term70 A B n m).
Proof. exact (eq_refl (term70 A B n m)). Qed.
Lemma lem4588450 {A B : Type'} (m : nat) : (term71 A B m) = (term71 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4588449 A B n m)). Qed.
Lemma lem4588451 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588452 {A B : Type'} (m : nat) : (term72 A B m) = (term72 A B m).
Proof. exact (MK_COMB (@lem4588451) (@lem4588450 A B m)). Qed.
Lemma lem4588453 {A B : Type'} : (term73 A B) = (term73 A B).
Proof. exact (fun_ext (fun m : nat => @lem4588452 A B m)). Qed.
Lemma lem4588454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588455 {A B : Type'} : (term11 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem4588454) (@lem4588453 A B)). Qed.
Lemma lem4588456 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588457 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4588456) (@lem4588455 A B)). Qed.
Lemma lem4588458 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem4588457 A B) (@lem4588440 A B)). Qed.
Lemma lem4588467 {A : Type'} (n : nat) (m : nat) : (term62 A n m) = (term62 A n m).
Proof. exact (eq_refl (term62 A n m)). Qed.
Lemma lem4588468 {A : Type'} (m : nat) : (term63 A m) = (term63 A m).
Proof. exact (fun_ext (fun n : nat => @lem4588467 A n m)). Qed.
Lemma lem4588469 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588470 {A : Type'} (m : nat) : (term64 A m) = (term64 A m).
Proof. exact (MK_COMB (@lem4588469) (@lem4588468 A m)). Qed.
Lemma lem4588471 {A : Type'} : (term65 A) = (term65 A).
Proof. exact (fun_ext (fun m : nat => @lem4588470 A m)). Qed.
Lemma lem4588472 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588473 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem4588472) (@lem4588471 A)). Qed.
Lemma lem4588474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588475 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem4588474) (@lem4588473 A)). Qed.
Lemma lem4588476 {A B : Type'} : (term36 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem4588475 A) (@lem4588458 A B)). Qed.
Lemma lem4588485 {A B : Type'} (s : type119 A B) (n : nat) : ((@HAS_SIZE ((A -> B) -> B) s n) = (term74 A B s n)) = ((@HAS_SIZE ((A -> B) -> B) s n) = (term74 A B s n)).
Proof. exact (eq_refl ((@HAS_SIZE ((A -> B) -> B) s n) = (term74 A B s n))). Qed.
Lemma lem4588486 {A B : Type'} (s : type119 A B) : (term75 A B s) = (term75 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4588485 A B s n)). Qed.
Lemma lem4588487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588488 {A B : Type'} (s : type119 A B) : (term76 A B s) = (term76 A B s).
Proof. exact (MK_COMB (@lem4588487) (@lem4588486 A B s)). Qed.
Lemma lem4588489 {A B : Type'} : (term77 A B) = (term77 A B).
Proof. exact (fun_ext (fun s : type119 A B => @lem4588488 A B s)). Qed.
Lemma lem4588490 {A B : Type'} : (@all (((A -> B) -> B) -> Prop)) = (@all (((A -> B) -> B) -> Prop)).
Proof. exact (eq_refl (@all (((A -> B) -> B) -> Prop))). Qed.
Lemma lem4588491 {A B : Type'} : (term17 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem4588490 A B) (@lem4588489 A B)). Qed.
Lemma lem4588492 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588493 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (MK_COMB (@lem4588492) (@lem4588491 A B)). Qed.
Lemma lem4588494 {A B : Type'} : (term39 A B) = (term39 A B).
Proof. exact (MK_COMB (@lem4588493 A B) (@lem4588476 A B)). Qed.
Lemma lem4588503 {B : Type'} (s : type488 B) (n : nat) : ((@HAS_SIZE (B -> B) s n) = (term78 B s n)) = ((@HAS_SIZE (B -> B) s n) = (term78 B s n)).
Proof. exact (eq_refl ((@HAS_SIZE (B -> B) s n) = (term78 B s n))). Qed.
Lemma lem4588504 {B : Type'} (s : type488 B) : (term79 B s) = (term79 B s).
Proof. exact (fun_ext (fun n : nat => @lem4588503 B s n)). Qed.
Lemma lem4588505 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588506 {B : Type'} (s : type488 B) : (term80 B s) = (term80 B s).
Proof. exact (MK_COMB (@lem4588505) (@lem4588504 B s)). Qed.
Lemma lem4588507 {B : Type'} : (term81 B) = (term81 B).
Proof. exact (fun_ext (fun s : type488 B => @lem4588506 B s)). Qed.
Lemma lem4588508 {B : Type'} : (@all ((B -> B) -> Prop)) = (@all ((B -> B) -> Prop)).
Proof. exact (eq_refl (@all ((B -> B) -> Prop))). Qed.
Lemma lem4588509 {B : Type'} : (term18 B) = (term18 B).
Proof. exact (MK_COMB (@lem4588508 B) (@lem4588507 B)). Qed.
Lemma lem4588510 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588511 {B : Type'} : (term40 B) = (term40 B).
Proof. exact (MK_COMB (@lem4588510) (@lem4588509 B)). Qed.
Lemma lem4588512 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem4588511 B) (@lem4588494 A B)). Qed.
Lemma lem4588521 {A B : Type'} (s : type404 A B) (n : nat) : ((@HAS_SIZE (A -> A -> B) s n) = (term82 A B s n)) = ((@HAS_SIZE (A -> A -> B) s n) = (term82 A B s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> A -> B) s n) = (term82 A B s n))). Qed.
Lemma lem4588522 {A B : Type'} (s : type404 A B) : (term83 A B s) = (term83 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4588521 A B s n)). Qed.
Lemma lem4588523 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588524 {A B : Type'} (s : type404 A B) : (term84 A B s) = (term84 A B s).
Proof. exact (MK_COMB (@lem4588523) (@lem4588522 A B s)). Qed.
Lemma lem4588525 {A B : Type'} : (term85 A B) = (term85 A B).
Proof. exact (fun_ext (fun s : type404 A B => @lem4588524 A B s)). Qed.
Lemma lem4588526 {A B : Type'} : (@all ((A -> A -> B) -> Prop)) = (@all ((A -> A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> B) -> Prop))). Qed.
Lemma lem4588527 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem4588526 A B) (@lem4588525 A B)). Qed.
Lemma lem4588528 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588529 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem4588528) (@lem4588527 A B)). Qed.
Lemma lem4588530 {A B : Type'} : (term45 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem4588529 A B) (@lem4588512 A B)). Qed.
Lemma lem4588539 {A B : Type'} (s : type572 A B) (n : nat) : ((@HAS_SIZE (A -> B) s n) = (term86 A B s n)) = ((@HAS_SIZE (A -> B) s n) = (term86 A B s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> B) s n) = (term86 A B s n))). Qed.
Lemma lem4588540 {A B : Type'} (s : type572 A B) : (term87 A B s) = (term87 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4588539 A B s n)). Qed.
Lemma lem4588541 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588542 {A B : Type'} (s : type572 A B) : (term88 A B s) = (term88 A B s).
Proof. exact (MK_COMB (@lem4588541) (@lem4588540 A B s)). Qed.
Lemma lem4588543 {A B : Type'} : (term89 A B) = (term89 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4588542 A B s)). Qed.
Lemma lem4588544 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4588545 {A B : Type'} : (term15 A B) = (term15 A B).
Proof. exact (MK_COMB (@lem4588544 A B) (@lem4588543 A B)). Qed.
Lemma lem4588546 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588547 {A B : Type'} : (term46 A B) = (term46 A B).
Proof. exact (MK_COMB (@lem4588546) (@lem4588545 A B)). Qed.
Lemma lem4588548 {A B : Type'} : (term48 A B) = (term48 A B).
Proof. exact (MK_COMB (@lem4588547 A B) (@lem4588530 A B)). Qed.
Lemma lem4588557 {A : Type'} (s : type488 A) (n : nat) : ((@HAS_SIZE (A -> A) s n) = (term78 A s n)) = ((@HAS_SIZE (A -> A) s n) = (term78 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> A) s n) = (term78 A s n))). Qed.
Lemma lem4588558 {A : Type'} (s : type488 A) : (term79 A s) = (term79 A s).
Proof. exact (fun_ext (fun n : nat => @lem4588557 A s n)). Qed.
Lemma lem4588559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588560 {A : Type'} (s : type488 A) : (term80 A s) = (term80 A s).
Proof. exact (MK_COMB (@lem4588559) (@lem4588558 A s)). Qed.
Lemma lem4588561 {A : Type'} : (term81 A) = (term81 A).
Proof. exact (fun_ext (fun s : type488 A => @lem4588560 A s)). Qed.
Lemma lem4588562 {A : Type'} : (@all ((A -> A) -> Prop)) = (@all ((A -> A) -> Prop)).
Proof. exact (eq_refl (@all ((A -> A) -> Prop))). Qed.
Lemma lem4588563 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem4588562 A) (@lem4588561 A)). Qed.
Lemma lem4588564 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588565 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem4588564) (@lem4588563 A)). Qed.
Lemma lem4588566 {A B : Type'} : (term50 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem4588565 A) (@lem4588548 A B)). Qed.
Lemma lem4588575 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term90 B s n)) = ((@HAS_SIZE B s n) = (term90 B s n)).
Proof. exact (eq_refl ((@HAS_SIZE B s n) = (term90 B s n))). Qed.
Lemma lem4588576 {B : Type'} (s : B -> Prop) : (term91 B s) = (term91 B s).
Proof. exact (fun_ext (fun n : nat => @lem4588575 B s n)). Qed.
Lemma lem4588577 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588578 {B : Type'} (s : B -> Prop) : (term92 B s) = (term92 B s).
Proof. exact (MK_COMB (@lem4588577) (@lem4588576 B s)). Qed.
Lemma lem4588579 {B : Type'} : (term93 B) = (term93 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4588578 B s)). Qed.
Lemma lem4588580 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4588581 {B : Type'} : (term16 B) = (term16 B).
Proof. exact (MK_COMB (@lem4588580 B) (@lem4588579 B)). Qed.
Lemma lem4588582 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588583 {B : Type'} : (term51 B) = (term51 B).
Proof. exact (MK_COMB (@lem4588582) (@lem4588581 B)). Qed.
Lemma lem4588584 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem4588583 B) (@lem4588566 A B)). Qed.
Lemma lem4588593 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term90 A s n)) = ((@HAS_SIZE A s n) = (term90 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term90 A s n))). Qed.
Lemma lem4588594 {A : Type'} (s : A -> Prop) : (term91 A s) = (term91 A s).
Proof. exact (fun_ext (fun n : nat => @lem4588593 A s n)). Qed.
Lemma lem4588595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588596 {A : Type'} (s : A -> Prop) : (term92 A s) = (term92 A s).
Proof. exact (MK_COMB (@lem4588595) (@lem4588594 A s)). Qed.
Lemma lem4588597 {A : Type'} : (term93 A) = (term93 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4588596 A s)). Qed.
Lemma lem4588598 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4588599 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4588598 A) (@lem4588597 A)). Qed.
Lemma lem4588600 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588601 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (MK_COMB (@lem4588600) (@lem4588599 A)). Qed.
Lemma lem4588602 {A B : Type'} : (term55 A B) = (term55 A B).
Proof. exact (MK_COMB (@lem4588601 A) (@lem4588584 A B)). Qed.
Lemma lem4588615 {A B : Type'} : (term56 A B) = (term56 A B).
Proof. exact (eq_refl (term56 A B)). Qed.
Lemma lem4588616 {A B : Type'} : (term57 A B) = (term57 A B).
Proof. exact (MK_COMB (@lem4588615 A B) (@lem4588602 A B)). Qed.
Lemma lem4588825 {A B : Type'} : (term20 A B) = (term57 A B).
Proof. exact (TRANS (@lem4588387 A B) (@lem4588616 A B)). Qed.
Lemma lem4588826 {A B : Type'} : (term57 A B) = (term20 A B).
Proof. exact (SYM (@lem4588825 A B)). Qed.
Lemma lem4588827 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem4588828 {A : Type'} (h1 : term16 A) : term16 A.
Proof. exact (h1). Qed.
Lemma lem4588829 {B : Type'} (h1 : term16 B) : term16 B.
Proof. exact (h1). Qed.
Lemma lem4588831 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem4588836 {A B : Type'} (h1 : term11 A B) : term11 A B.
Proof. exact (h1). Qed.
Lemma lem4588854 {A B : Type'} : (term10 A B) = (term94 A B).
Proof. exact (@lem17362 (term95 A B) (@FINITE (A -> B) (@UNIV (A -> B)))). Qed.
Lemma lem4588866 {A : Type'} (s : A -> Prop) (n : nat) : (term96 A s n) = (term97 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem4588872 {A : Type'} (s : A -> Prop) (n : nat) : (term98 A s n) = (term98 A s n).
Proof. exact (eq_refl (term98 A s n)). Qed.
Lemma lem4588874 {A : Type'} (s : A -> Prop) (n : nat) : (term99 A s n) = (term99 A s n).
Proof. exact (eq_refl (term99 A s n)). Qed.
Lemma lem4588875 {A : Type'} (s : A -> Prop) (n : nat) : (term100 A s n) = (term101 A s n).
Proof. exact (MK_COMB (@lem4588874 A s n) (@lem4588866 A s n)). Qed.
Lemma lem4588876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4588877 {A : Type'} (s : A -> Prop) (n : nat) : (term102 A s n) = (term103 A s n).
Proof. exact (MK_COMB (@lem4588876) (@lem4588875 A s n)). Qed.
Lemma lem4588878 {A : Type'} (s : A -> Prop) (n : nat) : (term104 A s n) = (term105 A s n).
Proof. exact (MK_COMB (@lem4588877 A s n) (@lem4588872 A s n)). Qed.
Lemma lem4588879 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term90 A s n)) = (term104 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term90 A s n)). Qed.
Lemma lem4588880 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term90 A s n)) = (term105 A s n).
Proof. exact (TRANS (@lem4588879 A s n) (@lem4588878 A s n)). Qed.
Lemma lem4588881 {A : Type'} (s : A -> Prop) : (term91 A s) = (term106 A s).
Proof. exact (fun_ext (fun n : nat => @lem4588880 A s n)). Qed.
Lemma lem4588882 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588883 {A : Type'} (s : A -> Prop) : (term92 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem4588882) (@lem4588881 A s)). Qed.
Lemma lem4588884 {A : Type'} : (term93 A) = (term108 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4588883 A s)). Qed.
Lemma lem4588885 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4588886 {A : Type'} : (term16 A) = (term109 A).
Proof. exact (MK_COMB (@lem4588885 A) (@lem4588884 A)). Qed.
Lemma lem4588892 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4588893 (P : nat -> Prop) (Q : nat -> Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem4588892 nat P Q). Qed.
Lemma lem4588894 {A : Type'} (s : A -> Prop) : (term114 A s) = (term115 A s).
Proof. exact (@lem4588893 (term116 A s) (term117 A s)). Qed.
Lemma lem4588895 {A : Type'} (s : A -> Prop) (n : nat) : (term118 A s n) = (term101 A s n).
Proof. exact (eq_refl (term118 A s n)). Qed.
Lemma lem4588896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4588897 {A : Type'} (s : A -> Prop) (n : nat) : (term119 A s n) = (term103 A s n).
Proof. exact (MK_COMB (@lem4588896) (@lem4588895 A s n)). Qed.
Lemma lem4588898 {A : Type'} (s : A -> Prop) (n : nat) : (term120 A s n) = (term98 A s n).
Proof. exact (eq_refl (term120 A s n)). Qed.
Lemma lem4588899 {A : Type'} (s : A -> Prop) (n : nat) : (term121 A s n) = (term105 A s n).
Proof. exact (MK_COMB (@lem4588897 A s n) (@lem4588898 A s n)). Qed.
Lemma lem4588900 {A : Type'} (s : A -> Prop) : (term122 A s) = (term106 A s).
Proof. exact (fun_ext (fun n : nat => @lem4588899 A s n)). Qed.
Lemma lem4588901 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588902 {A : Type'} (s : A -> Prop) : (term114 A s) = (term107 A s).
Proof. exact (MK_COMB (@lem4588901) (@lem4588900 A s)). Qed.
Lemma lem4588903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4588904 {A : Type'} (s : A -> Prop) : (term123 A s) = (term124 A s).
Proof. exact (MK_COMB (@lem4588903) (@lem4588902 A s)). Qed.
Lemma lem4588905 {A : Type'} (s : A -> Prop) (n : nat) : (term118 A s n) = (term101 A s n).
Proof. exact (eq_refl (term118 A s n)). Qed.
Lemma lem4588906 {A : Type'} (s : A -> Prop) : (term125 A s) = (term116 A s).
Proof. exact (fun_ext (fun n : nat => @lem4588905 A s n)). Qed.
Lemma lem4588907 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588908 {A : Type'} (s : A -> Prop) : (term126 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem4588907) (@lem4588906 A s)). Qed.
Lemma lem4588909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4588910 {A : Type'} (s : A -> Prop) : (term128 A s) = (term129 A s).
Proof. exact (MK_COMB (@lem4588909) (@lem4588908 A s)). Qed.
Lemma lem4588911 {A : Type'} (s : A -> Prop) (n : nat) : (term120 A s n) = (term98 A s n).
Proof. exact (eq_refl (term120 A s n)). Qed.
Lemma lem4588912 {A : Type'} (s : A -> Prop) : (term130 A s) = (term117 A s).
Proof. exact (fun_ext (fun n : nat => @lem4588911 A s n)). Qed.
Lemma lem4588913 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4588914 {A : Type'} (s : A -> Prop) : (term131 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem4588913) (@lem4588912 A s)). Qed.
Lemma lem4588915 {A : Type'} (s : A -> Prop) : (term115 A s) = (term133 A s).
Proof. exact (MK_COMB (@lem4588910 A s) (@lem4588914 A s)). Qed.
Lemma lem4588916 {A : Type'} (s : A -> Prop) : ((term114 A s) = (term115 A s)) = ((term107 A s) = (term133 A s)).
Proof. exact (MK_COMB (@lem4588904 A s) (@lem4588915 A s)). Qed.
Lemma lem4588917 {A : Type'} (s : A -> Prop) : (term107 A s) = (term133 A s).
Proof. exact (EQ_MP (@lem4588916 A s) (@lem4588894 A s)). Qed.
Lemma lem4589014 {A : Type'} : (term108 A) = (term134 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4588917 A s)). Qed.
Lemma lem4589015 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4589016 {A : Type'} : (term109 A) = (term135 A).
Proof. exact (MK_COMB (@lem4589015 A) (@lem4589014 A)). Qed.
Lemma lem4589018 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4589019 {A : Type'} (P : type686 A) (Q : type686 A) : (term136 A P Q) = (term137 A P Q).
Proof. exact (@lem4589018 (A -> Prop) P Q). Qed.
Lemma lem4589020 {A : Type'} : (term138 A) = (term139 A).
Proof. exact (@lem4589019 A (term140 A) (term141 A)). Qed.
Lemma lem4589021 {A : Type'} (s : A -> Prop) : (term142 A s) = (term127 A s).
Proof. exact (eq_refl (term142 A s)). Qed.
Lemma lem4589022 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589023 {A : Type'} (s : A -> Prop) : (term143 A s) = (term129 A s).
Proof. exact (MK_COMB (@lem4589022) (@lem4589021 A s)). Qed.
Lemma lem4589024 {A : Type'} (s : A -> Prop) : (term144 A s) = (term132 A s).
Proof. exact (eq_refl (term144 A s)). Qed.
Lemma lem4589025 {A : Type'} (s : A -> Prop) : (term145 A s) = (term133 A s).
Proof. exact (MK_COMB (@lem4589023 A s) (@lem4589024 A s)). Qed.
Lemma lem4589026 {A : Type'} : (term146 A) = (term134 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4589025 A s)). Qed.
Lemma lem4589027 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4589028 {A : Type'} : (term138 A) = (term135 A).
Proof. exact (MK_COMB (@lem4589027 A) (@lem4589026 A)). Qed.
Lemma lem4589029 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4589030 {A : Type'} : (term147 A) = (term148 A).
Proof. exact (MK_COMB (@lem4589029) (@lem4589028 A)). Qed.
Lemma lem4589031 {A : Type'} (s : A -> Prop) : (term142 A s) = (term127 A s).
Proof. exact (eq_refl (term142 A s)). Qed.
Lemma lem4589032 {A : Type'} : (term149 A) = (term140 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4589031 A s)). Qed.
Lemma lem4589033 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4589034 {A : Type'} : (term150 A) = (term151 A).
Proof. exact (MK_COMB (@lem4589033 A) (@lem4589032 A)). Qed.
Lemma lem4589035 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589036 {A : Type'} : (term152 A) = (term153 A).
Proof. exact (MK_COMB (@lem4589035) (@lem4589034 A)). Qed.
Lemma lem4589037 {A : Type'} (s : A -> Prop) : (term144 A s) = (term132 A s).
Proof. exact (eq_refl (term144 A s)). Qed.
Lemma lem4589038 {A : Type'} : (term154 A) = (term141 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4589037 A s)). Qed.
Lemma lem4589039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4589040 {A : Type'} : (term155 A) = (term156 A).
Proof. exact (MK_COMB (@lem4589039 A) (@lem4589038 A)). Qed.
Lemma lem4589041 {A : Type'} : (term139 A) = (term157 A).
Proof. exact (MK_COMB (@lem4589036 A) (@lem4589040 A)). Qed.
Lemma lem4589042 {A : Type'} : ((term138 A) = (term139 A)) = ((term135 A) = (term157 A)).
Proof. exact (MK_COMB (@lem4589030 A) (@lem4589041 A)). Qed.
Lemma lem4589043 {A : Type'} : (term135 A) = (term157 A).
Proof. exact (EQ_MP (@lem4589042 A) (@lem4589020 A)). Qed.
Lemma lem4589150 {A : Type'} : (term109 A) = (term157 A).
Proof. exact (TRANS (@lem4589016 A) (@lem4589043 A)). Qed.
Lemma lem4589151 {A : Type'} : (term16 A) = (term157 A).
Proof. exact (TRANS (@lem4588886 A) (@lem4589150 A)). Qed.
Lemma lem4589152 {A : Type'} (h1 : term16 A) : term157 A.
Proof. exact (EQ_MP (@lem4589151 A) (@lem4588828 A h1)). Qed.
Lemma lem4589163 {B : Type'} (s : B -> Prop) (n : nat) : (term96 B s n) = (term97 B s n).
Proof. exact (@lem17045 (@FINITE B s) ((@CARD B s) = n)). Qed.
Lemma lem4589169 {B : Type'} (s : B -> Prop) (n : nat) : (term98 B s n) = (term98 B s n).
Proof. exact (eq_refl (term98 B s n)). Qed.
Lemma lem4589171 {B : Type'} (s : B -> Prop) (n : nat) : (term99 B s n) = (term99 B s n).
Proof. exact (eq_refl (term99 B s n)). Qed.
Lemma lem4589172 {B : Type'} (s : B -> Prop) (n : nat) : (term100 B s n) = (term101 B s n).
Proof. exact (MK_COMB (@lem4589171 B s n) (@lem4589163 B s n)). Qed.
Lemma lem4589173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589174 {B : Type'} (s : B -> Prop) (n : nat) : (term102 B s n) = (term103 B s n).
Proof. exact (MK_COMB (@lem4589173) (@lem4589172 B s n)). Qed.
Lemma lem4589175 {B : Type'} (s : B -> Prop) (n : nat) : (term104 B s n) = (term105 B s n).
Proof. exact (MK_COMB (@lem4589174 B s n) (@lem4589169 B s n)). Qed.
Lemma lem4589176 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term90 B s n)) = (term104 B s n).
Proof. exact (@lem17784 (@HAS_SIZE B s n) (term90 B s n)). Qed.
Lemma lem4589177 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term90 B s n)) = (term105 B s n).
Proof. exact (TRANS (@lem4589176 B s n) (@lem4589175 B s n)). Qed.
Lemma lem4589178 {B : Type'} (s : B -> Prop) : (term91 B s) = (term106 B s).
Proof. exact (fun_ext (fun n : nat => @lem4589177 B s n)). Qed.
Lemma lem4589179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589180 {B : Type'} (s : B -> Prop) : (term92 B s) = (term107 B s).
Proof. exact (MK_COMB (@lem4589179) (@lem4589178 B s)). Qed.
Lemma lem4589181 {B : Type'} : (term93 B) = (term108 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4589180 B s)). Qed.
Lemma lem4589182 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4589183 {B : Type'} : (term16 B) = (term109 B).
Proof. exact (MK_COMB (@lem4589182 B) (@lem4589181 B)). Qed.
Lemma lem4589189 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4589190 (P : nat -> Prop) (Q : nat -> Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem4589189 nat P Q). Qed.
Lemma lem4589191 {B : Type'} (s : B -> Prop) : (term114 B s) = (term115 B s).
Proof. exact (@lem4589190 (term116 B s) (term117 B s)). Qed.
Lemma lem4589192 {B : Type'} (s : B -> Prop) (n : nat) : (term118 B s n) = (term101 B s n).
Proof. exact (eq_refl (term118 B s n)). Qed.
Lemma lem4589193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589194 {B : Type'} (s : B -> Prop) (n : nat) : (term119 B s n) = (term103 B s n).
Proof. exact (MK_COMB (@lem4589193) (@lem4589192 B s n)). Qed.
Lemma lem4589195 {B : Type'} (s : B -> Prop) (n : nat) : (term120 B s n) = (term98 B s n).
Proof. exact (eq_refl (term120 B s n)). Qed.
Lemma lem4589196 {B : Type'} (s : B -> Prop) (n : nat) : (term121 B s n) = (term105 B s n).
Proof. exact (MK_COMB (@lem4589194 B s n) (@lem4589195 B s n)). Qed.
Lemma lem4589197 {B : Type'} (s : B -> Prop) : (term122 B s) = (term106 B s).
Proof. exact (fun_ext (fun n : nat => @lem4589196 B s n)). Qed.
Lemma lem4589198 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589199 {B : Type'} (s : B -> Prop) : (term114 B s) = (term107 B s).
Proof. exact (MK_COMB (@lem4589198) (@lem4589197 B s)). Qed.
Lemma lem4589200 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4589201 {B : Type'} (s : B -> Prop) : (term123 B s) = (term124 B s).
Proof. exact (MK_COMB (@lem4589200) (@lem4589199 B s)). Qed.
Lemma lem4589202 {B : Type'} (s : B -> Prop) (n : nat) : (term118 B s n) = (term101 B s n).
Proof. exact (eq_refl (term118 B s n)). Qed.
Lemma lem4589203 {B : Type'} (s : B -> Prop) : (term125 B s) = (term116 B s).
Proof. exact (fun_ext (fun n : nat => @lem4589202 B s n)). Qed.
Lemma lem4589204 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589205 {B : Type'} (s : B -> Prop) : (term126 B s) = (term127 B s).
Proof. exact (MK_COMB (@lem4589204) (@lem4589203 B s)). Qed.
Lemma lem4589206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589207 {B : Type'} (s : B -> Prop) : (term128 B s) = (term129 B s).
Proof. exact (MK_COMB (@lem4589206) (@lem4589205 B s)). Qed.
Lemma lem4589208 {B : Type'} (s : B -> Prop) (n : nat) : (term120 B s n) = (term98 B s n).
Proof. exact (eq_refl (term120 B s n)). Qed.
Lemma lem4589209 {B : Type'} (s : B -> Prop) : (term130 B s) = (term117 B s).
Proof. exact (fun_ext (fun n : nat => @lem4589208 B s n)). Qed.
Lemma lem4589210 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589211 {B : Type'} (s : B -> Prop) : (term131 B s) = (term132 B s).
Proof. exact (MK_COMB (@lem4589210) (@lem4589209 B s)). Qed.
Lemma lem4589212 {B : Type'} (s : B -> Prop) : (term115 B s) = (term133 B s).
Proof. exact (MK_COMB (@lem4589207 B s) (@lem4589211 B s)). Qed.
Lemma lem4589213 {B : Type'} (s : B -> Prop) : ((term114 B s) = (term115 B s)) = ((term107 B s) = (term133 B s)).
Proof. exact (MK_COMB (@lem4589201 B s) (@lem4589212 B s)). Qed.
Lemma lem4589214 {B : Type'} (s : B -> Prop) : (term107 B s) = (term133 B s).
Proof. exact (EQ_MP (@lem4589213 B s) (@lem4589191 B s)). Qed.
Lemma lem4589311 {B : Type'} : (term108 B) = (term134 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4589214 B s)). Qed.
Lemma lem4589312 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4589313 {B : Type'} : (term109 B) = (term135 B).
Proof. exact (MK_COMB (@lem4589312 B) (@lem4589311 B)). Qed.
Lemma lem4589315 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4589316 {B : Type'} (P : type686 B) (Q : type686 B) : (term136 B P Q) = (term137 B P Q).
Proof. exact (@lem4589315 (B -> Prop) P Q). Qed.
Lemma lem4589317 {B : Type'} : (term138 B) = (term139 B).
Proof. exact (@lem4589316 B (term140 B) (term141 B)). Qed.
Lemma lem4589318 {B : Type'} (s : B -> Prop) : (term142 B s) = (term127 B s).
Proof. exact (eq_refl (term142 B s)). Qed.
Lemma lem4589319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589320 {B : Type'} (s : B -> Prop) : (term143 B s) = (term129 B s).
Proof. exact (MK_COMB (@lem4589319) (@lem4589318 B s)). Qed.
Lemma lem4589321 {B : Type'} (s : B -> Prop) : (term144 B s) = (term132 B s).
Proof. exact (eq_refl (term144 B s)). Qed.
Lemma lem4589322 {B : Type'} (s : B -> Prop) : (term145 B s) = (term133 B s).
Proof. exact (MK_COMB (@lem4589320 B s) (@lem4589321 B s)). Qed.
Lemma lem4589323 {B : Type'} : (term146 B) = (term134 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4589322 B s)). Qed.
Lemma lem4589324 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4589325 {B : Type'} : (term138 B) = (term135 B).
Proof. exact (MK_COMB (@lem4589324 B) (@lem4589323 B)). Qed.
Lemma lem4589326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4589327 {B : Type'} : (term147 B) = (term148 B).
Proof. exact (MK_COMB (@lem4589326) (@lem4589325 B)). Qed.
Lemma lem4589328 {B : Type'} (s : B -> Prop) : (term142 B s) = (term127 B s).
Proof. exact (eq_refl (term142 B s)). Qed.
Lemma lem4589329 {B : Type'} : (term149 B) = (term140 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4589328 B s)). Qed.
Lemma lem4589330 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4589331 {B : Type'} : (term150 B) = (term151 B).
Proof. exact (MK_COMB (@lem4589330 B) (@lem4589329 B)). Qed.
Lemma lem4589332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589333 {B : Type'} : (term152 B) = (term153 B).
Proof. exact (MK_COMB (@lem4589332) (@lem4589331 B)). Qed.
Lemma lem4589334 {B : Type'} (s : B -> Prop) : (term144 B s) = (term132 B s).
Proof. exact (eq_refl (term144 B s)). Qed.
Lemma lem4589335 {B : Type'} : (term154 B) = (term141 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4589334 B s)). Qed.
Lemma lem4589336 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4589337 {B : Type'} : (term155 B) = (term156 B).
Proof. exact (MK_COMB (@lem4589336 B) (@lem4589335 B)). Qed.
Lemma lem4589338 {B : Type'} : (term139 B) = (term157 B).
Proof. exact (MK_COMB (@lem4589333 B) (@lem4589337 B)). Qed.
Lemma lem4589339 {B : Type'} : ((term138 B) = (term139 B)) = ((term135 B) = (term157 B)).
Proof. exact (MK_COMB (@lem4589327 B) (@lem4589338 B)). Qed.
Lemma lem4589340 {B : Type'} : (term135 B) = (term157 B).
Proof. exact (EQ_MP (@lem4589339 B) (@lem4589317 B)). Qed.
Lemma lem4589447 {B : Type'} : (term109 B) = (term157 B).
Proof. exact (TRANS (@lem4589313 B) (@lem4589340 B)). Qed.
Lemma lem4589448 {B : Type'} : (term16 B) = (term157 B).
Proof. exact (TRANS (@lem4589183 B) (@lem4589447 B)). Qed.
Lemma lem4589449 {B : Type'} (h1 : term16 B) : term157 B.
Proof. exact (EQ_MP (@lem4589448 B) (@lem4588829 B h1)). Qed.
Lemma lem4589757 {A B : Type'} (s : type572 A B) (n : nat) : (term158 A B s n) = (term159 A B s n).
Proof. exact (@lem17045 (@FINITE (A -> B) s) ((@CARD (A -> B) s) = n)). Qed.
Lemma lem4589763 {A B : Type'} (s : type572 A B) (n : nat) : (term160 A B s n) = (term160 A B s n).
Proof. exact (eq_refl (term160 A B s n)). Qed.
Lemma lem4589765 {A B : Type'} (s : type572 A B) (n : nat) : (term161 A B s n) = (term161 A B s n).
Proof. exact (eq_refl (term161 A B s n)). Qed.
Lemma lem4589766 {A B : Type'} (s : type572 A B) (n : nat) : (term162 A B s n) = (term163 A B s n).
Proof. exact (MK_COMB (@lem4589765 A B s n) (@lem4589757 A B s n)). Qed.
Lemma lem4589767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589768 {A B : Type'} (s : type572 A B) (n : nat) : (term164 A B s n) = (term165 A B s n).
Proof. exact (MK_COMB (@lem4589767) (@lem4589766 A B s n)). Qed.
Lemma lem4589769 {A B : Type'} (s : type572 A B) (n : nat) : (term166 A B s n) = (term167 A B s n).
Proof. exact (MK_COMB (@lem4589768 A B s n) (@lem4589763 A B s n)). Qed.
Lemma lem4589770 {A B : Type'} (s : type572 A B) (n : nat) : ((@HAS_SIZE (A -> B) s n) = (term86 A B s n)) = (term166 A B s n).
Proof. exact (@lem17784 (@HAS_SIZE (A -> B) s n) (term86 A B s n)). Qed.
Lemma lem4589771 {A B : Type'} (s : type572 A B) (n : nat) : ((@HAS_SIZE (A -> B) s n) = (term86 A B s n)) = (term167 A B s n).
Proof. exact (TRANS (@lem4589770 A B s n) (@lem4589769 A B s n)). Qed.
Lemma lem4589772 {A B : Type'} (s : type572 A B) : (term87 A B s) = (term168 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4589771 A B s n)). Qed.
Lemma lem4589773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589774 {A B : Type'} (s : type572 A B) : (term88 A B s) = (term169 A B s).
Proof. exact (MK_COMB (@lem4589773) (@lem4589772 A B s)). Qed.
Lemma lem4589775 {A B : Type'} : (term89 A B) = (term170 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4589774 A B s)). Qed.
Lemma lem4589776 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4589777 {A B : Type'} : (term15 A B) = (term171 A B).
Proof. exact (MK_COMB (@lem4589776 A B) (@lem4589775 A B)). Qed.
Lemma lem4589783 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4589784 (P : nat -> Prop) (Q : nat -> Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem4589783 nat P Q). Qed.
Lemma lem4589785 {A B : Type'} (s : type572 A B) : (term172 A B s) = (term173 A B s).
Proof. exact (@lem4589784 (term174 A B s) (term175 A B s)). Qed.
Lemma lem4589786 {A B : Type'} (s : type572 A B) (n : nat) : (term176 A B s n) = (term163 A B s n).
Proof. exact (eq_refl (term176 A B s n)). Qed.
Lemma lem4589787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589788 {A B : Type'} (s : type572 A B) (n : nat) : (term177 A B s n) = (term165 A B s n).
Proof. exact (MK_COMB (@lem4589787) (@lem4589786 A B s n)). Qed.
Lemma lem4589789 {A B : Type'} (s : type572 A B) (n : nat) : (term178 A B s n) = (term160 A B s n).
Proof. exact (eq_refl (term178 A B s n)). Qed.
Lemma lem4589790 {A B : Type'} (s : type572 A B) (n : nat) : (term179 A B s n) = (term167 A B s n).
Proof. exact (MK_COMB (@lem4589788 A B s n) (@lem4589789 A B s n)). Qed.
Lemma lem4589791 {A B : Type'} (s : type572 A B) : (term180 A B s) = (term168 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4589790 A B s n)). Qed.
Lemma lem4589792 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589793 {A B : Type'} (s : type572 A B) : (term172 A B s) = (term169 A B s).
Proof. exact (MK_COMB (@lem4589792) (@lem4589791 A B s)). Qed.
Lemma lem4589794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4589795 {A B : Type'} (s : type572 A B) : (term181 A B s) = (term182 A B s).
Proof. exact (MK_COMB (@lem4589794) (@lem4589793 A B s)). Qed.
Lemma lem4589796 {A B : Type'} (s : type572 A B) (n : nat) : (term176 A B s n) = (term163 A B s n).
Proof. exact (eq_refl (term176 A B s n)). Qed.
Lemma lem4589797 {A B : Type'} (s : type572 A B) : (term183 A B s) = (term174 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4589796 A B s n)). Qed.
Lemma lem4589798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589799 {A B : Type'} (s : type572 A B) : (term184 A B s) = (term185 A B s).
Proof. exact (MK_COMB (@lem4589798) (@lem4589797 A B s)). Qed.
Lemma lem4589800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589801 {A B : Type'} (s : type572 A B) : (term186 A B s) = (term187 A B s).
Proof. exact (MK_COMB (@lem4589800) (@lem4589799 A B s)). Qed.
Lemma lem4589802 {A B : Type'} (s : type572 A B) (n : nat) : (term178 A B s n) = (term160 A B s n).
Proof. exact (eq_refl (term178 A B s n)). Qed.
Lemma lem4589803 {A B : Type'} (s : type572 A B) : (term188 A B s) = (term175 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4589802 A B s n)). Qed.
Lemma lem4589804 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4589805 {A B : Type'} (s : type572 A B) : (term189 A B s) = (term190 A B s).
Proof. exact (MK_COMB (@lem4589804) (@lem4589803 A B s)). Qed.
Lemma lem4589806 {A B : Type'} (s : type572 A B) : (term173 A B s) = (term191 A B s).
Proof. exact (MK_COMB (@lem4589801 A B s) (@lem4589805 A B s)). Qed.
Lemma lem4589807 {A B : Type'} (s : type572 A B) : ((term172 A B s) = (term173 A B s)) = ((term169 A B s) = (term191 A B s)).
Proof. exact (MK_COMB (@lem4589795 A B s) (@lem4589806 A B s)). Qed.
Lemma lem4589808 {A B : Type'} (s : type572 A B) : (term169 A B s) = (term191 A B s).
Proof. exact (EQ_MP (@lem4589807 A B s) (@lem4589785 A B s)). Qed.
Lemma lem4589905 {A B : Type'} : (term170 A B) = (term192 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4589808 A B s)). Qed.
Lemma lem4589906 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4589907 {A B : Type'} : (term171 A B) = (term193 A B).
Proof. exact (MK_COMB (@lem4589906 A B) (@lem4589905 A B)). Qed.
Lemma lem4589909 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4589910 {A B : Type'} (P : type122 A B) (Q : type122 A B) : (term194 A B P Q) = (term195 A B P Q).
Proof. exact (@lem4589909 (type572 A B) P Q). Qed.
Lemma lem4589911 {A B : Type'} : (term196 A B) = (term197 A B).
Proof. exact (@lem4589910 A B (term198 A B) (term199 A B)). Qed.
Lemma lem4589912 {A B : Type'} (s : type572 A B) : (term200 A B s) = (term185 A B s).
Proof. exact (eq_refl (term200 A B s)). Qed.
Lemma lem4589913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589914 {A B : Type'} (s : type572 A B) : (term201 A B s) = (term187 A B s).
Proof. exact (MK_COMB (@lem4589913) (@lem4589912 A B s)). Qed.
Lemma lem4589915 {A B : Type'} (s : type572 A B) : (term202 A B s) = (term190 A B s).
Proof. exact (eq_refl (term202 A B s)). Qed.
Lemma lem4589916 {A B : Type'} (s : type572 A B) : (term203 A B s) = (term191 A B s).
Proof. exact (MK_COMB (@lem4589914 A B s) (@lem4589915 A B s)). Qed.
Lemma lem4589917 {A B : Type'} : (term204 A B) = (term192 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4589916 A B s)). Qed.
Lemma lem4589918 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4589919 {A B : Type'} : (term196 A B) = (term193 A B).
Proof. exact (MK_COMB (@lem4589918 A B) (@lem4589917 A B)). Qed.
Lemma lem4589920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4589921 {A B : Type'} : (term205 A B) = (term206 A B).
Proof. exact (MK_COMB (@lem4589920) (@lem4589919 A B)). Qed.
Lemma lem4589922 {A B : Type'} (s : type572 A B) : (term200 A B s) = (term185 A B s).
Proof. exact (eq_refl (term200 A B s)). Qed.
Lemma lem4589923 {A B : Type'} : (term207 A B) = (term198 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4589922 A B s)). Qed.
Lemma lem4589924 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4589925 {A B : Type'} : (term208 A B) = (term209 A B).
Proof. exact (MK_COMB (@lem4589924 A B) (@lem4589923 A B)). Qed.
Lemma lem4589926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4589927 {A B : Type'} : (term210 A B) = (term211 A B).
Proof. exact (MK_COMB (@lem4589926) (@lem4589925 A B)). Qed.
Lemma lem4589928 {A B : Type'} (s : type572 A B) : (term202 A B s) = (term190 A B s).
Proof. exact (eq_refl (term202 A B s)). Qed.
Lemma lem4589929 {A B : Type'} : (term212 A B) = (term199 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4589928 A B s)). Qed.
Lemma lem4589930 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4589931 {A B : Type'} : (term213 A B) = (term214 A B).
Proof. exact (MK_COMB (@lem4589930 A B) (@lem4589929 A B)). Qed.
Lemma lem4589932 {A B : Type'} : (term197 A B) = (term215 A B).
Proof. exact (MK_COMB (@lem4589927 A B) (@lem4589931 A B)). Qed.
Lemma lem4589933 {A B : Type'} : ((term196 A B) = (term197 A B)) = ((term193 A B) = (term215 A B)).
Proof. exact (MK_COMB (@lem4589921 A B) (@lem4589932 A B)). Qed.
Lemma lem4589934 {A B : Type'} : (term193 A B) = (term215 A B).
Proof. exact (EQ_MP (@lem4589933 A B) (@lem4589911 A B)). Qed.
Lemma lem4590041 {A B : Type'} : (term171 A B) = (term215 A B).
Proof. exact (TRANS (@lem4589907 A B) (@lem4589934 A B)). Qed.
Lemma lem4590042 {A B : Type'} : (term15 A B) = (term215 A B).
Proof. exact (TRANS (@lem4589777 A B) (@lem4590041 A B)). Qed.
Lemma lem4590043 {A B : Type'} (h1 : term15 A B) : term215 A B.
Proof. exact (EQ_MP (@lem4590042 A B) (@lem4588831 A B h1)). Qed.
Lemma lem4591017 {A B : Type'} (m : nat) (n : nat) : (term216 A B m n) = (term217 A B m n).
Proof. exact (@lem17045 (@HAS_SIZE A (@UNIV A) m) (@HAS_SIZE B (@UNIV B) n)). Qed.
Lemma lem4591018 {A B : Type'} (n : nat) (m : nat) : (term218 A B n m) = (term218 A B n m).
Proof. exact (eq_refl (term218 A B n m)). Qed.
Lemma lem4591019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4591020 {A B : Type'} (m : nat) (n : nat) : (term219 A B m n) = (term220 A B m n).
Proof. exact (MK_COMB (@lem4591019) (@lem4591017 A B m n)). Qed.
Lemma lem4591021 {A B : Type'} (n : nat) (m : nat) : (term221 A B n m) = (term222 A B n m).
Proof. exact (MK_COMB (@lem4591020 A B m n) (@lem4591018 A B n m)). Qed.
Lemma lem4591022 {A B : Type'} (n : nat) (m : nat) : (term70 A B n m) = (term221 A B n m).
Proof. exact (@lem17265 (term223 A B m n) (term218 A B n m)). Qed.
Lemma lem4591023 {A B : Type'} (n : nat) (m : nat) : (term70 A B n m) = (term222 A B n m).
Proof. exact (TRANS (@lem4591022 A B n m) (@lem4591021 A B n m)). Qed.
Lemma lem4591024 {A B : Type'} (m : nat) : (term71 A B m) = (term224 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4591023 A B n m)). Qed.
Lemma lem4591025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591026 {A B : Type'} (m : nat) : (term72 A B m) = (term225 A B m).
Proof. exact (MK_COMB (@lem4591025) (@lem4591024 A B m)). Qed.
Lemma lem4591027 {A B : Type'} : (term73 A B) = (term226 A B).
Proof. exact (fun_ext (fun m : nat => @lem4591026 A B m)). Qed.
Lemma lem4591028 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591085 {A B : Type'} : (term11 A B) = (term227 A B).
Proof. exact (MK_COMB (@lem4591028) (@lem4591027 A B)). Qed.
Lemma lem4591086 {A B : Type'} (h1 : term11 A B) : term227 A B.
Proof. exact (EQ_MP (@lem4591085 A B) (@lem4588836 A B h1)). Qed.
Lemma lem4591332 {A B : Type'} (h1 : term10 A B) : term94 A B.
Proof. exact (EQ_MP (@lem4588854 A B) (@lem4588827 A B h1)). Qed.
Lemma lem4591355 {A : Type'} (s : A -> Prop) (n : nat) : (term98 A s n) = (term98 A s n).
Proof. exact (eq_refl (term98 A s n)). Qed.
Lemma lem4591356 {A : Type'} (s : A -> Prop) : (term117 A s) = (term117 A s).
Proof. exact (fun_ext (fun n : nat => @lem4591355 A s n)). Qed.
Lemma lem4591357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591358 {A : Type'} (s : A -> Prop) : (term132 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem4591357) (@lem4591356 A s)). Qed.
Lemma lem4591359 {A : Type'} : (term141 A) = (term141 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4591358 A s)). Qed.
Lemma lem4591360 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4591361 {A : Type'} : (term156 A) = (term156 A).
Proof. exact (MK_COMB (@lem4591360 A) (@lem4591359 A)). Qed.
Lemma lem4591386 {A : Type'} (s : A -> Prop) (n : nat) : (term101 A s n) = (term101 A s n).
Proof. exact (eq_refl (term101 A s n)). Qed.
Lemma lem4591387 {A : Type'} (s : A -> Prop) : (term116 A s) = (term116 A s).
Proof. exact (fun_ext (fun n : nat => @lem4591386 A s n)). Qed.
Lemma lem4591388 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591389 {A : Type'} (s : A -> Prop) : (term127 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem4591388) (@lem4591387 A s)). Qed.
Lemma lem4591390 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4591389 A s)). Qed.
Lemma lem4591391 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4591392 {A : Type'} : (term151 A) = (term151 A).
Proof. exact (MK_COMB (@lem4591391 A) (@lem4591390 A)). Qed.
Lemma lem4591393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4591394 {A : Type'} : (term153 A) = (term153 A).
Proof. exact (MK_COMB (@lem4591393) (@lem4591392 A)). Qed.
Lemma lem4591395 {A : Type'} : (term157 A) = (term157 A).
Proof. exact (MK_COMB (@lem4591394 A) (@lem4591361 A)). Qed.
Lemma lem4591396 {A : Type'} (h1 : term16 A) : term157 A.
Proof. exact (EQ_MP (@lem4591395 A) (@lem4589152 A h1)). Qed.
Lemma lem4591419 {B : Type'} (s : B -> Prop) (n : nat) : (term98 B s n) = (term98 B s n).
Proof. exact (eq_refl (term98 B s n)). Qed.
Lemma lem4591420 {B : Type'} (s : B -> Prop) : (term117 B s) = (term117 B s).
Proof. exact (fun_ext (fun n : nat => @lem4591419 B s n)). Qed.
Lemma lem4591421 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591422 {B : Type'} (s : B -> Prop) : (term132 B s) = (term132 B s).
Proof. exact (MK_COMB (@lem4591421) (@lem4591420 B s)). Qed.
Lemma lem4591423 {B : Type'} : (term141 B) = (term141 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4591422 B s)). Qed.
Lemma lem4591424 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4591425 {B : Type'} : (term156 B) = (term156 B).
Proof. exact (MK_COMB (@lem4591424 B) (@lem4591423 B)). Qed.
Lemma lem4591450 {B : Type'} (s : B -> Prop) (n : nat) : (term101 B s n) = (term101 B s n).
Proof. exact (eq_refl (term101 B s n)). Qed.
Lemma lem4591451 {B : Type'} (s : B -> Prop) : (term116 B s) = (term116 B s).
Proof. exact (fun_ext (fun n : nat => @lem4591450 B s n)). Qed.
Lemma lem4591452 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591453 {B : Type'} (s : B -> Prop) : (term127 B s) = (term127 B s).
Proof. exact (MK_COMB (@lem4591452) (@lem4591451 B s)). Qed.
Lemma lem4591454 {B : Type'} : (term140 B) = (term140 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4591453 B s)). Qed.
Lemma lem4591455 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4591456 {B : Type'} : (term151 B) = (term151 B).
Proof. exact (MK_COMB (@lem4591455 B) (@lem4591454 B)). Qed.
Lemma lem4591457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4591458 {B : Type'} : (term153 B) = (term153 B).
Proof. exact (MK_COMB (@lem4591457) (@lem4591456 B)). Qed.
Lemma lem4591459 {B : Type'} : (term157 B) = (term157 B).
Proof. exact (MK_COMB (@lem4591458 B) (@lem4591425 B)). Qed.
Lemma lem4591460 {B : Type'} (h1 : term16 B) : term157 B.
Proof. exact (EQ_MP (@lem4591459 B) (@lem4589449 B h1)). Qed.
Lemma lem4591547 {A B : Type'} (s : type572 A B) (n : nat) : (term160 A B s n) = (term160 A B s n).
Proof. exact (eq_refl (term160 A B s n)). Qed.
Lemma lem4591548 {A B : Type'} (s : type572 A B) : (term175 A B s) = (term175 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4591547 A B s n)). Qed.
Lemma lem4591549 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591550 {A B : Type'} (s : type572 A B) : (term190 A B s) = (term190 A B s).
Proof. exact (MK_COMB (@lem4591549) (@lem4591548 A B s)). Qed.
Lemma lem4591551 {A B : Type'} : (term199 A B) = (term199 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4591550 A B s)). Qed.
Lemma lem4591552 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4591553 {A B : Type'} : (term214 A B) = (term214 A B).
Proof. exact (MK_COMB (@lem4591552 A B) (@lem4591551 A B)). Qed.
Lemma lem4591578 {A B : Type'} (s : type572 A B) (n : nat) : (term163 A B s n) = (term163 A B s n).
Proof. exact (eq_refl (term163 A B s n)). Qed.
Lemma lem4591579 {A B : Type'} (s : type572 A B) : (term174 A B s) = (term174 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4591578 A B s n)). Qed.
Lemma lem4591580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591581 {A B : Type'} (s : type572 A B) : (term185 A B s) = (term185 A B s).
Proof. exact (MK_COMB (@lem4591580) (@lem4591579 A B s)). Qed.
Lemma lem4591582 {A B : Type'} : (term198 A B) = (term198 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4591581 A B s)). Qed.
Lemma lem4591583 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4591584 {A B : Type'} : (term209 A B) = (term209 A B).
Proof. exact (MK_COMB (@lem4591583 A B) (@lem4591582 A B)). Qed.
Lemma lem4591585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4591586 {A B : Type'} : (term211 A B) = (term211 A B).
Proof. exact (MK_COMB (@lem4591585) (@lem4591584 A B)). Qed.
Lemma lem4591587 {A B : Type'} : (term215 A B) = (term215 A B).
Proof. exact (MK_COMB (@lem4591586 A B) (@lem4591553 A B)). Qed.
Lemma lem4591588 {A B : Type'} (h1 : term15 A B) : term215 A B.
Proof. exact (EQ_MP (@lem4591587 A B) (@lem4590043 A B h1)). Qed.
Lemma lem4591845 {A B : Type'} (n : nat) (m : nat) : (term222 A B n m) = (term222 A B n m).
Proof. exact (eq_refl (term222 A B n m)). Qed.
Lemma lem4591846 {A B : Type'} (m : nat) : (term224 A B m) = (term224 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4591845 A B n m)). Qed.
Lemma lem4591847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591848 {A B : Type'} (m : nat) : (term225 A B m) = (term225 A B m).
Proof. exact (MK_COMB (@lem4591847) (@lem4591846 A B m)). Qed.
Lemma lem4591849 {A B : Type'} : (term226 A B) = (term226 A B).
Proof. exact (fun_ext (fun m : nat => @lem4591848 A B m)). Qed.
Lemma lem4591850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4591851 {A B : Type'} : (term227 A B) = (term227 A B).
Proof. exact (MK_COMB (@lem4591850) (@lem4591849 A B)). Qed.
Lemma lem4591852 {A B : Type'} (h1 : term11 A B) : term227 A B.
Proof. exact (EQ_MP (@lem4591851 A B) (@lem4591086 A B h1)). Qed.
Lemma lem4591967 {A B : Type'} (h1 : term15 A B) : term214 A B.
Proof. exact (proj2 (@lem4591588 A B h1)). Qed.
Lemma lem4591972 {B : Type'} (h1 : term16 B) : term151 B.
Proof. exact (proj1 (@lem4591460 B h1)). Qed.
Lemma lem4591974 {A : Type'} (h1 : term16 A) : term151 A.
Proof. exact (proj1 (@lem4591396 A h1)). Qed.
Lemma lem4591976 {A B : Type'} (h1 : term10 A B) : term95 A B.
Proof. exact (proj1 (@lem4591332 A B h1)). Qed.
Lemma lem4592014 {A B : Type'} (n : nat) (m : nat) : (term222 A B n m) = (term222 A B n m).
Proof. exact (eq_refl (term222 A B n m)). Qed.
Lemma lem4592015 {A B : Type'} (m : nat) : (term224 A B m) = (term224 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4592014 A B n m)). Qed.
Lemma lem4592016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4592017 {A B : Type'} (m : nat) : (term225 A B m) = (term225 A B m).
Proof. exact (MK_COMB (@lem4592016) (@lem4592015 A B m)). Qed.
Lemma lem4592018 {A B : Type'} : (term226 A B) = (term226 A B).
Proof. exact (fun_ext (fun m : nat => @lem4592017 A B m)). Qed.
Lemma lem4592019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4592021 {A B : Type'} : (term227 A B) = (term227 A B).
Proof. exact (MK_COMB (@lem4592019) (@lem4592018 A B)). Qed.
Lemma lem4592022 {A B : Type'} (h1 : term11 A B) : term227 A B.
Proof. exact (EQ_MP (@lem4592021 A B) (@lem4591852 A B h1)). Qed.
Lemma lem4592272 {A B : Type'} (s : type572 A B) (n : nat) : (term160 A B s n) = (term228 A B s n).
Proof. exact (@lem19490 (@FINITE (A -> B) s) (term229 A B s n) ((@CARD (A -> B) s) = n)). Qed.
Lemma lem4592273 {A B : Type'} (s : type572 A B) : (term175 A B s) = (term230 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4592272 A B s n)). Qed.
Lemma lem4592274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4592275 {A B : Type'} (s : type572 A B) : (term190 A B s) = (term231 A B s).
Proof. exact (MK_COMB (@lem4592274) (@lem4592273 A B s)). Qed.
Lemma lem4592276 {A B : Type'} : (term199 A B) = (term232 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4592275 A B s)). Qed.
Lemma lem4592277 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4592279 {A B : Type'} : (term214 A B) = (term233 A B).
Proof. exact (MK_COMB (@lem4592277 A B) (@lem4592276 A B)). Qed.
Lemma lem4592280 {A B : Type'} (h1 : term15 A B) : term233 A B.
Proof. exact (EQ_MP (@lem4592279 A B) (@lem4591967 A B h1)). Qed.
Lemma lem4592342 {B : Type'} (s : B -> Prop) (n : nat) : (term101 B s n) = (term101 B s n).
Proof. exact (eq_refl (term101 B s n)). Qed.
Lemma lem4592343 {B : Type'} (s : B -> Prop) : (term116 B s) = (term116 B s).
Proof. exact (fun_ext (fun n : nat => @lem4592342 B s n)). Qed.
Lemma lem4592344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4592345 {B : Type'} (s : B -> Prop) : (term127 B s) = (term127 B s).
Proof. exact (MK_COMB (@lem4592344) (@lem4592343 B s)). Qed.
Lemma lem4592346 {B : Type'} : (term140 B) = (term140 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4592345 B s)). Qed.
Lemma lem4592347 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4592349 {B : Type'} : (term151 B) = (term151 B).
Proof. exact (MK_COMB (@lem4592347 B) (@lem4592346 B)). Qed.
Lemma lem4592350 {B : Type'} (h1 : term16 B) : term151 B.
Proof. exact (EQ_MP (@lem4592349 B) (@lem4591972 B h1)). Qed.
Lemma lem4592390 {A : Type'} (s : A -> Prop) (n : nat) : (term101 A s n) = (term101 A s n).
Proof. exact (eq_refl (term101 A s n)). Qed.
Lemma lem4592391 {A : Type'} (s : A -> Prop) : (term116 A s) = (term116 A s).
Proof. exact (fun_ext (fun n : nat => @lem4592390 A s n)). Qed.
Lemma lem4592392 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4592393 {A : Type'} (s : A -> Prop) : (term127 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem4592392) (@lem4592391 A s)). Qed.
Lemma lem4592394 {A : Type'} : (term140 A) = (term140 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4592393 A s)). Qed.
Lemma lem4592395 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4592397 {A : Type'} : (term151 A) = (term151 A).
Proof. exact (MK_COMB (@lem4592395 A) (@lem4592394 A)). Qed.
Lemma lem4592398 {A : Type'} (h1 : term16 A) : term151 A.
Proof. exact (EQ_MP (@lem4592397 A) (@lem4591974 A h1)). Qed.
Lemma lem4592443 {A B : Type'} (_55059 : nat) (h1 : term11 A B) : term234 A B _55059.
Proof. exact (@lem4592022 A B h1 _55059). Qed.
Lemma lem4592444 {A B : Type'} (_55059 : nat) : (term234 A B _55059) = (term225 A B _55059).
Proof. exact (eq_refl (term234 A B _55059)). Qed.
Lemma lem4592445 {A B : Type'} (_55059 : nat) (h1 : term11 A B) : term225 A B _55059.
Proof. exact (EQ_MP (@lem4592444 A B _55059) (@lem4592443 A B _55059 h1)). Qed.
Lemma lem4592446 {A B : Type'} (_55059 : nat) (_55060 : nat) (h1 : term11 A B) : term235 A B _55059 _55060.
Proof. exact (@lem4592445 A B _55059 h1 _55060). Qed.
Lemma lem4592447 {A B : Type'} (_55060 : nat) (_55059 : nat) : (term235 A B _55059 _55060) = (term222 A B _55060 _55059).
Proof. exact (eq_refl (term235 A B _55059 _55060)). Qed.
Lemma lem4592448 {A B : Type'} (_55060 : nat) (_55059 : nat) (h1 : term11 A B) : term222 A B _55060 _55059.
Proof. exact (EQ_MP (@lem4592447 A B _55060 _55059) (@lem4592446 A B _55059 _55060 h1)). Qed.
Lemma lem4592509 {A B : Type'} (_55081 : type572 A B) (h1 : term15 A B) : term236 A B _55081.
Proof. exact (@lem4592280 A B h1 _55081). Qed.
Lemma lem4592510 {A B : Type'} (_55081 : type572 A B) : (term236 A B _55081) = (term231 A B _55081).
Proof. exact (eq_refl (term236 A B _55081)). Qed.
Lemma lem4592511 {A B : Type'} (_55081 : type572 A B) (h1 : term15 A B) : term231 A B _55081.
Proof. exact (EQ_MP (@lem4592510 A B _55081) (@lem4592509 A B _55081 h1)). Qed.
Lemma lem4592512 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) (h1 : term15 A B) : term237 A B _55081 _55082.
Proof. exact (@lem4592511 A B _55081 h1 _55082). Qed.
Lemma lem4592513 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : (term237 A B _55081 _55082) = (term228 A B _55081 _55082).
Proof. exact (eq_refl (term237 A B _55081 _55082)). Qed.
Lemma lem4592514 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) (h1 : term15 A B) : term228 A B _55081 _55082.
Proof. exact (EQ_MP (@lem4592513 A B _55081 _55082) (@lem4592512 A B _55081 _55082 h1)). Qed.
Lemma lem4592527 {B : Type'} (_55087 : B -> Prop) (h1 : term16 B) : term142 B _55087.
Proof. exact (@lem4592350 B h1 _55087). Qed.
Lemma lem4592528 {B : Type'} (_55087 : B -> Prop) : (term142 B _55087) = (term127 B _55087).
Proof. exact (eq_refl (term142 B _55087)). Qed.
Lemma lem4592529 {B : Type'} (_55087 : B -> Prop) (h1 : term16 B) : term127 B _55087.
Proof. exact (EQ_MP (@lem4592528 B _55087) (@lem4592527 B _55087 h1)). Qed.
Lemma lem4592530 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) (h1 : term16 B) : term118 B _55087 _55088.
Proof. exact (@lem4592529 B _55087 h1 _55088). Qed.
Lemma lem4592531 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term118 B _55087 _55088) = (term101 B _55087 _55088).
Proof. exact (eq_refl (term118 B _55087 _55088)). Qed.
Lemma lem4592539 {A : Type'} (_55091 : A -> Prop) (h1 : term16 A) : term142 A _55091.
Proof. exact (@lem4592398 A h1 _55091). Qed.
Lemma lem4592540 {A : Type'} (_55091 : A -> Prop) : (term142 A _55091) = (term127 A _55091).
Proof. exact (eq_refl (term142 A _55091)). Qed.
Lemma lem4592541 {A : Type'} (_55091 : A -> Prop) (h1 : term16 A) : term127 A _55091.
Proof. exact (EQ_MP (@lem4592540 A _55091) (@lem4592539 A _55091 h1)). Qed.
Lemma lem4592542 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) (h1 : term16 A) : term118 A _55091 _55092.
Proof. exact (@lem4592541 A _55091 h1 _55092). Qed.
Lemma lem4592543 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term118 A _55091 _55092) = (term101 A _55091 _55092).
Proof. exact (eq_refl (term118 A _55091 _55092)). Qed.
Lemma lem4592587 {A B : Type'} (_55060 : nat) (_55059 : nat) : (term222 A B _55060 _55059) = (term238 A B _55060 _55059).
Proof. exact (@lem4588136 (term239 A _55059) (term239 B _55060) (term218 A B _55060 _55059)). Qed.
Lemma lem4592588 {A B : Type'} (_55060 : nat) (_55059 : nat) (h1 : term11 A B) : term238 A B _55060 _55059.
Proof. exact (EQ_MP (@lem4592587 A B _55060 _55059) (@lem4592448 A B _55060 _55059 h1)). Qed.
Lemma lem4592684 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) (h1 : term16 B) : term101 B _55087 _55088.
Proof. exact (EQ_MP (@lem4592531 B _55087 _55088) (@lem4592530 B _55087 _55088 h1)). Qed.
Lemma lem4592694 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) (h1 : term16 A) : term101 A _55091 _55092.
Proof. exact (EQ_MP (@lem4592543 A _55091 _55092) (@lem4592542 A _55091 _55092 h1)). Qed.
Lemma lem4592696 {A B : Type'} (h1 : term10 A B) : term240 A B.
Proof. exact (proj2 (@lem4591332 A B h1)). Qed.
Lemma lem4592742 {A B : Type'} (_55082 : nat) (_55081 : type572 A B) (h1 : term15 A B) : term241 A B _55082 _55081.
Proof. exact (proj1 (@lem4592514 A B _55081 _55082 h1)). Qed.
Lemma lem4593090 {A B : Type'} (h1 : term10 A B) : @FINITE A (@UNIV A).
Proof. exact (proj1 (@lem4591976 A B h1)). Qed.
Lemma lem4593091 {A B : Type'} (h1 : term10 A B) : term242 A.
Proof. exact (fun h0 : term243 A => @lem4593090 A B h1). Qed.
Lemma lem4593093 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593094 {A : Type'} : (term242 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem4593093 (@FINITE A (@UNIV A))). Qed.
Lemma lem4593095 {A B : Type'} (h1 : term10 A B) : @FINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem4593094 A) (@lem4593091 A B h1)). Qed.
Lemma lem4593097 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4593098 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (@lem4593097 (@CARD A (@UNIV A))). Qed.
Lemma lem4593099 {A : Type'} : term245 A.
Proof. exact (fun h0 : term246 A => @lem4593098 A). Qed.
Lemma lem4593101 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593102 {A : Type'} : (term245 A) = ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A))).
Proof. exact (@lem4593101 ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A)))). Qed.
Lemma lem4593103 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (EQ_MP (@lem4593102 A) (@lem4593099 A)). Qed.
Lemma lem4593105 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4593106 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term101 A _55091 _55092) = (term248 A _55091 _55092).
Proof. exact (@lem4593105 (term97 A _55091 _55092) (@HAS_SIZE A _55091 _55092)). Qed.
Lemma lem4593108 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4593109 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term251 A _55091 _55092) = (term252 A _55091 _55092).
Proof. exact (@lem4593108 (term253 A _55091) (term254 A _55091 _55092)). Qed.
Lemma lem4593111 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4593112 {A : Type'} (_55091 : A -> Prop) : (term256 A _55091) = (@FINITE A _55091).
Proof. exact (@lem4593111 (@FINITE A _55091)). Qed.
Lemma lem4593113 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4593114 {A : Type'} (_55091 : A -> Prop) : (term257 A _55091) = (term258 A _55091).
Proof. exact (MK_COMB (@lem4593113) (@lem4593112 A _55091)). Qed.
Lemma lem4593116 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4593117 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term259 A _55091 _55092) = ((@CARD A _55091) = _55092).
Proof. exact (@lem4593116 ((@CARD A _55091) = _55092)). Qed.
Lemma lem4593118 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term252 A _55091 _55092) = (term90 A _55091 _55092).
Proof. exact (MK_COMB (@lem4593114 A _55091) (@lem4593117 A _55091 _55092)). Qed.
Lemma lem4593119 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term251 A _55091 _55092) = (term90 A _55091 _55092).
Proof. exact (TRANS (@lem4593109 A _55091 _55092) (@lem4593118 A _55091 _55092)). Qed.
Lemma lem4593120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4593121 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term260 A _55091 _55092) = (term261 A _55091 _55092).
Proof. exact (MK_COMB (@lem4593120) (@lem4593119 A _55091 _55092)). Qed.
Lemma lem4593122 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (@HAS_SIZE A _55091 _55092) = (@HAS_SIZE A _55091 _55092).
Proof. exact (eq_refl (@HAS_SIZE A _55091 _55092)). Qed.
Lemma lem4593123 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term248 A _55091 _55092) = (term262 A _55091 _55092).
Proof. exact (MK_COMB (@lem4593121 A _55091 _55092) (@lem4593122 A _55091 _55092)). Qed.
Lemma lem4593124 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) : (term101 A _55091 _55092) = (term262 A _55091 _55092).
Proof. exact (TRANS (@lem4593106 A _55091 _55092) (@lem4593123 A _55091 _55092)). Qed.
Lemma lem4593126 {A B : Type'} (h1 : term10 A B) : term263 A.
Proof. exact (conj (@lem4593095 A B h1) (@lem4593103 A)). Qed.
Lemma lem4593128 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) (h1 : term16 A) : term262 A _55091 _55092.
Proof. exact (EQ_MP (@lem4593124 A _55091 _55092) (@lem4592694 A _55091 _55092 h1)). Qed.
Lemma lem4593129 {A : Type'} (_55091 : A -> Prop) (_55092 : nat) (h1 : term16 A) : term262 A _55091 _55092.
Proof. exact (@lem4593128 A _55091 _55092 h1). Qed.
Lemma lem4593130 {A : Type'} (h1 : term16 A) : term264 A.
Proof. exact (@lem4593129 A (@UNIV A) (@CARD A (@UNIV A)) h1). Qed.
Lemma lem4593133 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term265 A.
Proof. exact (@lem4593130 A h1 (@lem4593126 A B h2)). Qed.
Lemma lem4593134 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term266 A.
Proof. exact (fun h0 : term267 A => @lem4593133 A B h1 h2). Qed.
Lemma lem4593136 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593137 {A : Type'} : (term266 A) = (term265 A).
Proof. exact (@lem4593136 (term265 A)). Qed.
Lemma lem4593138 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term265 A.
Proof. exact (EQ_MP (@lem4593137 A) (@lem4593134 A B h1 h2)). Qed.
Lemma lem4593140 {A B : Type'} (h1 : term10 A B) : @FINITE B (@UNIV B).
Proof. exact (proj2 (@lem4591976 A B h1)). Qed.
Lemma lem4593141 {A B : Type'} (h1 : term10 A B) : term242 B.
Proof. exact (fun h0 : term243 B => @lem4593140 A B h1). Qed.
Lemma lem4593143 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593144 {B : Type'} : (term242 B) = (@FINITE B (@UNIV B)).
Proof. exact (@lem4593143 (@FINITE B (@UNIV B))). Qed.
Lemma lem4593145 {A B : Type'} (h1 : term10 A B) : @FINITE B (@UNIV B).
Proof. exact (EQ_MP (@lem4593144 B) (@lem4593141 A B h1)). Qed.
Lemma lem4593147 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4593148 {B : Type'} : (@CARD B (@UNIV B)) = (@CARD B (@UNIV B)).
Proof. exact (@lem4593147 (@CARD B (@UNIV B))). Qed.
Lemma lem4593149 {B : Type'} : term245 B.
Proof. exact (fun h0 : term246 B => @lem4593148 B). Qed.
Lemma lem4593151 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593152 {B : Type'} : (term245 B) = ((@CARD B (@UNIV B)) = (@CARD B (@UNIV B))).
Proof. exact (@lem4593151 ((@CARD B (@UNIV B)) = (@CARD B (@UNIV B)))). Qed.
Lemma lem4593153 {B : Type'} : (@CARD B (@UNIV B)) = (@CARD B (@UNIV B)).
Proof. exact (EQ_MP (@lem4593152 B) (@lem4593149 B)). Qed.
Lemma lem4593155 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4593156 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term101 B _55087 _55088) = (term248 B _55087 _55088).
Proof. exact (@lem4593155 (term97 B _55087 _55088) (@HAS_SIZE B _55087 _55088)). Qed.
Lemma lem4593158 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4593159 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term251 B _55087 _55088) = (term252 B _55087 _55088).
Proof. exact (@lem4593158 (term253 B _55087) (term254 B _55087 _55088)). Qed.
Lemma lem4593161 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4593162 {B : Type'} (_55087 : B -> Prop) : (term256 B _55087) = (@FINITE B _55087).
Proof. exact (@lem4593161 (@FINITE B _55087)). Qed.
Lemma lem4593163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4593164 {B : Type'} (_55087 : B -> Prop) : (term257 B _55087) = (term258 B _55087).
Proof. exact (MK_COMB (@lem4593163) (@lem4593162 B _55087)). Qed.
Lemma lem4593166 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4593167 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term259 B _55087 _55088) = ((@CARD B _55087) = _55088).
Proof. exact (@lem4593166 ((@CARD B _55087) = _55088)). Qed.
Lemma lem4593168 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term252 B _55087 _55088) = (term90 B _55087 _55088).
Proof. exact (MK_COMB (@lem4593164 B _55087) (@lem4593167 B _55087 _55088)). Qed.
Lemma lem4593169 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term251 B _55087 _55088) = (term90 B _55087 _55088).
Proof. exact (TRANS (@lem4593159 B _55087 _55088) (@lem4593168 B _55087 _55088)). Qed.
Lemma lem4593170 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4593171 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term260 B _55087 _55088) = (term261 B _55087 _55088).
Proof. exact (MK_COMB (@lem4593170) (@lem4593169 B _55087 _55088)). Qed.
Lemma lem4593172 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (@HAS_SIZE B _55087 _55088) = (@HAS_SIZE B _55087 _55088).
Proof. exact (eq_refl (@HAS_SIZE B _55087 _55088)). Qed.
Lemma lem4593173 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term248 B _55087 _55088) = (term262 B _55087 _55088).
Proof. exact (MK_COMB (@lem4593171 B _55087 _55088) (@lem4593172 B _55087 _55088)). Qed.
Lemma lem4593174 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) : (term101 B _55087 _55088) = (term262 B _55087 _55088).
Proof. exact (TRANS (@lem4593156 B _55087 _55088) (@lem4593173 B _55087 _55088)). Qed.
Lemma lem4593176 {A B : Type'} (h1 : term10 A B) : term263 B.
Proof. exact (conj (@lem4593145 A B h1) (@lem4593153 B)). Qed.
Lemma lem4593178 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) (h1 : term16 B) : term262 B _55087 _55088.
Proof. exact (EQ_MP (@lem4593174 B _55087 _55088) (@lem4592684 B _55087 _55088 h1)). Qed.
Lemma lem4593179 {B : Type'} (_55087 : B -> Prop) (_55088 : nat) (h1 : term16 B) : term262 B _55087 _55088.
Proof. exact (@lem4593178 B _55087 _55088 h1). Qed.
Lemma lem4593180 {B : Type'} (h1 : term16 B) : term264 B.
Proof. exact (@lem4593179 B (@UNIV B) (@CARD B (@UNIV B)) h1). Qed.
Lemma lem4593183 {A B : Type'} (h1 : term16 B) (h2 : term10 A B) : term265 B.
Proof. exact (@lem4593180 B h1 (@lem4593176 A B h2)). Qed.
Lemma lem4593184 {A B : Type'} (h1 : term16 B) (h2 : term10 A B) : term266 B.
Proof. exact (fun h0 : term267 B => @lem4593183 A B h1 h2). Qed.
Lemma lem4593186 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593187 {B : Type'} : (term266 B) = (term265 B).
Proof. exact (@lem4593186 (term265 B)). Qed.
Lemma lem4593188 {A B : Type'} (h1 : term16 B) (h2 : term10 A B) : term265 B.
Proof. exact (EQ_MP (@lem4593187 B) (@lem4593184 A B h1 h2)). Qed.
Lemma lem4593204 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4593205 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term268 A B _55060 _55059) = (term269 A B _55059 _55060).
Proof. exact (@lem4593204 (term218 A B _55060 _55059) (term239 B _55060)). Qed.
Lemma lem4593211 {A : Type'} (_55059 : nat) : (term270 A _55059) = (term270 A _55059).
Proof. exact (eq_refl (term270 A _55059)). Qed.
Lemma lem4593212 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term238 A B _55060 _55059) = (term271 A B _55059 _55060).
Proof. exact (MK_COMB (@lem4593211 A _55059) (@lem4593205 A B _55059 _55060)). Qed.
Lemma lem4593216 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4593217 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term271 A B _55059 _55060) = (term272 A B _55059 _55060).
Proof. exact (@lem4593216 (term218 A B _55060 _55059) (term239 A _55059) (term239 B _55060)). Qed.
Lemma lem4593233 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term238 A B _55060 _55059) = (term272 A B _55059 _55060).
Proof. exact (TRANS (@lem4593212 A B _55059 _55060) (@lem4593217 A B _55059 _55060)). Qed.
Lemma lem4593234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4593235 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term273 A B _55060 _55059) = (term274 A B _55059 _55060).
Proof. exact (MK_COMB (@lem4593234) (@lem4593233 A B _55059 _55060)). Qed.
Lemma lem4593251 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term272 A B _55059 _55060) = (term272 A B _55059 _55060).
Proof. exact (eq_refl (term272 A B _55059 _55060)). Qed.
Lemma lem4593252 {A B : Type'} (_55059 : nat) (_55060 : nat) : ((term238 A B _55060 _55059) = (term272 A B _55059 _55060)) = ((term272 A B _55059 _55060) = (term272 A B _55059 _55060)).
Proof. exact (MK_COMB (@lem4593235 A B _55059 _55060) (@lem4593251 A B _55059 _55060)). Qed.
Lemma lem4593254 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4593255 (x : Prop) : (x = x) = True.
Proof. exact (@lem4593254 Prop x). Qed.
Lemma lem4593256 {A B : Type'} (_55059 : nat) (_55060 : nat) : ((term272 A B _55059 _55060) = (term272 A B _55059 _55060)) = True.
Proof. exact (@lem4593255 (term272 A B _55059 _55060)). Qed.
Lemma lem4593257 {A B : Type'} (_55059 : nat) (_55060 : nat) : ((term238 A B _55060 _55059) = (term272 A B _55059 _55060)) = True.
Proof. exact (TRANS (@lem4593252 A B _55059 _55060) (@lem4593256 A B _55059 _55060)). Qed.
Lemma lem4593258 {A B : Type'} (_55059 : nat) (_55060 : nat) : True = ((term238 A B _55060 _55059) = (term272 A B _55059 _55060)).
Proof. exact (SYM (@lem4593257 A B _55059 _55060)). Qed.
Lemma lem4593259 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term238 A B _55060 _55059) = (term272 A B _55059 _55060).
Proof. exact (EQ_MP (@lem4593258 A B _55059 _55060) (@lem0)). Qed.
Lemma lem4593260 {A B : Type'} (_55059 : nat) (_55060 : nat) (h1 : term11 A B) : term272 A B _55059 _55060.
Proof. exact (EQ_MP (@lem4593259 A B _55059 _55060) (@lem4592588 A B _55060 _55059 h1)). Qed.
Lemma lem4593262 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4593263 {A B : Type'} (_55060 : nat) (_55059 : nat) : (term272 A B _55059 _55060) = (term275 A B _55060 _55059).
Proof. exact (@lem4593262 (term217 A B _55059 _55060) (term218 A B _55060 _55059)). Qed.
Lemma lem4593265 (a : Prop) (b : Prop) : (term249 a b) = (term250 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4593266 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term276 A B _55059 _55060) = (term277 A B _55059 _55060).
Proof. exact (@lem4593265 (term239 A _55059) (term239 B _55060)). Qed.
Lemma lem4593268 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4593269 {A : Type'} (_55059 : nat) : (term278 A _55059) = (@HAS_SIZE A (@UNIV A) _55059).
Proof. exact (@lem4593268 (@HAS_SIZE A (@UNIV A) _55059)). Qed.
Lemma lem4593270 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4593271 {A : Type'} (_55059 : nat) : (term279 A _55059) = (term280 A _55059).
Proof. exact (MK_COMB (@lem4593270) (@lem4593269 A _55059)). Qed.
Lemma lem4593273 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4593274 {B : Type'} (_55060 : nat) : (term278 B _55060) = (@HAS_SIZE B (@UNIV B) _55060).
Proof. exact (@lem4593273 (@HAS_SIZE B (@UNIV B) _55060)). Qed.
Lemma lem4593275 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term277 A B _55059 _55060) = (term223 A B _55059 _55060).
Proof. exact (MK_COMB (@lem4593271 A _55059) (@lem4593274 B _55060)). Qed.
Lemma lem4593276 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term276 A B _55059 _55060) = (term223 A B _55059 _55060).
Proof. exact (TRANS (@lem4593266 A B _55059 _55060) (@lem4593275 A B _55059 _55060)). Qed.
Lemma lem4593277 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4593278 {A B : Type'} (_55059 : nat) (_55060 : nat) : (term281 A B _55059 _55060) = (term282 A B _55059 _55060).
Proof. exact (MK_COMB (@lem4593277) (@lem4593276 A B _55059 _55060)). Qed.
Lemma lem4593279 {A B : Type'} (_55060 : nat) (_55059 : nat) : (term218 A B _55060 _55059) = (term218 A B _55060 _55059).
Proof. exact (eq_refl (term218 A B _55060 _55059)). Qed.
Lemma lem4593280 {A B : Type'} (_55060 : nat) (_55059 : nat) : (term275 A B _55060 _55059) = (term70 A B _55060 _55059).
Proof. exact (MK_COMB (@lem4593278 A B _55059 _55060) (@lem4593279 A B _55060 _55059)). Qed.
Lemma lem4593281 {A B : Type'} (_55060 : nat) (_55059 : nat) : (term272 A B _55059 _55060) = (term70 A B _55060 _55059).
Proof. exact (TRANS (@lem4593263 A B _55060 _55059) (@lem4593280 A B _55060 _55059)). Qed.
Lemma lem4593283 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term10 A B) : term283 A B.
Proof. exact (conj (@lem4593138 A B h1 h3) (@lem4593188 A B h2 h3)). Qed.
Lemma lem4593285 {A B : Type'} (_55060 : nat) (_55059 : nat) (h1 : term11 A B) : term70 A B _55060 _55059.
Proof. exact (EQ_MP (@lem4593281 A B _55060 _55059) (@lem4593260 A B _55059 _55060 h1)). Qed.
Lemma lem4593286 {A B : Type'} (h1 : term11 A B) : term284 A B.
Proof. exact (@lem4593285 A B (@CARD B (@UNIV B)) (@CARD A (@UNIV A)) h1). Qed.
Lemma lem4593289 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term11 A B) (h4 : term10 A B) : term285 A B.
Proof. exact (@lem4593286 A B h3 (@lem4593283 A B h1 h2 h4)). Qed.
Lemma lem4593290 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term11 A B) (h4 : term10 A B) : term286 A B.
Proof. exact (fun h0 : term287 A B => @lem4593289 A B h1 h2 h3 h4). Qed.
Lemma lem4593292 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593293 {A B : Type'} : (term286 A B) = (term285 A B).
Proof. exact (@lem4593292 (term285 A B)). Qed.
Lemma lem4593294 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term11 A B) (h4 : term10 A B) : term285 A B.
Proof. exact (EQ_MP (@lem4593293 A B) (@lem4593290 A B h1 h2 h3 h4)). Qed.
Lemma lem4593300 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4593301 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : (term241 A B _55082 _55081) = (term288 A B _55081 _55082).
Proof. exact (@lem4593300 (@FINITE (A -> B) _55081) (term229 A B _55081 _55082)). Qed.
Lemma lem4593307 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4593308 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : (term289 A B _55082 _55081) = (term290 A B _55081 _55082).
Proof. exact (MK_COMB (@lem4593307) (@lem4593301 A B _55081 _55082)). Qed.
Lemma lem4593314 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : (term288 A B _55081 _55082) = (term288 A B _55081 _55082).
Proof. exact (eq_refl (term288 A B _55081 _55082)). Qed.
Lemma lem4593315 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : ((term241 A B _55082 _55081) = (term288 A B _55081 _55082)) = ((term288 A B _55081 _55082) = (term288 A B _55081 _55082)).
Proof. exact (MK_COMB (@lem4593308 A B _55081 _55082) (@lem4593314 A B _55081 _55082)). Qed.
Lemma lem4593317 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4593318 (x : Prop) : (x = x) = True.
Proof. exact (@lem4593317 Prop x). Qed.
Lemma lem4593319 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : ((term288 A B _55081 _55082) = (term288 A B _55081 _55082)) = True.
Proof. exact (@lem4593318 (term288 A B _55081 _55082)). Qed.
Lemma lem4593320 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : ((term241 A B _55082 _55081) = (term288 A B _55081 _55082)) = True.
Proof. exact (TRANS (@lem4593315 A B _55081 _55082) (@lem4593319 A B _55081 _55082)). Qed.
Lemma lem4593321 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : True = ((term241 A B _55082 _55081) = (term288 A B _55081 _55082)).
Proof. exact (SYM (@lem4593320 A B _55081 _55082)). Qed.
Lemma lem4593322 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : (term241 A B _55082 _55081) = (term288 A B _55081 _55082).
Proof. exact (EQ_MP (@lem4593321 A B _55081 _55082) (@lem0)). Qed.
Lemma lem4593323 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) (h1 : term15 A B) : term288 A B _55081 _55082.
Proof. exact (EQ_MP (@lem4593322 A B _55081 _55082) (@lem4592742 A B _55082 _55081 h1)). Qed.
Lemma lem4593325 (b : Prop) (a : Prop) : (a \/ b) = (term247 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4593326 {A B : Type'} (_55082 : nat) (_55081 : type572 A B) : (term288 A B _55081 _55082) = (term291 A B _55082 _55081).
Proof. exact (@lem4593325 (term229 A B _55081 _55082) (@FINITE (A -> B) _55081)). Qed.
Lemma lem4593328 (a : Prop) : (term255 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4593329 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : (term292 A B _55081 _55082) = (@HAS_SIZE (A -> B) _55081 _55082).
Proof. exact (@lem4593328 (@HAS_SIZE (A -> B) _55081 _55082)). Qed.
Lemma lem4593330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4593331 {A B : Type'} (_55081 : type572 A B) (_55082 : nat) : (term293 A B _55081 _55082) = (term294 A B _55081 _55082).
Proof. exact (MK_COMB (@lem4593330) (@lem4593329 A B _55081 _55082)). Qed.
Lemma lem4593332 {A B : Type'} (_55081 : type572 A B) : (@FINITE (A -> B) _55081) = (@FINITE (A -> B) _55081).
Proof. exact (eq_refl (@FINITE (A -> B) _55081)). Qed.
Lemma lem4593333 {A B : Type'} (_55082 : nat) (_55081 : type572 A B) : (term291 A B _55082 _55081) = (term295 A B _55082 _55081).
Proof. exact (MK_COMB (@lem4593331 A B _55081 _55082) (@lem4593332 A B _55081)). Qed.
Lemma lem4593334 {A B : Type'} (_55082 : nat) (_55081 : type572 A B) : (term288 A B _55081 _55082) = (term295 A B _55082 _55081).
Proof. exact (TRANS (@lem4593326 A B _55082 _55081) (@lem4593333 A B _55082 _55081)). Qed.
Lemma lem4593337 {A B : Type'} (_55082 : nat) (_55081 : type572 A B) (h1 : term15 A B) : term295 A B _55082 _55081.
Proof. exact (EQ_MP (@lem4593334 A B _55082 _55081) (@lem4593323 A B _55081 _55082 h1)). Qed.
Lemma lem4593338 {A B : Type'} (_55082 : nat) (_55081 : type572 A B) (h1 : term15 A B) : term295 A B _55082 _55081.
Proof. exact (@lem4593337 A B _55082 _55081 h1). Qed.
Lemma lem4593339 {A B : Type'} (h1 : term15 A B) : term296 A B.
Proof. exact (@lem4593338 A B (term297 A B) (@UNIV (A -> B)) h1). Qed.
Lemma lem4593342 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : @FINITE (A -> B) (@UNIV (A -> B)).
Proof. exact (@lem4593339 A B h3 (@lem4593294 A B h1 h2 h4 h5)). Qed.
Lemma lem4593343 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term298 A B.
Proof. exact (fun h0 : term240 A B => @lem4593342 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4593345 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593346 {A B : Type'} : (term298 A B) = (@FINITE (A -> B) (@UNIV (A -> B))).
Proof. exact (@lem4593345 (@FINITE (A -> B) (@UNIV (A -> B)))). Qed.
Lemma lem4593347 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : @FINITE (A -> B) (@UNIV (A -> B)).
Proof. exact (EQ_MP (@lem4593346 A B) (@lem4593343 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4593350 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4593352 {A B : Type'} : (term240 A B) = (term299 A B).
Proof. exact (@lem4593350 (@FINITE (A -> B) (@UNIV (A -> B)))). Qed.
Lemma lem4593355 {A B : Type'} (h1 : term10 A B) : term299 A B.
Proof. exact (EQ_MP (@lem4593352 A B) (@lem4592696 A B h1)). Qed.
Lemma lem4593358 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : False.
Proof. exact (@lem4593355 A B h5 (@lem4593347 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4593359 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term300.
Proof. exact (fun h0 : ~ False => @lem4593358 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4593361 (p : Prop) : (term244 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4593362 : term300 = False.
Proof. exact (@lem4593361 False). Qed.
Lemma lem4593363 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : False.
Proof. exact (EQ_MP (@lem4593362) (@lem4593359 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4593364 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term24 A B.
Proof. exact (fun h0 : term13 A B => @lem4593363 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4593365 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (@lem69 (term13 A B)). Qed.
Lemma lem4593366 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term25 A B.
Proof. exact (EQ_MP (@lem4593365 A B) (@lem4593364 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4593367 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term28 A B.
Proof. exact (fun h0 : term12 B => @lem4593366 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4593368 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term31 A B.
Proof. exact (fun h0 : term14 A B => @lem4593367 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4593369 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term34 A B.
Proof. exact (fun h0 : term11 A B => @lem4593368 A B h1 h2 h3 h0 h4). Qed.
Lemma lem4593370 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term36 A B.
Proof. exact (fun h0 : term12 A => @lem4593369 A B h1 h2 h3 h4). Qed.
Lemma lem4593371 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term39 A B.
Proof. exact (fun h0 : term17 A B => @lem4593370 A B h1 h2 h3 h4). Qed.
Lemma lem4593372 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term42 A B.
Proof. exact (fun h0 : term18 B => @lem4593371 A B h1 h2 h3 h4). Qed.
Lemma lem4593373 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term45 A B.
Proof. exact (fun h0 : term19 A B => @lem4593372 A B h1 h2 h3 h4). Qed.
Lemma lem4593374 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term10 A B) : term48 A B.
Proof. exact (fun h0 : term15 A B => @lem4593373 A B h1 h2 h0 h3). Qed.
Lemma lem4593375 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term10 A B) : term50 A B.
Proof. exact (fun h0 : term18 A => @lem4593374 A B h1 h2 h3). Qed.
Lemma lem4593376 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term53 A B.
Proof. exact (fun h0 : term16 B => @lem4593375 A B h1 h0 h2). Qed.
Lemma lem4593377 {A B : Type'} (h1 : term10 A B) : term55 A B.
Proof. exact (fun h0 : term16 A => @lem4593376 A B h0 h1). Qed.
Lemma lem4593378 {A B : Type'} : term57 A B.
Proof. exact (fun h0 : term10 A B => @lem4593377 A B h0). Qed.
Lemma lem4593379 {A B : Type'} : term20 A B.
Proof. exact (EQ_MP (@lem4588826 A B) (@lem4593378 A B)). Qed.
Lemma lem4593381 {A B : Type'} : term20 A B.
Proof. exact (@lem4588174 A B (@lem4593379 A B)). Qed.
Lemma lem4593382 {A B : Type'} (h1 : term10 A B) : term54 A B.
Proof. exact (@lem4593381 A B (@lem4588141 A B h1)). Qed.
Lemma lem4593383 {A B : Type'} (h1 : term10 A B) : term52 A B.
Proof. exact (@lem4593382 A B h1 (@lem4588153 A)). Qed.
Lemma lem4593384 {A B : Type'} (h1 : term10 A B) : term49 A B.
Proof. exact (@lem4593383 A B h1 (@lem4588150 B)). Qed.
Lemma lem4593385 {A B : Type'} (h1 : term10 A B) : term47 A B.
Proof. exact (@lem4593384 A B h1 (@lem4588155 A)). Qed.
Lemma lem4593386 {A B : Type'} (h1 : term10 A B) : term44 A B.
Proof. exact (@lem4593385 A B h1 (@lem4588149 A B)). Qed.
Lemma lem4593387 {A B : Type'} (h1 : term10 A B) : term41 A B.
Proof. exact (@lem4593386 A B h1 (@lem4588154 A B)). Qed.
Lemma lem4593388 {A B : Type'} (h1 : term10 A B) : term38 A B.
Proof. exact (@lem4593387 A B h1 (@lem4588152 B)). Qed.
Lemma lem4593389 {A B : Type'} (h1 : term10 A B) : term35 A B.
Proof. exact (@lem4593388 A B h1 (@lem4588151 A B)). Qed.
Lemma lem4593390 {A B : Type'} (h1 : term10 A B) : term33 A B.
Proof. exact (@lem4593389 A B h1 (@lem4588145 A)). Qed.
Lemma lem4593391 {A B : Type'} (h1 : term10 A B) : term30 A B.
Proof. exact (@lem4593390 A B h1 (@lem4588142 A B)). Qed.
Lemma lem4593392 {A B : Type'} (h1 : term10 A B) : term27 A B.
Proof. exact (@lem4593391 A B h1 (@lem4588147 A B)). Qed.
Lemma lem4593393 {A B : Type'} (h1 : term10 A B) : term24 A B.
Proof. exact (@lem4593392 A B h1 (@lem4588143 B)). Qed.
Lemma lem4593394 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (@lem4593393 A B h1 (@lem4588144 A B)). Qed.
Lemma lem4593395 {A B : Type'} (h1 : term10 A B) : (term10 A B) = False.
Proof. exact (prop_ext (fun h2 : term10 A B => @lem4593394 A B h1) (fun h2 : False => @lem4588141 A B h1)). Qed.
Lemma lem4593396 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (EQ_MP (@lem4593395 A B h1) (@lem4588141 A B h1)). Qed.
Lemma lem4593397 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term10 A B => @lem4593396 A B h0). Qed.
Lemma lem4593398 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem4588140 A B) (@lem4593397 A B)). Qed.
