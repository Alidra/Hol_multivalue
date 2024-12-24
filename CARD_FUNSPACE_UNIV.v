Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_FUNSPACE_UNIV_term_abbrevs.
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
Lemma lem4582296 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4582297 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4582298 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4582297 t1) (@lem4582296 t1)). Qed.
Lemma lem4582299 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4582298 t1 t2). Qed.
Lemma lem4582300 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4582301 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4582300 t1 t2) (@lem4582299 t1 t2)). Qed.
Lemma lem4582302 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4582301 t1 t2 t3). Qed.
Lemma lem4582303 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4582304 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4582303 t1 t2 t3) (@lem4582302 t1 t2 t3)). Qed.
Lemma lem4582305 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4582304 t1 t2 t3)). Qed.
Lemma lem4582307 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4582308 {A B : Type'} : (term8 A B) = (term9 A B).
Proof. exact (@lem4582307 (term8 A B)). Qed.
Lemma lem4582309 {A B : Type'} : (term9 A B) = (term8 A B).
Proof. exact (SYM (@lem4582308 A B)). Qed.
Lemma lem4582310 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem4582311 {A B : Type'} : term11 A B.
Proof. exact (@lem4582295 A B). Qed.
Lemma lem4582312 {B : Type'} : term12 B.
Proof. exact (@lem4582295 B B). Qed.
Lemma lem4582313 {A B : Type'} : term13 A B.
Proof. exact (@lem4582295 (A -> B) B). Qed.
Lemma lem4582314 {A : Type'} : term12 A.
Proof. exact (@lem4582295 A A). Qed.
Lemma lem4582316 {A B : Type'} : term14 A B.
Proof. exact (@lem4582295 A (A -> B)). Qed.
Lemma lem4582318 {A B : Type'} : term15 A B.
Proof. exact (@lem3863773 (A -> B)). Qed.
Lemma lem4582319 {B : Type'} : term16 B.
Proof. exact (@lem3863773 B). Qed.
Lemma lem4582320 {A B : Type'} : term17 A B.
Proof. exact (@lem3863773 (type570 A B)). Qed.
Lemma lem4582321 {B : Type'} : term18 B.
Proof. exact (@lem3863773 (B -> B)). Qed.
Lemma lem4582322 {A : Type'} : term16 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem4582323 {A B : Type'} : term19 A B.
Proof. exact (@lem3863773 (type1401 A B)). Qed.
Lemma lem4582324 {A : Type'} : term18 A.
Proof. exact (@lem3863773 (A -> A)). Qed.
Lemma lem4582332 {_100044 A B : Type'} (h1 : term20 _100044 A B) : term20 _100044 A B.
Proof. exact (h1). Qed.
Lemma lem4582333 {_100044 A B : Type'} : term21 _100044 A B.
Proof. exact (fun h0 : term20 _100044 A B => @lem4582332 _100044 A B h0). Qed.
Lemma lem4582334 {_100044 A B : Type'} (h1 : term21 _100044 A B) : term21 _100044 A B.
Proof. exact (h1). Qed.
Lemma lem4582335 {_100044 A B : Type'} (h1 : term20 _100044 A B) : term20 _100044 A B.
Proof. exact (h1). Qed.
Lemma lem4582336 {_100044 A B : Type'} (h1 : term20 _100044 A B) (h2 : term21 _100044 A B) : term20 _100044 A B.
Proof. exact (@lem4582334 _100044 A B h2 (@lem4582335 _100044 A B h1)). Qed.
Lemma lem4582337 {_100044 A B : Type'} (h1 : term20 _100044 A B) : term22 _100044 A B.
Proof. exact (fun h0 : term21 _100044 A B => @lem4582336 _100044 A B h1 h0). Qed.
Lemma lem4582338 {_100044 A B : Type'} (h1 : term21 _100044 A B) : term21 _100044 A B.
Proof. exact (h1). Qed.
Lemma lem4582339 {_100044 A B : Type'} (h1 : term20 _100044 A B) (h2 : term21 _100044 A B) : term20 _100044 A B.
Proof. exact (@lem4582337 _100044 A B h1 (@lem4582338 _100044 A B h2)). Qed.
Lemma lem4582340 {_100044 A B : Type'} (h1 : term21 _100044 A B) : term21 _100044 A B.
Proof. exact (fun h0 : term20 _100044 A B => @lem4582339 _100044 A B h0 h1). Qed.
Lemma lem4582341 {_100044 A B : Type'} : term23 _100044 A B.
Proof. exact (fun h0 : term21 _100044 A B => @lem4582340 _100044 A B h0). Qed.
Lemma lem4582344 {_100044 A B : Type'} : term21 _100044 A B.
Proof. exact (@lem4582341 _100044 A B (@lem4582333 _100044 A B)). Qed.
Lemma lem4582345 {_100044 A B : Type'} : term21 _100044 A B.
Proof. exact (@lem4582344 _100044 A B). Qed.
Lemma lem4582505 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4582506 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (@lem4582505 (term13 A B)). Qed.
Lemma lem4582519 {B : Type'} : (term26 B) = (term26 B).
Proof. exact (eq_refl (term26 B)). Qed.
Lemma lem4582520 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (MK_COMB (@lem4582519 B) (@lem4582506 A B)). Qed.
Lemma lem4582523 {A B : Type'} : (term29 A B) = (term29 A B).
Proof. exact (eq_refl (term29 A B)). Qed.
Lemma lem4582524 {A B : Type'} : (term30 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem4582523 A B) (@lem4582520 A B)). Qed.
Lemma lem4582527 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (eq_refl (term32 A B)). Qed.
Lemma lem4582528 {A B : Type'} : (term33 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem4582527 A B) (@lem4582524 A B)). Qed.
Lemma lem4582531 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (eq_refl (term26 A)). Qed.
Lemma lem4582532 {A B : Type'} : (term35 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem4582531 A) (@lem4582528 A B)). Qed.
Lemma lem4582535 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (eq_refl (term37 A B)). Qed.
Lemma lem4582536 {A B : Type'} : (term38 A B) = (term39 A B).
Proof. exact (MK_COMB (@lem4582535 A B) (@lem4582532 A B)). Qed.
Lemma lem4582539 {B : Type'} : (term40 B) = (term40 B).
Proof. exact (eq_refl (term40 B)). Qed.
Lemma lem4582540 {A B : Type'} : (term41 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem4582539 B) (@lem4582536 A B)). Qed.
Lemma lem4582543 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (eq_refl (term43 A B)). Qed.
Lemma lem4582544 {A B : Type'} : (term44 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem4582543 A B) (@lem4582540 A B)). Qed.
Lemma lem4582547 {A B : Type'} : (term46 A B) = (term46 A B).
Proof. exact (eq_refl (term46 A B)). Qed.
Lemma lem4582548 {A B : Type'} : (term47 A B) = (term48 A B).
Proof. exact (MK_COMB (@lem4582547 A B) (@lem4582544 A B)). Qed.
Lemma lem4582551 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (eq_refl (term40 A)). Qed.
Lemma lem4582552 {A B : Type'} : (term49 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem4582551 A) (@lem4582548 A B)). Qed.
Lemma lem4582555 {B : Type'} : (term51 B) = (term51 B).
Proof. exact (eq_refl (term51 B)). Qed.
Lemma lem4582556 {A B : Type'} : (term52 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem4582555 B) (@lem4582552 A B)). Qed.
Lemma lem4582559 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (eq_refl (term51 A)). Qed.
Lemma lem4582560 {A B : Type'} : (term54 A B) = (term55 A B).
Proof. exact (MK_COMB (@lem4582559 A) (@lem4582556 A B)). Qed.
Lemma lem4582563 {_100044 : Type'} : (term51 _100044) = (term51 _100044).
Proof. exact (eq_refl (term51 _100044)). Qed.
Lemma lem4582564 {_100044 A B : Type'} : (term56 _100044 A B) = (term57 _100044 A B).
Proof. exact (MK_COMB (@lem4582563 _100044) (@lem4582560 A B)). Qed.
Lemma lem4582567 {A B : Type'} : (term58 A B) = (term58 A B).
Proof. exact (eq_refl (term58 A B)). Qed.
Lemma lem4582574 {_100044 A B : Type'} : (term20 _100044 A B) = (term59 _100044 A B).
Proof. exact (MK_COMB (@lem4582567 A B) (@lem4582564 _100044 A B)). Qed.
Lemma lem4582583 {A B : Type'} (n : nat) (m : nat) : (term60 A B n m) = (term60 A B n m).
Proof. exact (eq_refl (term60 A B n m)). Qed.
Lemma lem4582584 {A B : Type'} (m : nat) : (term61 A B m) = (term61 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4582583 A B n m)). Qed.
Lemma lem4582585 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582586 {A B : Type'} (m : nat) : (term62 A B m) = (term62 A B m).
Proof. exact (MK_COMB (@lem4582585) (@lem4582584 A B m)). Qed.
Lemma lem4582587 {A B : Type'} : (term63 A B) = (term63 A B).
Proof. exact (fun_ext (fun m : nat => @lem4582586 A B m)). Qed.
Lemma lem4582588 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582589 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (MK_COMB (@lem4582588) (@lem4582587 A B)). Qed.
Lemma lem4582590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4582591 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem4582590) (@lem4582589 A B)). Qed.
Lemma lem4582600 {B : Type'} (n : nat) (m : nat) : (term64 B n m) = (term64 B n m).
Proof. exact (eq_refl (term64 B n m)). Qed.
Lemma lem4582601 {B : Type'} (m : nat) : (term65 B m) = (term65 B m).
Proof. exact (fun_ext (fun n : nat => @lem4582600 B n m)). Qed.
Lemma lem4582602 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582603 {B : Type'} (m : nat) : (term66 B m) = (term66 B m).
Proof. exact (MK_COMB (@lem4582602) (@lem4582601 B m)). Qed.
Lemma lem4582604 {B : Type'} : (term67 B) = (term67 B).
Proof. exact (fun_ext (fun m : nat => @lem4582603 B m)). Qed.
Lemma lem4582605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582606 {B : Type'} : (term12 B) = (term12 B).
Proof. exact (MK_COMB (@lem4582605) (@lem4582604 B)). Qed.
Lemma lem4582607 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582608 {B : Type'} : (term26 B) = (term26 B).
Proof. exact (MK_COMB (@lem4582607) (@lem4582606 B)). Qed.
Lemma lem4582609 {A B : Type'} : (term28 A B) = (term28 A B).
Proof. exact (MK_COMB (@lem4582608 B) (@lem4582591 A B)). Qed.
Lemma lem4582618 {A B : Type'} (n : nat) (m : nat) : (term68 A B n m) = (term68 A B n m).
Proof. exact (eq_refl (term68 A B n m)). Qed.
Lemma lem4582619 {A B : Type'} (m : nat) : (term69 A B m) = (term69 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4582618 A B n m)). Qed.
Lemma lem4582620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582621 {A B : Type'} (m : nat) : (term70 A B m) = (term70 A B m).
Proof. exact (MK_COMB (@lem4582620) (@lem4582619 A B m)). Qed.
Lemma lem4582622 {A B : Type'} : (term71 A B) = (term71 A B).
Proof. exact (fun_ext (fun m : nat => @lem4582621 A B m)). Qed.
Lemma lem4582623 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582624 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem4582623) (@lem4582622 A B)). Qed.
Lemma lem4582625 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582626 {A B : Type'} : (term29 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem4582625) (@lem4582624 A B)). Qed.
Lemma lem4582627 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem4582626 A B) (@lem4582609 A B)). Qed.
Lemma lem4582636 {A B : Type'} (n : nat) (m : nat) : (term72 A B n m) = (term72 A B n m).
Proof. exact (eq_refl (term72 A B n m)). Qed.
Lemma lem4582637 {A B : Type'} (m : nat) : (term73 A B m) = (term73 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4582636 A B n m)). Qed.
Lemma lem4582638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582639 {A B : Type'} (m : nat) : (term74 A B m) = (term74 A B m).
Proof. exact (MK_COMB (@lem4582638) (@lem4582637 A B m)). Qed.
Lemma lem4582640 {A B : Type'} : (term75 A B) = (term75 A B).
Proof. exact (fun_ext (fun m : nat => @lem4582639 A B m)). Qed.
Lemma lem4582641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582642 {A B : Type'} : (term11 A B) = (term11 A B).
Proof. exact (MK_COMB (@lem4582641) (@lem4582640 A B)). Qed.
Lemma lem4582643 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582644 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4582643) (@lem4582642 A B)). Qed.
Lemma lem4582645 {A B : Type'} : (term34 A B) = (term34 A B).
Proof. exact (MK_COMB (@lem4582644 A B) (@lem4582627 A B)). Qed.
Lemma lem4582654 {A : Type'} (n : nat) (m : nat) : (term64 A n m) = (term64 A n m).
Proof. exact (eq_refl (term64 A n m)). Qed.
Lemma lem4582655 {A : Type'} (m : nat) : (term65 A m) = (term65 A m).
Proof. exact (fun_ext (fun n : nat => @lem4582654 A n m)). Qed.
Lemma lem4582656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582657 {A : Type'} (m : nat) : (term66 A m) = (term66 A m).
Proof. exact (MK_COMB (@lem4582656) (@lem4582655 A m)). Qed.
Lemma lem4582658 {A : Type'} : (term67 A) = (term67 A).
Proof. exact (fun_ext (fun m : nat => @lem4582657 A m)). Qed.
Lemma lem4582659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582660 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem4582659) (@lem4582658 A)). Qed.
Lemma lem4582661 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582662 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem4582661) (@lem4582660 A)). Qed.
Lemma lem4582663 {A B : Type'} : (term36 A B) = (term36 A B).
Proof. exact (MK_COMB (@lem4582662 A) (@lem4582645 A B)). Qed.
Lemma lem4582672 {A B : Type'} (s : type119 A B) (n : nat) : ((@HAS_SIZE ((A -> B) -> B) s n) = (term76 A B s n)) = ((@HAS_SIZE ((A -> B) -> B) s n) = (term76 A B s n)).
Proof. exact (eq_refl ((@HAS_SIZE ((A -> B) -> B) s n) = (term76 A B s n))). Qed.
Lemma lem4582673 {A B : Type'} (s : type119 A B) : (term77 A B s) = (term77 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4582672 A B s n)). Qed.
Lemma lem4582674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582675 {A B : Type'} (s : type119 A B) : (term78 A B s) = (term78 A B s).
Proof. exact (MK_COMB (@lem4582674) (@lem4582673 A B s)). Qed.
Lemma lem4582676 {A B : Type'} : (term79 A B) = (term79 A B).
Proof. exact (fun_ext (fun s : type119 A B => @lem4582675 A B s)). Qed.
Lemma lem4582677 {A B : Type'} : (@all (((A -> B) -> B) -> Prop)) = (@all (((A -> B) -> B) -> Prop)).
Proof. exact (eq_refl (@all (((A -> B) -> B) -> Prop))). Qed.
Lemma lem4582678 {A B : Type'} : (term17 A B) = (term17 A B).
Proof. exact (MK_COMB (@lem4582677 A B) (@lem4582676 A B)). Qed.
Lemma lem4582679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582680 {A B : Type'} : (term37 A B) = (term37 A B).
Proof. exact (MK_COMB (@lem4582679) (@lem4582678 A B)). Qed.
Lemma lem4582681 {A B : Type'} : (term39 A B) = (term39 A B).
Proof. exact (MK_COMB (@lem4582680 A B) (@lem4582663 A B)). Qed.
Lemma lem4582690 {B : Type'} (s : type488 B) (n : nat) : ((@HAS_SIZE (B -> B) s n) = (term80 B s n)) = ((@HAS_SIZE (B -> B) s n) = (term80 B s n)).
Proof. exact (eq_refl ((@HAS_SIZE (B -> B) s n) = (term80 B s n))). Qed.
Lemma lem4582691 {B : Type'} (s : type488 B) : (term81 B s) = (term81 B s).
Proof. exact (fun_ext (fun n : nat => @lem4582690 B s n)). Qed.
Lemma lem4582692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582693 {B : Type'} (s : type488 B) : (term82 B s) = (term82 B s).
Proof. exact (MK_COMB (@lem4582692) (@lem4582691 B s)). Qed.
Lemma lem4582694 {B : Type'} : (term83 B) = (term83 B).
Proof. exact (fun_ext (fun s : type488 B => @lem4582693 B s)). Qed.
Lemma lem4582695 {B : Type'} : (@all ((B -> B) -> Prop)) = (@all ((B -> B) -> Prop)).
Proof. exact (eq_refl (@all ((B -> B) -> Prop))). Qed.
Lemma lem4582696 {B : Type'} : (term18 B) = (term18 B).
Proof. exact (MK_COMB (@lem4582695 B) (@lem4582694 B)). Qed.
Lemma lem4582697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582698 {B : Type'} : (term40 B) = (term40 B).
Proof. exact (MK_COMB (@lem4582697) (@lem4582696 B)). Qed.
Lemma lem4582699 {A B : Type'} : (term42 A B) = (term42 A B).
Proof. exact (MK_COMB (@lem4582698 B) (@lem4582681 A B)). Qed.
Lemma lem4582708 {A B : Type'} (s : type404 A B) (n : nat) : ((@HAS_SIZE (A -> A -> B) s n) = (term84 A B s n)) = ((@HAS_SIZE (A -> A -> B) s n) = (term84 A B s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> A -> B) s n) = (term84 A B s n))). Qed.
Lemma lem4582709 {A B : Type'} (s : type404 A B) : (term85 A B s) = (term85 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4582708 A B s n)). Qed.
Lemma lem4582710 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582711 {A B : Type'} (s : type404 A B) : (term86 A B s) = (term86 A B s).
Proof. exact (MK_COMB (@lem4582710) (@lem4582709 A B s)). Qed.
Lemma lem4582712 {A B : Type'} : (term87 A B) = (term87 A B).
Proof. exact (fun_ext (fun s : type404 A B => @lem4582711 A B s)). Qed.
Lemma lem4582713 {A B : Type'} : (@all ((A -> A -> B) -> Prop)) = (@all ((A -> A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> A -> B) -> Prop))). Qed.
Lemma lem4582714 {A B : Type'} : (term19 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem4582713 A B) (@lem4582712 A B)). Qed.
Lemma lem4582715 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582716 {A B : Type'} : (term43 A B) = (term43 A B).
Proof. exact (MK_COMB (@lem4582715) (@lem4582714 A B)). Qed.
Lemma lem4582717 {A B : Type'} : (term45 A B) = (term45 A B).
Proof. exact (MK_COMB (@lem4582716 A B) (@lem4582699 A B)). Qed.
Lemma lem4582726 {A B : Type'} (s : type572 A B) (n : nat) : ((@HAS_SIZE (A -> B) s n) = (term88 A B s n)) = ((@HAS_SIZE (A -> B) s n) = (term88 A B s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> B) s n) = (term88 A B s n))). Qed.
Lemma lem4582727 {A B : Type'} (s : type572 A B) : (term89 A B s) = (term89 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4582726 A B s n)). Qed.
Lemma lem4582728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582729 {A B : Type'} (s : type572 A B) : (term90 A B s) = (term90 A B s).
Proof. exact (MK_COMB (@lem4582728) (@lem4582727 A B s)). Qed.
Lemma lem4582730 {A B : Type'} : (term91 A B) = (term91 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4582729 A B s)). Qed.
Lemma lem4582731 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4582732 {A B : Type'} : (term15 A B) = (term15 A B).
Proof. exact (MK_COMB (@lem4582731 A B) (@lem4582730 A B)). Qed.
Lemma lem4582733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582734 {A B : Type'} : (term46 A B) = (term46 A B).
Proof. exact (MK_COMB (@lem4582733) (@lem4582732 A B)). Qed.
Lemma lem4582735 {A B : Type'} : (term48 A B) = (term48 A B).
Proof. exact (MK_COMB (@lem4582734 A B) (@lem4582717 A B)). Qed.
Lemma lem4582744 {A : Type'} (s : type488 A) (n : nat) : ((@HAS_SIZE (A -> A) s n) = (term80 A s n)) = ((@HAS_SIZE (A -> A) s n) = (term80 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> A) s n) = (term80 A s n))). Qed.
Lemma lem4582745 {A : Type'} (s : type488 A) : (term81 A s) = (term81 A s).
Proof. exact (fun_ext (fun n : nat => @lem4582744 A s n)). Qed.
Lemma lem4582746 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582747 {A : Type'} (s : type488 A) : (term82 A s) = (term82 A s).
Proof. exact (MK_COMB (@lem4582746) (@lem4582745 A s)). Qed.
Lemma lem4582748 {A : Type'} : (term83 A) = (term83 A).
Proof. exact (fun_ext (fun s : type488 A => @lem4582747 A s)). Qed.
Lemma lem4582749 {A : Type'} : (@all ((A -> A) -> Prop)) = (@all ((A -> A) -> Prop)).
Proof. exact (eq_refl (@all ((A -> A) -> Prop))). Qed.
Lemma lem4582750 {A : Type'} : (term18 A) = (term18 A).
Proof. exact (MK_COMB (@lem4582749 A) (@lem4582748 A)). Qed.
Lemma lem4582751 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582752 {A : Type'} : (term40 A) = (term40 A).
Proof. exact (MK_COMB (@lem4582751) (@lem4582750 A)). Qed.
Lemma lem4582753 {A B : Type'} : (term50 A B) = (term50 A B).
Proof. exact (MK_COMB (@lem4582752 A) (@lem4582735 A B)). Qed.
Lemma lem4582762 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term92 B s n)) = ((@HAS_SIZE B s n) = (term92 B s n)).
Proof. exact (eq_refl ((@HAS_SIZE B s n) = (term92 B s n))). Qed.
Lemma lem4582763 {B : Type'} (s : B -> Prop) : (term93 B s) = (term93 B s).
Proof. exact (fun_ext (fun n : nat => @lem4582762 B s n)). Qed.
Lemma lem4582764 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582765 {B : Type'} (s : B -> Prop) : (term94 B s) = (term94 B s).
Proof. exact (MK_COMB (@lem4582764) (@lem4582763 B s)). Qed.
Lemma lem4582766 {B : Type'} : (term95 B) = (term95 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4582765 B s)). Qed.
Lemma lem4582767 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4582768 {B : Type'} : (term16 B) = (term16 B).
Proof. exact (MK_COMB (@lem4582767 B) (@lem4582766 B)). Qed.
Lemma lem4582769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582770 {B : Type'} : (term51 B) = (term51 B).
Proof. exact (MK_COMB (@lem4582769) (@lem4582768 B)). Qed.
Lemma lem4582771 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem4582770 B) (@lem4582753 A B)). Qed.
Lemma lem4582780 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term92 A s n)) = ((@HAS_SIZE A s n) = (term92 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term92 A s n))). Qed.
Lemma lem4582781 {A : Type'} (s : A -> Prop) : (term93 A s) = (term93 A s).
Proof. exact (fun_ext (fun n : nat => @lem4582780 A s n)). Qed.
Lemma lem4582782 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582783 {A : Type'} (s : A -> Prop) : (term94 A s) = (term94 A s).
Proof. exact (MK_COMB (@lem4582782) (@lem4582781 A s)). Qed.
Lemma lem4582784 {A : Type'} : (term95 A) = (term95 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4582783 A s)). Qed.
Lemma lem4582785 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4582786 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4582785 A) (@lem4582784 A)). Qed.
Lemma lem4582787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582788 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (MK_COMB (@lem4582787) (@lem4582786 A)). Qed.
Lemma lem4582789 {A B : Type'} : (term55 A B) = (term55 A B).
Proof. exact (MK_COMB (@lem4582788 A) (@lem4582771 A B)). Qed.
Lemma lem4582798 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : ((@HAS_SIZE _100044 s n) = (term92 _100044 s n)) = ((@HAS_SIZE _100044 s n) = (term92 _100044 s n)).
Proof. exact (eq_refl ((@HAS_SIZE _100044 s n) = (term92 _100044 s n))). Qed.
Lemma lem4582799 {_100044 : Type'} (s : _100044 -> Prop) : (term93 _100044 s) = (term93 _100044 s).
Proof. exact (fun_ext (fun n : nat => @lem4582798 _100044 s n)). Qed.
Lemma lem4582800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4582801 {_100044 : Type'} (s : _100044 -> Prop) : (term94 _100044 s) = (term94 _100044 s).
Proof. exact (MK_COMB (@lem4582800) (@lem4582799 _100044 s)). Qed.
Lemma lem4582802 {_100044 : Type'} : (term95 _100044) = (term95 _100044).
Proof. exact (fun_ext (fun s : _100044 -> Prop => @lem4582801 _100044 s)). Qed.
Lemma lem4582803 {_100044 : Type'} : (@all (_100044 -> Prop)) = (@all (_100044 -> Prop)).
Proof. exact (eq_refl (@all (_100044 -> Prop))). Qed.
Lemma lem4582804 {_100044 : Type'} : (term16 _100044) = (term16 _100044).
Proof. exact (MK_COMB (@lem4582803 _100044) (@lem4582802 _100044)). Qed.
Lemma lem4582805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4582806 {_100044 : Type'} : (term51 _100044) = (term51 _100044).
Proof. exact (MK_COMB (@lem4582805) (@lem4582804 _100044)). Qed.
Lemma lem4582807 {_100044 A B : Type'} : (term57 _100044 A B) = (term57 _100044 A B).
Proof. exact (MK_COMB (@lem4582806 _100044) (@lem4582789 A B)). Qed.
Lemma lem4582820 {A B : Type'} : (term58 A B) = (term58 A B).
Proof. exact (eq_refl (term58 A B)). Qed.
Lemma lem4582821 {_100044 A B : Type'} : (term59 _100044 A B) = (term59 _100044 A B).
Proof. exact (MK_COMB (@lem4582820 A B) (@lem4582807 _100044 A B)). Qed.
Lemma lem4583046 {_100044 A B : Type'} : (term20 _100044 A B) = (term59 _100044 A B).
Proof. exact (TRANS (@lem4582574 _100044 A B) (@lem4582821 _100044 A B)). Qed.
Lemma lem4583047 {_100044 A B : Type'} : (term59 _100044 A B) = (term20 _100044 A B).
Proof. exact (SYM (@lem4583046 _100044 A B)). Qed.
Lemma lem4583048 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem4583050 {A : Type'} (h1 : term16 A) : term16 A.
Proof. exact (h1). Qed.
Lemma lem4583051 {B : Type'} (h1 : term16 B) : term16 B.
Proof. exact (h1). Qed.
Lemma lem4583053 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem4583058 {A B : Type'} (h1 : term11 A B) : term11 A B.
Proof. exact (h1). Qed.
Lemma lem4583076 {A B : Type'} : (term10 A B) = (term96 A B).
Proof. exact (@lem17362 (term97 A B) ((@CARD (A -> B) (@UNIV (A -> B))) = (term98 A B))). Qed.
Lemma lem4583385 {A : Type'} (s : A -> Prop) (n : nat) : (term99 A s n) = (term100 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem4583391 {A : Type'} (s : A -> Prop) (n : nat) : (term101 A s n) = (term101 A s n).
Proof. exact (eq_refl (term101 A s n)). Qed.
Lemma lem4583393 {A : Type'} (s : A -> Prop) (n : nat) : (term102 A s n) = (term102 A s n).
Proof. exact (eq_refl (term102 A s n)). Qed.
Lemma lem4583394 {A : Type'} (s : A -> Prop) (n : nat) : (term103 A s n) = (term104 A s n).
Proof. exact (MK_COMB (@lem4583393 A s n) (@lem4583385 A s n)). Qed.
Lemma lem4583395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583396 {A : Type'} (s : A -> Prop) (n : nat) : (term105 A s n) = (term106 A s n).
Proof. exact (MK_COMB (@lem4583395) (@lem4583394 A s n)). Qed.
Lemma lem4583397 {A : Type'} (s : A -> Prop) (n : nat) : (term107 A s n) = (term108 A s n).
Proof. exact (MK_COMB (@lem4583396 A s n) (@lem4583391 A s n)). Qed.
Lemma lem4583398 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term92 A s n)) = (term107 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term92 A s n)). Qed.
Lemma lem4583399 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term92 A s n)) = (term108 A s n).
Proof. exact (TRANS (@lem4583398 A s n) (@lem4583397 A s n)). Qed.
Lemma lem4583400 {A : Type'} (s : A -> Prop) : (term93 A s) = (term109 A s).
Proof. exact (fun_ext (fun n : nat => @lem4583399 A s n)). Qed.
Lemma lem4583401 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583402 {A : Type'} (s : A -> Prop) : (term94 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem4583401) (@lem4583400 A s)). Qed.
Lemma lem4583403 {A : Type'} : (term95 A) = (term111 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4583402 A s)). Qed.
Lemma lem4583404 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4583405 {A : Type'} : (term16 A) = (term112 A).
Proof. exact (MK_COMB (@lem4583404 A) (@lem4583403 A)). Qed.
Lemma lem4583411 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4583412 (P : nat -> Prop) (Q : nat -> Prop) : (term115 P Q) = (term116 P Q).
Proof. exact (@lem4583411 nat P Q). Qed.
Lemma lem4583413 {A : Type'} (s : A -> Prop) : (term117 A s) = (term118 A s).
Proof. exact (@lem4583412 (term119 A s) (term120 A s)). Qed.
Lemma lem4583414 {A : Type'} (s : A -> Prop) (n : nat) : (term121 A s n) = (term104 A s n).
Proof. exact (eq_refl (term121 A s n)). Qed.
Lemma lem4583415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583416 {A : Type'} (s : A -> Prop) (n : nat) : (term122 A s n) = (term106 A s n).
Proof. exact (MK_COMB (@lem4583415) (@lem4583414 A s n)). Qed.
Lemma lem4583417 {A : Type'} (s : A -> Prop) (n : nat) : (term123 A s n) = (term101 A s n).
Proof. exact (eq_refl (term123 A s n)). Qed.
Lemma lem4583418 {A : Type'} (s : A -> Prop) (n : nat) : (term124 A s n) = (term108 A s n).
Proof. exact (MK_COMB (@lem4583416 A s n) (@lem4583417 A s n)). Qed.
Lemma lem4583419 {A : Type'} (s : A -> Prop) : (term125 A s) = (term109 A s).
Proof. exact (fun_ext (fun n : nat => @lem4583418 A s n)). Qed.
Lemma lem4583420 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583421 {A : Type'} (s : A -> Prop) : (term117 A s) = (term110 A s).
Proof. exact (MK_COMB (@lem4583420) (@lem4583419 A s)). Qed.
Lemma lem4583422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4583423 {A : Type'} (s : A -> Prop) : (term126 A s) = (term127 A s).
Proof. exact (MK_COMB (@lem4583422) (@lem4583421 A s)). Qed.
Lemma lem4583424 {A : Type'} (s : A -> Prop) (n : nat) : (term121 A s n) = (term104 A s n).
Proof. exact (eq_refl (term121 A s n)). Qed.
Lemma lem4583425 {A : Type'} (s : A -> Prop) : (term128 A s) = (term119 A s).
Proof. exact (fun_ext (fun n : nat => @lem4583424 A s n)). Qed.
Lemma lem4583426 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583427 {A : Type'} (s : A -> Prop) : (term129 A s) = (term130 A s).
Proof. exact (MK_COMB (@lem4583426) (@lem4583425 A s)). Qed.
Lemma lem4583428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583429 {A : Type'} (s : A -> Prop) : (term131 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem4583428) (@lem4583427 A s)). Qed.
Lemma lem4583430 {A : Type'} (s : A -> Prop) (n : nat) : (term123 A s n) = (term101 A s n).
Proof. exact (eq_refl (term123 A s n)). Qed.
Lemma lem4583431 {A : Type'} (s : A -> Prop) : (term133 A s) = (term120 A s).
Proof. exact (fun_ext (fun n : nat => @lem4583430 A s n)). Qed.
Lemma lem4583432 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583433 {A : Type'} (s : A -> Prop) : (term134 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem4583432) (@lem4583431 A s)). Qed.
Lemma lem4583434 {A : Type'} (s : A -> Prop) : (term118 A s) = (term136 A s).
Proof. exact (MK_COMB (@lem4583429 A s) (@lem4583433 A s)). Qed.
Lemma lem4583435 {A : Type'} (s : A -> Prop) : ((term117 A s) = (term118 A s)) = ((term110 A s) = (term136 A s)).
Proof. exact (MK_COMB (@lem4583423 A s) (@lem4583434 A s)). Qed.
Lemma lem4583436 {A : Type'} (s : A -> Prop) : (term110 A s) = (term136 A s).
Proof. exact (EQ_MP (@lem4583435 A s) (@lem4583413 A s)). Qed.
Lemma lem4583533 {A : Type'} : (term111 A) = (term137 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4583436 A s)). Qed.
Lemma lem4583534 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4583535 {A : Type'} : (term112 A) = (term138 A).
Proof. exact (MK_COMB (@lem4583534 A) (@lem4583533 A)). Qed.
Lemma lem4583537 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4583538 {A : Type'} (P : type686 A) (Q : type686 A) : (term139 A P Q) = (term140 A P Q).
Proof. exact (@lem4583537 (A -> Prop) P Q). Qed.
Lemma lem4583539 {A : Type'} : (term141 A) = (term142 A).
Proof. exact (@lem4583538 A (term143 A) (term144 A)). Qed.
Lemma lem4583540 {A : Type'} (s : A -> Prop) : (term145 A s) = (term130 A s).
Proof. exact (eq_refl (term145 A s)). Qed.
Lemma lem4583541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583542 {A : Type'} (s : A -> Prop) : (term146 A s) = (term132 A s).
Proof. exact (MK_COMB (@lem4583541) (@lem4583540 A s)). Qed.
Lemma lem4583543 {A : Type'} (s : A -> Prop) : (term147 A s) = (term135 A s).
Proof. exact (eq_refl (term147 A s)). Qed.
Lemma lem4583544 {A : Type'} (s : A -> Prop) : (term148 A s) = (term136 A s).
Proof. exact (MK_COMB (@lem4583542 A s) (@lem4583543 A s)). Qed.
Lemma lem4583545 {A : Type'} : (term149 A) = (term137 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4583544 A s)). Qed.
Lemma lem4583546 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4583547 {A : Type'} : (term141 A) = (term138 A).
Proof. exact (MK_COMB (@lem4583546 A) (@lem4583545 A)). Qed.
Lemma lem4583548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4583549 {A : Type'} : (term150 A) = (term151 A).
Proof. exact (MK_COMB (@lem4583548) (@lem4583547 A)). Qed.
Lemma lem4583550 {A : Type'} (s : A -> Prop) : (term145 A s) = (term130 A s).
Proof. exact (eq_refl (term145 A s)). Qed.
Lemma lem4583551 {A : Type'} : (term152 A) = (term143 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4583550 A s)). Qed.
Lemma lem4583552 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4583553 {A : Type'} : (term153 A) = (term154 A).
Proof. exact (MK_COMB (@lem4583552 A) (@lem4583551 A)). Qed.
Lemma lem4583554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583555 {A : Type'} : (term155 A) = (term156 A).
Proof. exact (MK_COMB (@lem4583554) (@lem4583553 A)). Qed.
Lemma lem4583556 {A : Type'} (s : A -> Prop) : (term147 A s) = (term135 A s).
Proof. exact (eq_refl (term147 A s)). Qed.
Lemma lem4583557 {A : Type'} : (term157 A) = (term144 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4583556 A s)). Qed.
Lemma lem4583558 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4583559 {A : Type'} : (term158 A) = (term159 A).
Proof. exact (MK_COMB (@lem4583558 A) (@lem4583557 A)). Qed.
Lemma lem4583560 {A : Type'} : (term142 A) = (term160 A).
Proof. exact (MK_COMB (@lem4583555 A) (@lem4583559 A)). Qed.
Lemma lem4583561 {A : Type'} : ((term141 A) = (term142 A)) = ((term138 A) = (term160 A)).
Proof. exact (MK_COMB (@lem4583549 A) (@lem4583560 A)). Qed.
Lemma lem4583562 {A : Type'} : (term138 A) = (term160 A).
Proof. exact (EQ_MP (@lem4583561 A) (@lem4583539 A)). Qed.
Lemma lem4583669 {A : Type'} : (term112 A) = (term160 A).
Proof. exact (TRANS (@lem4583535 A) (@lem4583562 A)). Qed.
Lemma lem4583670 {A : Type'} : (term16 A) = (term160 A).
Proof. exact (TRANS (@lem4583405 A) (@lem4583669 A)). Qed.
Lemma lem4583671 {A : Type'} (h1 : term16 A) : term160 A.
Proof. exact (EQ_MP (@lem4583670 A) (@lem4583050 A h1)). Qed.
Lemma lem4583682 {B : Type'} (s : B -> Prop) (n : nat) : (term99 B s n) = (term100 B s n).
Proof. exact (@lem17045 (@FINITE B s) ((@CARD B s) = n)). Qed.
Lemma lem4583688 {B : Type'} (s : B -> Prop) (n : nat) : (term101 B s n) = (term101 B s n).
Proof. exact (eq_refl (term101 B s n)). Qed.
Lemma lem4583690 {B : Type'} (s : B -> Prop) (n : nat) : (term102 B s n) = (term102 B s n).
Proof. exact (eq_refl (term102 B s n)). Qed.
Lemma lem4583691 {B : Type'} (s : B -> Prop) (n : nat) : (term103 B s n) = (term104 B s n).
Proof. exact (MK_COMB (@lem4583690 B s n) (@lem4583682 B s n)). Qed.
Lemma lem4583692 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583693 {B : Type'} (s : B -> Prop) (n : nat) : (term105 B s n) = (term106 B s n).
Proof. exact (MK_COMB (@lem4583692) (@lem4583691 B s n)). Qed.
Lemma lem4583694 {B : Type'} (s : B -> Prop) (n : nat) : (term107 B s n) = (term108 B s n).
Proof. exact (MK_COMB (@lem4583693 B s n) (@lem4583688 B s n)). Qed.
Lemma lem4583695 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term92 B s n)) = (term107 B s n).
Proof. exact (@lem17784 (@HAS_SIZE B s n) (term92 B s n)). Qed.
Lemma lem4583696 {B : Type'} (s : B -> Prop) (n : nat) : ((@HAS_SIZE B s n) = (term92 B s n)) = (term108 B s n).
Proof. exact (TRANS (@lem4583695 B s n) (@lem4583694 B s n)). Qed.
Lemma lem4583697 {B : Type'} (s : B -> Prop) : (term93 B s) = (term109 B s).
Proof. exact (fun_ext (fun n : nat => @lem4583696 B s n)). Qed.
Lemma lem4583698 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583699 {B : Type'} (s : B -> Prop) : (term94 B s) = (term110 B s).
Proof. exact (MK_COMB (@lem4583698) (@lem4583697 B s)). Qed.
Lemma lem4583700 {B : Type'} : (term95 B) = (term111 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4583699 B s)). Qed.
Lemma lem4583701 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4583702 {B : Type'} : (term16 B) = (term112 B).
Proof. exact (MK_COMB (@lem4583701 B) (@lem4583700 B)). Qed.
Lemma lem4583708 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4583709 (P : nat -> Prop) (Q : nat -> Prop) : (term115 P Q) = (term116 P Q).
Proof. exact (@lem4583708 nat P Q). Qed.
Lemma lem4583710 {B : Type'} (s : B -> Prop) : (term117 B s) = (term118 B s).
Proof. exact (@lem4583709 (term119 B s) (term120 B s)). Qed.
Lemma lem4583711 {B : Type'} (s : B -> Prop) (n : nat) : (term121 B s n) = (term104 B s n).
Proof. exact (eq_refl (term121 B s n)). Qed.
Lemma lem4583712 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583713 {B : Type'} (s : B -> Prop) (n : nat) : (term122 B s n) = (term106 B s n).
Proof. exact (MK_COMB (@lem4583712) (@lem4583711 B s n)). Qed.
Lemma lem4583714 {B : Type'} (s : B -> Prop) (n : nat) : (term123 B s n) = (term101 B s n).
Proof. exact (eq_refl (term123 B s n)). Qed.
Lemma lem4583715 {B : Type'} (s : B -> Prop) (n : nat) : (term124 B s n) = (term108 B s n).
Proof. exact (MK_COMB (@lem4583713 B s n) (@lem4583714 B s n)). Qed.
Lemma lem4583716 {B : Type'} (s : B -> Prop) : (term125 B s) = (term109 B s).
Proof. exact (fun_ext (fun n : nat => @lem4583715 B s n)). Qed.
Lemma lem4583717 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583718 {B : Type'} (s : B -> Prop) : (term117 B s) = (term110 B s).
Proof. exact (MK_COMB (@lem4583717) (@lem4583716 B s)). Qed.
Lemma lem4583719 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4583720 {B : Type'} (s : B -> Prop) : (term126 B s) = (term127 B s).
Proof. exact (MK_COMB (@lem4583719) (@lem4583718 B s)). Qed.
Lemma lem4583721 {B : Type'} (s : B -> Prop) (n : nat) : (term121 B s n) = (term104 B s n).
Proof. exact (eq_refl (term121 B s n)). Qed.
Lemma lem4583722 {B : Type'} (s : B -> Prop) : (term128 B s) = (term119 B s).
Proof. exact (fun_ext (fun n : nat => @lem4583721 B s n)). Qed.
Lemma lem4583723 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583724 {B : Type'} (s : B -> Prop) : (term129 B s) = (term130 B s).
Proof. exact (MK_COMB (@lem4583723) (@lem4583722 B s)). Qed.
Lemma lem4583725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583726 {B : Type'} (s : B -> Prop) : (term131 B s) = (term132 B s).
Proof. exact (MK_COMB (@lem4583725) (@lem4583724 B s)). Qed.
Lemma lem4583727 {B : Type'} (s : B -> Prop) (n : nat) : (term123 B s n) = (term101 B s n).
Proof. exact (eq_refl (term123 B s n)). Qed.
Lemma lem4583728 {B : Type'} (s : B -> Prop) : (term133 B s) = (term120 B s).
Proof. exact (fun_ext (fun n : nat => @lem4583727 B s n)). Qed.
Lemma lem4583729 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4583730 {B : Type'} (s : B -> Prop) : (term134 B s) = (term135 B s).
Proof. exact (MK_COMB (@lem4583729) (@lem4583728 B s)). Qed.
Lemma lem4583731 {B : Type'} (s : B -> Prop) : (term118 B s) = (term136 B s).
Proof. exact (MK_COMB (@lem4583726 B s) (@lem4583730 B s)). Qed.
Lemma lem4583732 {B : Type'} (s : B -> Prop) : ((term117 B s) = (term118 B s)) = ((term110 B s) = (term136 B s)).
Proof. exact (MK_COMB (@lem4583720 B s) (@lem4583731 B s)). Qed.
Lemma lem4583733 {B : Type'} (s : B -> Prop) : (term110 B s) = (term136 B s).
Proof. exact (EQ_MP (@lem4583732 B s) (@lem4583710 B s)). Qed.
Lemma lem4583830 {B : Type'} : (term111 B) = (term137 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4583733 B s)). Qed.
Lemma lem4583831 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4583832 {B : Type'} : (term112 B) = (term138 B).
Proof. exact (MK_COMB (@lem4583831 B) (@lem4583830 B)). Qed.
Lemma lem4583834 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4583835 {B : Type'} (P : type686 B) (Q : type686 B) : (term139 B P Q) = (term140 B P Q).
Proof. exact (@lem4583834 (B -> Prop) P Q). Qed.
Lemma lem4583836 {B : Type'} : (term141 B) = (term142 B).
Proof. exact (@lem4583835 B (term143 B) (term144 B)). Qed.
Lemma lem4583837 {B : Type'} (s : B -> Prop) : (term145 B s) = (term130 B s).
Proof. exact (eq_refl (term145 B s)). Qed.
Lemma lem4583838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583839 {B : Type'} (s : B -> Prop) : (term146 B s) = (term132 B s).
Proof. exact (MK_COMB (@lem4583838) (@lem4583837 B s)). Qed.
Lemma lem4583840 {B : Type'} (s : B -> Prop) : (term147 B s) = (term135 B s).
Proof. exact (eq_refl (term147 B s)). Qed.
Lemma lem4583841 {B : Type'} (s : B -> Prop) : (term148 B s) = (term136 B s).
Proof. exact (MK_COMB (@lem4583839 B s) (@lem4583840 B s)). Qed.
Lemma lem4583842 {B : Type'} : (term149 B) = (term137 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4583841 B s)). Qed.
Lemma lem4583843 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4583844 {B : Type'} : (term141 B) = (term138 B).
Proof. exact (MK_COMB (@lem4583843 B) (@lem4583842 B)). Qed.
Lemma lem4583845 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4583846 {B : Type'} : (term150 B) = (term151 B).
Proof. exact (MK_COMB (@lem4583845) (@lem4583844 B)). Qed.
Lemma lem4583847 {B : Type'} (s : B -> Prop) : (term145 B s) = (term130 B s).
Proof. exact (eq_refl (term145 B s)). Qed.
Lemma lem4583848 {B : Type'} : (term152 B) = (term143 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4583847 B s)). Qed.
Lemma lem4583849 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4583850 {B : Type'} : (term153 B) = (term154 B).
Proof. exact (MK_COMB (@lem4583849 B) (@lem4583848 B)). Qed.
Lemma lem4583851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4583852 {B : Type'} : (term155 B) = (term156 B).
Proof. exact (MK_COMB (@lem4583851) (@lem4583850 B)). Qed.
Lemma lem4583853 {B : Type'} (s : B -> Prop) : (term147 B s) = (term135 B s).
Proof. exact (eq_refl (term147 B s)). Qed.
Lemma lem4583854 {B : Type'} : (term157 B) = (term144 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4583853 B s)). Qed.
Lemma lem4583855 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4583856 {B : Type'} : (term158 B) = (term159 B).
Proof. exact (MK_COMB (@lem4583855 B) (@lem4583854 B)). Qed.
Lemma lem4583857 {B : Type'} : (term142 B) = (term160 B).
Proof. exact (MK_COMB (@lem4583852 B) (@lem4583856 B)). Qed.
Lemma lem4583858 {B : Type'} : ((term141 B) = (term142 B)) = ((term138 B) = (term160 B)).
Proof. exact (MK_COMB (@lem4583846 B) (@lem4583857 B)). Qed.
Lemma lem4583859 {B : Type'} : (term138 B) = (term160 B).
Proof. exact (EQ_MP (@lem4583858 B) (@lem4583836 B)). Qed.
Lemma lem4583966 {B : Type'} : (term112 B) = (term160 B).
Proof. exact (TRANS (@lem4583832 B) (@lem4583859 B)). Qed.
Lemma lem4583967 {B : Type'} : (term16 B) = (term160 B).
Proof. exact (TRANS (@lem4583702 B) (@lem4583966 B)). Qed.
Lemma lem4583968 {B : Type'} (h1 : term16 B) : term160 B.
Proof. exact (EQ_MP (@lem4583967 B) (@lem4583051 B h1)). Qed.
Lemma lem4584276 {A B : Type'} (s : type572 A B) (n : nat) : (term161 A B s n) = (term162 A B s n).
Proof. exact (@lem17045 (@FINITE (A -> B) s) ((@CARD (A -> B) s) = n)). Qed.
Lemma lem4584282 {A B : Type'} (s : type572 A B) (n : nat) : (term163 A B s n) = (term163 A B s n).
Proof. exact (eq_refl (term163 A B s n)). Qed.
Lemma lem4584284 {A B : Type'} (s : type572 A B) (n : nat) : (term164 A B s n) = (term164 A B s n).
Proof. exact (eq_refl (term164 A B s n)). Qed.
Lemma lem4584285 {A B : Type'} (s : type572 A B) (n : nat) : (term165 A B s n) = (term166 A B s n).
Proof. exact (MK_COMB (@lem4584284 A B s n) (@lem4584276 A B s n)). Qed.
Lemma lem4584286 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4584287 {A B : Type'} (s : type572 A B) (n : nat) : (term167 A B s n) = (term168 A B s n).
Proof. exact (MK_COMB (@lem4584286) (@lem4584285 A B s n)). Qed.
Lemma lem4584288 {A B : Type'} (s : type572 A B) (n : nat) : (term169 A B s n) = (term170 A B s n).
Proof. exact (MK_COMB (@lem4584287 A B s n) (@lem4584282 A B s n)). Qed.
Lemma lem4584289 {A B : Type'} (s : type572 A B) (n : nat) : ((@HAS_SIZE (A -> B) s n) = (term88 A B s n)) = (term169 A B s n).
Proof. exact (@lem17784 (@HAS_SIZE (A -> B) s n) (term88 A B s n)). Qed.
Lemma lem4584290 {A B : Type'} (s : type572 A B) (n : nat) : ((@HAS_SIZE (A -> B) s n) = (term88 A B s n)) = (term170 A B s n).
Proof. exact (TRANS (@lem4584289 A B s n) (@lem4584288 A B s n)). Qed.
Lemma lem4584291 {A B : Type'} (s : type572 A B) : (term89 A B s) = (term171 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4584290 A B s n)). Qed.
Lemma lem4584292 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4584293 {A B : Type'} (s : type572 A B) : (term90 A B s) = (term172 A B s).
Proof. exact (MK_COMB (@lem4584292) (@lem4584291 A B s)). Qed.
Lemma lem4584294 {A B : Type'} : (term91 A B) = (term173 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4584293 A B s)). Qed.
Lemma lem4584295 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4584296 {A B : Type'} : (term15 A B) = (term174 A B).
Proof. exact (MK_COMB (@lem4584295 A B) (@lem4584294 A B)). Qed.
Lemma lem4584302 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4584303 (P : nat -> Prop) (Q : nat -> Prop) : (term115 P Q) = (term116 P Q).
Proof. exact (@lem4584302 nat P Q). Qed.
Lemma lem4584304 {A B : Type'} (s : type572 A B) : (term175 A B s) = (term176 A B s).
Proof. exact (@lem4584303 (term177 A B s) (term178 A B s)). Qed.
Lemma lem4584305 {A B : Type'} (s : type572 A B) (n : nat) : (term179 A B s n) = (term166 A B s n).
Proof. exact (eq_refl (term179 A B s n)). Qed.
Lemma lem4584306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4584307 {A B : Type'} (s : type572 A B) (n : nat) : (term180 A B s n) = (term168 A B s n).
Proof. exact (MK_COMB (@lem4584306) (@lem4584305 A B s n)). Qed.
Lemma lem4584308 {A B : Type'} (s : type572 A B) (n : nat) : (term181 A B s n) = (term163 A B s n).
Proof. exact (eq_refl (term181 A B s n)). Qed.
Lemma lem4584309 {A B : Type'} (s : type572 A B) (n : nat) : (term182 A B s n) = (term170 A B s n).
Proof. exact (MK_COMB (@lem4584307 A B s n) (@lem4584308 A B s n)). Qed.
Lemma lem4584310 {A B : Type'} (s : type572 A B) : (term183 A B s) = (term171 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4584309 A B s n)). Qed.
Lemma lem4584311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4584312 {A B : Type'} (s : type572 A B) : (term175 A B s) = (term172 A B s).
Proof. exact (MK_COMB (@lem4584311) (@lem4584310 A B s)). Qed.
Lemma lem4584313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4584314 {A B : Type'} (s : type572 A B) : (term184 A B s) = (term185 A B s).
Proof. exact (MK_COMB (@lem4584313) (@lem4584312 A B s)). Qed.
Lemma lem4584315 {A B : Type'} (s : type572 A B) (n : nat) : (term179 A B s n) = (term166 A B s n).
Proof. exact (eq_refl (term179 A B s n)). Qed.
Lemma lem4584316 {A B : Type'} (s : type572 A B) : (term186 A B s) = (term177 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4584315 A B s n)). Qed.
Lemma lem4584317 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4584318 {A B : Type'} (s : type572 A B) : (term187 A B s) = (term188 A B s).
Proof. exact (MK_COMB (@lem4584317) (@lem4584316 A B s)). Qed.
Lemma lem4584319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4584320 {A B : Type'} (s : type572 A B) : (term189 A B s) = (term190 A B s).
Proof. exact (MK_COMB (@lem4584319) (@lem4584318 A B s)). Qed.
Lemma lem4584321 {A B : Type'} (s : type572 A B) (n : nat) : (term181 A B s n) = (term163 A B s n).
Proof. exact (eq_refl (term181 A B s n)). Qed.
Lemma lem4584322 {A B : Type'} (s : type572 A B) : (term191 A B s) = (term178 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4584321 A B s n)). Qed.
Lemma lem4584323 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4584324 {A B : Type'} (s : type572 A B) : (term192 A B s) = (term193 A B s).
Proof. exact (MK_COMB (@lem4584323) (@lem4584322 A B s)). Qed.
Lemma lem4584325 {A B : Type'} (s : type572 A B) : (term176 A B s) = (term194 A B s).
Proof. exact (MK_COMB (@lem4584320 A B s) (@lem4584324 A B s)). Qed.
Lemma lem4584326 {A B : Type'} (s : type572 A B) : ((term175 A B s) = (term176 A B s)) = ((term172 A B s) = (term194 A B s)).
Proof. exact (MK_COMB (@lem4584314 A B s) (@lem4584325 A B s)). Qed.
Lemma lem4584327 {A B : Type'} (s : type572 A B) : (term172 A B s) = (term194 A B s).
Proof. exact (EQ_MP (@lem4584326 A B s) (@lem4584304 A B s)). Qed.
Lemma lem4584424 {A B : Type'} : (term173 A B) = (term195 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4584327 A B s)). Qed.
Lemma lem4584425 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4584426 {A B : Type'} : (term174 A B) = (term196 A B).
Proof. exact (MK_COMB (@lem4584425 A B) (@lem4584424 A B)). Qed.
Lemma lem4584428 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term113 A P Q) = (term114 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4584429 {A B : Type'} (P : type122 A B) (Q : type122 A B) : (term197 A B P Q) = (term198 A B P Q).
Proof. exact (@lem4584428 (type572 A B) P Q). Qed.
Lemma lem4584430 {A B : Type'} : (term199 A B) = (term200 A B).
Proof. exact (@lem4584429 A B (term201 A B) (term202 A B)). Qed.
Lemma lem4584431 {A B : Type'} (s : type572 A B) : (term203 A B s) = (term188 A B s).
Proof. exact (eq_refl (term203 A B s)). Qed.
Lemma lem4584432 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4584433 {A B : Type'} (s : type572 A B) : (term204 A B s) = (term190 A B s).
Proof. exact (MK_COMB (@lem4584432) (@lem4584431 A B s)). Qed.
Lemma lem4584434 {A B : Type'} (s : type572 A B) : (term205 A B s) = (term193 A B s).
Proof. exact (eq_refl (term205 A B s)). Qed.
Lemma lem4584435 {A B : Type'} (s : type572 A B) : (term206 A B s) = (term194 A B s).
Proof. exact (MK_COMB (@lem4584433 A B s) (@lem4584434 A B s)). Qed.
Lemma lem4584436 {A B : Type'} : (term207 A B) = (term195 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4584435 A B s)). Qed.
Lemma lem4584437 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4584438 {A B : Type'} : (term199 A B) = (term196 A B).
Proof. exact (MK_COMB (@lem4584437 A B) (@lem4584436 A B)). Qed.
Lemma lem4584439 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4584440 {A B : Type'} : (term208 A B) = (term209 A B).
Proof. exact (MK_COMB (@lem4584439) (@lem4584438 A B)). Qed.
Lemma lem4584441 {A B : Type'} (s : type572 A B) : (term203 A B s) = (term188 A B s).
Proof. exact (eq_refl (term203 A B s)). Qed.
Lemma lem4584442 {A B : Type'} : (term210 A B) = (term201 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4584441 A B s)). Qed.
Lemma lem4584443 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4584444 {A B : Type'} : (term211 A B) = (term212 A B).
Proof. exact (MK_COMB (@lem4584443 A B) (@lem4584442 A B)). Qed.
Lemma lem4584445 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4584446 {A B : Type'} : (term213 A B) = (term214 A B).
Proof. exact (MK_COMB (@lem4584445) (@lem4584444 A B)). Qed.
Lemma lem4584447 {A B : Type'} (s : type572 A B) : (term205 A B s) = (term193 A B s).
Proof. exact (eq_refl (term205 A B s)). Qed.
Lemma lem4584448 {A B : Type'} : (term215 A B) = (term202 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4584447 A B s)). Qed.
Lemma lem4584449 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4584450 {A B : Type'} : (term216 A B) = (term217 A B).
Proof. exact (MK_COMB (@lem4584449 A B) (@lem4584448 A B)). Qed.
Lemma lem4584451 {A B : Type'} : (term200 A B) = (term218 A B).
Proof. exact (MK_COMB (@lem4584446 A B) (@lem4584450 A B)). Qed.
Lemma lem4584452 {A B : Type'} : ((term199 A B) = (term200 A B)) = ((term196 A B) = (term218 A B)).
Proof. exact (MK_COMB (@lem4584440 A B) (@lem4584451 A B)). Qed.
Lemma lem4584453 {A B : Type'} : (term196 A B) = (term218 A B).
Proof. exact (EQ_MP (@lem4584452 A B) (@lem4584430 A B)). Qed.
Lemma lem4584560 {A B : Type'} : (term174 A B) = (term218 A B).
Proof. exact (TRANS (@lem4584426 A B) (@lem4584453 A B)). Qed.
Lemma lem4584561 {A B : Type'} : (term15 A B) = (term218 A B).
Proof. exact (TRANS (@lem4584296 A B) (@lem4584560 A B)). Qed.
Lemma lem4584562 {A B : Type'} (h1 : term15 A B) : term218 A B.
Proof. exact (EQ_MP (@lem4584561 A B) (@lem4583053 A B h1)). Qed.
Lemma lem4585536 {A B : Type'} (m : nat) (n : nat) : (term219 A B m n) = (term220 A B m n).
Proof. exact (@lem17045 (@HAS_SIZE A (@UNIV A) m) (@HAS_SIZE B (@UNIV B) n)). Qed.
Lemma lem4585537 {A B : Type'} (n : nat) (m : nat) : (term221 A B n m) = (term221 A B n m).
Proof. exact (eq_refl (term221 A B n m)). Qed.
Lemma lem4585538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4585539 {A B : Type'} (m : nat) (n : nat) : (term222 A B m n) = (term223 A B m n).
Proof. exact (MK_COMB (@lem4585538) (@lem4585536 A B m n)). Qed.
Lemma lem4585540 {A B : Type'} (n : nat) (m : nat) : (term224 A B n m) = (term225 A B n m).
Proof. exact (MK_COMB (@lem4585539 A B m n) (@lem4585537 A B n m)). Qed.
Lemma lem4585541 {A B : Type'} (n : nat) (m : nat) : (term72 A B n m) = (term224 A B n m).
Proof. exact (@lem17265 (term226 A B m n) (term221 A B n m)). Qed.
Lemma lem4585542 {A B : Type'} (n : nat) (m : nat) : (term72 A B n m) = (term225 A B n m).
Proof. exact (TRANS (@lem4585541 A B n m) (@lem4585540 A B n m)). Qed.
Lemma lem4585543 {A B : Type'} (m : nat) : (term73 A B m) = (term227 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4585542 A B n m)). Qed.
Lemma lem4585544 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4585545 {A B : Type'} (m : nat) : (term74 A B m) = (term228 A B m).
Proof. exact (MK_COMB (@lem4585544) (@lem4585543 A B m)). Qed.
Lemma lem4585546 {A B : Type'} : (term75 A B) = (term229 A B).
Proof. exact (fun_ext (fun m : nat => @lem4585545 A B m)). Qed.
Lemma lem4585547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4585604 {A B : Type'} : (term11 A B) = (term230 A B).
Proof. exact (MK_COMB (@lem4585547) (@lem4585546 A B)). Qed.
Lemma lem4585605 {A B : Type'} (h1 : term11 A B) : term230 A B.
Proof. exact (EQ_MP (@lem4585604 A B) (@lem4583058 A B h1)). Qed.
Lemma lem4585863 {A B : Type'} (h1 : term10 A B) : term96 A B.
Proof. exact (EQ_MP (@lem4583076 A B) (@lem4583048 A B h1)). Qed.
Lemma lem4585950 {A : Type'} (s : A -> Prop) (n : nat) : (term101 A s n) = (term101 A s n).
Proof. exact (eq_refl (term101 A s n)). Qed.
Lemma lem4585951 {A : Type'} (s : A -> Prop) : (term120 A s) = (term120 A s).
Proof. exact (fun_ext (fun n : nat => @lem4585950 A s n)). Qed.
Lemma lem4585952 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4585953 {A : Type'} (s : A -> Prop) : (term135 A s) = (term135 A s).
Proof. exact (MK_COMB (@lem4585952) (@lem4585951 A s)). Qed.
Lemma lem4585954 {A : Type'} : (term144 A) = (term144 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4585953 A s)). Qed.
Lemma lem4585955 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4585956 {A : Type'} : (term159 A) = (term159 A).
Proof. exact (MK_COMB (@lem4585955 A) (@lem4585954 A)). Qed.
Lemma lem4585981 {A : Type'} (s : A -> Prop) (n : nat) : (term104 A s n) = (term104 A s n).
Proof. exact (eq_refl (term104 A s n)). Qed.
Lemma lem4585982 {A : Type'} (s : A -> Prop) : (term119 A s) = (term119 A s).
Proof. exact (fun_ext (fun n : nat => @lem4585981 A s n)). Qed.
Lemma lem4585983 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4585984 {A : Type'} (s : A -> Prop) : (term130 A s) = (term130 A s).
Proof. exact (MK_COMB (@lem4585983) (@lem4585982 A s)). Qed.
Lemma lem4585985 {A : Type'} : (term143 A) = (term143 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4585984 A s)). Qed.
Lemma lem4585986 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4585987 {A : Type'} : (term154 A) = (term154 A).
Proof. exact (MK_COMB (@lem4585986 A) (@lem4585985 A)). Qed.
Lemma lem4585988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4585989 {A : Type'} : (term156 A) = (term156 A).
Proof. exact (MK_COMB (@lem4585988) (@lem4585987 A)). Qed.
Lemma lem4585990 {A : Type'} : (term160 A) = (term160 A).
Proof. exact (MK_COMB (@lem4585989 A) (@lem4585956 A)). Qed.
Lemma lem4585991 {A : Type'} (h1 : term16 A) : term160 A.
Proof. exact (EQ_MP (@lem4585990 A) (@lem4583671 A h1)). Qed.
Lemma lem4586014 {B : Type'} (s : B -> Prop) (n : nat) : (term101 B s n) = (term101 B s n).
Proof. exact (eq_refl (term101 B s n)). Qed.
Lemma lem4586015 {B : Type'} (s : B -> Prop) : (term120 B s) = (term120 B s).
Proof. exact (fun_ext (fun n : nat => @lem4586014 B s n)). Qed.
Lemma lem4586016 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586017 {B : Type'} (s : B -> Prop) : (term135 B s) = (term135 B s).
Proof. exact (MK_COMB (@lem4586016) (@lem4586015 B s)). Qed.
Lemma lem4586018 {B : Type'} : (term144 B) = (term144 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4586017 B s)). Qed.
Lemma lem4586019 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4586020 {B : Type'} : (term159 B) = (term159 B).
Proof. exact (MK_COMB (@lem4586019 B) (@lem4586018 B)). Qed.
Lemma lem4586045 {B : Type'} (s : B -> Prop) (n : nat) : (term104 B s n) = (term104 B s n).
Proof. exact (eq_refl (term104 B s n)). Qed.
Lemma lem4586046 {B : Type'} (s : B -> Prop) : (term119 B s) = (term119 B s).
Proof. exact (fun_ext (fun n : nat => @lem4586045 B s n)). Qed.
Lemma lem4586047 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586048 {B : Type'} (s : B -> Prop) : (term130 B s) = (term130 B s).
Proof. exact (MK_COMB (@lem4586047) (@lem4586046 B s)). Qed.
Lemma lem4586049 {B : Type'} : (term143 B) = (term143 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4586048 B s)). Qed.
Lemma lem4586050 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4586051 {B : Type'} : (term154 B) = (term154 B).
Proof. exact (MK_COMB (@lem4586050 B) (@lem4586049 B)). Qed.
Lemma lem4586052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4586053 {B : Type'} : (term156 B) = (term156 B).
Proof. exact (MK_COMB (@lem4586052) (@lem4586051 B)). Qed.
Lemma lem4586054 {B : Type'} : (term160 B) = (term160 B).
Proof. exact (MK_COMB (@lem4586053 B) (@lem4586020 B)). Qed.
Lemma lem4586055 {B : Type'} (h1 : term16 B) : term160 B.
Proof. exact (EQ_MP (@lem4586054 B) (@lem4583968 B h1)). Qed.
Lemma lem4586142 {A B : Type'} (s : type572 A B) (n : nat) : (term163 A B s n) = (term163 A B s n).
Proof. exact (eq_refl (term163 A B s n)). Qed.
Lemma lem4586143 {A B : Type'} (s : type572 A B) : (term178 A B s) = (term178 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4586142 A B s n)). Qed.
Lemma lem4586144 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586145 {A B : Type'} (s : type572 A B) : (term193 A B s) = (term193 A B s).
Proof. exact (MK_COMB (@lem4586144) (@lem4586143 A B s)). Qed.
Lemma lem4586146 {A B : Type'} : (term202 A B) = (term202 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4586145 A B s)). Qed.
Lemma lem4586147 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4586148 {A B : Type'} : (term217 A B) = (term217 A B).
Proof. exact (MK_COMB (@lem4586147 A B) (@lem4586146 A B)). Qed.
Lemma lem4586173 {A B : Type'} (s : type572 A B) (n : nat) : (term166 A B s n) = (term166 A B s n).
Proof. exact (eq_refl (term166 A B s n)). Qed.
Lemma lem4586174 {A B : Type'} (s : type572 A B) : (term177 A B s) = (term177 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4586173 A B s n)). Qed.
Lemma lem4586175 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586176 {A B : Type'} (s : type572 A B) : (term188 A B s) = (term188 A B s).
Proof. exact (MK_COMB (@lem4586175) (@lem4586174 A B s)). Qed.
Lemma lem4586177 {A B : Type'} : (term201 A B) = (term201 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4586176 A B s)). Qed.
Lemma lem4586178 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4586179 {A B : Type'} : (term212 A B) = (term212 A B).
Proof. exact (MK_COMB (@lem4586178 A B) (@lem4586177 A B)). Qed.
Lemma lem4586180 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4586181 {A B : Type'} : (term214 A B) = (term214 A B).
Proof. exact (MK_COMB (@lem4586180) (@lem4586179 A B)). Qed.
Lemma lem4586182 {A B : Type'} : (term218 A B) = (term218 A B).
Proof. exact (MK_COMB (@lem4586181 A B) (@lem4586148 A B)). Qed.
Lemma lem4586183 {A B : Type'} (h1 : term15 A B) : term218 A B.
Proof. exact (EQ_MP (@lem4586182 A B) (@lem4584562 A B h1)). Qed.
Lemma lem4586440 {A B : Type'} (n : nat) (m : nat) : (term225 A B n m) = (term225 A B n m).
Proof. exact (eq_refl (term225 A B n m)). Qed.
Lemma lem4586441 {A B : Type'} (m : nat) : (term227 A B m) = (term227 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4586440 A B n m)). Qed.
Lemma lem4586442 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586443 {A B : Type'} (m : nat) : (term228 A B m) = (term228 A B m).
Proof. exact (MK_COMB (@lem4586442) (@lem4586441 A B m)). Qed.
Lemma lem4586444 {A B : Type'} : (term229 A B) = (term229 A B).
Proof. exact (fun_ext (fun m : nat => @lem4586443 A B m)). Qed.
Lemma lem4586445 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586446 {A B : Type'} : (term230 A B) = (term230 A B).
Proof. exact (MK_COMB (@lem4586445) (@lem4586444 A B)). Qed.
Lemma lem4586447 {A B : Type'} (h1 : term11 A B) : term230 A B.
Proof. exact (EQ_MP (@lem4586446 A B) (@lem4585605 A B h1)). Qed.
Lemma lem4586562 {A B : Type'} (h1 : term15 A B) : term217 A B.
Proof. exact (proj2 (@lem4586183 A B h1)). Qed.
Lemma lem4586567 {B : Type'} (h1 : term16 B) : term154 B.
Proof. exact (proj1 (@lem4586055 B h1)). Qed.
Lemma lem4586569 {A : Type'} (h1 : term16 A) : term154 A.
Proof. exact (proj1 (@lem4585991 A h1)). Qed.
Lemma lem4586573 {A B : Type'} (h1 : term10 A B) : term97 A B.
Proof. exact (proj1 (@lem4585863 A B h1)). Qed.
Lemma lem4586611 {A B : Type'} (n : nat) (m : nat) : (term225 A B n m) = (term225 A B n m).
Proof. exact (eq_refl (term225 A B n m)). Qed.
Lemma lem4586612 {A B : Type'} (m : nat) : (term227 A B m) = (term227 A B m).
Proof. exact (fun_ext (fun n : nat => @lem4586611 A B n m)). Qed.
Lemma lem4586613 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586614 {A B : Type'} (m : nat) : (term228 A B m) = (term228 A B m).
Proof. exact (MK_COMB (@lem4586613) (@lem4586612 A B m)). Qed.
Lemma lem4586615 {A B : Type'} : (term229 A B) = (term229 A B).
Proof. exact (fun_ext (fun m : nat => @lem4586614 A B m)). Qed.
Lemma lem4586616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586618 {A B : Type'} : (term230 A B) = (term230 A B).
Proof. exact (MK_COMB (@lem4586616) (@lem4586615 A B)). Qed.
Lemma lem4586619 {A B : Type'} (h1 : term11 A B) : term230 A B.
Proof. exact (EQ_MP (@lem4586618 A B) (@lem4586447 A B h1)). Qed.
Lemma lem4586869 {A B : Type'} (s : type572 A B) (n : nat) : (term163 A B s n) = (term231 A B s n).
Proof. exact (@lem19490 (@FINITE (A -> B) s) (term232 A B s n) ((@CARD (A -> B) s) = n)). Qed.
Lemma lem4586870 {A B : Type'} (s : type572 A B) : (term178 A B s) = (term233 A B s).
Proof. exact (fun_ext (fun n : nat => @lem4586869 A B s n)). Qed.
Lemma lem4586871 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586872 {A B : Type'} (s : type572 A B) : (term193 A B s) = (term234 A B s).
Proof. exact (MK_COMB (@lem4586871) (@lem4586870 A B s)). Qed.
Lemma lem4586873 {A B : Type'} : (term202 A B) = (term235 A B).
Proof. exact (fun_ext (fun s : type572 A B => @lem4586872 A B s)). Qed.
Lemma lem4586874 {A B : Type'} : (@all ((A -> B) -> Prop)) = (@all ((A -> B) -> Prop)).
Proof. exact (eq_refl (@all ((A -> B) -> Prop))). Qed.
Lemma lem4586876 {A B : Type'} : (term217 A B) = (term236 A B).
Proof. exact (MK_COMB (@lem4586874 A B) (@lem4586873 A B)). Qed.
Lemma lem4586877 {A B : Type'} (h1 : term15 A B) : term236 A B.
Proof. exact (EQ_MP (@lem4586876 A B) (@lem4586562 A B h1)). Qed.
Lemma lem4586939 {B : Type'} (s : B -> Prop) (n : nat) : (term104 B s n) = (term104 B s n).
Proof. exact (eq_refl (term104 B s n)). Qed.
Lemma lem4586940 {B : Type'} (s : B -> Prop) : (term119 B s) = (term119 B s).
Proof. exact (fun_ext (fun n : nat => @lem4586939 B s n)). Qed.
Lemma lem4586941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586942 {B : Type'} (s : B -> Prop) : (term130 B s) = (term130 B s).
Proof. exact (MK_COMB (@lem4586941) (@lem4586940 B s)). Qed.
Lemma lem4586943 {B : Type'} : (term143 B) = (term143 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem4586942 B s)). Qed.
Lemma lem4586944 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem4586946 {B : Type'} : (term154 B) = (term154 B).
Proof. exact (MK_COMB (@lem4586944 B) (@lem4586943 B)). Qed.
Lemma lem4586947 {B : Type'} (h1 : term16 B) : term154 B.
Proof. exact (EQ_MP (@lem4586946 B) (@lem4586567 B h1)). Qed.
Lemma lem4586987 {A : Type'} (s : A -> Prop) (n : nat) : (term104 A s n) = (term104 A s n).
Proof. exact (eq_refl (term104 A s n)). Qed.
Lemma lem4586988 {A : Type'} (s : A -> Prop) : (term119 A s) = (term119 A s).
Proof. exact (fun_ext (fun n : nat => @lem4586987 A s n)). Qed.
Lemma lem4586989 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4586990 {A : Type'} (s : A -> Prop) : (term130 A s) = (term130 A s).
Proof. exact (MK_COMB (@lem4586989) (@lem4586988 A s)). Qed.
Lemma lem4586991 {A : Type'} : (term143 A) = (term143 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4586990 A s)). Qed.
Lemma lem4586992 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4586994 {A : Type'} : (term154 A) = (term154 A).
Proof. exact (MK_COMB (@lem4586992 A) (@lem4586991 A)). Qed.
Lemma lem4586995 {A : Type'} (h1 : term16 A) : term154 A.
Proof. exact (EQ_MP (@lem4586994 A) (@lem4586569 A h1)). Qed.
Lemma lem4587088 {A B : Type'} (_54949 : nat) (h1 : term11 A B) : term237 A B _54949.
Proof. exact (@lem4586619 A B h1 _54949). Qed.
Lemma lem4587089 {A B : Type'} (_54949 : nat) : (term237 A B _54949) = (term228 A B _54949).
Proof. exact (eq_refl (term237 A B _54949)). Qed.
Lemma lem4587090 {A B : Type'} (_54949 : nat) (h1 : term11 A B) : term228 A B _54949.
Proof. exact (EQ_MP (@lem4587089 A B _54949) (@lem4587088 A B _54949 h1)). Qed.
Lemma lem4587091 {A B : Type'} (_54949 : nat) (_54950 : nat) (h1 : term11 A B) : term238 A B _54949 _54950.
Proof. exact (@lem4587090 A B _54949 h1 _54950). Qed.
Lemma lem4587092 {A B : Type'} (_54950 : nat) (_54949 : nat) : (term238 A B _54949 _54950) = (term225 A B _54950 _54949).
Proof. exact (eq_refl (term238 A B _54949 _54950)). Qed.
Lemma lem4587093 {A B : Type'} (_54950 : nat) (_54949 : nat) (h1 : term11 A B) : term225 A B _54950 _54949.
Proof. exact (EQ_MP (@lem4587092 A B _54950 _54949) (@lem4587091 A B _54949 _54950 h1)). Qed.
Lemma lem4587154 {A B : Type'} (_54971 : type572 A B) (h1 : term15 A B) : term239 A B _54971.
Proof. exact (@lem4586877 A B h1 _54971). Qed.
Lemma lem4587155 {A B : Type'} (_54971 : type572 A B) : (term239 A B _54971) = (term234 A B _54971).
Proof. exact (eq_refl (term239 A B _54971)). Qed.
Lemma lem4587156 {A B : Type'} (_54971 : type572 A B) (h1 : term15 A B) : term234 A B _54971.
Proof. exact (EQ_MP (@lem4587155 A B _54971) (@lem4587154 A B _54971 h1)). Qed.
Lemma lem4587157 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) (h1 : term15 A B) : term240 A B _54971 _54972.
Proof. exact (@lem4587156 A B _54971 h1 _54972). Qed.
Lemma lem4587158 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term240 A B _54971 _54972) = (term231 A B _54971 _54972).
Proof. exact (eq_refl (term240 A B _54971 _54972)). Qed.
Lemma lem4587159 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) (h1 : term15 A B) : term231 A B _54971 _54972.
Proof. exact (EQ_MP (@lem4587158 A B _54971 _54972) (@lem4587157 A B _54971 _54972 h1)). Qed.
Lemma lem4587172 {B : Type'} (_54977 : B -> Prop) (h1 : term16 B) : term145 B _54977.
Proof. exact (@lem4586947 B h1 _54977). Qed.
Lemma lem4587173 {B : Type'} (_54977 : B -> Prop) : (term145 B _54977) = (term130 B _54977).
Proof. exact (eq_refl (term145 B _54977)). Qed.
Lemma lem4587174 {B : Type'} (_54977 : B -> Prop) (h1 : term16 B) : term130 B _54977.
Proof. exact (EQ_MP (@lem4587173 B _54977) (@lem4587172 B _54977 h1)). Qed.
Lemma lem4587175 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) (h1 : term16 B) : term121 B _54977 _54978.
Proof. exact (@lem4587174 B _54977 h1 _54978). Qed.
Lemma lem4587176 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term121 B _54977 _54978) = (term104 B _54977 _54978).
Proof. exact (eq_refl (term121 B _54977 _54978)). Qed.
Lemma lem4587184 {A : Type'} (_54981 : A -> Prop) (h1 : term16 A) : term145 A _54981.
Proof. exact (@lem4586995 A h1 _54981). Qed.
Lemma lem4587185 {A : Type'} (_54981 : A -> Prop) : (term145 A _54981) = (term130 A _54981).
Proof. exact (eq_refl (term145 A _54981)). Qed.
Lemma lem4587186 {A : Type'} (_54981 : A -> Prop) (h1 : term16 A) : term130 A _54981.
Proof. exact (EQ_MP (@lem4587185 A _54981) (@lem4587184 A _54981 h1)). Qed.
Lemma lem4587187 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) (h1 : term16 A) : term121 A _54981 _54982.
Proof. exact (@lem4587186 A _54981 h1 _54982). Qed.
Lemma lem4587188 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term121 A _54981 _54982) = (term104 A _54981 _54982).
Proof. exact (eq_refl (term121 A _54981 _54982)). Qed.
Lemma lem4587246 {A B : Type'} (_54950 : nat) (_54949 : nat) : (term225 A B _54950 _54949) = (term241 A B _54950 _54949).
Proof. exact (@lem4582305 (term242 A _54949) (term242 B _54950) (term221 A B _54950 _54949)). Qed.
Lemma lem4587247 {A B : Type'} (_54950 : nat) (_54949 : nat) (h1 : term11 A B) : term241 A B _54950 _54949.
Proof. exact (EQ_MP (@lem4587246 A B _54950 _54949) (@lem4587093 A B _54950 _54949 h1)). Qed.
Lemma lem4587343 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) (h1 : term16 B) : term104 B _54977 _54978.
Proof. exact (EQ_MP (@lem4587176 B _54977 _54978) (@lem4587175 B _54977 _54978 h1)). Qed.
Lemma lem4587353 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) (h1 : term16 A) : term104 A _54981 _54982.
Proof. exact (EQ_MP (@lem4587188 A _54981 _54982) (@lem4587187 A _54981 _54982 h1)). Qed.
Lemma lem4587365 {A B : Type'} (h1 : term10 A B) : term243 A B.
Proof. exact (proj2 (@lem4585863 A B h1)). Qed.
Lemma lem4587429 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) (h1 : term15 A B) : term244 A B _54971 _54972.
Proof. exact (proj2 (@lem4587159 A B _54971 _54972 h1)). Qed.
Lemma lem4587812 {A B : Type'} (h1 : term10 A B) : @FINITE A (@UNIV A).
Proof. exact (proj1 (@lem4586573 A B h1)). Qed.
Lemma lem4587813 {A B : Type'} (h1 : term10 A B) : term245 A.
Proof. exact (fun h0 : term246 A => @lem4587812 A B h1). Qed.
Lemma lem4587815 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4587816 {A : Type'} : (term245 A) = (@FINITE A (@UNIV A)).
Proof. exact (@lem4587815 (@FINITE A (@UNIV A))). Qed.
Lemma lem4587817 {A B : Type'} (h1 : term10 A B) : @FINITE A (@UNIV A).
Proof. exact (EQ_MP (@lem4587816 A) (@lem4587813 A B h1)). Qed.
Lemma lem4587819 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4587820 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (@lem4587819 (@CARD A (@UNIV A))). Qed.
Lemma lem4587821 {A : Type'} : term248 A.
Proof. exact (fun h0 : term249 A => @lem4587820 A). Qed.
Lemma lem4587823 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4587824 {A : Type'} : (term248 A) = ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A))).
Proof. exact (@lem4587823 ((@CARD A (@UNIV A)) = (@CARD A (@UNIV A)))). Qed.
Lemma lem4587825 {A : Type'} : (@CARD A (@UNIV A)) = (@CARD A (@UNIV A)).
Proof. exact (EQ_MP (@lem4587824 A) (@lem4587821 A)). Qed.
Lemma lem4587827 (b : Prop) (a : Prop) : (a \/ b) = (term250 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4587828 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term104 A _54981 _54982) = (term251 A _54981 _54982).
Proof. exact (@lem4587827 (term100 A _54981 _54982) (@HAS_SIZE A _54981 _54982)). Qed.
Lemma lem4587830 (a : Prop) (b : Prop) : (term252 a b) = (term253 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4587831 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term254 A _54981 _54982) = (term255 A _54981 _54982).
Proof. exact (@lem4587830 (term256 A _54981) (term257 A _54981 _54982)). Qed.
Lemma lem4587833 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4587834 {A : Type'} (_54981 : A -> Prop) : (term259 A _54981) = (@FINITE A _54981).
Proof. exact (@lem4587833 (@FINITE A _54981)). Qed.
Lemma lem4587835 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4587836 {A : Type'} (_54981 : A -> Prop) : (term260 A _54981) = (term261 A _54981).
Proof. exact (MK_COMB (@lem4587835) (@lem4587834 A _54981)). Qed.
Lemma lem4587838 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4587839 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term262 A _54981 _54982) = ((@CARD A _54981) = _54982).
Proof. exact (@lem4587838 ((@CARD A _54981) = _54982)). Qed.
Lemma lem4587840 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term255 A _54981 _54982) = (term92 A _54981 _54982).
Proof. exact (MK_COMB (@lem4587836 A _54981) (@lem4587839 A _54981 _54982)). Qed.
Lemma lem4587841 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term254 A _54981 _54982) = (term92 A _54981 _54982).
Proof. exact (TRANS (@lem4587831 A _54981 _54982) (@lem4587840 A _54981 _54982)). Qed.
Lemma lem4587842 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4587843 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term263 A _54981 _54982) = (term264 A _54981 _54982).
Proof. exact (MK_COMB (@lem4587842) (@lem4587841 A _54981 _54982)). Qed.
Lemma lem4587844 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (@HAS_SIZE A _54981 _54982) = (@HAS_SIZE A _54981 _54982).
Proof. exact (eq_refl (@HAS_SIZE A _54981 _54982)). Qed.
Lemma lem4587845 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term251 A _54981 _54982) = (term265 A _54981 _54982).
Proof. exact (MK_COMB (@lem4587843 A _54981 _54982) (@lem4587844 A _54981 _54982)). Qed.
Lemma lem4587846 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) : (term104 A _54981 _54982) = (term265 A _54981 _54982).
Proof. exact (TRANS (@lem4587828 A _54981 _54982) (@lem4587845 A _54981 _54982)). Qed.
Lemma lem4587848 {A B : Type'} (h1 : term10 A B) : term266 A.
Proof. exact (conj (@lem4587817 A B h1) (@lem4587825 A)). Qed.
Lemma lem4587850 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) (h1 : term16 A) : term265 A _54981 _54982.
Proof. exact (EQ_MP (@lem4587846 A _54981 _54982) (@lem4587353 A _54981 _54982 h1)). Qed.
Lemma lem4587851 {A : Type'} (_54981 : A -> Prop) (_54982 : nat) (h1 : term16 A) : term265 A _54981 _54982.
Proof. exact (@lem4587850 A _54981 _54982 h1). Qed.
Lemma lem4587852 {A : Type'} (h1 : term16 A) : term267 A.
Proof. exact (@lem4587851 A (@UNIV A) (@CARD A (@UNIV A)) h1). Qed.
Lemma lem4587855 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term268 A.
Proof. exact (@lem4587852 A h1 (@lem4587848 A B h2)). Qed.
Lemma lem4587856 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term269 A.
Proof. exact (fun h0 : term270 A => @lem4587855 A B h1 h2). Qed.
Lemma lem4587858 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4587859 {A : Type'} : (term269 A) = (term268 A).
Proof. exact (@lem4587858 (term268 A)). Qed.
Lemma lem4587860 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term268 A.
Proof. exact (EQ_MP (@lem4587859 A) (@lem4587856 A B h1 h2)). Qed.
Lemma lem4587862 {A B : Type'} (h1 : term10 A B) : @FINITE B (@UNIV B).
Proof. exact (proj2 (@lem4586573 A B h1)). Qed.
Lemma lem4587863 {A B : Type'} (h1 : term10 A B) : term245 B.
Proof. exact (fun h0 : term246 B => @lem4587862 A B h1). Qed.
Lemma lem4587865 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4587866 {B : Type'} : (term245 B) = (@FINITE B (@UNIV B)).
Proof. exact (@lem4587865 (@FINITE B (@UNIV B))). Qed.
Lemma lem4587867 {A B : Type'} (h1 : term10 A B) : @FINITE B (@UNIV B).
Proof. exact (EQ_MP (@lem4587866 B) (@lem4587863 A B h1)). Qed.
Lemma lem4587869 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4587870 {B : Type'} : (@CARD B (@UNIV B)) = (@CARD B (@UNIV B)).
Proof. exact (@lem4587869 (@CARD B (@UNIV B))). Qed.
Lemma lem4587871 {B : Type'} : term248 B.
Proof. exact (fun h0 : term249 B => @lem4587870 B). Qed.
Lemma lem4587873 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4587874 {B : Type'} : (term248 B) = ((@CARD B (@UNIV B)) = (@CARD B (@UNIV B))).
Proof. exact (@lem4587873 ((@CARD B (@UNIV B)) = (@CARD B (@UNIV B)))). Qed.
Lemma lem4587875 {B : Type'} : (@CARD B (@UNIV B)) = (@CARD B (@UNIV B)).
Proof. exact (EQ_MP (@lem4587874 B) (@lem4587871 B)). Qed.
Lemma lem4587877 (b : Prop) (a : Prop) : (a \/ b) = (term250 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4587878 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term104 B _54977 _54978) = (term251 B _54977 _54978).
Proof. exact (@lem4587877 (term100 B _54977 _54978) (@HAS_SIZE B _54977 _54978)). Qed.
Lemma lem4587880 (a : Prop) (b : Prop) : (term252 a b) = (term253 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4587881 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term254 B _54977 _54978) = (term255 B _54977 _54978).
Proof. exact (@lem4587880 (term256 B _54977) (term257 B _54977 _54978)). Qed.
Lemma lem4587883 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4587884 {B : Type'} (_54977 : B -> Prop) : (term259 B _54977) = (@FINITE B _54977).
Proof. exact (@lem4587883 (@FINITE B _54977)). Qed.
Lemma lem4587885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4587886 {B : Type'} (_54977 : B -> Prop) : (term260 B _54977) = (term261 B _54977).
Proof. exact (MK_COMB (@lem4587885) (@lem4587884 B _54977)). Qed.
Lemma lem4587888 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4587889 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term262 B _54977 _54978) = ((@CARD B _54977) = _54978).
Proof. exact (@lem4587888 ((@CARD B _54977) = _54978)). Qed.
Lemma lem4587890 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term255 B _54977 _54978) = (term92 B _54977 _54978).
Proof. exact (MK_COMB (@lem4587886 B _54977) (@lem4587889 B _54977 _54978)). Qed.
Lemma lem4587891 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term254 B _54977 _54978) = (term92 B _54977 _54978).
Proof. exact (TRANS (@lem4587881 B _54977 _54978) (@lem4587890 B _54977 _54978)). Qed.
Lemma lem4587892 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4587893 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term263 B _54977 _54978) = (term264 B _54977 _54978).
Proof. exact (MK_COMB (@lem4587892) (@lem4587891 B _54977 _54978)). Qed.
Lemma lem4587894 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (@HAS_SIZE B _54977 _54978) = (@HAS_SIZE B _54977 _54978).
Proof. exact (eq_refl (@HAS_SIZE B _54977 _54978)). Qed.
Lemma lem4587895 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term251 B _54977 _54978) = (term265 B _54977 _54978).
Proof. exact (MK_COMB (@lem4587893 B _54977 _54978) (@lem4587894 B _54977 _54978)). Qed.
Lemma lem4587896 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) : (term104 B _54977 _54978) = (term265 B _54977 _54978).
Proof. exact (TRANS (@lem4587878 B _54977 _54978) (@lem4587895 B _54977 _54978)). Qed.
Lemma lem4587898 {A B : Type'} (h1 : term10 A B) : term266 B.
Proof. exact (conj (@lem4587867 A B h1) (@lem4587875 B)). Qed.
Lemma lem4587900 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) (h1 : term16 B) : term265 B _54977 _54978.
Proof. exact (EQ_MP (@lem4587896 B _54977 _54978) (@lem4587343 B _54977 _54978 h1)). Qed.
Lemma lem4587901 {B : Type'} (_54977 : B -> Prop) (_54978 : nat) (h1 : term16 B) : term265 B _54977 _54978.
Proof. exact (@lem4587900 B _54977 _54978 h1). Qed.
Lemma lem4587902 {B : Type'} (h1 : term16 B) : term267 B.
Proof. exact (@lem4587901 B (@UNIV B) (@CARD B (@UNIV B)) h1). Qed.
Lemma lem4587905 {A B : Type'} (h1 : term16 B) (h2 : term10 A B) : term268 B.
Proof. exact (@lem4587902 B h1 (@lem4587898 A B h2)). Qed.
Lemma lem4587906 {A B : Type'} (h1 : term16 B) (h2 : term10 A B) : term269 B.
Proof. exact (fun h0 : term270 B => @lem4587905 A B h1 h2). Qed.
Lemma lem4587908 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4587909 {B : Type'} : (term269 B) = (term268 B).
Proof. exact (@lem4587908 (term268 B)). Qed.
Lemma lem4587910 {A B : Type'} (h1 : term16 B) (h2 : term10 A B) : term268 B.
Proof. exact (EQ_MP (@lem4587909 B) (@lem4587906 A B h1 h2)). Qed.
Lemma lem4587926 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4587927 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term271 A B _54950 _54949) = (term272 A B _54949 _54950).
Proof. exact (@lem4587926 (term221 A B _54950 _54949) (term242 B _54950)). Qed.
Lemma lem4587933 {A : Type'} (_54949 : nat) : (term273 A _54949) = (term273 A _54949).
Proof. exact (eq_refl (term273 A _54949)). Qed.
Lemma lem4587934 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term241 A B _54950 _54949) = (term274 A B _54949 _54950).
Proof. exact (MK_COMB (@lem4587933 A _54949) (@lem4587927 A B _54949 _54950)). Qed.
Lemma lem4587938 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4587939 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term274 A B _54949 _54950) = (term275 A B _54949 _54950).
Proof. exact (@lem4587938 (term221 A B _54950 _54949) (term242 A _54949) (term242 B _54950)). Qed.
Lemma lem4587955 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term241 A B _54950 _54949) = (term275 A B _54949 _54950).
Proof. exact (TRANS (@lem4587934 A B _54949 _54950) (@lem4587939 A B _54949 _54950)). Qed.
Lemma lem4587956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4587957 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term276 A B _54950 _54949) = (term277 A B _54949 _54950).
Proof. exact (MK_COMB (@lem4587956) (@lem4587955 A B _54949 _54950)). Qed.
Lemma lem4587973 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term275 A B _54949 _54950) = (term275 A B _54949 _54950).
Proof. exact (eq_refl (term275 A B _54949 _54950)). Qed.
Lemma lem4587974 {A B : Type'} (_54949 : nat) (_54950 : nat) : ((term241 A B _54950 _54949) = (term275 A B _54949 _54950)) = ((term275 A B _54949 _54950) = (term275 A B _54949 _54950)).
Proof. exact (MK_COMB (@lem4587957 A B _54949 _54950) (@lem4587973 A B _54949 _54950)). Qed.
Lemma lem4587976 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4587977 (x : Prop) : (x = x) = True.
Proof. exact (@lem4587976 Prop x). Qed.
Lemma lem4587978 {A B : Type'} (_54949 : nat) (_54950 : nat) : ((term275 A B _54949 _54950) = (term275 A B _54949 _54950)) = True.
Proof. exact (@lem4587977 (term275 A B _54949 _54950)). Qed.
Lemma lem4587979 {A B : Type'} (_54949 : nat) (_54950 : nat) : ((term241 A B _54950 _54949) = (term275 A B _54949 _54950)) = True.
Proof. exact (TRANS (@lem4587974 A B _54949 _54950) (@lem4587978 A B _54949 _54950)). Qed.
Lemma lem4587980 {A B : Type'} (_54949 : nat) (_54950 : nat) : True = ((term241 A B _54950 _54949) = (term275 A B _54949 _54950)).
Proof. exact (SYM (@lem4587979 A B _54949 _54950)). Qed.
Lemma lem4587981 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term241 A B _54950 _54949) = (term275 A B _54949 _54950).
Proof. exact (EQ_MP (@lem4587980 A B _54949 _54950) (@lem0)). Qed.
Lemma lem4587982 {A B : Type'} (_54949 : nat) (_54950 : nat) (h1 : term11 A B) : term275 A B _54949 _54950.
Proof. exact (EQ_MP (@lem4587981 A B _54949 _54950) (@lem4587247 A B _54950 _54949 h1)). Qed.
Lemma lem4587984 (b : Prop) (a : Prop) : (a \/ b) = (term250 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4587985 {A B : Type'} (_54950 : nat) (_54949 : nat) : (term275 A B _54949 _54950) = (term278 A B _54950 _54949).
Proof. exact (@lem4587984 (term220 A B _54949 _54950) (term221 A B _54950 _54949)). Qed.
Lemma lem4587987 (a : Prop) (b : Prop) : (term252 a b) = (term253 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4587988 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term279 A B _54949 _54950) = (term280 A B _54949 _54950).
Proof. exact (@lem4587987 (term242 A _54949) (term242 B _54950)). Qed.
Lemma lem4587990 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4587991 {A : Type'} (_54949 : nat) : (term281 A _54949) = (@HAS_SIZE A (@UNIV A) _54949).
Proof. exact (@lem4587990 (@HAS_SIZE A (@UNIV A) _54949)). Qed.
Lemma lem4587992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4587993 {A : Type'} (_54949 : nat) : (term282 A _54949) = (term283 A _54949).
Proof. exact (MK_COMB (@lem4587992) (@lem4587991 A _54949)). Qed.
Lemma lem4587995 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4587996 {B : Type'} (_54950 : nat) : (term281 B _54950) = (@HAS_SIZE B (@UNIV B) _54950).
Proof. exact (@lem4587995 (@HAS_SIZE B (@UNIV B) _54950)). Qed.
Lemma lem4587997 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term280 A B _54949 _54950) = (term226 A B _54949 _54950).
Proof. exact (MK_COMB (@lem4587993 A _54949) (@lem4587996 B _54950)). Qed.
Lemma lem4587998 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term279 A B _54949 _54950) = (term226 A B _54949 _54950).
Proof. exact (TRANS (@lem4587988 A B _54949 _54950) (@lem4587997 A B _54949 _54950)). Qed.
Lemma lem4587999 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588000 {A B : Type'} (_54949 : nat) (_54950 : nat) : (term284 A B _54949 _54950) = (term285 A B _54949 _54950).
Proof. exact (MK_COMB (@lem4587999) (@lem4587998 A B _54949 _54950)). Qed.
Lemma lem4588001 {A B : Type'} (_54950 : nat) (_54949 : nat) : (term221 A B _54950 _54949) = (term221 A B _54950 _54949).
Proof. exact (eq_refl (term221 A B _54950 _54949)). Qed.
Lemma lem4588002 {A B : Type'} (_54950 : nat) (_54949 : nat) : (term278 A B _54950 _54949) = (term72 A B _54950 _54949).
Proof. exact (MK_COMB (@lem4588000 A B _54949 _54950) (@lem4588001 A B _54950 _54949)). Qed.
Lemma lem4588003 {A B : Type'} (_54950 : nat) (_54949 : nat) : (term275 A B _54949 _54950) = (term72 A B _54950 _54949).
Proof. exact (TRANS (@lem4587985 A B _54950 _54949) (@lem4588002 A B _54950 _54949)). Qed.
Lemma lem4588005 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term10 A B) : term286 A B.
Proof. exact (conj (@lem4587860 A B h1 h3) (@lem4587910 A B h2 h3)). Qed.
Lemma lem4588007 {A B : Type'} (_54950 : nat) (_54949 : nat) (h1 : term11 A B) : term72 A B _54950 _54949.
Proof. exact (EQ_MP (@lem4588003 A B _54950 _54949) (@lem4587982 A B _54949 _54950 h1)). Qed.
Lemma lem4588008 {A B : Type'} (h1 : term11 A B) : term287 A B.
Proof. exact (@lem4588007 A B (@CARD B (@UNIV B)) (@CARD A (@UNIV A)) h1). Qed.
Lemma lem4588011 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term11 A B) (h4 : term10 A B) : term288 A B.
Proof. exact (@lem4588008 A B h3 (@lem4588005 A B h1 h2 h4)). Qed.
Lemma lem4588012 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term11 A B) (h4 : term10 A B) : term289 A B.
Proof. exact (fun h0 : term290 A B => @lem4588011 A B h1 h2 h3 h4). Qed.
Lemma lem4588014 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4588015 {A B : Type'} : (term289 A B) = (term288 A B).
Proof. exact (@lem4588014 (term288 A B)). Qed.
Lemma lem4588016 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term11 A B) (h4 : term10 A B) : term288 A B.
Proof. exact (EQ_MP (@lem4588015 A B) (@lem4588012 A B h1 h2 h3 h4)). Qed.
Lemma lem4588022 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4588023 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term244 A B _54971 _54972) = (term291 A B _54971 _54972).
Proof. exact (@lem4588022 ((@CARD (A -> B) _54971) = _54972) (term232 A B _54971 _54972)). Qed.
Lemma lem4588031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4588032 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term292 A B _54971 _54972) = (term293 A B _54971 _54972).
Proof. exact (MK_COMB (@lem4588031) (@lem4588023 A B _54971 _54972)). Qed.
Lemma lem4588040 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term291 A B _54971 _54972) = (term291 A B _54971 _54972).
Proof. exact (eq_refl (term291 A B _54971 _54972)). Qed.
Lemma lem4588041 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : ((term244 A B _54971 _54972) = (term291 A B _54971 _54972)) = ((term291 A B _54971 _54972) = (term291 A B _54971 _54972)).
Proof. exact (MK_COMB (@lem4588032 A B _54971 _54972) (@lem4588040 A B _54971 _54972)). Qed.
Lemma lem4588043 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4588044 (x : Prop) : (x = x) = True.
Proof. exact (@lem4588043 Prop x). Qed.
Lemma lem4588045 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : ((term291 A B _54971 _54972) = (term291 A B _54971 _54972)) = True.
Proof. exact (@lem4588044 (term291 A B _54971 _54972)). Qed.
Lemma lem4588046 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : ((term244 A B _54971 _54972) = (term291 A B _54971 _54972)) = True.
Proof. exact (TRANS (@lem4588041 A B _54971 _54972) (@lem4588045 A B _54971 _54972)). Qed.
Lemma lem4588047 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : True = ((term244 A B _54971 _54972) = (term291 A B _54971 _54972)).
Proof. exact (SYM (@lem4588046 A B _54971 _54972)). Qed.
Lemma lem4588048 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term244 A B _54971 _54972) = (term291 A B _54971 _54972).
Proof. exact (EQ_MP (@lem4588047 A B _54971 _54972) (@lem0)). Qed.
Lemma lem4588049 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) (h1 : term15 A B) : term291 A B _54971 _54972.
Proof. exact (EQ_MP (@lem4588048 A B _54971 _54972) (@lem4587429 A B _54971 _54972 h1)). Qed.
Lemma lem4588051 (b : Prop) (a : Prop) : (a \/ b) = (term250 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4588052 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term291 A B _54971 _54972) = (term294 A B _54971 _54972).
Proof. exact (@lem4588051 (term232 A B _54971 _54972) ((@CARD (A -> B) _54971) = _54972)). Qed.
Lemma lem4588054 (a : Prop) : (term258 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4588055 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term295 A B _54971 _54972) = (@HAS_SIZE (A -> B) _54971 _54972).
Proof. exact (@lem4588054 (@HAS_SIZE (A -> B) _54971 _54972)). Qed.
Lemma lem4588056 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4588057 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term296 A B _54971 _54972) = (term297 A B _54971 _54972).
Proof. exact (MK_COMB (@lem4588056) (@lem4588055 A B _54971 _54972)). Qed.
Lemma lem4588058 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : ((@CARD (A -> B) _54971) = _54972) = ((@CARD (A -> B) _54971) = _54972).
Proof. exact (eq_refl ((@CARD (A -> B) _54971) = _54972)). Qed.
Lemma lem4588059 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term294 A B _54971 _54972) = (term298 A B _54971 _54972).
Proof. exact (MK_COMB (@lem4588057 A B _54971 _54972) (@lem4588058 A B _54971 _54972)). Qed.
Lemma lem4588060 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) : (term291 A B _54971 _54972) = (term298 A B _54971 _54972).
Proof. exact (TRANS (@lem4588052 A B _54971 _54972) (@lem4588059 A B _54971 _54972)). Qed.
Lemma lem4588063 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) (h1 : term15 A B) : term298 A B _54971 _54972.
Proof. exact (EQ_MP (@lem4588060 A B _54971 _54972) (@lem4588049 A B _54971 _54972 h1)). Qed.
Lemma lem4588064 {A B : Type'} (_54971 : type572 A B) (_54972 : nat) (h1 : term15 A B) : term298 A B _54971 _54972.
Proof. exact (@lem4588063 A B _54971 _54972 h1). Qed.
Lemma lem4588065 {A B : Type'} (h1 : term15 A B) : term299 A B.
Proof. exact (@lem4588064 A B (@UNIV (A -> B)) (term98 A B) h1). Qed.
Lemma lem4588068 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : (@CARD (A -> B) (@UNIV (A -> B))) = (term98 A B).
Proof. exact (@lem4588065 A B h3 (@lem4588016 A B h1 h2 h4 h5)). Qed.
Lemma lem4588069 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term300 A B.
Proof. exact (fun h0 : term243 A B => @lem4588068 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4588071 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4588072 {A B : Type'} : (term300 A B) = ((@CARD (A -> B) (@UNIV (A -> B))) = (term98 A B)).
Proof. exact (@lem4588071 ((@CARD (A -> B) (@UNIV (A -> B))) = (term98 A B))). Qed.
Lemma lem4588073 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : (@CARD (A -> B) (@UNIV (A -> B))) = (term98 A B).
Proof. exact (EQ_MP (@lem4588072 A B) (@lem4588069 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4588076 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4588078 {A B : Type'} : (term243 A B) = (term301 A B).
Proof. exact (@lem4588076 ((@CARD (A -> B) (@UNIV (A -> B))) = (term98 A B))). Qed.
Lemma lem4588081 {A B : Type'} (h1 : term10 A B) : term301 A B.
Proof. exact (EQ_MP (@lem4588078 A B) (@lem4587365 A B h1)). Qed.
Lemma lem4588084 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : False.
Proof. exact (@lem4588081 A B h5 (@lem4588073 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4588085 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term302.
Proof. exact (fun h0 : ~ False => @lem4588084 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4588087 (p : Prop) : (term247 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4588088 : term302 = False.
Proof. exact (@lem4588087 False). Qed.
Lemma lem4588089 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : False.
Proof. exact (EQ_MP (@lem4588088) (@lem4588085 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4588090 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term24 A B.
Proof. exact (fun h0 : term13 A B => @lem4588089 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4588091 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (@lem69 (term13 A B)). Qed.
Lemma lem4588092 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term25 A B.
Proof. exact (EQ_MP (@lem4588091 A B) (@lem4588090 A B h1 h2 h3 h4 h5)). Qed.
Lemma lem4588093 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term28 A B.
Proof. exact (fun h0 : term12 B => @lem4588092 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4588094 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term11 A B) (h5 : term10 A B) : term31 A B.
Proof. exact (fun h0 : term14 A B => @lem4588093 A B h1 h2 h3 h4 h5). Qed.
Lemma lem4588095 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term34 A B.
Proof. exact (fun h0 : term11 A B => @lem4588094 A B h1 h2 h3 h0 h4). Qed.
Lemma lem4588096 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term36 A B.
Proof. exact (fun h0 : term12 A => @lem4588095 A B h1 h2 h3 h4). Qed.
Lemma lem4588097 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term39 A B.
Proof. exact (fun h0 : term17 A B => @lem4588096 A B h1 h2 h3 h4). Qed.
Lemma lem4588098 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term42 A B.
Proof. exact (fun h0 : term18 B => @lem4588097 A B h1 h2 h3 h4). Qed.
Lemma lem4588099 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term15 A B) (h4 : term10 A B) : term45 A B.
Proof. exact (fun h0 : term19 A B => @lem4588098 A B h1 h2 h3 h4). Qed.
Lemma lem4588100 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term10 A B) : term48 A B.
Proof. exact (fun h0 : term15 A B => @lem4588099 A B h1 h2 h0 h3). Qed.
Lemma lem4588101 {A B : Type'} (h1 : term16 A) (h2 : term16 B) (h3 : term10 A B) : term50 A B.
Proof. exact (fun h0 : term18 A => @lem4588100 A B h1 h2 h3). Qed.
Lemma lem4588102 {A B : Type'} (h1 : term16 A) (h2 : term10 A B) : term53 A B.
Proof. exact (fun h0 : term16 B => @lem4588101 A B h1 h0 h2). Qed.
Lemma lem4588103 {A B : Type'} (h1 : term10 A B) : term55 A B.
Proof. exact (fun h0 : term16 A => @lem4588102 A B h0 h1). Qed.
Lemma lem4588104 {_100044 A B : Type'} (h1 : term10 A B) : term57 _100044 A B.
Proof. exact (fun h0 : term16 _100044 => @lem4588103 A B h1). Qed.
Lemma lem4588105 {_100044 A B : Type'} : term59 _100044 A B.
Proof. exact (fun h0 : term10 A B => @lem4588104 _100044 A B h0). Qed.
Lemma lem4588106 {_100044 A B : Type'} : term20 _100044 A B.
Proof. exact (EQ_MP (@lem4583047 _100044 A B) (@lem4588105 _100044 A B)). Qed.
Lemma lem4588108 {_100044 A B : Type'} : term20 _100044 A B.
Proof. exact (@lem4582345 _100044 A B (@lem4588106 _100044 A B)). Qed.
Lemma lem4588109 {_100044 A B : Type'} (h1 : term10 A B) : term56 _100044 A B.
Proof. exact (@lem4588108 _100044 A B (@lem4582310 A B h1)). Qed.
Lemma lem4588110 {A B : Type'} (h1 : term10 A B) : term54 A B.
Proof. exact (@lem4588109 Prop A B h1 (@lem3863773 Prop)). Qed.
Lemma lem4588111 {A B : Type'} (h1 : term10 A B) : term52 A B.
Proof. exact (@lem4588110 A B h1 (@lem4582322 A)). Qed.
Lemma lem4588112 {A B : Type'} (h1 : term10 A B) : term49 A B.
Proof. exact (@lem4588111 A B h1 (@lem4582319 B)). Qed.
Lemma lem4588113 {A B : Type'} (h1 : term10 A B) : term47 A B.
Proof. exact (@lem4588112 A B h1 (@lem4582324 A)). Qed.
Lemma lem4588114 {A B : Type'} (h1 : term10 A B) : term44 A B.
Proof. exact (@lem4588113 A B h1 (@lem4582318 A B)). Qed.
Lemma lem4588115 {A B : Type'} (h1 : term10 A B) : term41 A B.
Proof. exact (@lem4588114 A B h1 (@lem4582323 A B)). Qed.
Lemma lem4588116 {A B : Type'} (h1 : term10 A B) : term38 A B.
Proof. exact (@lem4588115 A B h1 (@lem4582321 B)). Qed.
Lemma lem4588117 {A B : Type'} (h1 : term10 A B) : term35 A B.
Proof. exact (@lem4588116 A B h1 (@lem4582320 A B)). Qed.
Lemma lem4588118 {A B : Type'} (h1 : term10 A B) : term33 A B.
Proof. exact (@lem4588117 A B h1 (@lem4582314 A)). Qed.
Lemma lem4588119 {A B : Type'} (h1 : term10 A B) : term30 A B.
Proof. exact (@lem4588118 A B h1 (@lem4582311 A B)). Qed.
Lemma lem4588120 {A B : Type'} (h1 : term10 A B) : term27 A B.
Proof. exact (@lem4588119 A B h1 (@lem4582316 A B)). Qed.
Lemma lem4588121 {A B : Type'} (h1 : term10 A B) : term24 A B.
Proof. exact (@lem4588120 A B h1 (@lem4582312 B)). Qed.
Lemma lem4588122 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (@lem4588121 A B h1 (@lem4582313 A B)). Qed.
Lemma lem4588123 {A B : Type'} (h1 : term10 A B) : (term10 A B) = False.
Proof. exact (prop_ext (fun h2 : term10 A B => @lem4588122 A B h1) (fun h2 : False => @lem4582310 A B h1)). Qed.
Lemma lem4588124 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (EQ_MP (@lem4588123 A B h1) (@lem4582310 A B h1)). Qed.
Lemma lem4588125 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term10 A B => @lem4588124 A B h0). Qed.
Lemma lem4588126 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem4582309 A B) (@lem4588125 A B)). Qed.
