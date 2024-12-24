Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_POWERSET_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_POWERSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
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
Lemma lem4600514 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4600515 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem4600514 (term1 A)). Qed.
Lemma lem4600516 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem4600515 A)). Qed.
Lemma lem4600517 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem4600518 {A : Type'} : term4 A.
Proof. exact (@lem4597289 A). Qed.
Lemma lem4600522 {A : Type'} : term5 A.
Proof. exact (@lem3863773 A). Qed.
Lemma lem4600523 {A : Type'} : term6 A.
Proof. exact (@lem3863773 (A -> Prop)). Qed.
Lemma lem4600528 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem4600529 {A : Type'} : term8 A.
Proof. exact (fun h0 : term7 A => @lem4600528 A h0). Qed.
Lemma lem4600530 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem4600531 {A : Type'} (h1 : term7 A) : term7 A.
Proof. exact (h1). Qed.
Lemma lem4600532 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem4600530 A h2 (@lem4600531 A h1)). Qed.
Lemma lem4600533 {A : Type'} (h1 : term7 A) : term9 A.
Proof. exact (fun h0 : term8 A => @lem4600532 A h1 h0). Qed.
Lemma lem4600534 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (h1). Qed.
Lemma lem4600535 {A : Type'} (h1 : term7 A) (h2 : term8 A) : term7 A.
Proof. exact (@lem4600533 A h1 (@lem4600534 A h2)). Qed.
Lemma lem4600536 {A : Type'} (h1 : term8 A) : term8 A.
Proof. exact (fun h0 : term7 A => @lem4600535 A h0 h1). Qed.
Lemma lem4600537 {A : Type'} : term10 A.
Proof. exact (fun h0 : term8 A => @lem4600536 A h0). Qed.
Lemma lem4600540 {A : Type'} : term8 A.
Proof. exact (@lem4600537 A (@lem4600529 A)). Qed.
Lemma lem4600541 {A : Type'} : term8 A.
Proof. exact (@lem4600540 A). Qed.
Lemma lem4600579 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4600580 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (@lem4600579 (term4 A)). Qed.
Lemma lem4600595 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (eq_refl (term13 A)). Qed.
Lemma lem4600596 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem4600595 A) (@lem4600580 A)). Qed.
Lemma lem4600599 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (eq_refl (term16 A)). Qed.
Lemma lem4600600 {A : Type'} : (term17 A) = (term18 A).
Proof. exact (MK_COMB (@lem4600599 A) (@lem4600596 A)). Qed.
Lemma lem4600603 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (eq_refl (term19 A)). Qed.
Lemma lem4600608 {A : Type'} : (term7 A) = (term20 A).
Proof. exact (MK_COMB (@lem4600603 A) (@lem4600600 A)). Qed.
Lemma lem4600609 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : _55291 = (term21 A).
Proof. exact (h1). Qed.
Lemma lem4600610 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4600611 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (_55291 s) = (term22 A s).
Proof. exact (MK_COMB (@lem4600609 A _55291 h1) (@lem4600610 A s)). Qed.
Lemma lem4600612 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (eq_refl (term22 A s)). Qed.
Lemma lem4600613 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term24 A _55291 s) = (term24 A _55291 s).
Proof. exact (eq_refl (term24 A _55291 s)). Qed.
Lemma lem4600614 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((_55291 s) = (term22 A s)) = ((_55291 s) = (term23 A s)).
Proof. exact (MK_COMB (@lem4600613 A _55291 s) (@lem4600612 A s)). Qed.
Lemma lem4600615 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (_55291 s) = (term23 A s).
Proof. exact (EQ_MP (@lem4600614 A _55291 s) (@lem4600611 A s _55291 h1)). Qed.
Lemma lem4600627 (n : nat) : (term25 n) = (term25 n).
Proof. exact (eq_refl (term25 n)). Qed.
Lemma lem4600629 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term23 A s) = (_55291 s).
Proof. exact (SYM (@lem4600615 A s _55291 h1)). Qed.
Lemma lem4600630 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term23 A s) = (_55291 s).
Proof. exact (@lem4600629 A s _55291 h1). Qed.
Lemma lem4600631 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4600632 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term26 A s) = (term27 A _55291 s).
Proof. exact (MK_COMB (@lem4600631 A) (@lem4600630 A s _55291 h1)). Qed.
Lemma lem4600633 {A : Type'} : (@HAS_SIZE (A -> Prop)) = (@HAS_SIZE (A -> Prop)).
Proof. exact (eq_refl (@HAS_SIZE (A -> Prop))). Qed.
Lemma lem4600634 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term28 A s) = (term29 A _55291 s).
Proof. exact (MK_COMB (@lem4600633 A) (@lem4600632 A s _55291 h1)). Qed.
Lemma lem4600635 {A : Type'} (s : A -> Prop) (n : nat) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term30 A s n) = (term31 A _55291 s n).
Proof. exact (MK_COMB (@lem4600634 A s _55291 h1) (@lem4600627 n)). Qed.
Lemma lem4600642 {A : Type'} (s : A -> Prop) (n : nat) : (term32 A s n) = (term32 A s n).
Proof. exact (eq_refl (term32 A s n)). Qed.
Lemma lem4600643 {A : Type'} (s : A -> Prop) (n : nat) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term33 A s n) = (term34 A _55291 s n).
Proof. exact (MK_COMB (@lem4600642 A s n) (@lem4600635 A s n _55291 h1)). Qed.
Lemma lem4600644 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term35 A s) = (term36 A _55291 s).
Proof. exact (fun_ext (fun n : nat => @lem4600643 A s n _55291 h1)). Qed.
Lemma lem4600645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4600646 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term37 A s) = (term38 A _55291 s).
Proof. exact (MK_COMB (@lem4600645) (@lem4600644 A s _55291 h1)). Qed.
Lemma lem4600647 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term39 A) = (term40 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600646 A s _55291 h1)). Qed.
Lemma lem4600648 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600649 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term4 A) = (term41 A _55291).
Proof. exact (MK_COMB (@lem4600648 A) (@lem4600647 A _55291 h1)). Qed.
Lemma lem4600650 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4600651 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term12 A) = (term42 A _55291).
Proof. exact (MK_COMB (@lem4600650) (@lem4600649 A _55291 h1)). Qed.
Lemma lem4600672 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n)) = ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n))). Qed.
Lemma lem4600673 {A : Type'} (s : type686 A) : (term44 A s) = (term44 A s).
Proof. exact (fun_ext (fun n : nat => @lem4600672 A s n)). Qed.
Lemma lem4600674 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4600675 {A : Type'} (s : type686 A) : (term45 A s) = (term45 A s).
Proof. exact (MK_COMB (@lem4600674) (@lem4600673 A s)). Qed.
Lemma lem4600676 {A : Type'} : (term46 A) = (term46 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4600675 A s)). Qed.
Lemma lem4600677 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4600678 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem4600677 A) (@lem4600676 A)). Qed.
Lemma lem4600679 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600680 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem4600679) (@lem4600678 A)). Qed.
Lemma lem4600681 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term15 A) = (term47 A _55291).
Proof. exact (MK_COMB (@lem4600680 A) (@lem4600651 A _55291 h1)). Qed.
Lemma lem4600702 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term48 A s n)) = ((@HAS_SIZE A s n) = (term48 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term48 A s n))). Qed.
Lemma lem4600703 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun n : nat => @lem4600702 A s n)). Qed.
Lemma lem4600704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4600705 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem4600704) (@lem4600703 A s)). Qed.
Lemma lem4600706 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600705 A s)). Qed.
Lemma lem4600707 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600708 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem4600707 A) (@lem4600706 A)). Qed.
Lemma lem4600709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600710 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4600709) (@lem4600708 A)). Qed.
Lemma lem4600711 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term18 A) = (term52 A _55291).
Proof. exact (MK_COMB (@lem4600710 A) (@lem4600681 A _55291 h1)). Qed.
Lemma lem4600713 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term23 A s) = (_55291 s).
Proof. exact (SYM (@lem4600615 A s _55291 h1)). Qed.
Lemma lem4600714 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term23 A s) = (_55291 s).
Proof. exact (@lem4600713 A s _55291 h1). Qed.
Lemma lem4600715 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4600716 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term26 A s) = (term27 A _55291 s).
Proof. exact (MK_COMB (@lem4600715 A) (@lem4600714 A s _55291 h1)). Qed.
Lemma lem4600717 {A : Type'} : (@FINITE (A -> Prop)) = (@FINITE (A -> Prop)).
Proof. exact (eq_refl (@FINITE (A -> Prop))). Qed.
Lemma lem4600718 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term53 A s) = (term54 A _55291 s).
Proof. exact (MK_COMB (@lem4600717 A) (@lem4600716 A s _55291 h1)). Qed.
Lemma lem4600723 {A : Type'} (s : A -> Prop) : (term55 A s) = (term55 A s).
Proof. exact (eq_refl (term55 A s)). Qed.
Lemma lem4600724 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term56 A s) = (term57 A _55291 s).
Proof. exact (MK_COMB (@lem4600723 A s) (@lem4600718 A s _55291 h1)). Qed.
Lemma lem4600725 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term58 A) = (term59 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600724 A s _55291 h1)). Qed.
Lemma lem4600726 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600727 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term1 A) = (term60 A _55291).
Proof. exact (MK_COMB (@lem4600726 A) (@lem4600725 A _55291 h1)). Qed.
Lemma lem4600728 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4600729 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term3 A) = (term61 A _55291).
Proof. exact (MK_COMB (@lem4600728) (@lem4600727 A _55291 h1)). Qed.
Lemma lem4600730 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600731 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term19 A) = (term62 A _55291).
Proof. exact (MK_COMB (@lem4600730) (@lem4600729 A _55291 h1)). Qed.
Lemma lem4600732 {A : Type'} (_55291 : type639 A) (h1 : _55291 = (term21 A)) : (term20 A) = (term63 A _55291).
Proof. exact (MK_COMB (@lem4600731 A _55291 h1) (@lem4600711 A _55291 h1)). Qed.
Lemma lem4600733 {A : Type'} (_55291 : type639 A) : term64 A _55291.
Proof. exact (fun h0 : _55291 = (term21 A) => @lem4600732 A _55291 h0). Qed.
Lemma lem4600734 {A : Type'} : term65 A.
Proof. exact (fun _55291 : type639 A => @lem4600733 A _55291). Qed.
Lemma lem4600736 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term66 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem4600737 {A : Type'} (P : Prop) (c : type639 A) (Q : type141 A) : term67 A P c Q.
Proof. exact (@lem4600736 (type639 A) P c Q). Qed.
Lemma lem4600738 {A : Type'} : term68 A.
Proof. exact (@lem4600737 A (term20 A) (term21 A) (term69 A)). Qed.
Lemma lem4600739 {A : Type'} (_55291 : type639 A) : (term70 A _55291) = (term63 A _55291).
Proof. exact (eq_refl (term70 A _55291)). Qed.
Lemma lem4600740 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (eq_refl (term71 A)). Qed.
Lemma lem4600741 {A : Type'} (_55291 : type639 A) : ((term20 A) = (term70 A _55291)) = ((term20 A) = (term63 A _55291)).
Proof. exact (MK_COMB (@lem4600740 A) (@lem4600739 A _55291)). Qed.
Lemma lem4600742 {A : Type'} (_55291 : type639 A) : (term72 A _55291) = (term72 A _55291).
Proof. exact (eq_refl (term72 A _55291)). Qed.
Lemma lem4600743 {A : Type'} (_55291 : type639 A) : (term73 A _55291) = (term64 A _55291).
Proof. exact (MK_COMB (@lem4600742 A _55291) (@lem4600741 A _55291)). Qed.
Lemma lem4600744 {A : Type'} : (term74 A) = (term75 A).
Proof. exact (fun_ext (fun _55291 : type639 A => @lem4600743 A _55291)). Qed.
Lemma lem4600745 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4600746 {A : Type'} : (term76 A) = (term65 A).
Proof. exact (MK_COMB (@lem4600745 A) (@lem4600744 A)). Qed.
Lemma lem4600747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600748 {A : Type'} : (term77 A) = (term78 A).
Proof. exact (MK_COMB (@lem4600747) (@lem4600746 A)). Qed.
Lemma lem4600749 {A : Type'} (_55291 : type639 A) : (term70 A _55291) = (term63 A _55291).
Proof. exact (eq_refl (term70 A _55291)). Qed.
Lemma lem4600750 {A : Type'} (_55291 : type639 A) : (term72 A _55291) = (term72 A _55291).
Proof. exact (eq_refl (term72 A _55291)). Qed.
Lemma lem4600751 {A : Type'} (_55291 : type639 A) : (term79 A _55291) = (term80 A _55291).
Proof. exact (MK_COMB (@lem4600750 A _55291) (@lem4600749 A _55291)). Qed.
Lemma lem4600752 {A : Type'} : (term81 A) = (term82 A).
Proof. exact (fun_ext (fun _55291 : type639 A => @lem4600751 A _55291)). Qed.
Lemma lem4600753 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4600754 {A : Type'} : (term83 A) = (term84 A).
Proof. exact (MK_COMB (@lem4600753 A) (@lem4600752 A)). Qed.
Lemma lem4600755 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (eq_refl (term71 A)). Qed.
Lemma lem4600756 {A : Type'} : ((term20 A) = (term83 A)) = ((term20 A) = (term84 A)).
Proof. exact (MK_COMB (@lem4600755 A) (@lem4600754 A)). Qed.
Lemma lem4600757 {A : Type'} : (term68 A) = (term85 A).
Proof. exact (MK_COMB (@lem4600748 A) (@lem4600756 A)). Qed.
Lemma lem4600758 {A : Type'} : term85 A.
Proof. exact (EQ_MP (@lem4600757 A) (@lem4600738 A)). Qed.
Lemma lem4600759 {A : Type'} : (term20 A) = (term84 A).
Proof. exact (@lem4600758 A (@lem4600734 A)). Qed.
Lemma lem4600761 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term86 _3571 _3575 t)) = (term87 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4600762 {A : Type'} (s : type639 A) (t : type639 A) : (s = (term88 A t)) = (term89 A s t).
Proof. exact (@lem4600761 (type686 A) (A -> Prop) s t). Qed.
Lemma lem4600763 {A : Type'} (_55291 : type639 A) : (_55291 = (term90 A)) = (term91 A _55291).
Proof. exact (@lem4600762 A _55291 (term21 A)). Qed.
Lemma lem4600764 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (eq_refl (term22 A s)). Qed.
Lemma lem4600765 {A : Type'} : (term90 A) = (term21 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600764 A s)). Qed.
Lemma lem4600766 {A : Type'} (_55291 : type639 A) : (@eq ((A -> Prop) -> (A -> Prop) -> Prop) _55291) = (@eq ((A -> Prop) -> (A -> Prop) -> Prop) _55291).
Proof. exact (eq_refl (@eq ((A -> Prop) -> (A -> Prop) -> Prop) _55291)). Qed.
Lemma lem4600767 {A : Type'} (_55291 : type639 A) : (_55291 = (term90 A)) = (_55291 = (term21 A)).
Proof. exact (MK_COMB (@lem4600766 A _55291) (@lem4600765 A)). Qed.
Lemma lem4600768 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4600769 {A : Type'} (_55291 : type639 A) : (term92 A _55291) = (term93 A _55291).
Proof. exact (MK_COMB (@lem4600768) (@lem4600767 A _55291)). Qed.
Lemma lem4600770 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (eq_refl (term22 A s)). Qed.
Lemma lem4600771 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term24 A _55291 s) = (term24 A _55291 s).
Proof. exact (eq_refl (term24 A _55291 s)). Qed.
Lemma lem4600772 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((_55291 s) = (term22 A s)) = ((_55291 s) = (term23 A s)).
Proof. exact (MK_COMB (@lem4600771 A _55291 s) (@lem4600770 A s)). Qed.
Lemma lem4600773 {A : Type'} (_55291 : type639 A) : (term94 A _55291) = (term95 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600772 A _55291 s)). Qed.
Lemma lem4600774 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600775 {A : Type'} (_55291 : type639 A) : (term91 A _55291) = (term96 A _55291).
Proof. exact (MK_COMB (@lem4600774 A) (@lem4600773 A _55291)). Qed.
Lemma lem4600776 {A : Type'} (_55291 : type639 A) : ((_55291 = (term90 A)) = (term91 A _55291)) = ((_55291 = (term21 A)) = (term96 A _55291)).
Proof. exact (MK_COMB (@lem4600769 A _55291) (@lem4600775 A _55291)). Qed.
Lemma lem4600777 {A : Type'} (_55291 : type639 A) : (_55291 = (term21 A)) = (term96 A _55291).
Proof. exact (EQ_MP (@lem4600776 A _55291) (@lem4600763 A _55291)). Qed.
Lemma lem4600779 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term86 _3571 _3575 t)) = (term87 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem4600780 {A : Type'} (s : type686 A) (t : type686 A) : (s = (term97 A t)) = (term98 A s t).
Proof. exact (@lem4600779 Prop (A -> Prop) s t). Qed.
Lemma lem4600781 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((_55291 s) = (term99 A s)) = (term100 A _55291 s).
Proof. exact (@lem4600780 A (_55291 s) (term23 A s)). Qed.
Lemma lem4600782 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term101 A s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s).
Proof. exact (eq_refl (term101 A s GEN_PVAR_155)). Qed.
Lemma lem4600783 {A : Type'} (s : A -> Prop) : (term99 A s) = (term23 A s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4600782 A GEN_PVAR_155 s)). Qed.
Lemma lem4600784 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term24 A _55291 s) = (term24 A _55291 s).
Proof. exact (eq_refl (term24 A _55291 s)). Qed.
Lemma lem4600785 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((_55291 s) = (term99 A s)) = ((_55291 s) = (term23 A s)).
Proof. exact (MK_COMB (@lem4600784 A _55291 s) (@lem4600783 A s)). Qed.
Lemma lem4600786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4600787 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term103 A _55291 s) = (term104 A _55291 s).
Proof. exact (MK_COMB (@lem4600786) (@lem4600785 A _55291 s)). Qed.
Lemma lem4600788 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term101 A s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s).
Proof. exact (eq_refl (term101 A s GEN_PVAR_155)). Qed.
Lemma lem4600789 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (GEN_PVAR_155 : A -> Prop) : (term105 A _55291 s GEN_PVAR_155) = (term105 A _55291 s GEN_PVAR_155).
Proof. exact (eq_refl (term105 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4600790 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : ((_55291 s GEN_PVAR_155) = (term101 A s GEN_PVAR_155)) = ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s)).
Proof. exact (MK_COMB (@lem4600789 A _55291 s GEN_PVAR_155) (@lem4600788 A GEN_PVAR_155 s)). Qed.
Lemma lem4600791 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term106 A _55291 s) = (term107 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4600790 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4600792 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600793 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term100 A _55291 s) = (term108 A _55291 s).
Proof. exact (MK_COMB (@lem4600792 A) (@lem4600791 A _55291 s)). Qed.
Lemma lem4600794 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (((_55291 s) = (term99 A s)) = (term100 A _55291 s)) = (((_55291 s) = (term23 A s)) = (term108 A _55291 s)).
Proof. exact (MK_COMB (@lem4600787 A _55291 s) (@lem4600793 A _55291 s)). Qed.
Lemma lem4600795 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((_55291 s) = (term23 A s)) = (term108 A _55291 s).
Proof. exact (EQ_MP (@lem4600794 A _55291 s) (@lem4600781 A _55291 s)). Qed.
Lemma lem4600796 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s)) = ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s)).
Proof. exact (eq_refl ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s))). Qed.
Lemma lem4600797 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term107 A _55291 s) = (term107 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4600796 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4600798 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600799 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term108 A _55291 s) = (term108 A _55291 s).
Proof. exact (MK_COMB (@lem4600798 A) (@lem4600797 A _55291 s)). Qed.
Lemma lem4600800 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((_55291 s) = (term23 A s)) = (term108 A _55291 s).
Proof. exact (TRANS (@lem4600795 A _55291 s) (@lem4600799 A _55291 s)). Qed.
Lemma lem4600801 {A : Type'} (_55291 : type639 A) : (term95 A _55291) = (term109 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600800 A _55291 s)). Qed.
Lemma lem4600802 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600803 {A : Type'} (_55291 : type639 A) : (term96 A _55291) = (term110 A _55291).
Proof. exact (MK_COMB (@lem4600802 A) (@lem4600801 A _55291)). Qed.
Lemma lem4600804 {A : Type'} (_55291 : type639 A) : (_55291 = (term21 A)) = (term110 A _55291).
Proof. exact (TRANS (@lem4600777 A _55291) (@lem4600803 A _55291)). Qed.
Lemma lem4600805 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600806 {A : Type'} (_55291 : type639 A) : (term72 A _55291) = (term111 A _55291).
Proof. exact (MK_COMB (@lem4600805) (@lem4600804 A _55291)). Qed.
Lemma lem4600807 {A : Type'} (_55291 : type639 A) : (term63 A _55291) = (term63 A _55291).
Proof. exact (eq_refl (term63 A _55291)). Qed.
Lemma lem4600808 {A : Type'} (_55291 : type639 A) : (term80 A _55291) = (term112 A _55291).
Proof. exact (MK_COMB (@lem4600806 A _55291) (@lem4600807 A _55291)). Qed.
Lemma lem4600809 {A : Type'} : (term82 A) = (term113 A).
Proof. exact (fun_ext (fun _55291 : type639 A => @lem4600808 A _55291)). Qed.
Lemma lem4600810 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4600811 {A : Type'} : (term84 A) = (term114 A).
Proof. exact (MK_COMB (@lem4600810 A) (@lem4600809 A)). Qed.
Lemma lem4600812 {A : Type'} : (term71 A) = (term71 A).
Proof. exact (eq_refl (term71 A)). Qed.
Lemma lem4600813 {A : Type'} : ((term20 A) = (term84 A)) = ((term20 A) = (term114 A)).
Proof. exact (MK_COMB (@lem4600812 A) (@lem4600811 A)). Qed.
Lemma lem4600816 {A : Type'} : (term20 A) = (term114 A).
Proof. exact (EQ_MP (@lem4600813 A) (@lem4600759 A)). Qed.
Lemma lem4600817 {A : Type'} : (term7 A) = (term114 A).
Proof. exact (TRANS (@lem4600608 A) (@lem4600816 A)). Qed.
Lemma lem4600822 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (n : nat) : (term34 A _55291 s n) = (term34 A _55291 s n).
Proof. exact (eq_refl (term34 A _55291 s n)). Qed.
Lemma lem4600823 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term36 A _55291 s) = (term36 A _55291 s).
Proof. exact (fun_ext (fun n : nat => @lem4600822 A _55291 s n)). Qed.
Lemma lem4600824 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4600825 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term38 A _55291 s) = (term38 A _55291 s).
Proof. exact (MK_COMB (@lem4600824) (@lem4600823 A _55291 s)). Qed.
Lemma lem4600826 {A : Type'} (_55291 : type639 A) : (term40 A _55291) = (term40 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600825 A _55291 s)). Qed.
Lemma lem4600827 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600828 {A : Type'} (_55291 : type639 A) : (term41 A _55291) = (term41 A _55291).
Proof. exact (MK_COMB (@lem4600827 A) (@lem4600826 A _55291)). Qed.
Lemma lem4600829 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4600830 {A : Type'} (_55291 : type639 A) : (term42 A _55291) = (term42 A _55291).
Proof. exact (MK_COMB (@lem4600829) (@lem4600828 A _55291)). Qed.
Lemma lem4600839 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n)) = ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n))). Qed.
Lemma lem4600840 {A : Type'} (s : type686 A) : (term44 A s) = (term44 A s).
Proof. exact (fun_ext (fun n : nat => @lem4600839 A s n)). Qed.
Lemma lem4600841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4600842 {A : Type'} (s : type686 A) : (term45 A s) = (term45 A s).
Proof. exact (MK_COMB (@lem4600841) (@lem4600840 A s)). Qed.
Lemma lem4600843 {A : Type'} : (term46 A) = (term46 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4600842 A s)). Qed.
Lemma lem4600844 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4600845 {A : Type'} : (term6 A) = (term6 A).
Proof. exact (MK_COMB (@lem4600844 A) (@lem4600843 A)). Qed.
Lemma lem4600846 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600847 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem4600846) (@lem4600845 A)). Qed.
Lemma lem4600848 {A : Type'} (_55291 : type639 A) : (term47 A _55291) = (term47 A _55291).
Proof. exact (MK_COMB (@lem4600847 A) (@lem4600830 A _55291)). Qed.
Lemma lem4600857 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term48 A s n)) = ((@HAS_SIZE A s n) = (term48 A s n)).
Proof. exact (eq_refl ((@HAS_SIZE A s n) = (term48 A s n))). Qed.
Lemma lem4600858 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun n : nat => @lem4600857 A s n)). Qed.
Lemma lem4600859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4600860 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem4600859) (@lem4600858 A s)). Qed.
Lemma lem4600861 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600860 A s)). Qed.
Lemma lem4600862 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600863 {A : Type'} : (term5 A) = (term5 A).
Proof. exact (MK_COMB (@lem4600862 A) (@lem4600861 A)). Qed.
Lemma lem4600864 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600865 {A : Type'} : (term16 A) = (term16 A).
Proof. exact (MK_COMB (@lem4600864) (@lem4600863 A)). Qed.
Lemma lem4600866 {A : Type'} (_55291 : type639 A) : (term52 A _55291) = (term52 A _55291).
Proof. exact (MK_COMB (@lem4600865 A) (@lem4600848 A _55291)). Qed.
Lemma lem4600871 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term57 A _55291 s) = (term57 A _55291 s).
Proof. exact (eq_refl (term57 A _55291 s)). Qed.
Lemma lem4600872 {A : Type'} (_55291 : type639 A) : (term59 A _55291) = (term59 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600871 A _55291 s)). Qed.
Lemma lem4600873 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600874 {A : Type'} (_55291 : type639 A) : (term60 A _55291) = (term60 A _55291).
Proof. exact (MK_COMB (@lem4600873 A) (@lem4600872 A _55291)). Qed.
Lemma lem4600875 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4600876 {A : Type'} (_55291 : type639 A) : (term61 A _55291) = (term61 A _55291).
Proof. exact (MK_COMB (@lem4600875) (@lem4600874 A _55291)). Qed.
Lemma lem4600877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600878 {A : Type'} (_55291 : type639 A) : (term62 A _55291) = (term62 A _55291).
Proof. exact (MK_COMB (@lem4600877) (@lem4600876 A _55291)). Qed.
Lemma lem4600879 {A : Type'} (_55291 : type639 A) : (term63 A _55291) = (term63 A _55291).
Proof. exact (MK_COMB (@lem4600878 A _55291) (@lem4600866 A _55291)). Qed.
Lemma lem4600880 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term115 A GEN_PVAR_155 s t) = (term115 A GEN_PVAR_155 s t).
Proof. exact (eq_refl (term115 A GEN_PVAR_155 s t)). Qed.
Lemma lem4600881 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term116 A GEN_PVAR_155 s) = (term116 A GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4600880 A GEN_PVAR_155 s t)). Qed.
Lemma lem4600882 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4600883 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term102 A GEN_PVAR_155 s) = (term102 A GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4600882 A) (@lem4600881 A GEN_PVAR_155 s)). Qed.
Lemma lem4600886 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (GEN_PVAR_155 : A -> Prop) : (term105 A _55291 s GEN_PVAR_155) = (term105 A _55291 s GEN_PVAR_155).
Proof. exact (eq_refl (term105 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4600887 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s)) = ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s)).
Proof. exact (MK_COMB (@lem4600886 A _55291 s GEN_PVAR_155) (@lem4600883 A GEN_PVAR_155 s)). Qed.
Lemma lem4600888 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term107 A _55291 s) = (term107 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4600887 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4600889 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600890 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term108 A _55291 s) = (term108 A _55291 s).
Proof. exact (MK_COMB (@lem4600889 A) (@lem4600888 A _55291 s)). Qed.
Lemma lem4600891 {A : Type'} (_55291 : type639 A) : (term109 A _55291) = (term109 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4600890 A _55291 s)). Qed.
Lemma lem4600892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4600893 {A : Type'} (_55291 : type639 A) : (term110 A _55291) = (term110 A _55291).
Proof. exact (MK_COMB (@lem4600892 A) (@lem4600891 A _55291)). Qed.
Lemma lem4600894 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4600895 {A : Type'} (_55291 : type639 A) : (term111 A _55291) = (term111 A _55291).
Proof. exact (MK_COMB (@lem4600894) (@lem4600893 A _55291)). Qed.
Lemma lem4600896 {A : Type'} (_55291 : type639 A) : (term112 A _55291) = (term112 A _55291).
Proof. exact (MK_COMB (@lem4600895 A _55291) (@lem4600879 A _55291)). Qed.
Lemma lem4600897 {A : Type'} : (term113 A) = (term113 A).
Proof. exact (fun_ext (fun _55291 : type639 A => @lem4600896 A _55291)). Qed.
Lemma lem4600898 {A : Type'} : (@all ((A -> Prop) -> (A -> Prop) -> Prop)) = (@all ((A -> Prop) -> (A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> (A -> Prop) -> Prop))). Qed.
Lemma lem4600899 {A : Type'} : (term114 A) = (term114 A).
Proof. exact (MK_COMB (@lem4600898 A) (@lem4600897 A)). Qed.
Lemma lem4600984 {A : Type'} : (term7 A) = (term114 A).
Proof. exact (TRANS (@lem4600817 A) (@lem4600899 A)). Qed.
Lemma lem4600985 {A : Type'} : (term114 A) = (term7 A).
Proof. exact (SYM (@lem4600984 A)). Qed.
Lemma lem4600986 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) : term110 A _55291.
Proof. exact (h1). Qed.
Lemma lem4600987 {A : Type'} (_55291 : type639 A) (h1 : term61 A _55291) : term61 A _55291.
Proof. exact (h1). Qed.
Lemma lem4600988 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem4600989 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem4600990 {A : Type'} (_55291 : type639 A) (h1 : term41 A _55291) : term41 A _55291.
Proof. exact (h1). Qed.
Lemma lem4600994 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term115 A GEN_PVAR_155 s t) = (term115 A GEN_PVAR_155 s t).
Proof. exact (eq_refl (term115 A GEN_PVAR_155 s t)). Qed.
Lemma lem4600995 {A : Type'} (P : type686 A) : (term117 A P) = (term118 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4600996 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term119 A GEN_PVAR_155 s) = (term120 A GEN_PVAR_155 s).
Proof. exact (@lem4600995 A (term116 A GEN_PVAR_155 s)). Qed.
Lemma lem4600997 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term121 A GEN_PVAR_155 s t) = (term115 A GEN_PVAR_155 s t).
Proof. exact (eq_refl (term121 A GEN_PVAR_155 s t)). Qed.
Lemma lem4600998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4601000 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term122 A GEN_PVAR_155 s t) = (term123 A GEN_PVAR_155 s t).
Proof. exact (MK_COMB (@lem4600998) (@lem4600997 A GEN_PVAR_155 s t)). Qed.
Lemma lem4601001 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term124 A GEN_PVAR_155 s) = (term125 A GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4601000 A GEN_PVAR_155 s t)). Qed.
Lemma lem4601002 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601003 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term120 A GEN_PVAR_155 s) = (term126 A GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601002 A) (@lem4601001 A GEN_PVAR_155 s)). Qed.
Lemma lem4601004 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term119 A GEN_PVAR_155 s) = (term126 A GEN_PVAR_155 s).
Proof. exact (TRANS (@lem4600996 A GEN_PVAR_155 s) (@lem4601003 A GEN_PVAR_155 s)). Qed.
Lemma lem4601005 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term116 A GEN_PVAR_155 s) = (term116 A GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4600994 A GEN_PVAR_155 s t)). Qed.
Lemma lem4601006 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4601007 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term102 A GEN_PVAR_155 s) = (term102 A GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601006 A) (@lem4601005 A GEN_PVAR_155 s)). Qed.
Lemma lem4601009 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (GEN_PVAR_155 : A -> Prop) : (term127 A _55291 s GEN_PVAR_155) = (term127 A _55291 s GEN_PVAR_155).
Proof. exact (eq_refl (term127 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601010 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term128 A _55291 GEN_PVAR_155 s) = (term128 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601009 A _55291 s GEN_PVAR_155) (@lem4601007 A GEN_PVAR_155 s)). Qed.
Lemma lem4601012 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (GEN_PVAR_155 : A -> Prop) : (term129 A _55291 s GEN_PVAR_155) = (term129 A _55291 s GEN_PVAR_155).
Proof. exact (eq_refl (term129 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601013 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term130 A _55291 GEN_PVAR_155 s) = (term131 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601012 A _55291 s GEN_PVAR_155) (@lem4601004 A GEN_PVAR_155 s)). Qed.
Lemma lem4601014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601015 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term132 A _55291 GEN_PVAR_155 s) = (term133 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601014) (@lem4601013 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601016 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term134 A _55291 GEN_PVAR_155 s) = (term135 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601015 A _55291 GEN_PVAR_155 s) (@lem4601010 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601017 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s)) = (term134 A _55291 GEN_PVAR_155 s).
Proof. exact (@lem17784 (_55291 s GEN_PVAR_155) (term102 A GEN_PVAR_155 s)). Qed.
Lemma lem4601018 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : ((_55291 s GEN_PVAR_155) = (term102 A GEN_PVAR_155 s)) = (term135 A _55291 GEN_PVAR_155 s).
Proof. exact (TRANS (@lem4601017 A _55291 GEN_PVAR_155 s) (@lem4601016 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601019 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term107 A _55291 s) = (term136 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4601018 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601020 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601021 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term108 A _55291 s) = (term137 A _55291 s).
Proof. exact (MK_COMB (@lem4601020 A) (@lem4601019 A _55291 s)). Qed.
Lemma lem4601022 {A : Type'} (_55291 : type639 A) : (term109 A _55291) = (term138 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601021 A _55291 s)). Qed.
Lemma lem4601023 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601024 {A : Type'} (_55291 : type639 A) : (term110 A _55291) = (term139 A _55291).
Proof. exact (MK_COMB (@lem4601023 A) (@lem4601022 A _55291)). Qed.
Lemma lem4601030 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4601031 {A : Type'} (P : type686 A) (Q : type686 A) : (term142 A P Q) = (term143 A P Q).
Proof. exact (@lem4601030 (A -> Prop) P Q). Qed.
Lemma lem4601032 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term144 A _55291 s) = (term145 A _55291 s).
Proof. exact (@lem4601031 A (term146 A _55291 s) (term147 A _55291 s)). Qed.
Lemma lem4601033 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term148 A _55291 s GEN_PVAR_155) = (term131 A _55291 GEN_PVAR_155 s).
Proof. exact (eq_refl (term148 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601035 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term149 A _55291 s GEN_PVAR_155) = (term133 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601034) (@lem4601033 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601036 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term150 A _55291 s GEN_PVAR_155) = (term128 A _55291 GEN_PVAR_155 s).
Proof. exact (eq_refl (term150 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601037 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term151 A _55291 s GEN_PVAR_155) = (term135 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601035 A _55291 GEN_PVAR_155 s) (@lem4601036 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601038 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term152 A _55291 s) = (term136 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4601037 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601039 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601040 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term144 A _55291 s) = (term137 A _55291 s).
Proof. exact (MK_COMB (@lem4601039 A) (@lem4601038 A _55291 s)). Qed.
Lemma lem4601041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601042 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term153 A _55291 s) = (term154 A _55291 s).
Proof. exact (MK_COMB (@lem4601041) (@lem4601040 A _55291 s)). Qed.
Lemma lem4601043 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term148 A _55291 s GEN_PVAR_155) = (term131 A _55291 GEN_PVAR_155 s).
Proof. exact (eq_refl (term148 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601044 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term155 A _55291 s) = (term146 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4601043 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601045 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601046 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term156 A _55291 s) = (term157 A _55291 s).
Proof. exact (MK_COMB (@lem4601045 A) (@lem4601044 A _55291 s)). Qed.
Lemma lem4601047 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601048 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term158 A _55291 s) = (term159 A _55291 s).
Proof. exact (MK_COMB (@lem4601047) (@lem4601046 A _55291 s)). Qed.
Lemma lem4601049 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term150 A _55291 s GEN_PVAR_155) = (term128 A _55291 GEN_PVAR_155 s).
Proof. exact (eq_refl (term150 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601050 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term160 A _55291 s) = (term147 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4601049 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601051 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601052 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term161 A _55291 s) = (term162 A _55291 s).
Proof. exact (MK_COMB (@lem4601051 A) (@lem4601050 A _55291 s)). Qed.
Lemma lem4601053 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term145 A _55291 s) = (term163 A _55291 s).
Proof. exact (MK_COMB (@lem4601048 A _55291 s) (@lem4601052 A _55291 s)). Qed.
Lemma lem4601054 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((term144 A _55291 s) = (term145 A _55291 s)) = ((term137 A _55291 s) = (term163 A _55291 s)).
Proof. exact (MK_COMB (@lem4601042 A _55291 s) (@lem4601053 A _55291 s)). Qed.
Lemma lem4601055 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term137 A _55291 s) = (term163 A _55291 s).
Proof. exact (EQ_MP (@lem4601054 A _55291 s) (@lem4601032 A _55291 s)). Qed.
Lemma lem4601160 {A : Type'} (_55291 : type639 A) : (term138 A _55291) = (term164 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601055 A _55291 s)). Qed.
Lemma lem4601161 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601162 {A : Type'} (_55291 : type639 A) : (term139 A _55291) = (term165 A _55291).
Proof. exact (MK_COMB (@lem4601161 A) (@lem4601160 A _55291)). Qed.
Lemma lem4601164 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4601165 {A : Type'} (P : type686 A) (Q : type686 A) : (term142 A P Q) = (term143 A P Q).
Proof. exact (@lem4601164 (A -> Prop) P Q). Qed.
Lemma lem4601166 {A : Type'} (_55291 : type639 A) : (term166 A _55291) = (term167 A _55291).
Proof. exact (@lem4601165 A (term168 A _55291) (term169 A _55291)). Qed.
Lemma lem4601167 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term170 A _55291 s) = (term157 A _55291 s).
Proof. exact (eq_refl (term170 A _55291 s)). Qed.
Lemma lem4601168 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601169 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term171 A _55291 s) = (term159 A _55291 s).
Proof. exact (MK_COMB (@lem4601168) (@lem4601167 A _55291 s)). Qed.
Lemma lem4601170 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term172 A _55291 s) = (term162 A _55291 s).
Proof. exact (eq_refl (term172 A _55291 s)). Qed.
Lemma lem4601171 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term173 A _55291 s) = (term163 A _55291 s).
Proof. exact (MK_COMB (@lem4601169 A _55291 s) (@lem4601170 A _55291 s)). Qed.
Lemma lem4601172 {A : Type'} (_55291 : type639 A) : (term174 A _55291) = (term164 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601171 A _55291 s)). Qed.
Lemma lem4601173 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601174 {A : Type'} (_55291 : type639 A) : (term166 A _55291) = (term165 A _55291).
Proof. exact (MK_COMB (@lem4601173 A) (@lem4601172 A _55291)). Qed.
Lemma lem4601175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601176 {A : Type'} (_55291 : type639 A) : (term175 A _55291) = (term176 A _55291).
Proof. exact (MK_COMB (@lem4601175) (@lem4601174 A _55291)). Qed.
Lemma lem4601177 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term170 A _55291 s) = (term157 A _55291 s).
Proof. exact (eq_refl (term170 A _55291 s)). Qed.
Lemma lem4601178 {A : Type'} (_55291 : type639 A) : (term177 A _55291) = (term168 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601177 A _55291 s)). Qed.
Lemma lem4601179 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601180 {A : Type'} (_55291 : type639 A) : (term178 A _55291) = (term179 A _55291).
Proof. exact (MK_COMB (@lem4601179 A) (@lem4601178 A _55291)). Qed.
Lemma lem4601181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601182 {A : Type'} (_55291 : type639 A) : (term180 A _55291) = (term181 A _55291).
Proof. exact (MK_COMB (@lem4601181) (@lem4601180 A _55291)). Qed.
Lemma lem4601183 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term172 A _55291 s) = (term162 A _55291 s).
Proof. exact (eq_refl (term172 A _55291 s)). Qed.
Lemma lem4601184 {A : Type'} (_55291 : type639 A) : (term182 A _55291) = (term169 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601183 A _55291 s)). Qed.
Lemma lem4601185 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601186 {A : Type'} (_55291 : type639 A) : (term183 A _55291) = (term184 A _55291).
Proof. exact (MK_COMB (@lem4601185 A) (@lem4601184 A _55291)). Qed.
Lemma lem4601187 {A : Type'} (_55291 : type639 A) : (term167 A _55291) = (term185 A _55291).
Proof. exact (MK_COMB (@lem4601182 A _55291) (@lem4601186 A _55291)). Qed.
Lemma lem4601188 {A : Type'} (_55291 : type639 A) : ((term166 A _55291) = (term167 A _55291)) = ((term165 A _55291) = (term185 A _55291)).
Proof. exact (MK_COMB (@lem4601176 A _55291) (@lem4601187 A _55291)). Qed.
Lemma lem4601189 {A : Type'} (_55291 : type639 A) : (term165 A _55291) = (term185 A _55291).
Proof. exact (EQ_MP (@lem4601188 A _55291) (@lem4601166 A _55291)). Qed.
Lemma lem4601302 {A : Type'} (_55291 : type639 A) : (term139 A _55291) = (term185 A _55291).
Proof. exact (TRANS (@lem4601162 A _55291) (@lem4601189 A _55291)). Qed.
Lemma lem4601304 {A : Type'} (P : Prop) (Q : A -> Prop) : (term186 A P Q) = (term187 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4601305 {A : Type'} (P : Prop) (Q : type686 A) : (term188 A P Q) = (term189 A P Q).
Proof. exact (@lem4601304 (A -> Prop) P Q). Qed.
Lemma lem4601306 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term190 A _55291 GEN_PVAR_155 s) = (term191 A _55291 GEN_PVAR_155 s).
Proof. exact (@lem4601305 A (term192 A _55291 s GEN_PVAR_155) (term116 A GEN_PVAR_155 s)). Qed.
Lemma lem4601307 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term121 A GEN_PVAR_155 s t) = (term115 A GEN_PVAR_155 s t).
Proof. exact (eq_refl (term121 A GEN_PVAR_155 s t)). Qed.
Lemma lem4601308 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term193 A GEN_PVAR_155 s) = (term116 A GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4601307 A GEN_PVAR_155 s t)). Qed.
Lemma lem4601309 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4601310 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term194 A GEN_PVAR_155 s) = (term102 A GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601309 A) (@lem4601308 A GEN_PVAR_155 s)). Qed.
Lemma lem4601311 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (GEN_PVAR_155 : A -> Prop) : (term127 A _55291 s GEN_PVAR_155) = (term127 A _55291 s GEN_PVAR_155).
Proof. exact (eq_refl (term127 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601312 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term190 A _55291 GEN_PVAR_155 s) = (term128 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601311 A _55291 s GEN_PVAR_155) (@lem4601310 A GEN_PVAR_155 s)). Qed.
Lemma lem4601313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601314 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term195 A _55291 GEN_PVAR_155 s) = (term196 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601313) (@lem4601312 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601315 {A : Type'} (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term121 A GEN_PVAR_155 s t) = (term115 A GEN_PVAR_155 s t).
Proof. exact (eq_refl (term121 A GEN_PVAR_155 s t)). Qed.
Lemma lem4601316 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (GEN_PVAR_155 : A -> Prop) : (term127 A _55291 s GEN_PVAR_155) = (term127 A _55291 s GEN_PVAR_155).
Proof. exact (eq_refl (term127 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601317 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term197 A _55291 GEN_PVAR_155 s t) = (term198 A _55291 GEN_PVAR_155 s t).
Proof. exact (MK_COMB (@lem4601316 A _55291 s GEN_PVAR_155) (@lem4601315 A GEN_PVAR_155 s t)). Qed.
Lemma lem4601318 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term199 A _55291 GEN_PVAR_155 s) = (term200 A _55291 GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4601317 A _55291 GEN_PVAR_155 s t)). Qed.
Lemma lem4601319 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4601320 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term191 A _55291 GEN_PVAR_155 s) = (term201 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601319 A) (@lem4601318 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601321 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : ((term190 A _55291 GEN_PVAR_155 s) = (term191 A _55291 GEN_PVAR_155 s)) = ((term128 A _55291 GEN_PVAR_155 s) = (term201 A _55291 GEN_PVAR_155 s)).
Proof. exact (MK_COMB (@lem4601314 A _55291 GEN_PVAR_155 s) (@lem4601320 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601322 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term128 A _55291 GEN_PVAR_155 s) = (term201 A _55291 GEN_PVAR_155 s).
Proof. exact (EQ_MP (@lem4601321 A _55291 GEN_PVAR_155 s) (@lem4601306 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601323 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term147 A _55291 s) = (term202 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4601322 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601324 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601325 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term162 A _55291 s) = (term203 A _55291 s).
Proof. exact (MK_COMB (@lem4601324 A) (@lem4601323 A _55291 s)). Qed.
Lemma lem4601327 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4601328 {A : Type'} (P : type639 A) : (term206 A P) = (term207 A P).
Proof. exact (@lem4601327 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem4601329 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term208 A _55291 s) = (term209 A _55291 s).
Proof. exact (@lem4601328 A (term210 A _55291 s)). Qed.
Lemma lem4601330 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term211 A _55291 s GEN_PVAR_155) = (term200 A _55291 GEN_PVAR_155 s).
Proof. exact (eq_refl (term211 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601331 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4601332 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term212 A _55291 s GEN_PVAR_155 t) = (term213 A _55291 GEN_PVAR_155 s t).
Proof. exact (MK_COMB (@lem4601330 A _55291 GEN_PVAR_155 s) (@lem4601331 A t)). Qed.
Lemma lem4601333 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term213 A _55291 GEN_PVAR_155 s t) = (term198 A _55291 GEN_PVAR_155 s t).
Proof. exact (eq_refl (term213 A _55291 GEN_PVAR_155 s t)). Qed.
Lemma lem4601334 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) (t : A -> Prop) : (term212 A _55291 s GEN_PVAR_155 t) = (term198 A _55291 GEN_PVAR_155 s t).
Proof. exact (TRANS (@lem4601332 A _55291 GEN_PVAR_155 s t) (@lem4601333 A _55291 GEN_PVAR_155 s t)). Qed.
Lemma lem4601335 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term214 A _55291 s GEN_PVAR_155) = (term200 A _55291 GEN_PVAR_155 s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4601334 A _55291 GEN_PVAR_155 s t)). Qed.
Lemma lem4601336 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4601337 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term215 A _55291 s GEN_PVAR_155) = (term201 A _55291 GEN_PVAR_155 s).
Proof. exact (MK_COMB (@lem4601336 A) (@lem4601335 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601338 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term216 A _55291 s) = (term202 A _55291 s).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4601337 A _55291 GEN_PVAR_155 s)). Qed.
Lemma lem4601339 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601340 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term208 A _55291 s) = (term203 A _55291 s).
Proof. exact (MK_COMB (@lem4601339 A) (@lem4601338 A _55291 s)). Qed.
Lemma lem4601341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601342 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term217 A _55291 s) = (term218 A _55291 s).
Proof. exact (MK_COMB (@lem4601341) (@lem4601340 A _55291 s)). Qed.
Lemma lem4601343 {A : Type'} (_55291 : type639 A) (GEN_PVAR_155 : A -> Prop) (s : A -> Prop) : (term211 A _55291 s GEN_PVAR_155) = (term200 A _55291 GEN_PVAR_155 s).
Proof. exact (eq_refl (term211 A _55291 s GEN_PVAR_155)). Qed.
Lemma lem4601344 {A : Type'} (t : type672 A) (GEN_PVAR_155 : A -> Prop) : (t GEN_PVAR_155) = (t GEN_PVAR_155).
Proof. exact (eq_refl (t GEN_PVAR_155)). Qed.
Lemma lem4601345 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) (GEN_PVAR_155 : A -> Prop) : (term219 A _55291 s t GEN_PVAR_155) = (term220 A _55291 s t GEN_PVAR_155).
Proof. exact (MK_COMB (@lem4601343 A _55291 GEN_PVAR_155 s) (@lem4601344 A t GEN_PVAR_155)). Qed.
Lemma lem4601346 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) (GEN_PVAR_155 : A -> Prop) : (term220 A _55291 s t GEN_PVAR_155) = (term221 A _55291 s t GEN_PVAR_155).
Proof. exact (eq_refl (term220 A _55291 s t GEN_PVAR_155)). Qed.
Lemma lem4601347 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) (GEN_PVAR_155 : A -> Prop) : (term219 A _55291 s t GEN_PVAR_155) = (term221 A _55291 s t GEN_PVAR_155).
Proof. exact (TRANS (@lem4601345 A _55291 s t GEN_PVAR_155) (@lem4601346 A _55291 s t GEN_PVAR_155)). Qed.
Lemma lem4601348 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) : (term222 A _55291 s t) = (term223 A _55291 s t).
Proof. exact (fun_ext (fun GEN_PVAR_155 : A -> Prop => @lem4601347 A _55291 s t GEN_PVAR_155)). Qed.
Lemma lem4601349 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601350 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) : (term224 A _55291 s t) = (term225 A _55291 s t).
Proof. exact (MK_COMB (@lem4601349 A) (@lem4601348 A _55291 s t)). Qed.
Lemma lem4601351 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term226 A _55291 s) = (term227 A _55291 s).
Proof. exact (fun_ext (fun t : type672 A => @lem4601350 A _55291 s t)). Qed.
Lemma lem4601352 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem4601353 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term209 A _55291 s) = (term228 A _55291 s).
Proof. exact (MK_COMB (@lem4601352 A) (@lem4601351 A _55291 s)). Qed.
Lemma lem4601354 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : ((term208 A _55291 s) = (term209 A _55291 s)) = ((term203 A _55291 s) = (term228 A _55291 s)).
Proof. exact (MK_COMB (@lem4601342 A _55291 s) (@lem4601353 A _55291 s)). Qed.
Lemma lem4601355 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term203 A _55291 s) = (term228 A _55291 s).
Proof. exact (EQ_MP (@lem4601354 A _55291 s) (@lem4601329 A _55291 s)). Qed.
Lemma lem4601356 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term162 A _55291 s) = (term228 A _55291 s).
Proof. exact (TRANS (@lem4601325 A _55291 s) (@lem4601355 A _55291 s)). Qed.
Lemma lem4601357 {A : Type'} (_55291 : type639 A) : (term169 A _55291) = (term229 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601356 A _55291 s)). Qed.
Lemma lem4601358 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601359 {A : Type'} (_55291 : type639 A) : (term184 A _55291) = (term230 A _55291).
Proof. exact (MK_COMB (@lem4601358 A) (@lem4601357 A _55291)). Qed.
Lemma lem4601361 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4601362 {A : Type'} (P : type596 A) : (term231 A P) = (term232 A P).
Proof. exact (@lem4601361 (A -> Prop) (type672 A) P). Qed.
Lemma lem4601363 {A : Type'} (_55291 : type639 A) : (term233 A _55291) = (term234 A _55291).
Proof. exact (@lem4601362 A (term235 A _55291)). Qed.
Lemma lem4601364 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term236 A _55291 s) = (term227 A _55291 s).
Proof. exact (eq_refl (term236 A _55291 s)). Qed.
Lemma lem4601365 {A : Type'} (t : type672 A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4601366 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) : (term237 A _55291 s t) = (term238 A _55291 s t).
Proof. exact (MK_COMB (@lem4601364 A _55291 s) (@lem4601365 A t)). Qed.
Lemma lem4601367 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) : (term238 A _55291 s t) = (term225 A _55291 s t).
Proof. exact (eq_refl (term238 A _55291 s t)). Qed.
Lemma lem4601368 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (t : type672 A) : (term237 A _55291 s t) = (term225 A _55291 s t).
Proof. exact (TRANS (@lem4601366 A _55291 s t) (@lem4601367 A _55291 s t)). Qed.
Lemma lem4601369 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term239 A _55291 s) = (term227 A _55291 s).
Proof. exact (fun_ext (fun t : type672 A => @lem4601368 A _55291 s t)). Qed.
Lemma lem4601370 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem4601371 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term240 A _55291 s) = (term228 A _55291 s).
Proof. exact (MK_COMB (@lem4601370 A) (@lem4601369 A _55291 s)). Qed.
Lemma lem4601372 {A : Type'} (_55291 : type639 A) : (term241 A _55291) = (term229 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601371 A _55291 s)). Qed.
Lemma lem4601373 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601374 {A : Type'} (_55291 : type639 A) : (term233 A _55291) = (term230 A _55291).
Proof. exact (MK_COMB (@lem4601373 A) (@lem4601372 A _55291)). Qed.
Lemma lem4601375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601376 {A : Type'} (_55291 : type639 A) : (term242 A _55291) = (term243 A _55291).
Proof. exact (MK_COMB (@lem4601375) (@lem4601374 A _55291)). Qed.
Lemma lem4601377 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term236 A _55291 s) = (term227 A _55291 s).
Proof. exact (eq_refl (term236 A _55291 s)). Qed.
Lemma lem4601378 {A : Type'} (t : type636 A) (s : A -> Prop) : (t s) = (t s).
Proof. exact (eq_refl (t s)). Qed.
Lemma lem4601379 {A : Type'} (_55291 : type639 A) (t : type636 A) (s : A -> Prop) : (term244 A _55291 t s) = (term245 A _55291 t s).
Proof. exact (MK_COMB (@lem4601377 A _55291 s) (@lem4601378 A t s)). Qed.
Lemma lem4601380 {A : Type'} (_55291 : type639 A) (t : type636 A) (s : A -> Prop) : (term245 A _55291 t s) = (term246 A _55291 t s).
Proof. exact (eq_refl (term245 A _55291 t s)). Qed.
Lemma lem4601381 {A : Type'} (_55291 : type639 A) (t : type636 A) (s : A -> Prop) : (term244 A _55291 t s) = (term246 A _55291 t s).
Proof. exact (TRANS (@lem4601379 A _55291 t s) (@lem4601380 A _55291 t s)). Qed.
Lemma lem4601382 {A : Type'} (_55291 : type639 A) (t : type636 A) : (term247 A _55291 t) = (term248 A _55291 t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601381 A _55291 t s)). Qed.
Lemma lem4601383 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601384 {A : Type'} (_55291 : type639 A) (t : type636 A) : (term249 A _55291 t) = (term250 A _55291 t).
Proof. exact (MK_COMB (@lem4601383 A) (@lem4601382 A _55291 t)). Qed.
Lemma lem4601385 {A : Type'} (_55291 : type639 A) : (term251 A _55291) = (term252 A _55291).
Proof. exact (fun_ext (fun t : type636 A => @lem4601384 A _55291 t)). Qed.
Lemma lem4601386 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem4601387 {A : Type'} (_55291 : type639 A) : (term234 A _55291) = (term253 A _55291).
Proof. exact (MK_COMB (@lem4601386 A) (@lem4601385 A _55291)). Qed.
Lemma lem4601388 {A : Type'} (_55291 : type639 A) : ((term233 A _55291) = (term234 A _55291)) = ((term230 A _55291) = (term253 A _55291)).
Proof. exact (MK_COMB (@lem4601376 A _55291) (@lem4601387 A _55291)). Qed.
Lemma lem4601389 {A : Type'} (_55291 : type639 A) : (term230 A _55291) = (term253 A _55291).
Proof. exact (EQ_MP (@lem4601388 A _55291) (@lem4601363 A _55291)). Qed.
Lemma lem4601390 {A : Type'} (_55291 : type639 A) : (term184 A _55291) = (term253 A _55291).
Proof. exact (TRANS (@lem4601359 A _55291) (@lem4601389 A _55291)). Qed.
Lemma lem4601391 {A : Type'} (_55291 : type639 A) : (term181 A _55291) = (term181 A _55291).
Proof. exact (eq_refl (term181 A _55291)). Qed.
Lemma lem4601392 {A : Type'} (_55291 : type639 A) : (term185 A _55291) = (term254 A _55291).
Proof. exact (MK_COMB (@lem4601391 A _55291) (@lem4601390 A _55291)). Qed.
Lemma lem4601394 {A : Type'} (P : Prop) (Q : A -> Prop) : (term255 A P Q) = (term256 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4601395 {A : Type'} (P : Prop) (Q : type138 A) : (term257 A P Q) = (term258 A P Q).
Proof. exact (@lem4601394 (type636 A) P Q). Qed.
Lemma lem4601396 {A : Type'} (_55291 : type639 A) : (term259 A _55291) = (term260 A _55291).
Proof. exact (@lem4601395 A (term179 A _55291) (term252 A _55291)). Qed.
Lemma lem4601397 {A : Type'} (_55291 : type639 A) (t : type636 A) : (term261 A _55291 t) = (term250 A _55291 t).
Proof. exact (eq_refl (term261 A _55291 t)). Qed.
Lemma lem4601398 {A : Type'} (_55291 : type639 A) : (term262 A _55291) = (term252 A _55291).
Proof. exact (fun_ext (fun t : type636 A => @lem4601397 A _55291 t)). Qed.
Lemma lem4601399 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem4601400 {A : Type'} (_55291 : type639 A) : (term263 A _55291) = (term253 A _55291).
Proof. exact (MK_COMB (@lem4601399 A) (@lem4601398 A _55291)). Qed.
Lemma lem4601401 {A : Type'} (_55291 : type639 A) : (term181 A _55291) = (term181 A _55291).
Proof. exact (eq_refl (term181 A _55291)). Qed.
Lemma lem4601402 {A : Type'} (_55291 : type639 A) : (term259 A _55291) = (term254 A _55291).
Proof. exact (MK_COMB (@lem4601401 A _55291) (@lem4601400 A _55291)). Qed.
Lemma lem4601403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601404 {A : Type'} (_55291 : type639 A) : (term264 A _55291) = (term265 A _55291).
Proof. exact (MK_COMB (@lem4601403) (@lem4601402 A _55291)). Qed.
Lemma lem4601405 {A : Type'} (_55291 : type639 A) (t : type636 A) : (term261 A _55291 t) = (term250 A _55291 t).
Proof. exact (eq_refl (term261 A _55291 t)). Qed.
Lemma lem4601406 {A : Type'} (_55291 : type639 A) : (term181 A _55291) = (term181 A _55291).
Proof. exact (eq_refl (term181 A _55291)). Qed.
Lemma lem4601407 {A : Type'} (_55291 : type639 A) (t : type636 A) : (term266 A _55291 t) = (term267 A _55291 t).
Proof. exact (MK_COMB (@lem4601406 A _55291) (@lem4601405 A _55291 t)). Qed.
Lemma lem4601408 {A : Type'} (_55291 : type639 A) : (term268 A _55291) = (term269 A _55291).
Proof. exact (fun_ext (fun t : type636 A => @lem4601407 A _55291 t)). Qed.
Lemma lem4601409 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem4601410 {A : Type'} (_55291 : type639 A) : (term260 A _55291) = (term270 A _55291).
Proof. exact (MK_COMB (@lem4601409 A) (@lem4601408 A _55291)). Qed.
Lemma lem4601411 {A : Type'} (_55291 : type639 A) : ((term259 A _55291) = (term260 A _55291)) = ((term254 A _55291) = (term270 A _55291)).
Proof. exact (MK_COMB (@lem4601404 A _55291) (@lem4601410 A _55291)). Qed.
Lemma lem4601412 {A : Type'} (_55291 : type639 A) : (term254 A _55291) = (term270 A _55291).
Proof. exact (EQ_MP (@lem4601411 A _55291) (@lem4601396 A _55291)). Qed.
Lemma lem4601413 {A : Type'} (_55291 : type639 A) : (term185 A _55291) = (term270 A _55291).
Proof. exact (TRANS (@lem4601392 A _55291) (@lem4601412 A _55291)). Qed.
Lemma lem4601414 {A : Type'} (_55291 : type639 A) : (term139 A _55291) = (term270 A _55291).
Proof. exact (TRANS (@lem4601302 A _55291) (@lem4601413 A _55291)). Qed.
Lemma lem4601415 {A : Type'} (_55291 : type639 A) : (term110 A _55291) = (term270 A _55291).
Proof. exact (TRANS (@lem4601024 A _55291) (@lem4601414 A _55291)). Qed.
Lemma lem4601416 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) : term270 A _55291.
Proof. exact (EQ_MP (@lem4601415 A _55291) (@lem4600986 A _55291 h1)). Qed.
Lemma lem4601423 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term271 A _55291 s) = (term272 A _55291 s).
Proof. exact (@lem17362 (@FINITE A s) (term54 A _55291 s)). Qed.
Lemma lem4601424 {A : Type'} (P : type686 A) : (term273 A P) = (term274 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4601425 {A : Type'} (_55291 : type639 A) : (term61 A _55291) = (term275 A _55291).
Proof. exact (@lem4601424 A (term59 A _55291)). Qed.
Lemma lem4601426 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term276 A _55291 s) = (term57 A _55291 s).
Proof. exact (eq_refl (term276 A _55291 s)). Qed.
Lemma lem4601427 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4601428 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term277 A _55291 s) = (term271 A _55291 s).
Proof. exact (MK_COMB (@lem4601427) (@lem4601426 A _55291 s)). Qed.
Lemma lem4601429 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term277 A _55291 s) = (term272 A _55291 s).
Proof. exact (TRANS (@lem4601428 A _55291 s) (@lem4601423 A _55291 s)). Qed.
Lemma lem4601430 {A : Type'} (_55291 : type639 A) : (term278 A _55291) = (term279 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601429 A _55291 s)). Qed.
Lemma lem4601431 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4601432 {A : Type'} (_55291 : type639 A) : (term275 A _55291) = (term280 A _55291).
Proof. exact (MK_COMB (@lem4601431 A) (@lem4601430 A _55291)). Qed.
Lemma lem4601465 {A : Type'} (_55291 : type639 A) : (term61 A _55291) = (term280 A _55291).
Proof. exact (TRANS (@lem4601425 A _55291) (@lem4601432 A _55291)). Qed.
Lemma lem4601466 {A : Type'} (_55291 : type639 A) (h1 : term61 A _55291) : term280 A _55291.
Proof. exact (EQ_MP (@lem4601465 A _55291) (@lem4600987 A _55291 h1)). Qed.
Lemma lem4601477 {A : Type'} (s : A -> Prop) (n : nat) : (term281 A s n) = (term282 A s n).
Proof. exact (@lem17045 (@FINITE A s) ((@CARD A s) = n)). Qed.
Lemma lem4601483 {A : Type'} (s : A -> Prop) (n : nat) : (term283 A s n) = (term283 A s n).
Proof. exact (eq_refl (term283 A s n)). Qed.
Lemma lem4601485 {A : Type'} (s : A -> Prop) (n : nat) : (term284 A s n) = (term284 A s n).
Proof. exact (eq_refl (term284 A s n)). Qed.
Lemma lem4601486 {A : Type'} (s : A -> Prop) (n : nat) : (term285 A s n) = (term286 A s n).
Proof. exact (MK_COMB (@lem4601485 A s n) (@lem4601477 A s n)). Qed.
Lemma lem4601487 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601488 {A : Type'} (s : A -> Prop) (n : nat) : (term287 A s n) = (term288 A s n).
Proof. exact (MK_COMB (@lem4601487) (@lem4601486 A s n)). Qed.
Lemma lem4601489 {A : Type'} (s : A -> Prop) (n : nat) : (term289 A s n) = (term290 A s n).
Proof. exact (MK_COMB (@lem4601488 A s n) (@lem4601483 A s n)). Qed.
Lemma lem4601490 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term48 A s n)) = (term289 A s n).
Proof. exact (@lem17784 (@HAS_SIZE A s n) (term48 A s n)). Qed.
Lemma lem4601491 {A : Type'} (s : A -> Prop) (n : nat) : ((@HAS_SIZE A s n) = (term48 A s n)) = (term290 A s n).
Proof. exact (TRANS (@lem4601490 A s n) (@lem4601489 A s n)). Qed.
Lemma lem4601492 {A : Type'} (s : A -> Prop) : (term49 A s) = (term291 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601491 A s n)). Qed.
Lemma lem4601493 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601494 {A : Type'} (s : A -> Prop) : (term50 A s) = (term292 A s).
Proof. exact (MK_COMB (@lem4601493) (@lem4601492 A s)). Qed.
Lemma lem4601495 {A : Type'} : (term51 A) = (term293 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601494 A s)). Qed.
Lemma lem4601496 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601497 {A : Type'} : (term5 A) = (term294 A).
Proof. exact (MK_COMB (@lem4601496 A) (@lem4601495 A)). Qed.
Lemma lem4601503 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4601504 (P : nat -> Prop) (Q : nat -> Prop) : (term295 P Q) = (term296 P Q).
Proof. exact (@lem4601503 nat P Q). Qed.
Lemma lem4601505 {A : Type'} (s : A -> Prop) : (term297 A s) = (term298 A s).
Proof. exact (@lem4601504 (term299 A s) (term300 A s)). Qed.
Lemma lem4601506 {A : Type'} (s : A -> Prop) (n : nat) : (term301 A s n) = (term286 A s n).
Proof. exact (eq_refl (term301 A s n)). Qed.
Lemma lem4601507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601508 {A : Type'} (s : A -> Prop) (n : nat) : (term302 A s n) = (term288 A s n).
Proof. exact (MK_COMB (@lem4601507) (@lem4601506 A s n)). Qed.
Lemma lem4601509 {A : Type'} (s : A -> Prop) (n : nat) : (term303 A s n) = (term283 A s n).
Proof. exact (eq_refl (term303 A s n)). Qed.
Lemma lem4601510 {A : Type'} (s : A -> Prop) (n : nat) : (term304 A s n) = (term290 A s n).
Proof. exact (MK_COMB (@lem4601508 A s n) (@lem4601509 A s n)). Qed.
Lemma lem4601511 {A : Type'} (s : A -> Prop) : (term305 A s) = (term291 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601510 A s n)). Qed.
Lemma lem4601512 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601513 {A : Type'} (s : A -> Prop) : (term297 A s) = (term292 A s).
Proof. exact (MK_COMB (@lem4601512) (@lem4601511 A s)). Qed.
Lemma lem4601514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601515 {A : Type'} (s : A -> Prop) : (term306 A s) = (term307 A s).
Proof. exact (MK_COMB (@lem4601514) (@lem4601513 A s)). Qed.
Lemma lem4601516 {A : Type'} (s : A -> Prop) (n : nat) : (term301 A s n) = (term286 A s n).
Proof. exact (eq_refl (term301 A s n)). Qed.
Lemma lem4601517 {A : Type'} (s : A -> Prop) : (term308 A s) = (term299 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601516 A s n)). Qed.
Lemma lem4601518 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601519 {A : Type'} (s : A -> Prop) : (term309 A s) = (term310 A s).
Proof. exact (MK_COMB (@lem4601518) (@lem4601517 A s)). Qed.
Lemma lem4601520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601521 {A : Type'} (s : A -> Prop) : (term311 A s) = (term312 A s).
Proof. exact (MK_COMB (@lem4601520) (@lem4601519 A s)). Qed.
Lemma lem4601522 {A : Type'} (s : A -> Prop) (n : nat) : (term303 A s n) = (term283 A s n).
Proof. exact (eq_refl (term303 A s n)). Qed.
Lemma lem4601523 {A : Type'} (s : A -> Prop) : (term313 A s) = (term300 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601522 A s n)). Qed.
Lemma lem4601524 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601525 {A : Type'} (s : A -> Prop) : (term314 A s) = (term315 A s).
Proof. exact (MK_COMB (@lem4601524) (@lem4601523 A s)). Qed.
Lemma lem4601526 {A : Type'} (s : A -> Prop) : (term298 A s) = (term316 A s).
Proof. exact (MK_COMB (@lem4601521 A s) (@lem4601525 A s)). Qed.
Lemma lem4601527 {A : Type'} (s : A -> Prop) : ((term297 A s) = (term298 A s)) = ((term292 A s) = (term316 A s)).
Proof. exact (MK_COMB (@lem4601515 A s) (@lem4601526 A s)). Qed.
Lemma lem4601528 {A : Type'} (s : A -> Prop) : (term292 A s) = (term316 A s).
Proof. exact (EQ_MP (@lem4601527 A s) (@lem4601505 A s)). Qed.
Lemma lem4601625 {A : Type'} : (term293 A) = (term317 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601528 A s)). Qed.
Lemma lem4601626 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601627 {A : Type'} : (term294 A) = (term318 A).
Proof. exact (MK_COMB (@lem4601626 A) (@lem4601625 A)). Qed.
Lemma lem4601629 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4601630 {A : Type'} (P : type686 A) (Q : type686 A) : (term142 A P Q) = (term143 A P Q).
Proof. exact (@lem4601629 (A -> Prop) P Q). Qed.
Lemma lem4601631 {A : Type'} : (term319 A) = (term320 A).
Proof. exact (@lem4601630 A (term321 A) (term322 A)). Qed.
Lemma lem4601632 {A : Type'} (s : A -> Prop) : (term323 A s) = (term310 A s).
Proof. exact (eq_refl (term323 A s)). Qed.
Lemma lem4601633 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601634 {A : Type'} (s : A -> Prop) : (term324 A s) = (term312 A s).
Proof. exact (MK_COMB (@lem4601633) (@lem4601632 A s)). Qed.
Lemma lem4601635 {A : Type'} (s : A -> Prop) : (term325 A s) = (term315 A s).
Proof. exact (eq_refl (term325 A s)). Qed.
Lemma lem4601636 {A : Type'} (s : A -> Prop) : (term326 A s) = (term316 A s).
Proof. exact (MK_COMB (@lem4601634 A s) (@lem4601635 A s)). Qed.
Lemma lem4601637 {A : Type'} : (term327 A) = (term317 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601636 A s)). Qed.
Lemma lem4601638 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601639 {A : Type'} : (term319 A) = (term318 A).
Proof. exact (MK_COMB (@lem4601638 A) (@lem4601637 A)). Qed.
Lemma lem4601640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601641 {A : Type'} : (term328 A) = (term329 A).
Proof. exact (MK_COMB (@lem4601640) (@lem4601639 A)). Qed.
Lemma lem4601642 {A : Type'} (s : A -> Prop) : (term323 A s) = (term310 A s).
Proof. exact (eq_refl (term323 A s)). Qed.
Lemma lem4601643 {A : Type'} : (term330 A) = (term321 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601642 A s)). Qed.
Lemma lem4601644 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601645 {A : Type'} : (term331 A) = (term332 A).
Proof. exact (MK_COMB (@lem4601644 A) (@lem4601643 A)). Qed.
Lemma lem4601646 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601647 {A : Type'} : (term333 A) = (term334 A).
Proof. exact (MK_COMB (@lem4601646) (@lem4601645 A)). Qed.
Lemma lem4601648 {A : Type'} (s : A -> Prop) : (term325 A s) = (term315 A s).
Proof. exact (eq_refl (term325 A s)). Qed.
Lemma lem4601649 {A : Type'} : (term335 A) = (term322 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4601648 A s)). Qed.
Lemma lem4601650 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4601651 {A : Type'} : (term336 A) = (term337 A).
Proof. exact (MK_COMB (@lem4601650 A) (@lem4601649 A)). Qed.
Lemma lem4601652 {A : Type'} : (term320 A) = (term338 A).
Proof. exact (MK_COMB (@lem4601647 A) (@lem4601651 A)). Qed.
Lemma lem4601653 {A : Type'} : ((term319 A) = (term320 A)) = ((term318 A) = (term338 A)).
Proof. exact (MK_COMB (@lem4601641 A) (@lem4601652 A)). Qed.
Lemma lem4601654 {A : Type'} : (term318 A) = (term338 A).
Proof. exact (EQ_MP (@lem4601653 A) (@lem4601631 A)). Qed.
Lemma lem4601761 {A : Type'} : (term294 A) = (term338 A).
Proof. exact (TRANS (@lem4601627 A) (@lem4601654 A)). Qed.
Lemma lem4601762 {A : Type'} : (term5 A) = (term338 A).
Proof. exact (TRANS (@lem4601497 A) (@lem4601761 A)). Qed.
Lemma lem4601763 {A : Type'} (h1 : term5 A) : term338 A.
Proof. exact (EQ_MP (@lem4601762 A) (@lem4600988 A h1)). Qed.
Lemma lem4601774 {A : Type'} (s : type686 A) (n : nat) : (term339 A s n) = (term340 A s n).
Proof. exact (@lem17045 (@FINITE (A -> Prop) s) ((@CARD (A -> Prop) s) = n)). Qed.
Lemma lem4601780 {A : Type'} (s : type686 A) (n : nat) : (term341 A s n) = (term341 A s n).
Proof. exact (eq_refl (term341 A s n)). Qed.
Lemma lem4601782 {A : Type'} (s : type686 A) (n : nat) : (term342 A s n) = (term342 A s n).
Proof. exact (eq_refl (term342 A s n)). Qed.
Lemma lem4601783 {A : Type'} (s : type686 A) (n : nat) : (term343 A s n) = (term344 A s n).
Proof. exact (MK_COMB (@lem4601782 A s n) (@lem4601774 A s n)). Qed.
Lemma lem4601784 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601785 {A : Type'} (s : type686 A) (n : nat) : (term345 A s n) = (term346 A s n).
Proof. exact (MK_COMB (@lem4601784) (@lem4601783 A s n)). Qed.
Lemma lem4601786 {A : Type'} (s : type686 A) (n : nat) : (term347 A s n) = (term348 A s n).
Proof. exact (MK_COMB (@lem4601785 A s n) (@lem4601780 A s n)). Qed.
Lemma lem4601787 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n)) = (term347 A s n).
Proof. exact (@lem17784 (@HAS_SIZE (A -> Prop) s n) (term43 A s n)). Qed.
Lemma lem4601788 {A : Type'} (s : type686 A) (n : nat) : ((@HAS_SIZE (A -> Prop) s n) = (term43 A s n)) = (term348 A s n).
Proof. exact (TRANS (@lem4601787 A s n) (@lem4601786 A s n)). Qed.
Lemma lem4601789 {A : Type'} (s : type686 A) : (term44 A s) = (term349 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601788 A s n)). Qed.
Lemma lem4601790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601791 {A : Type'} (s : type686 A) : (term45 A s) = (term350 A s).
Proof. exact (MK_COMB (@lem4601790) (@lem4601789 A s)). Qed.
Lemma lem4601792 {A : Type'} : (term46 A) = (term351 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4601791 A s)). Qed.
Lemma lem4601793 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4601794 {A : Type'} : (term6 A) = (term352 A).
Proof. exact (MK_COMB (@lem4601793 A) (@lem4601792 A)). Qed.
Lemma lem4601800 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4601801 (P : nat -> Prop) (Q : nat -> Prop) : (term295 P Q) = (term296 P Q).
Proof. exact (@lem4601800 nat P Q). Qed.
Lemma lem4601802 {A : Type'} (s : type686 A) : (term353 A s) = (term354 A s).
Proof. exact (@lem4601801 (term355 A s) (term356 A s)). Qed.
Lemma lem4601803 {A : Type'} (s : type686 A) (n : nat) : (term357 A s n) = (term344 A s n).
Proof. exact (eq_refl (term357 A s n)). Qed.
Lemma lem4601804 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601805 {A : Type'} (s : type686 A) (n : nat) : (term358 A s n) = (term346 A s n).
Proof. exact (MK_COMB (@lem4601804) (@lem4601803 A s n)). Qed.
Lemma lem4601806 {A : Type'} (s : type686 A) (n : nat) : (term359 A s n) = (term341 A s n).
Proof. exact (eq_refl (term359 A s n)). Qed.
Lemma lem4601807 {A : Type'} (s : type686 A) (n : nat) : (term360 A s n) = (term348 A s n).
Proof. exact (MK_COMB (@lem4601805 A s n) (@lem4601806 A s n)). Qed.
Lemma lem4601808 {A : Type'} (s : type686 A) : (term361 A s) = (term349 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601807 A s n)). Qed.
Lemma lem4601809 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601810 {A : Type'} (s : type686 A) : (term353 A s) = (term350 A s).
Proof. exact (MK_COMB (@lem4601809) (@lem4601808 A s)). Qed.
Lemma lem4601811 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601812 {A : Type'} (s : type686 A) : (term362 A s) = (term363 A s).
Proof. exact (MK_COMB (@lem4601811) (@lem4601810 A s)). Qed.
Lemma lem4601813 {A : Type'} (s : type686 A) (n : nat) : (term357 A s n) = (term344 A s n).
Proof. exact (eq_refl (term357 A s n)). Qed.
Lemma lem4601814 {A : Type'} (s : type686 A) : (term364 A s) = (term355 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601813 A s n)). Qed.
Lemma lem4601815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601816 {A : Type'} (s : type686 A) : (term365 A s) = (term366 A s).
Proof. exact (MK_COMB (@lem4601815) (@lem4601814 A s)). Qed.
Lemma lem4601817 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601818 {A : Type'} (s : type686 A) : (term367 A s) = (term368 A s).
Proof. exact (MK_COMB (@lem4601817) (@lem4601816 A s)). Qed.
Lemma lem4601819 {A : Type'} (s : type686 A) (n : nat) : (term359 A s n) = (term341 A s n).
Proof. exact (eq_refl (term359 A s n)). Qed.
Lemma lem4601820 {A : Type'} (s : type686 A) : (term369 A s) = (term356 A s).
Proof. exact (fun_ext (fun n : nat => @lem4601819 A s n)). Qed.
Lemma lem4601821 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4601822 {A : Type'} (s : type686 A) : (term370 A s) = (term371 A s).
Proof. exact (MK_COMB (@lem4601821) (@lem4601820 A s)). Qed.
Lemma lem4601823 {A : Type'} (s : type686 A) : (term354 A s) = (term372 A s).
Proof. exact (MK_COMB (@lem4601818 A s) (@lem4601822 A s)). Qed.
Lemma lem4601824 {A : Type'} (s : type686 A) : ((term353 A s) = (term354 A s)) = ((term350 A s) = (term372 A s)).
Proof. exact (MK_COMB (@lem4601812 A s) (@lem4601823 A s)). Qed.
Lemma lem4601825 {A : Type'} (s : type686 A) : (term350 A s) = (term372 A s).
Proof. exact (EQ_MP (@lem4601824 A s) (@lem4601802 A s)). Qed.
Lemma lem4601922 {A : Type'} : (term351 A) = (term373 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4601825 A s)). Qed.
Lemma lem4601923 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4601924 {A : Type'} : (term352 A) = (term374 A).
Proof. exact (MK_COMB (@lem4601923 A) (@lem4601922 A)). Qed.
Lemma lem4601926 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4601927 {A : Type'} (P : type180 A) (Q : type180 A) : (term375 A P Q) = (term376 A P Q).
Proof. exact (@lem4601926 (type686 A) P Q). Qed.
Lemma lem4601928 {A : Type'} : (term377 A) = (term378 A).
Proof. exact (@lem4601927 A (term379 A) (term380 A)). Qed.
Lemma lem4601929 {A : Type'} (s : type686 A) : (term381 A s) = (term366 A s).
Proof. exact (eq_refl (term381 A s)). Qed.
Lemma lem4601930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601931 {A : Type'} (s : type686 A) : (term382 A s) = (term368 A s).
Proof. exact (MK_COMB (@lem4601930) (@lem4601929 A s)). Qed.
Lemma lem4601932 {A : Type'} (s : type686 A) : (term383 A s) = (term371 A s).
Proof. exact (eq_refl (term383 A s)). Qed.
Lemma lem4601933 {A : Type'} (s : type686 A) : (term384 A s) = (term372 A s).
Proof. exact (MK_COMB (@lem4601931 A s) (@lem4601932 A s)). Qed.
Lemma lem4601934 {A : Type'} : (term385 A) = (term373 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4601933 A s)). Qed.
Lemma lem4601935 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4601936 {A : Type'} : (term377 A) = (term374 A).
Proof. exact (MK_COMB (@lem4601935 A) (@lem4601934 A)). Qed.
Lemma lem4601937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4601938 {A : Type'} : (term386 A) = (term387 A).
Proof. exact (MK_COMB (@lem4601937) (@lem4601936 A)). Qed.
Lemma lem4601939 {A : Type'} (s : type686 A) : (term381 A s) = (term366 A s).
Proof. exact (eq_refl (term381 A s)). Qed.
Lemma lem4601940 {A : Type'} : (term388 A) = (term379 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4601939 A s)). Qed.
Lemma lem4601941 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4601942 {A : Type'} : (term389 A) = (term390 A).
Proof. exact (MK_COMB (@lem4601941 A) (@lem4601940 A)). Qed.
Lemma lem4601943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4601944 {A : Type'} : (term391 A) = (term392 A).
Proof. exact (MK_COMB (@lem4601943) (@lem4601942 A)). Qed.
Lemma lem4601945 {A : Type'} (s : type686 A) : (term383 A s) = (term371 A s).
Proof. exact (eq_refl (term383 A s)). Qed.
Lemma lem4601946 {A : Type'} : (term393 A) = (term380 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4601945 A s)). Qed.
Lemma lem4601947 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4601948 {A : Type'} : (term394 A) = (term395 A).
Proof. exact (MK_COMB (@lem4601947 A) (@lem4601946 A)). Qed.
Lemma lem4601949 {A : Type'} : (term378 A) = (term396 A).
Proof. exact (MK_COMB (@lem4601944 A) (@lem4601948 A)). Qed.
Lemma lem4601950 {A : Type'} : ((term377 A) = (term378 A)) = ((term374 A) = (term396 A)).
Proof. exact (MK_COMB (@lem4601938 A) (@lem4601949 A)). Qed.
Lemma lem4601951 {A : Type'} : (term374 A) = (term396 A).
Proof. exact (EQ_MP (@lem4601950 A) (@lem4601928 A)). Qed.
Lemma lem4602058 {A : Type'} : (term352 A) = (term396 A).
Proof. exact (TRANS (@lem4601924 A) (@lem4601951 A)). Qed.
Lemma lem4602059 {A : Type'} : (term6 A) = (term396 A).
Proof. exact (TRANS (@lem4601794 A) (@lem4602058 A)). Qed.
Lemma lem4602060 {A : Type'} (h1 : term6 A) : term396 A.
Proof. exact (EQ_MP (@lem4602059 A) (@lem4600989 A h1)). Qed.
Lemma lem4602067 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (n : nat) : (term34 A _55291 s n) = (term397 A _55291 s n).
Proof. exact (@lem17265 (@HAS_SIZE A s n) (term31 A _55291 s n)). Qed.
Lemma lem4602068 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term36 A _55291 s) = (term398 A _55291 s).
Proof. exact (fun_ext (fun n : nat => @lem4602067 A _55291 s n)). Qed.
Lemma lem4602069 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602070 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term38 A _55291 s) = (term399 A _55291 s).
Proof. exact (MK_COMB (@lem4602069) (@lem4602068 A _55291 s)). Qed.
Lemma lem4602071 {A : Type'} (_55291 : type639 A) : (term40 A _55291) = (term400 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4602070 A _55291 s)). Qed.
Lemma lem4602072 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4602129 {A : Type'} (_55291 : type639 A) : (term41 A _55291) = (term401 A _55291).
Proof. exact (MK_COMB (@lem4602072 A) (@lem4602071 A _55291)). Qed.
Lemma lem4602130 {A : Type'} (_55291 : type639 A) (h1 : term41 A _55291) : term401 A _55291.
Proof. exact (EQ_MP (@lem4602129 A _55291) (@lem4600990 A _55291 h1)). Qed.
Lemma lem4602155 {A : Type'} (s : A -> Prop) (n : nat) : (term283 A s n) = (term283 A s n).
Proof. exact (eq_refl (term283 A s n)). Qed.
Lemma lem4602156 {A : Type'} (s : A -> Prop) : (term300 A s) = (term300 A s).
Proof. exact (fun_ext (fun n : nat => @lem4602155 A s n)). Qed.
Lemma lem4602157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602158 {A : Type'} (s : A -> Prop) : (term315 A s) = (term315 A s).
Proof. exact (MK_COMB (@lem4602157) (@lem4602156 A s)). Qed.
Lemma lem4602159 {A : Type'} : (term322 A) = (term322 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4602158 A s)). Qed.
Lemma lem4602160 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4602161 {A : Type'} : (term337 A) = (term337 A).
Proof. exact (MK_COMB (@lem4602160 A) (@lem4602159 A)). Qed.
Lemma lem4602186 {A : Type'} (s : A -> Prop) (n : nat) : (term286 A s n) = (term286 A s n).
Proof. exact (eq_refl (term286 A s n)). Qed.
Lemma lem4602187 {A : Type'} (s : A -> Prop) : (term299 A s) = (term299 A s).
Proof. exact (fun_ext (fun n : nat => @lem4602186 A s n)). Qed.
Lemma lem4602188 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602189 {A : Type'} (s : A -> Prop) : (term310 A s) = (term310 A s).
Proof. exact (MK_COMB (@lem4602188) (@lem4602187 A s)). Qed.
Lemma lem4602190 {A : Type'} : (term321 A) = (term321 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4602189 A s)). Qed.
Lemma lem4602191 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4602192 {A : Type'} : (term332 A) = (term332 A).
Proof. exact (MK_COMB (@lem4602191 A) (@lem4602190 A)). Qed.
Lemma lem4602193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4602194 {A : Type'} : (term334 A) = (term334 A).
Proof. exact (MK_COMB (@lem4602193) (@lem4602192 A)). Qed.
Lemma lem4602195 {A : Type'} : (term338 A) = (term338 A).
Proof. exact (MK_COMB (@lem4602194 A) (@lem4602161 A)). Qed.
Lemma lem4602196 {A : Type'} (h1 : term5 A) : term338 A.
Proof. exact (EQ_MP (@lem4602195 A) (@lem4601763 A h1)). Qed.
Lemma lem4602219 {A : Type'} (s : type686 A) (n : nat) : (term341 A s n) = (term341 A s n).
Proof. exact (eq_refl (term341 A s n)). Qed.
Lemma lem4602220 {A : Type'} (s : type686 A) : (term356 A s) = (term356 A s).
Proof. exact (fun_ext (fun n : nat => @lem4602219 A s n)). Qed.
Lemma lem4602221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602222 {A : Type'} (s : type686 A) : (term371 A s) = (term371 A s).
Proof. exact (MK_COMB (@lem4602221) (@lem4602220 A s)). Qed.
Lemma lem4602223 {A : Type'} : (term380 A) = (term380 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4602222 A s)). Qed.
Lemma lem4602224 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4602225 {A : Type'} : (term395 A) = (term395 A).
Proof. exact (MK_COMB (@lem4602224 A) (@lem4602223 A)). Qed.
Lemma lem4602250 {A : Type'} (s : type686 A) (n : nat) : (term344 A s n) = (term344 A s n).
Proof. exact (eq_refl (term344 A s n)). Qed.
Lemma lem4602251 {A : Type'} (s : type686 A) : (term355 A s) = (term355 A s).
Proof. exact (fun_ext (fun n : nat => @lem4602250 A s n)). Qed.
Lemma lem4602252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602253 {A : Type'} (s : type686 A) : (term366 A s) = (term366 A s).
Proof. exact (MK_COMB (@lem4602252) (@lem4602251 A s)). Qed.
Lemma lem4602254 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4602253 A s)). Qed.
Lemma lem4602255 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4602256 {A : Type'} : (term390 A) = (term390 A).
Proof. exact (MK_COMB (@lem4602255 A) (@lem4602254 A)). Qed.
Lemma lem4602257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4602258 {A : Type'} : (term392 A) = (term392 A).
Proof. exact (MK_COMB (@lem4602257) (@lem4602256 A)). Qed.
Lemma lem4602259 {A : Type'} : (term396 A) = (term396 A).
Proof. exact (MK_COMB (@lem4602258 A) (@lem4602225 A)). Qed.
Lemma lem4602260 {A : Type'} (h1 : term6 A) : term396 A.
Proof. exact (EQ_MP (@lem4602259 A) (@lem4602060 A h1)). Qed.
Lemma lem4602289 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (n : nat) : (term397 A _55291 s n) = (term397 A _55291 s n).
Proof. exact (eq_refl (term397 A _55291 s n)). Qed.
Lemma lem4602290 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term398 A _55291 s) = (term398 A _55291 s).
Proof. exact (fun_ext (fun n : nat => @lem4602289 A _55291 s n)). Qed.
Lemma lem4602291 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602292 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term399 A _55291 s) = (term399 A _55291 s).
Proof. exact (MK_COMB (@lem4602291) (@lem4602290 A _55291 s)). Qed.
Lemma lem4602293 {A : Type'} (_55291 : type639 A) : (term400 A _55291) = (term400 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4602292 A _55291 s)). Qed.
Lemma lem4602294 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4602295 {A : Type'} (_55291 : type639 A) : (term401 A _55291) = (term401 A _55291).
Proof. exact (MK_COMB (@lem4602294 A) (@lem4602293 A _55291)). Qed.
Lemma lem4602296 {A : Type'} (_55291 : type639 A) (h1 : term41 A _55291) : term401 A _55291.
Proof. exact (EQ_MP (@lem4602295 A _55291) (@lem4602130 A _55291 h1)). Qed.
Lemma lem4602312 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term272 A _55291 s) : term272 A _55291 s.
Proof. exact (h1). Qed.
Lemma lem4602396 {A : Type'} (h1 : term6 A) : term395 A.
Proof. exact (proj2 (@lem4602260 A h1)). Qed.
Lemma lem4602399 {A : Type'} (h1 : term5 A) : term332 A.
Proof. exact (proj1 (@lem4602196 A h1)). Qed.
Lemma lem4602407 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (n : nat) : (term397 A _55291 s n) = (term397 A _55291 s n).
Proof. exact (eq_refl (term397 A _55291 s n)). Qed.
Lemma lem4602408 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term398 A _55291 s) = (term398 A _55291 s).
Proof. exact (fun_ext (fun n : nat => @lem4602407 A _55291 s n)). Qed.
Lemma lem4602409 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602410 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term399 A _55291 s) = (term399 A _55291 s).
Proof. exact (MK_COMB (@lem4602409) (@lem4602408 A _55291 s)). Qed.
Lemma lem4602411 {A : Type'} (_55291 : type639 A) : (term400 A _55291) = (term400 A _55291).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4602410 A _55291 s)). Qed.
Lemma lem4602412 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4602414 {A : Type'} (_55291 : type639 A) : (term401 A _55291) = (term401 A _55291).
Proof. exact (MK_COMB (@lem4602412 A) (@lem4602411 A _55291)). Qed.
Lemma lem4602415 {A : Type'} (_55291 : type639 A) (h1 : term41 A _55291) : term401 A _55291.
Proof. exact (EQ_MP (@lem4602414 A _55291) (@lem4602296 A _55291 h1)). Qed.
Lemma lem4602523 {A : Type'} (s : type686 A) (n : nat) : (term341 A s n) = (term402 A s n).
Proof. exact (@lem19490 (@FINITE (A -> Prop) s) (term403 A s n) ((@CARD (A -> Prop) s) = n)). Qed.
Lemma lem4602524 {A : Type'} (s : type686 A) : (term356 A s) = (term404 A s).
Proof. exact (fun_ext (fun n : nat => @lem4602523 A s n)). Qed.
Lemma lem4602525 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602526 {A : Type'} (s : type686 A) : (term371 A s) = (term405 A s).
Proof. exact (MK_COMB (@lem4602525) (@lem4602524 A s)). Qed.
Lemma lem4602527 {A : Type'} : (term380 A) = (term406 A).
Proof. exact (fun_ext (fun s : type686 A => @lem4602526 A s)). Qed.
Lemma lem4602528 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4602530 {A : Type'} : (term395 A) = (term407 A).
Proof. exact (MK_COMB (@lem4602528 A) (@lem4602527 A)). Qed.
Lemma lem4602531 {A : Type'} (h1 : term6 A) : term407 A.
Proof. exact (EQ_MP (@lem4602530 A) (@lem4602396 A h1)). Qed.
Lemma lem4602545 {A : Type'} (s : A -> Prop) (n : nat) : (term286 A s n) = (term286 A s n).
Proof. exact (eq_refl (term286 A s n)). Qed.
Lemma lem4602546 {A : Type'} (s : A -> Prop) : (term299 A s) = (term299 A s).
Proof. exact (fun_ext (fun n : nat => @lem4602545 A s n)). Qed.
Lemma lem4602547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4602548 {A : Type'} (s : A -> Prop) : (term310 A s) = (term310 A s).
Proof. exact (MK_COMB (@lem4602547) (@lem4602546 A s)). Qed.
Lemma lem4602549 {A : Type'} : (term321 A) = (term321 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4602548 A s)). Qed.
Lemma lem4602550 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4602552 {A : Type'} : (term332 A) = (term332 A).
Proof. exact (MK_COMB (@lem4602550 A) (@lem4602549 A)). Qed.
Lemma lem4602553 {A : Type'} (h1 : term5 A) : term332 A.
Proof. exact (EQ_MP (@lem4602552 A) (@lem4602399 A h1)). Qed.
Lemma lem4602580 {A : Type'} (_55292 : A -> Prop) (_55291 : type639 A) (h1 : term41 A _55291) : term408 A _55291 _55292.
Proof. exact (@lem4602415 A _55291 h1 _55292). Qed.
Lemma lem4602581 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) : (term408 A _55291 _55292) = (term399 A _55291 _55292).
Proof. exact (eq_refl (term408 A _55291 _55292)). Qed.
Lemma lem4602582 {A : Type'} (_55292 : A -> Prop) (_55291 : type639 A) (h1 : term41 A _55291) : term399 A _55291 _55292.
Proof. exact (EQ_MP (@lem4602581 A _55291 _55292) (@lem4602580 A _55292 _55291 h1)). Qed.
Lemma lem4602583 {A : Type'} (_55292 : A -> Prop) (_55293 : nat) (_55291 : type639 A) (h1 : term41 A _55291) : term409 A _55291 _55292 _55293.
Proof. exact (@lem4602582 A _55292 _55291 h1 _55293). Qed.
Lemma lem4602584 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term409 A _55291 _55292 _55293) = (term397 A _55291 _55292 _55293).
Proof. exact (eq_refl (term409 A _55291 _55292 _55293)). Qed.
Lemma lem4602607 {A : Type'} (_55301 : type686 A) (h1 : term6 A) : term410 A _55301.
Proof. exact (@lem4602531 A h1 _55301). Qed.
Lemma lem4602608 {A : Type'} (_55301 : type686 A) : (term410 A _55301) = (term405 A _55301).
Proof. exact (eq_refl (term410 A _55301)). Qed.
Lemma lem4602609 {A : Type'} (_55301 : type686 A) (h1 : term6 A) : term405 A _55301.
Proof. exact (EQ_MP (@lem4602608 A _55301) (@lem4602607 A _55301 h1)). Qed.
Lemma lem4602610 {A : Type'} (_55301 : type686 A) (_55302 : nat) (h1 : term6 A) : term411 A _55301 _55302.
Proof. exact (@lem4602609 A _55301 h1 _55302). Qed.
Lemma lem4602611 {A : Type'} (_55301 : type686 A) (_55302 : nat) : (term411 A _55301 _55302) = (term402 A _55301 _55302).
Proof. exact (eq_refl (term411 A _55301 _55302)). Qed.
Lemma lem4602612 {A : Type'} (_55301 : type686 A) (_55302 : nat) (h1 : term6 A) : term402 A _55301 _55302.
Proof. exact (EQ_MP (@lem4602611 A _55301 _55302) (@lem4602610 A _55301 _55302 h1)). Qed.
Lemma lem4602613 {A : Type'} (_55303 : A -> Prop) (h1 : term5 A) : term323 A _55303.
Proof. exact (@lem4602553 A h1 _55303). Qed.
Lemma lem4602614 {A : Type'} (_55303 : A -> Prop) : (term323 A _55303) = (term310 A _55303).
Proof. exact (eq_refl (term323 A _55303)). Qed.
Lemma lem4602615 {A : Type'} (_55303 : A -> Prop) (h1 : term5 A) : term310 A _55303.
Proof. exact (EQ_MP (@lem4602614 A _55303) (@lem4602613 A _55303 h1)). Qed.
Lemma lem4602616 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) (h1 : term5 A) : term301 A _55303 _55304.
Proof. exact (@lem4602615 A _55303 h1 _55304). Qed.
Lemma lem4602617 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term301 A _55303 _55304) = (term286 A _55303 _55304).
Proof. exact (eq_refl (term301 A _55303 _55304)). Qed.
Lemma lem4602634 {A : Type'} (_55292 : A -> Prop) (_55293 : nat) (_55291 : type639 A) (h1 : term41 A _55291) : term397 A _55291 _55292 _55293.
Proof. exact (EQ_MP (@lem4602584 A _55291 _55292 _55293) (@lem4602583 A _55292 _55293 _55291 h1)). Qed.
Lemma lem4602650 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term272 A _55291 s) : term412 A _55291 s.
Proof. exact (proj2 (@lem4602312 A _55291 s h1)). Qed.
Lemma lem4602670 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) (h1 : term5 A) : term286 A _55303 _55304.
Proof. exact (EQ_MP (@lem4602617 A _55303 _55304) (@lem4602616 A _55303 _55304 h1)). Qed.
Lemma lem4602688 {A : Type'} (_55302 : nat) (_55301 : type686 A) (h1 : term6 A) : term413 A _55302 _55301.
Proof. exact (proj1 (@lem4602612 A _55301 _55302 h1)). Qed.
Lemma lem4602910 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term272 A _55291 s) : @FINITE A s.
Proof. exact (proj1 (@lem4602312 A _55291 s h1)). Qed.
Lemma lem4602911 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term272 A _55291 s) : term414 A s.
Proof. exact (fun h0 : term415 A s => @lem4602910 A _55291 s h1). Qed.
Lemma lem4602913 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4602914 {A : Type'} (s : A -> Prop) : (term414 A s) = (@FINITE A s).
Proof. exact (@lem4602913 (@FINITE A s)). Qed.
Lemma lem4602915 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term272 A _55291 s) : @FINITE A s.
Proof. exact (EQ_MP (@lem4602914 A s) (@lem4602911 A _55291 s h1)). Qed.
Lemma lem4602917 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem4602918 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (@lem4602917 (@CARD A s)). Qed.
Lemma lem4602919 {A : Type'} (s : A -> Prop) : term417 A s.
Proof. exact (fun h0 : term418 A s => @lem4602918 A s). Qed.
Lemma lem4602921 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4602922 {A : Type'} (s : A -> Prop) : (term417 A s) = ((@CARD A s) = (@CARD A s)).
Proof. exact (@lem4602921 ((@CARD A s) = (@CARD A s))). Qed.
Lemma lem4602923 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (EQ_MP (@lem4602922 A s) (@lem4602919 A s)). Qed.
Lemma lem4602925 (b : Prop) (a : Prop) : (a \/ b) = (term419 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4602926 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term286 A _55303 _55304) = (term420 A _55303 _55304).
Proof. exact (@lem4602925 (term282 A _55303 _55304) (@HAS_SIZE A _55303 _55304)). Qed.
Lemma lem4602928 (a : Prop) (b : Prop) : (term421 a b) = (term422 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4602929 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term423 A _55303 _55304) = (term424 A _55303 _55304).
Proof. exact (@lem4602928 (term415 A _55303) (term425 A _55303 _55304)). Qed.
Lemma lem4602931 (a : Prop) : (term426 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4602932 {A : Type'} (_55303 : A -> Prop) : (term427 A _55303) = (@FINITE A _55303).
Proof. exact (@lem4602931 (@FINITE A _55303)). Qed.
Lemma lem4602933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4602934 {A : Type'} (_55303 : A -> Prop) : (term428 A _55303) = (term429 A _55303).
Proof. exact (MK_COMB (@lem4602933) (@lem4602932 A _55303)). Qed.
Lemma lem4602936 (a : Prop) : (term426 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4602937 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term430 A _55303 _55304) = ((@CARD A _55303) = _55304).
Proof. exact (@lem4602936 ((@CARD A _55303) = _55304)). Qed.
Lemma lem4602938 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term424 A _55303 _55304) = (term48 A _55303 _55304).
Proof. exact (MK_COMB (@lem4602934 A _55303) (@lem4602937 A _55303 _55304)). Qed.
Lemma lem4602939 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term423 A _55303 _55304) = (term48 A _55303 _55304).
Proof. exact (TRANS (@lem4602929 A _55303 _55304) (@lem4602938 A _55303 _55304)). Qed.
Lemma lem4602940 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4602941 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term431 A _55303 _55304) = (term432 A _55303 _55304).
Proof. exact (MK_COMB (@lem4602940) (@lem4602939 A _55303 _55304)). Qed.
Lemma lem4602942 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (@HAS_SIZE A _55303 _55304) = (@HAS_SIZE A _55303 _55304).
Proof. exact (eq_refl (@HAS_SIZE A _55303 _55304)). Qed.
Lemma lem4602943 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term420 A _55303 _55304) = (term433 A _55303 _55304).
Proof. exact (MK_COMB (@lem4602941 A _55303 _55304) (@lem4602942 A _55303 _55304)). Qed.
Lemma lem4602944 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) : (term286 A _55303 _55304) = (term433 A _55303 _55304).
Proof. exact (TRANS (@lem4602926 A _55303 _55304) (@lem4602943 A _55303 _55304)). Qed.
Lemma lem4602946 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term272 A _55291 s) : term434 A s.
Proof. exact (conj (@lem4602915 A _55291 s h1) (@lem4602923 A s)). Qed.
Lemma lem4602948 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) (h1 : term5 A) : term433 A _55303 _55304.
Proof. exact (EQ_MP (@lem4602944 A _55303 _55304) (@lem4602670 A _55303 _55304 h1)). Qed.
Lemma lem4602949 {A : Type'} (_55303 : A -> Prop) (_55304 : nat) (h1 : term5 A) : term433 A _55303 _55304.
Proof. exact (@lem4602948 A _55303 _55304 h1). Qed.
Lemma lem4602950 {A : Type'} (s : A -> Prop) (h1 : term5 A) : term435 A s.
Proof. exact (@lem4602949 A s (@CARD A s) h1). Qed.
Lemma lem4602953 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term272 A _55291 s) : term436 A s.
Proof. exact (@lem4602950 A s h1 (@lem4602946 A _55291 s h2)). Qed.
Lemma lem4602954 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term272 A _55291 s) : term437 A s.
Proof. exact (fun h0 : term438 A s => @lem4602953 A _55291 s h1 h2). Qed.
Lemma lem4602956 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4602957 {A : Type'} (s : A -> Prop) : (term437 A s) = (term436 A s).
Proof. exact (@lem4602956 (term436 A s)). Qed.
Lemma lem4602958 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term272 A _55291 s) : term436 A s.
Proof. exact (EQ_MP (@lem4602957 A s) (@lem4602954 A _55291 s h1 h2)). Qed.
Lemma lem4602964 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4602965 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term397 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293).
Proof. exact (@lem4602964 (term31 A _55291 _55292 _55293) (term440 A _55292 _55293)). Qed.
Lemma lem4602971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4602972 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term441 A _55291 _55292 _55293) = (term442 A _55291 _55292 _55293).
Proof. exact (MK_COMB (@lem4602971) (@lem4602965 A _55291 _55292 _55293)). Qed.
Lemma lem4602978 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term439 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293).
Proof. exact (eq_refl (term439 A _55291 _55292 _55293)). Qed.
Lemma lem4602979 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : ((term397 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293)) = ((term439 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293)).
Proof. exact (MK_COMB (@lem4602972 A _55291 _55292 _55293) (@lem4602978 A _55291 _55292 _55293)). Qed.
Lemma lem4602981 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4602982 (x : Prop) : (x = x) = True.
Proof. exact (@lem4602981 Prop x). Qed.
Lemma lem4602983 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : ((term439 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293)) = True.
Proof. exact (@lem4602982 (term439 A _55291 _55292 _55293)). Qed.
Lemma lem4602984 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : ((term397 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293)) = True.
Proof. exact (TRANS (@lem4602979 A _55291 _55292 _55293) (@lem4602983 A _55291 _55292 _55293)). Qed.
Lemma lem4602985 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : True = ((term397 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293)).
Proof. exact (SYM (@lem4602984 A _55291 _55292 _55293)). Qed.
Lemma lem4602986 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term397 A _55291 _55292 _55293) = (term439 A _55291 _55292 _55293).
Proof. exact (EQ_MP (@lem4602985 A _55291 _55292 _55293) (@lem0)). Qed.
Lemma lem4602987 {A : Type'} (_55292 : A -> Prop) (_55293 : nat) (_55291 : type639 A) (h1 : term41 A _55291) : term439 A _55291 _55292 _55293.
Proof. exact (EQ_MP (@lem4602986 A _55291 _55292 _55293) (@lem4602634 A _55292 _55293 _55291 h1)). Qed.
Lemma lem4602989 (b : Prop) (a : Prop) : (a \/ b) = (term419 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4602990 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term439 A _55291 _55292 _55293) = (term443 A _55291 _55292 _55293).
Proof. exact (@lem4602989 (term440 A _55292 _55293) (term31 A _55291 _55292 _55293)). Qed.
Lemma lem4602992 (a : Prop) : (term426 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4602993 {A : Type'} (_55292 : A -> Prop) (_55293 : nat) : (term444 A _55292 _55293) = (@HAS_SIZE A _55292 _55293).
Proof. exact (@lem4602992 (@HAS_SIZE A _55292 _55293)). Qed.
Lemma lem4602994 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4602995 {A : Type'} (_55292 : A -> Prop) (_55293 : nat) : (term445 A _55292 _55293) = (term32 A _55292 _55293).
Proof. exact (MK_COMB (@lem4602994) (@lem4602993 A _55292 _55293)). Qed.
Lemma lem4602996 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term31 A _55291 _55292 _55293) = (term31 A _55291 _55292 _55293).
Proof. exact (eq_refl (term31 A _55291 _55292 _55293)). Qed.
Lemma lem4602997 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term443 A _55291 _55292 _55293) = (term34 A _55291 _55292 _55293).
Proof. exact (MK_COMB (@lem4602995 A _55292 _55293) (@lem4602996 A _55291 _55292 _55293)). Qed.
Lemma lem4602998 {A : Type'} (_55291 : type639 A) (_55292 : A -> Prop) (_55293 : nat) : (term439 A _55291 _55292 _55293) = (term34 A _55291 _55292 _55293).
Proof. exact (TRANS (@lem4602990 A _55291 _55292 _55293) (@lem4602997 A _55291 _55292 _55293)). Qed.
Lemma lem4603001 {A : Type'} (_55292 : A -> Prop) (_55293 : nat) (_55291 : type639 A) (h1 : term41 A _55291) : term34 A _55291 _55292 _55293.
Proof. exact (EQ_MP (@lem4602998 A _55291 _55292 _55293) (@lem4602987 A _55292 _55293 _55291 h1)). Qed.
Lemma lem4603002 {A : Type'} (_55292 : A -> Prop) (_55293 : nat) (_55291 : type639 A) (h1 : term41 A _55291) : term34 A _55291 _55292 _55293.
Proof. exact (@lem4603001 A _55292 _55293 _55291 h1). Qed.
Lemma lem4603003 {A : Type'} (s : A -> Prop) (_55291 : type639 A) (h1 : term41 A _55291) : term446 A _55291 s.
Proof. exact (@lem4603002 A s (@CARD A s) _55291 h1). Qed.
Lemma lem4603006 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term272 A _55291 s) : term447 A _55291 s.
Proof. exact (@lem4603003 A s _55291 h2 (@lem4602958 A _55291 s h1 h3)). Qed.
Lemma lem4603007 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term272 A _55291 s) : term448 A _55291 s.
Proof. exact (fun h0 : term449 A _55291 s => @lem4603006 A _55291 s h1 h2 h3). Qed.
Lemma lem4603009 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4603010 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term448 A _55291 s) = (term447 A _55291 s).
Proof. exact (@lem4603009 (term447 A _55291 s)). Qed.
Lemma lem4603011 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term272 A _55291 s) : term447 A _55291 s.
Proof. exact (EQ_MP (@lem4603010 A _55291 s) (@lem4603007 A _55291 s h1 h2 h3)). Qed.
Lemma lem4603017 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4603018 {A : Type'} (_55301 : type686 A) (_55302 : nat) : (term413 A _55302 _55301) = (term450 A _55301 _55302).
Proof. exact (@lem4603017 (@FINITE (A -> Prop) _55301) (term403 A _55301 _55302)). Qed.
Lemma lem4603024 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4603025 {A : Type'} (_55301 : type686 A) (_55302 : nat) : (term451 A _55302 _55301) = (term452 A _55301 _55302).
Proof. exact (MK_COMB (@lem4603024) (@lem4603018 A _55301 _55302)). Qed.
Lemma lem4603031 {A : Type'} (_55301 : type686 A) (_55302 : nat) : (term450 A _55301 _55302) = (term450 A _55301 _55302).
Proof. exact (eq_refl (term450 A _55301 _55302)). Qed.
Lemma lem4603032 {A : Type'} (_55301 : type686 A) (_55302 : nat) : ((term413 A _55302 _55301) = (term450 A _55301 _55302)) = ((term450 A _55301 _55302) = (term450 A _55301 _55302)).
Proof. exact (MK_COMB (@lem4603025 A _55301 _55302) (@lem4603031 A _55301 _55302)). Qed.
Lemma lem4603034 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4603035 (x : Prop) : (x = x) = True.
Proof. exact (@lem4603034 Prop x). Qed.
Lemma lem4603036 {A : Type'} (_55301 : type686 A) (_55302 : nat) : ((term450 A _55301 _55302) = (term450 A _55301 _55302)) = True.
Proof. exact (@lem4603035 (term450 A _55301 _55302)). Qed.
Lemma lem4603037 {A : Type'} (_55301 : type686 A) (_55302 : nat) : ((term413 A _55302 _55301) = (term450 A _55301 _55302)) = True.
Proof. exact (TRANS (@lem4603032 A _55301 _55302) (@lem4603036 A _55301 _55302)). Qed.
Lemma lem4603038 {A : Type'} (_55301 : type686 A) (_55302 : nat) : True = ((term413 A _55302 _55301) = (term450 A _55301 _55302)).
Proof. exact (SYM (@lem4603037 A _55301 _55302)). Qed.
Lemma lem4603039 {A : Type'} (_55301 : type686 A) (_55302 : nat) : (term413 A _55302 _55301) = (term450 A _55301 _55302).
Proof. exact (EQ_MP (@lem4603038 A _55301 _55302) (@lem0)). Qed.
Lemma lem4603040 {A : Type'} (_55301 : type686 A) (_55302 : nat) (h1 : term6 A) : term450 A _55301 _55302.
Proof. exact (EQ_MP (@lem4603039 A _55301 _55302) (@lem4602688 A _55302 _55301 h1)). Qed.
Lemma lem4603042 (b : Prop) (a : Prop) : (a \/ b) = (term419 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4603043 {A : Type'} (_55302 : nat) (_55301 : type686 A) : (term450 A _55301 _55302) = (term453 A _55302 _55301).
Proof. exact (@lem4603042 (term403 A _55301 _55302) (@FINITE (A -> Prop) _55301)). Qed.
Lemma lem4603045 (a : Prop) : (term426 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4603046 {A : Type'} (_55301 : type686 A) (_55302 : nat) : (term454 A _55301 _55302) = (@HAS_SIZE (A -> Prop) _55301 _55302).
Proof. exact (@lem4603045 (@HAS_SIZE (A -> Prop) _55301 _55302)). Qed.
Lemma lem4603047 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4603048 {A : Type'} (_55301 : type686 A) (_55302 : nat) : (term455 A _55301 _55302) = (term456 A _55301 _55302).
Proof. exact (MK_COMB (@lem4603047) (@lem4603046 A _55301 _55302)). Qed.
Lemma lem4603049 {A : Type'} (_55301 : type686 A) : (@FINITE (A -> Prop) _55301) = (@FINITE (A -> Prop) _55301).
Proof. exact (eq_refl (@FINITE (A -> Prop) _55301)). Qed.
Lemma lem4603050 {A : Type'} (_55302 : nat) (_55301 : type686 A) : (term453 A _55302 _55301) = (term457 A _55302 _55301).
Proof. exact (MK_COMB (@lem4603048 A _55301 _55302) (@lem4603049 A _55301)). Qed.
Lemma lem4603051 {A : Type'} (_55302 : nat) (_55301 : type686 A) : (term450 A _55301 _55302) = (term457 A _55302 _55301).
Proof. exact (TRANS (@lem4603043 A _55302 _55301) (@lem4603050 A _55302 _55301)). Qed.
Lemma lem4603054 {A : Type'} (_55302 : nat) (_55301 : type686 A) (h1 : term6 A) : term457 A _55302 _55301.
Proof. exact (EQ_MP (@lem4603051 A _55302 _55301) (@lem4603040 A _55301 _55302 h1)). Qed.
Lemma lem4603055 {A : Type'} (_55302 : nat) (_55301 : type686 A) (h1 : term6 A) : term457 A _55302 _55301.
Proof. exact (@lem4603054 A _55302 _55301 h1). Qed.
Lemma lem4603056 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term6 A) : term458 A _55291 s.
Proof. exact (@lem4603055 A (term459 A s) (term27 A _55291 s) h1). Qed.
Lemma lem4603059 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : term54 A _55291 s.
Proof. exact (@lem4603056 A _55291 s h3 (@lem4603011 A _55291 s h1 h2 h4)). Qed.
Lemma lem4603060 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : term460 A _55291 s.
Proof. exact (fun h0 : term412 A _55291 s => @lem4603059 A _55291 s h1 h2 h3 h4). Qed.
Lemma lem4603062 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4603063 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term460 A _55291 s) = (term54 A _55291 s).
Proof. exact (@lem4603062 (term54 A _55291 s)). Qed.
Lemma lem4603064 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : term54 A _55291 s.
Proof. exact (EQ_MP (@lem4603063 A _55291 s) (@lem4603060 A _55291 s h1 h2 h3 h4)). Qed.
Lemma lem4603067 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4603069 {A : Type'} (_55291 : type639 A) (s : A -> Prop) : (term412 A _55291 s) = (term461 A _55291 s).
Proof. exact (@lem4603067 (term54 A _55291 s)). Qed.
Lemma lem4603072 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term272 A _55291 s) : term461 A _55291 s.
Proof. exact (EQ_MP (@lem4603069 A _55291 s) (@lem4602650 A _55291 s h1)). Qed.
Lemma lem4603075 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : False.
Proof. exact (@lem4603072 A _55291 s h4 (@lem4603064 A _55291 s h1 h2 h3 h4)). Qed.
Lemma lem4603076 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : term462.
Proof. exact (fun h0 : ~ False => @lem4603075 A _55291 s h1 h2 h3 h4). Qed.
Lemma lem4603078 (p : Prop) : (term416 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4603079 : term462 = False.
Proof. exact (@lem4603078 False). Qed.
Lemma lem4603080 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : False.
Proof. exact (EQ_MP (@lem4603079) (@lem4603076 A _55291 s h1 h2 h3 h4)). Qed.
Lemma lem4603081 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : (term272 A _55291 s) = False.
Proof. exact (prop_ext (fun h5 : term272 A _55291 s => @lem4603080 A _55291 s h1 h2 h3 h4) (fun h5 : False => @lem4602312 A _55291 s h4)). Qed.
Lemma lem4603082 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term5 A) (h2 : term41 A _55291) (h3 : term6 A) (h4 : term272 A _55291 s) : False.
Proof. exact (EQ_MP (@lem4603081 A _55291 s h1 h2 h3 h4) (@lem4602312 A _55291 s h4)). Qed.
Lemma lem4603083 {A : Type'} (_55291 : type639 A) (s : A -> Prop) (h1 : term110 A _55291) (h2 : term5 A) (h3 : term41 A _55291) (h4 : term6 A) (h5 : term272 A _55291 s) : False.
Proof. exact (ex_elim (@lem4601416 A _55291 h1) (fun t : type636 A => fun h0 : term269 A _55291 t => @lem4603082 A _55291 s h2 h3 h4 h5)). Qed.
Lemma lem4603084 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) (h2 : term5 A) (h3 : term41 A _55291) (h4 : term6 A) (h5 : term61 A _55291) : False.
Proof. exact (ex_elim (@lem4601466 A _55291 h5) (fun s : A -> Prop => fun h0 : term279 A _55291 s => @lem4603083 A _55291 s h1 h2 h3 h4 h0)). Qed.
Lemma lem4603085 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) (h2 : term5 A) (h3 : term6 A) (h4 : term61 A _55291) : term463 A _55291.
Proof. exact (fun h0 : term41 A _55291 => @lem4603084 A _55291 h1 h2 h0 h3 h4). Qed.
Lemma lem4603086 {A : Type'} (_55291 : type639 A) : (term463 A _55291) = (term42 A _55291).
Proof. exact (@lem69 (term41 A _55291)). Qed.
Lemma lem4603087 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) (h2 : term5 A) (h3 : term6 A) (h4 : term61 A _55291) : term42 A _55291.
Proof. exact (EQ_MP (@lem4603086 A _55291) (@lem4603085 A _55291 h1 h2 h3 h4)). Qed.
Lemma lem4603088 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) (h2 : term5 A) (h3 : term61 A _55291) : term47 A _55291.
Proof. exact (fun h0 : term6 A => @lem4603087 A _55291 h1 h2 h0 h3). Qed.
Lemma lem4603089 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) (h2 : term61 A _55291) : term52 A _55291.
Proof. exact (fun h0 : term5 A => @lem4603088 A _55291 h1 h0 h2). Qed.
Lemma lem4603090 {A : Type'} (_55291 : type639 A) (h1 : term110 A _55291) : term63 A _55291.
Proof. exact (fun h0 : term61 A _55291 => @lem4603089 A _55291 h1 h0). Qed.
Lemma lem4603091 {A : Type'} (_55291 : type639 A) : term112 A _55291.
Proof. exact (fun h0 : term110 A _55291 => @lem4603090 A _55291 h0). Qed.
Lemma lem4603096 {A : Type'} : term114 A.
Proof. exact (fun _55291 : type639 A => @lem4603091 A _55291). Qed.
Lemma lem4603097 {A : Type'} : term7 A.
Proof. exact (EQ_MP (@lem4600985 A) (@lem4603096 A)). Qed.
Lemma lem4603099 {A : Type'} : term7 A.
Proof. exact (@lem4600541 A (@lem4603097 A)). Qed.
Lemma lem4603100 {A : Type'} (h1 : term3 A) : term17 A.
Proof. exact (@lem4603099 A (@lem4600517 A h1)). Qed.
Lemma lem4603101 {A : Type'} (h1 : term3 A) : term14 A.
Proof. exact (@lem4603100 A h1 (@lem4600522 A)). Qed.
Lemma lem4603102 {A : Type'} (h1 : term3 A) : term11 A.
Proof. exact (@lem4603101 A h1 (@lem4600523 A)). Qed.
Lemma lem4603103 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem4603102 A h1 (@lem4600518 A)). Qed.
Lemma lem4603104 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem4603103 A h1) (fun h2 : False => @lem4600517 A h1)). Qed.
Lemma lem4603105 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem4603104 A h1) (@lem4600517 A h1)). Qed.
Lemma lem4603106 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem4603105 A h0). Qed.
Lemma lem4603107 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem4600516 A) (@lem4603106 A)). Qed.
