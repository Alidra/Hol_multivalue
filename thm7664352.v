Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm7664352_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FSTCART_PASTECART_spec.
Require Import PASTECART_FST_SND_spec.
Require Import SNDCART_PASTECART_spec.
Require Import thm0_spec.
Require Import thm16474_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem7662555 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term0 _140476 _140477 _140478 P.
Proof. exact (h1). Qed.
Lemma lem7662556 {_140476 _140477 _140478 : Type'} : term1 _140476 _140477 _140478.
Proof. exact (@lem7659572 _140478 _140477 _140476). Qed.
Lemma lem7662557 {_140476 _140477 _140478 N : Type'} : term2 _140476 _140477 _140478 N.
Proof. exact (@lem7643282 _140476 (finite_sum _140477 _140478) N). Qed.
Lemma lem7662558 {_140476 _140477 _140478 : Type'} : term3 _140476 _140477 _140478.
Proof. exact (@lem7643282 _140476 _140477 _140478). Qed.
Lemma lem7662560 {_140476 _140477 _140478 M : Type'} : term4 _140476 _140477 _140478 M.
Proof. exact (@lem7648197 _140476 M (finite_sum _140477 _140478)). Qed.
Lemma lem7662561 {_140476 _140477 M : Type'} : term5 _140476 _140477 M.
Proof. exact (@lem7648197 _140476 M _140477). Qed.
Lemma lem7662562 {_140476 _140477 _140478 : Type'} : term6 _140476 _140477 _140478.
Proof. exact (@lem7648197 _140476 _140477 _140478). Qed.
Lemma lem7662564 {_140476 _140477 _140478 N : Type'} : term7 _140476 _140477 _140478 N.
Proof. exact (@lem7648197 _140476 (finite_sum _140477 _140478) N). Qed.
Lemma lem7662567 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term8 _140476 _140477 _140478 M N P) : term8 _140476 _140477 _140478 M N P.
Proof. exact (h1). Qed.
Lemma lem7662568 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term9 _140476 _140477 _140478 M N P.
Proof. exact (fun h0 : term8 _140476 _140477 _140478 M N P => @lem7662567 _140476 _140477 _140478 M N P h0). Qed.
Lemma lem7662569 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term9 _140476 _140477 _140478 M N P) : term9 _140476 _140477 _140478 M N P.
Proof. exact (h1). Qed.
Lemma lem7662570 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term8 _140476 _140477 _140478 M N P) : term8 _140476 _140477 _140478 M N P.
Proof. exact (h1). Qed.
Lemma lem7662571 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term8 _140476 _140477 _140478 M N P) (h2 : term9 _140476 _140477 _140478 M N P) : term8 _140476 _140477 _140478 M N P.
Proof. exact (@lem7662569 _140476 _140477 _140478 M N P h2 (@lem7662570 _140476 _140477 _140478 M N P h1)). Qed.
Lemma lem7662572 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term8 _140476 _140477 _140478 M N P) : term10 _140476 _140477 _140478 M N P.
Proof. exact (fun h0 : term9 _140476 _140477 _140478 M N P => @lem7662571 _140476 _140477 _140478 M N P h1 h0). Qed.
Lemma lem7662573 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term9 _140476 _140477 _140478 M N P) : term9 _140476 _140477 _140478 M N P.
Proof. exact (h1). Qed.
Lemma lem7662574 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term8 _140476 _140477 _140478 M N P) (h2 : term9 _140476 _140477 _140478 M N P) : term8 _140476 _140477 _140478 M N P.
Proof. exact (@lem7662572 _140476 _140477 _140478 M N P h1 (@lem7662573 _140476 _140477 _140478 M N P h2)). Qed.
Lemma lem7662575 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term9 _140476 _140477 _140478 M N P) : term9 _140476 _140477 _140478 M N P.
Proof. exact (fun h0 : term8 _140476 _140477 _140478 M N P => @lem7662574 _140476 _140477 _140478 M N P h0 h1). Qed.
Lemma lem7662576 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term11 _140476 _140477 _140478 M N P.
Proof. exact (fun h0 : term9 _140476 _140477 _140478 M N P => @lem7662575 _140476 _140477 _140478 M N P h0). Qed.
Lemma lem7662579 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term9 _140476 _140477 _140478 M N P.
Proof. exact (@lem7662576 _140476 _140477 _140478 M N P (@lem7662568 _140476 _140477 _140478 M N P)). Qed.
Lemma lem7662580 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term9 _140476 _140477 _140478 M N P.
Proof. exact (@lem7662579 _140476 _140477 _140478 M N P). Qed.
Lemma lem7662660 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7662661 {_140476 _140477 _140478 : Type'} : (term12 _140476 _140477 _140478) = (term13 _140476 _140477 _140478).
Proof. exact (@lem7662660 (term1 _140476 _140477 _140478)). Qed.
Lemma lem7662666 {_140476 _140477 _140478 N : Type'} : (term14 _140476 _140477 _140478 N) = (term14 _140476 _140477 _140478 N).
Proof. exact (eq_refl (term14 _140476 _140477 _140478 N)). Qed.
Lemma lem7662667 {_140476 _140477 _140478 N : Type'} : (term15 _140476 _140477 _140478 N) = (term16 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662666 _140476 _140477 _140478 N) (@lem7662661 _140476 _140477 _140478)). Qed.
Lemma lem7662670 {_140476 _140477 _140478 : Type'} : (term17 _140476 _140477 _140478) = (term17 _140476 _140477 _140478).
Proof. exact (eq_refl (term17 _140476 _140477 _140478)). Qed.
Lemma lem7662671 {_140476 _140477 _140478 N : Type'} : (term18 _140476 _140477 _140478 N) = (term19 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662670 _140476 _140477 _140478) (@lem7662667 _140476 _140477 _140478 N)). Qed.
Lemma lem7662674 {_140476 _140477 _140478 N : Type'} : (term20 _140476 _140477 _140478 N) = (term20 _140476 _140477 _140478 N).
Proof. exact (eq_refl (term20 _140476 _140477 _140478 N)). Qed.
Lemma lem7662675 {_140476 _140477 _140478 N : Type'} : (term21 _140476 _140477 _140478 N) = (term22 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662674 _140476 _140477 _140478 N) (@lem7662671 _140476 _140477 _140478 N)). Qed.
Lemma lem7662678 {_140476 _140477 _140478 M : Type'} : (term23 _140476 _140477 _140478 M) = (term23 _140476 _140477 _140478 M).
Proof. exact (eq_refl (term23 _140476 _140477 _140478 M)). Qed.
Lemma lem7662679 {_140476 _140477 _140478 M N : Type'} : (term24 _140476 _140477 _140478 M N) = (term25 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662678 _140476 _140477 _140478 M) (@lem7662675 _140476 _140477 _140478 N)). Qed.
Lemma lem7662682 {_140476 _140477 M : Type'} : (term26 _140476 _140477 M) = (term26 _140476 _140477 M).
Proof. exact (eq_refl (term26 _140476 _140477 M)). Qed.
Lemma lem7662683 {_140476 _140477 _140478 M N : Type'} : (term27 _140476 _140477 _140478 M N) = (term28 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662682 _140476 _140477 M) (@lem7662679 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662686 {_140476 _140477 _140478 : Type'} : (term29 _140476 _140477 _140478) = (term29 _140476 _140477 _140478).
Proof. exact (eq_refl (term29 _140476 _140477 _140478)). Qed.
Lemma lem7662687 {_140476 _140477 _140478 M N : Type'} : (term30 _140476 _140477 _140478 M N) = (term31 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662686 _140476 _140477 _140478) (@lem7662683 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662690 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term32 _140476 _140477 _140478 P) = (term32 _140476 _140477 _140478 P).
Proof. exact (eq_refl (term32 _140476 _140477 _140478 P)). Qed.
Lemma lem7662691 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : (term8 _140476 _140477 _140478 M N P) = (term33 _140476 _140477 _140478 M N P).
Proof. exact (MK_COMB (@lem7662690 _140476 _140477 _140478 P) (@lem7662687 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662694 {_140476 _140477 _140478 M N : Type'} : (term34 _140476 _140477 _140478 M N) = (term35 _140476 _140477 _140478 M N).
Proof. exact (fun_ext (fun P : type16 _140476 _140477 _140478 => @lem7662691 _140476 _140477 _140478 M N P)). Qed.
Lemma lem7662695 {_140476 _140477 _140478 : Type'} : (@all ((cart _140476 (finite_sum _140477 _140478)) -> Prop)) = (@all ((cart _140476 (finite_sum _140477 _140478)) -> Prop)).
Proof. exact (eq_refl (@all ((cart _140476 (finite_sum _140477 _140478)) -> Prop))). Qed.
Lemma lem7662704 {_140476 _140477 _140478 M N : Type'} : (term36 _140476 _140477 _140478 M N) = (term37 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662695 _140476 _140477 _140478) (@lem7662694 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662705 {_140476 _140477 _140478 : Type'} (z : type2 _140476 _140477 _140478) : ((term38 _140476 _140477 _140478 z) = z) = ((term38 _140476 _140477 _140478 z) = z).
Proof. exact (eq_refl ((term38 _140476 _140477 _140478 z) = z)). Qed.
Lemma lem7662706 {_140476 _140477 _140478 : Type'} : (term39 _140476 _140477 _140478) = (term39 _140476 _140477 _140478).
Proof. exact (fun_ext (fun z : type2 _140476 _140477 _140478 => @lem7662705 _140476 _140477 _140478 z)). Qed.
Lemma lem7662707 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7662708 {_140476 _140477 _140478 : Type'} : (term1 _140476 _140477 _140478) = (term1 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7662707 _140476 _140477 _140478) (@lem7662706 _140476 _140477 _140478)). Qed.
Lemma lem7662709 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7662710 {_140476 _140477 _140478 : Type'} : (term13 _140476 _140477 _140478) = (term13 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7662709) (@lem7662708 _140476 _140477 _140478)). Qed.
Lemma lem7662711 {_140476 _140477 _140478 N : Type'} (y : cart _140476 N) (x : type2 _140476 _140477 _140478) : ((term40 _140476 _140477 _140478 N x y) = x) = ((term40 _140476 _140477 _140478 N x y) = x).
Proof. exact (eq_refl ((term40 _140476 _140477 _140478 N x y) = x)). Qed.
Lemma lem7662712 {_140476 _140477 _140478 N : Type'} (x : type2 _140476 _140477 _140478) : (term41 _140476 _140477 _140478 N x) = (term41 _140476 _140477 _140478 N x).
Proof. exact (fun_ext (fun y : cart _140476 N => @lem7662711 _140476 _140477 _140478 N y x)). Qed.
Lemma lem7662713 {_140476 N : Type'} : (@all (cart _140476 N)) = (@all (cart _140476 N)).
Proof. exact (eq_refl (@all (cart _140476 N))). Qed.
Lemma lem7662714 {_140476 _140477 _140478 N : Type'} (x : type2 _140476 _140477 _140478) : (term42 _140476 _140477 _140478 N x) = (term42 _140476 _140477 _140478 N x).
Proof. exact (MK_COMB (@lem7662713 _140476 N) (@lem7662712 _140476 _140477 _140478 N x)). Qed.
Lemma lem7662715 {_140476 _140477 _140478 N : Type'} : (term43 _140476 _140477 _140478 N) = (term43 _140476 _140477 _140478 N).
Proof. exact (fun_ext (fun x : type2 _140476 _140477 _140478 => @lem7662714 _140476 _140477 _140478 N x)). Qed.
Lemma lem7662716 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7662717 {_140476 _140477 _140478 N : Type'} : (term2 _140476 _140477 _140478 N) = (term2 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662716 _140476 _140477 _140478) (@lem7662715 _140476 _140477 _140478 N)). Qed.
Lemma lem7662718 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662719 {_140476 _140477 _140478 N : Type'} : (term14 _140476 _140477 _140478 N) = (term14 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662718) (@lem7662717 _140476 _140477 _140478 N)). Qed.
Lemma lem7662720 {_140476 _140477 _140478 N : Type'} : (term16 _140476 _140477 _140478 N) = (term16 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662719 _140476 _140477 _140478 N) (@lem7662710 _140476 _140477 _140478)). Qed.
Lemma lem7662721 {_140476 _140477 _140478 : Type'} (y : cart _140476 _140478) (x : cart _140476 _140477) : ((term44 _140476 _140477 _140478 x y) = x) = ((term44 _140476 _140477 _140478 x y) = x).
Proof. exact (eq_refl ((term44 _140476 _140477 _140478 x y) = x)). Qed.
Lemma lem7662722 {_140476 _140477 _140478 : Type'} (x : cart _140476 _140477) : (term45 _140476 _140477 _140478 x) = (term45 _140476 _140477 _140478 x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7662721 _140476 _140477 _140478 y x)). Qed.
Lemma lem7662723 {_140476 _140478 : Type'} : (@all (cart _140476 _140478)) = (@all (cart _140476 _140478)).
Proof. exact (eq_refl (@all (cart _140476 _140478))). Qed.
Lemma lem7662724 {_140476 _140477 _140478 : Type'} (x : cart _140476 _140477) : (term46 _140476 _140477 _140478 x) = (term46 _140476 _140477 _140478 x).
Proof. exact (MK_COMB (@lem7662723 _140476 _140478) (@lem7662722 _140476 _140477 _140478 x)). Qed.
Lemma lem7662725 {_140476 _140477 _140478 : Type'} : (term47 _140476 _140477 _140478) = (term47 _140476 _140477 _140478).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7662724 _140476 _140477 _140478 x)). Qed.
Lemma lem7662726 {_140476 _140477 : Type'} : (@all (cart _140476 _140477)) = (@all (cart _140476 _140477)).
Proof. exact (eq_refl (@all (cart _140476 _140477))). Qed.
Lemma lem7662727 {_140476 _140477 _140478 : Type'} : (term3 _140476 _140477 _140478) = (term3 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7662726 _140476 _140477) (@lem7662725 _140476 _140477 _140478)). Qed.
Lemma lem7662728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662729 {_140476 _140477 _140478 : Type'} : (term17 _140476 _140477 _140478) = (term17 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7662728) (@lem7662727 _140476 _140477 _140478)). Qed.
Lemma lem7662730 {_140476 _140477 _140478 N : Type'} : (term19 _140476 _140477 _140478 N) = (term19 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662729 _140476 _140477 _140478) (@lem7662720 _140476 _140477 _140478 N)). Qed.
Lemma lem7662731 {_140476 _140477 _140478 N : Type'} (x : type2 _140476 _140477 _140478) (y : cart _140476 N) : ((term48 _140476 _140477 _140478 N x y) = y) = ((term48 _140476 _140477 _140478 N x y) = y).
Proof. exact (eq_refl ((term48 _140476 _140477 _140478 N x y) = y)). Qed.
Lemma lem7662732 {_140476 _140477 _140478 N : Type'} (x : type2 _140476 _140477 _140478) : (term49 _140476 _140477 _140478 N x) = (term49 _140476 _140477 _140478 N x).
Proof. exact (fun_ext (fun y : cart _140476 N => @lem7662731 _140476 _140477 _140478 N x y)). Qed.
Lemma lem7662733 {_140476 N : Type'} : (@all (cart _140476 N)) = (@all (cart _140476 N)).
Proof. exact (eq_refl (@all (cart _140476 N))). Qed.
Lemma lem7662734 {_140476 _140477 _140478 N : Type'} (x : type2 _140476 _140477 _140478) : (term50 _140476 _140477 _140478 N x) = (term50 _140476 _140477 _140478 N x).
Proof. exact (MK_COMB (@lem7662733 _140476 N) (@lem7662732 _140476 _140477 _140478 N x)). Qed.
Lemma lem7662735 {_140476 _140477 _140478 N : Type'} : (term51 _140476 _140477 _140478 N) = (term51 _140476 _140477 _140478 N).
Proof. exact (fun_ext (fun x : type2 _140476 _140477 _140478 => @lem7662734 _140476 _140477 _140478 N x)). Qed.
Lemma lem7662736 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7662737 {_140476 _140477 _140478 N : Type'} : (term7 _140476 _140477 _140478 N) = (term7 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662736 _140476 _140477 _140478) (@lem7662735 _140476 _140477 _140478 N)). Qed.
Lemma lem7662738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662739 {_140476 _140477 _140478 N : Type'} : (term20 _140476 _140477 _140478 N) = (term20 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662738) (@lem7662737 _140476 _140477 _140478 N)). Qed.
Lemma lem7662740 {_140476 _140477 _140478 N : Type'} : (term22 _140476 _140477 _140478 N) = (term22 _140476 _140477 _140478 N).
Proof. exact (MK_COMB (@lem7662739 _140476 _140477 _140478 N) (@lem7662730 _140476 _140477 _140478 N)). Qed.
Lemma lem7662741 {_140476 _140477 _140478 M : Type'} (x : cart _140476 M) (y : type2 _140476 _140477 _140478) : ((term52 _140476 _140477 _140478 M x y) = y) = ((term52 _140476 _140477 _140478 M x y) = y).
Proof. exact (eq_refl ((term52 _140476 _140477 _140478 M x y) = y)). Qed.
Lemma lem7662742 {_140476 _140477 _140478 M : Type'} (x : cart _140476 M) : (term53 _140476 _140477 _140478 M x) = (term53 _140476 _140477 _140478 M x).
Proof. exact (fun_ext (fun y : type2 _140476 _140477 _140478 => @lem7662741 _140476 _140477 _140478 M x y)). Qed.
Lemma lem7662743 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7662744 {_140476 _140477 _140478 M : Type'} (x : cart _140476 M) : (term54 _140476 _140477 _140478 M x) = (term54 _140476 _140477 _140478 M x).
Proof. exact (MK_COMB (@lem7662743 _140476 _140477 _140478) (@lem7662742 _140476 _140477 _140478 M x)). Qed.
Lemma lem7662745 {_140476 _140477 _140478 M : Type'} : (term55 _140476 _140477 _140478 M) = (term55 _140476 _140477 _140478 M).
Proof. exact (fun_ext (fun x : cart _140476 M => @lem7662744 _140476 _140477 _140478 M x)). Qed.
Lemma lem7662746 {_140476 M : Type'} : (@all (cart _140476 M)) = (@all (cart _140476 M)).
Proof. exact (eq_refl (@all (cart _140476 M))). Qed.
Lemma lem7662747 {_140476 _140477 _140478 M : Type'} : (term4 _140476 _140477 _140478 M) = (term4 _140476 _140477 _140478 M).
Proof. exact (MK_COMB (@lem7662746 _140476 M) (@lem7662745 _140476 _140477 _140478 M)). Qed.
Lemma lem7662748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662749 {_140476 _140477 _140478 M : Type'} : (term23 _140476 _140477 _140478 M) = (term23 _140476 _140477 _140478 M).
Proof. exact (MK_COMB (@lem7662748) (@lem7662747 _140476 _140477 _140478 M)). Qed.
Lemma lem7662750 {_140476 _140477 _140478 M N : Type'} : (term25 _140476 _140477 _140478 M N) = (term25 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662749 _140476 _140477 _140478 M) (@lem7662740 _140476 _140477 _140478 N)). Qed.
Lemma lem7662751 {_140476 _140477 M : Type'} (x : cart _140476 M) (y : cart _140476 _140477) : ((term56 _140476 _140477 M x y) = y) = ((term56 _140476 _140477 M x y) = y).
Proof. exact (eq_refl ((term56 _140476 _140477 M x y) = y)). Qed.
Lemma lem7662752 {_140476 _140477 M : Type'} (x : cart _140476 M) : (term57 _140476 _140477 M x) = (term57 _140476 _140477 M x).
Proof. exact (fun_ext (fun y : cart _140476 _140477 => @lem7662751 _140476 _140477 M x y)). Qed.
Lemma lem7662753 {_140476 _140477 : Type'} : (@all (cart _140476 _140477)) = (@all (cart _140476 _140477)).
Proof. exact (eq_refl (@all (cart _140476 _140477))). Qed.
Lemma lem7662754 {_140476 _140477 M : Type'} (x : cart _140476 M) : (term58 _140476 _140477 M x) = (term58 _140476 _140477 M x).
Proof. exact (MK_COMB (@lem7662753 _140476 _140477) (@lem7662752 _140476 _140477 M x)). Qed.
Lemma lem7662755 {_140476 _140477 M : Type'} : (term59 _140476 _140477 M) = (term59 _140476 _140477 M).
Proof. exact (fun_ext (fun x : cart _140476 M => @lem7662754 _140476 _140477 M x)). Qed.
Lemma lem7662756 {_140476 M : Type'} : (@all (cart _140476 M)) = (@all (cart _140476 M)).
Proof. exact (eq_refl (@all (cart _140476 M))). Qed.
Lemma lem7662757 {_140476 _140477 M : Type'} : (term5 _140476 _140477 M) = (term5 _140476 _140477 M).
Proof. exact (MK_COMB (@lem7662756 _140476 M) (@lem7662755 _140476 _140477 M)). Qed.
Lemma lem7662758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662759 {_140476 _140477 M : Type'} : (term26 _140476 _140477 M) = (term26 _140476 _140477 M).
Proof. exact (MK_COMB (@lem7662758) (@lem7662757 _140476 _140477 M)). Qed.
Lemma lem7662760 {_140476 _140477 _140478 M N : Type'} : (term28 _140476 _140477 _140478 M N) = (term28 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662759 _140476 _140477 M) (@lem7662750 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662761 {_140476 _140477 _140478 : Type'} (x : cart _140476 _140477) (y : cart _140476 _140478) : ((term60 _140476 _140477 _140478 x y) = y) = ((term60 _140476 _140477 _140478 x y) = y).
Proof. exact (eq_refl ((term60 _140476 _140477 _140478 x y) = y)). Qed.
Lemma lem7662762 {_140476 _140477 _140478 : Type'} (x : cart _140476 _140477) : (term61 _140476 _140477 _140478 x) = (term61 _140476 _140477 _140478 x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7662761 _140476 _140477 _140478 x y)). Qed.
Lemma lem7662763 {_140476 _140478 : Type'} : (@all (cart _140476 _140478)) = (@all (cart _140476 _140478)).
Proof. exact (eq_refl (@all (cart _140476 _140478))). Qed.
Lemma lem7662764 {_140476 _140477 _140478 : Type'} (x : cart _140476 _140477) : (term62 _140476 _140477 _140478 x) = (term62 _140476 _140477 _140478 x).
Proof. exact (MK_COMB (@lem7662763 _140476 _140478) (@lem7662762 _140476 _140477 _140478 x)). Qed.
Lemma lem7662765 {_140476 _140477 _140478 : Type'} : (term63 _140476 _140477 _140478) = (term63 _140476 _140477 _140478).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7662764 _140476 _140477 _140478 x)). Qed.
Lemma lem7662766 {_140476 _140477 : Type'} : (@all (cart _140476 _140477)) = (@all (cart _140476 _140477)).
Proof. exact (eq_refl (@all (cart _140476 _140477))). Qed.
Lemma lem7662767 {_140476 _140477 _140478 : Type'} : (term6 _140476 _140477 _140478) = (term6 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7662766 _140476 _140477) (@lem7662765 _140476 _140477 _140478)). Qed.
Lemma lem7662768 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662769 {_140476 _140477 _140478 : Type'} : (term29 _140476 _140477 _140478) = (term29 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7662768) (@lem7662767 _140476 _140477 _140478)). Qed.
Lemma lem7662770 {_140476 _140477 _140478 M N : Type'} : (term31 _140476 _140477 _140478 M N) = (term31 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662769 _140476 _140477 _140478) (@lem7662760 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662771 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term64 _140476 _140477 _140478 P x y) = (term64 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term64 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7662772 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term65 _140476 _140477 _140478 P x) = (term65 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7662771 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7662773 {_140476 _140478 : Type'} : (@ex (cart _140476 _140478)) = (@ex (cart _140476 _140478)).
Proof. exact (eq_refl (@ex (cart _140476 _140478))). Qed.
Lemma lem7662774 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term66 _140476 _140477 _140478 P x) = (term66 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7662773 _140476 _140478) (@lem7662772 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662775 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term67 _140476 _140477 _140478 P) = (term67 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7662774 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662776 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7662777 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term68 _140476 _140477 _140478 P) = (term68 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662776 _140476 _140477) (@lem7662775 _140476 _140477 _140478 P)). Qed.
Lemma lem7662778 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7662779 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term69 _140476 _140477 _140478 P) = (term69 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7662778 _140476 _140477 _140478 P p)). Qed.
Lemma lem7662780 {_140476 _140477 _140478 : Type'} : (@ex (cart _140476 (finite_sum _140477 _140478))) = (@ex (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@ex (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7662781 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term70 _140476 _140477 _140478 P) = (term70 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662780 _140476 _140477 _140478) (@lem7662779 _140476 _140477 _140478 P)). Qed.
Lemma lem7662782 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7662783 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term71 _140476 _140477 _140478 P) = (term71 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662782) (@lem7662781 _140476 _140477 _140478 P)). Qed.
Lemma lem7662784 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : ((term70 _140476 _140477 _140478 P) = (term68 _140476 _140477 _140478 P)) = ((term70 _140476 _140477 _140478 P) = (term68 _140476 _140477 _140478 P)).
Proof. exact (MK_COMB (@lem7662783 _140476 _140477 _140478 P) (@lem7662777 _140476 _140477 _140478 P)). Qed.
Lemma lem7662785 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7662786 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term0 _140476 _140477 _140478 P) = (term0 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662785) (@lem7662784 _140476 _140477 _140478 P)). Qed.
Lemma lem7662787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7662788 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term32 _140476 _140477 _140478 P) = (term32 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662787) (@lem7662786 _140476 _140477 _140478 P)). Qed.
Lemma lem7662789 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : (term33 _140476 _140477 _140478 M N P) = (term33 _140476 _140477 _140478 M N P).
Proof. exact (MK_COMB (@lem7662788 _140476 _140477 _140478 P) (@lem7662770 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662790 {_140476 _140477 _140478 M N : Type'} : (term35 _140476 _140477 _140478 M N) = (term35 _140476 _140477 _140478 M N).
Proof. exact (fun_ext (fun P : type16 _140476 _140477 _140478 => @lem7662789 _140476 _140477 _140478 M N P)). Qed.
Lemma lem7662791 {_140476 _140477 _140478 : Type'} : (@all ((cart _140476 (finite_sum _140477 _140478)) -> Prop)) = (@all ((cart _140476 (finite_sum _140477 _140478)) -> Prop)).
Proof. exact (eq_refl (@all ((cart _140476 (finite_sum _140477 _140478)) -> Prop))). Qed.
Lemma lem7662792 {_140476 _140477 _140478 M N : Type'} : (term37 _140476 _140477 _140478 M N) = (term37 _140476 _140477 _140478 M N).
Proof. exact (MK_COMB (@lem7662791 _140476 _140477 _140478) (@lem7662790 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662911 {_140476 _140477 _140478 M N : Type'} : (term36 _140476 _140477 _140478 M N) = (term37 _140476 _140477 _140478 M N).
Proof. exact (TRANS (@lem7662704 _140476 _140477 _140478 M N) (@lem7662792 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662912 {_140476 _140477 _140478 M N : Type'} : (term37 _140476 _140477 _140478 M N) = (term36 _140476 _140477 _140478 M N).
Proof. exact (SYM (@lem7662911 _140476 _140477 _140478 M N)). Qed.
Lemma lem7662913 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term0 _140476 _140477 _140478 P.
Proof. exact (h1). Qed.
Lemma lem7662920 {_140476 _140477 _140478 : Type'} (h1 : term1 _140476 _140477 _140478) : term1 _140476 _140477 _140478.
Proof. exact (h1). Qed.
Lemma lem7662922 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (P p) = (P p).
Proof. exact (eq_refl (P p)). Qed.
Lemma lem7662923 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term72 _140476 _140477 _140478 P) = (term73 _140476 _140477 _140478 P).
Proof. exact (@lem18394 (type2 _140476 _140477 _140478) P). Qed.
Lemma lem7662924 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term74 _140476 _140477 _140478 P) = (term75 _140476 _140477 _140478 P).
Proof. exact (@lem7662923 _140476 _140477 _140478 (term69 _140476 _140477 _140478 P)). Qed.
Lemma lem7662925 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (term76 _140476 _140477 _140478 P p) = (P p).
Proof. exact (eq_refl (term76 _140476 _140477 _140478 P p)). Qed.
Lemma lem7662926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7662928 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (term77 _140476 _140477 _140478 P p) = (term78 _140476 _140477 _140478 P p).
Proof. exact (MK_COMB (@lem7662926) (@lem7662925 _140476 _140477 _140478 P p)). Qed.
Lemma lem7662929 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term79 _140476 _140477 _140478 P) = (term80 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7662928 _140476 _140477 _140478 P p)). Qed.
Lemma lem7662930 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7662931 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term75 _140476 _140477 _140478 P) = (term73 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662930 _140476 _140477 _140478) (@lem7662929 _140476 _140477 _140478 P)). Qed.
Lemma lem7662932 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term74 _140476 _140477 _140478 P) = (term73 _140476 _140477 _140478 P).
Proof. exact (TRANS (@lem7662924 _140476 _140477 _140478 P) (@lem7662931 _140476 _140477 _140478 P)). Qed.
Lemma lem7662933 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term69 _140476 _140477 _140478 P) = (term69 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7662922 _140476 _140477 _140478 P p)). Qed.
Lemma lem7662934 {_140476 _140477 _140478 : Type'} : (@ex (cart _140476 (finite_sum _140477 _140478))) = (@ex (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@ex (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7662935 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term70 _140476 _140477 _140478 P) = (term70 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662934 _140476 _140477 _140478) (@lem7662933 _140476 _140477 _140478 P)). Qed.
Lemma lem7662937 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term64 _140476 _140477 _140478 P x y) = (term64 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term64 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7662938 {_140476 _140478 : Type'} (P : type24 _140476 _140478) : (term81 _140476 _140478 P) = (term82 _140476 _140478 P).
Proof. exact (@lem18394 (cart _140476 _140478) P). Qed.
Lemma lem7662939 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term83 _140476 _140477 _140478 P x) = (term84 _140476 _140477 _140478 P x).
Proof. exact (@lem7662938 _140476 _140478 (term65 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662940 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term85 _140476 _140477 _140478 P x y) = (term64 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term85 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7662941 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7662943 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term86 _140476 _140477 _140478 P x y) = (term87 _140476 _140477 _140478 P x y).
Proof. exact (MK_COMB (@lem7662941) (@lem7662940 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7662944 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term88 _140476 _140477 _140478 P x) = (term89 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7662943 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7662945 {_140476 _140478 : Type'} : (@all (cart _140476 _140478)) = (@all (cart _140476 _140478)).
Proof. exact (eq_refl (@all (cart _140476 _140478))). Qed.
Lemma lem7662946 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term84 _140476 _140477 _140478 P x) = (term90 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7662945 _140476 _140478) (@lem7662944 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662947 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term83 _140476 _140477 _140478 P x) = (term90 _140476 _140477 _140478 P x).
Proof. exact (TRANS (@lem7662939 _140476 _140477 _140478 P x) (@lem7662946 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662948 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term65 _140476 _140477 _140478 P x) = (term65 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7662937 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7662949 {_140476 _140478 : Type'} : (@ex (cart _140476 _140478)) = (@ex (cart _140476 _140478)).
Proof. exact (eq_refl (@ex (cart _140476 _140478))). Qed.
Lemma lem7662950 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term66 _140476 _140477 _140478 P x) = (term66 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7662949 _140476 _140478) (@lem7662948 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662951 {_140476 _140477 : Type'} (P : type24 _140476 _140477) : (term81 _140476 _140477 P) = (term82 _140476 _140477 P).
Proof. exact (@lem18394 (cart _140476 _140477) P). Qed.
Lemma lem7662952 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term91 _140476 _140477 _140478 P) = (term92 _140476 _140477 _140478 P).
Proof. exact (@lem7662951 _140476 _140477 (term67 _140476 _140477 _140478 P)). Qed.
Lemma lem7662953 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term93 _140476 _140477 _140478 P x) = (term66 _140476 _140477 _140478 P x).
Proof. exact (eq_refl (term93 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7662955 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term94 _140476 _140477 _140478 P x) = (term83 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7662954) (@lem7662953 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662956 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term94 _140476 _140477 _140478 P x) = (term90 _140476 _140477 _140478 P x).
Proof. exact (TRANS (@lem7662955 _140476 _140477 _140478 P x) (@lem7662947 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662957 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term95 _140476 _140477 _140478 P) = (term96 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7662956 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662958 {_140476 _140477 : Type'} : (@all (cart _140476 _140477)) = (@all (cart _140476 _140477)).
Proof. exact (eq_refl (@all (cart _140476 _140477))). Qed.
Lemma lem7662959 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term92 _140476 _140477 _140478 P) = (term97 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662958 _140476 _140477) (@lem7662957 _140476 _140477 _140478 P)). Qed.
Lemma lem7662960 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term91 _140476 _140477 _140478 P) = (term97 _140476 _140477 _140478 P).
Proof. exact (TRANS (@lem7662952 _140476 _140477 _140478 P) (@lem7662959 _140476 _140477 _140478 P)). Qed.
Lemma lem7662961 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term67 _140476 _140477 _140478 P) = (term67 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7662950 _140476 _140477 _140478 P x)). Qed.
Lemma lem7662962 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7662963 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term68 _140476 _140477 _140478 P) = (term68 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662962 _140476 _140477) (@lem7662961 _140476 _140477 _140478 P)). Qed.
Lemma lem7662964 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7662965 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term98 _140476 _140477 _140478 P) = (term99 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662964) (@lem7662932 _140476 _140477 _140478 P)). Qed.
Lemma lem7662966 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term100 _140476 _140477 _140478 P) = (term101 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662965 _140476 _140477 _140478 P) (@lem7662963 _140476 _140477 _140478 P)). Qed.
Lemma lem7662967 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7662968 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term102 _140476 _140477 _140478 P) = (term102 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662967) (@lem7662935 _140476 _140477 _140478 P)). Qed.
Lemma lem7662969 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term103 _140476 _140477 _140478 P) = (term104 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662968 _140476 _140477 _140478 P) (@lem7662960 _140476 _140477 _140478 P)). Qed.
Lemma lem7662970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7662971 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term105 _140476 _140477 _140478 P) = (term106 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662970) (@lem7662969 _140476 _140477 _140478 P)). Qed.
Lemma lem7662972 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term107 _140476 _140477 _140478 P) = (term108 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7662971 _140476 _140477 _140478 P) (@lem7662966 _140476 _140477 _140478 P)). Qed.
Lemma lem7662973 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term0 _140476 _140477 _140478 P) = (term107 _140476 _140477 _140478 P).
Proof. exact (@lem17646 (term70 _140476 _140477 _140478 P) (term68 _140476 _140477 _140478 P)). Qed.
Lemma lem7662974 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term0 _140476 _140477 _140478 P) = (term108 _140476 _140477 _140478 P).
Proof. exact (TRANS (@lem7662973 _140476 _140477 _140478 P) (@lem7662972 _140476 _140477 _140478 P)). Qed.
Lemma lem7663001 {A : Type'} (P : A -> Prop) (Q : Prop) : (term109 A P Q) = (term110 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7663002 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (Q : Prop) : (term111 _140476 _140477 _140478 P Q) = (term112 _140476 _140477 _140478 P Q).
Proof. exact (@lem7663001 (type2 _140476 _140477 _140478) P Q). Qed.
Lemma lem7663003 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term104 _140476 _140477 _140478 P) = (term113 _140476 _140477 _140478 P).
Proof. exact (@lem7663002 _140476 _140477 _140478 P (term97 _140476 _140477 _140478 P)). Qed.
Lemma lem7663004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7663005 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term106 _140476 _140477 _140478 P) = (term114 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663004) (@lem7663003 _140476 _140477 _140478 P)). Qed.
Lemma lem7663007 {A : Type'} (P : Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7663008 {_140476 _140477 : Type'} (P : Prop) (Q : type24 _140476 _140477) : (term117 _140476 _140477 P Q) = (term118 _140476 _140477 P Q).
Proof. exact (@lem7663007 (cart _140476 _140477) P Q). Qed.
Lemma lem7663009 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term119 _140476 _140477 _140478 P) = (term120 _140476 _140477 _140478 P).
Proof. exact (@lem7663008 _140476 _140477 (term73 _140476 _140477 _140478 P) (term67 _140476 _140477 _140478 P)). Qed.
Lemma lem7663010 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term93 _140476 _140477 _140478 P x) = (term66 _140476 _140477 _140478 P x).
Proof. exact (eq_refl (term93 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663011 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term121 _140476 _140477 _140478 P) = (term67 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663010 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663012 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7663013 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term122 _140476 _140477 _140478 P) = (term68 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663012 _140476 _140477) (@lem7663011 _140476 _140477 _140478 P)). Qed.
Lemma lem7663014 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term99 _140476 _140477 _140478 P) = (term99 _140476 _140477 _140478 P).
Proof. exact (eq_refl (term99 _140476 _140477 _140478 P)). Qed.
Lemma lem7663015 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term119 _140476 _140477 _140478 P) = (term101 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663014 _140476 _140477 _140478 P) (@lem7663013 _140476 _140477 _140478 P)). Qed.
Lemma lem7663016 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7663017 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term123 _140476 _140477 _140478 P) = (term124 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663016) (@lem7663015 _140476 _140477 _140478 P)). Qed.
Lemma lem7663018 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term93 _140476 _140477 _140478 P x) = (term66 _140476 _140477 _140478 P x).
Proof. exact (eq_refl (term93 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663019 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term99 _140476 _140477 _140478 P) = (term99 _140476 _140477 _140478 P).
Proof. exact (eq_refl (term99 _140476 _140477 _140478 P)). Qed.
Lemma lem7663020 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term125 _140476 _140477 _140478 P x) = (term126 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663019 _140476 _140477 _140478 P) (@lem7663018 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663021 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term127 _140476 _140477 _140478 P) = (term128 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663020 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663022 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7663023 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term120 _140476 _140477 _140478 P) = (term129 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663022 _140476 _140477) (@lem7663021 _140476 _140477 _140478 P)). Qed.
Lemma lem7663024 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : ((term119 _140476 _140477 _140478 P) = (term120 _140476 _140477 _140478 P)) = ((term101 _140476 _140477 _140478 P) = (term129 _140476 _140477 _140478 P)).
Proof. exact (MK_COMB (@lem7663017 _140476 _140477 _140478 P) (@lem7663023 _140476 _140477 _140478 P)). Qed.
Lemma lem7663025 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term101 _140476 _140477 _140478 P) = (term129 _140476 _140477 _140478 P).
Proof. exact (EQ_MP (@lem7663024 _140476 _140477 _140478 P) (@lem7663009 _140476 _140477 _140478 P)). Qed.
Lemma lem7663027 {A : Type'} (P : Prop) (Q : A -> Prop) : (term115 A P Q) = (term116 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem7663028 {_140476 _140478 : Type'} (P : Prop) (Q : type24 _140476 _140478) : (term117 _140476 _140478 P Q) = (term118 _140476 _140478 P Q).
Proof. exact (@lem7663027 (cart _140476 _140478) P Q). Qed.
Lemma lem7663029 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term130 _140476 _140477 _140478 P x) = (term131 _140476 _140477 _140478 P x).
Proof. exact (@lem7663028 _140476 _140478 (term73 _140476 _140477 _140478 P) (term65 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663030 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term85 _140476 _140477 _140478 P x y) = (term64 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term85 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663031 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term132 _140476 _140477 _140478 P x) = (term65 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7663030 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663032 {_140476 _140478 : Type'} : (@ex (cart _140476 _140478)) = (@ex (cart _140476 _140478)).
Proof. exact (eq_refl (@ex (cart _140476 _140478))). Qed.
Lemma lem7663033 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term133 _140476 _140477 _140478 P x) = (term66 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663032 _140476 _140478) (@lem7663031 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663034 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term99 _140476 _140477 _140478 P) = (term99 _140476 _140477 _140478 P).
Proof. exact (eq_refl (term99 _140476 _140477 _140478 P)). Qed.
Lemma lem7663035 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term130 _140476 _140477 _140478 P x) = (term126 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663034 _140476 _140477 _140478 P) (@lem7663033 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663036 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7663037 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term134 _140476 _140477 _140478 P x) = (term135 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663036) (@lem7663035 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663038 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term85 _140476 _140477 _140478 P x y) = (term64 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term85 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663039 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term99 _140476 _140477 _140478 P) = (term99 _140476 _140477 _140478 P).
Proof. exact (eq_refl (term99 _140476 _140477 _140478 P)). Qed.
Lemma lem7663040 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term136 _140476 _140477 _140478 P x y) = (term137 _140476 _140477 _140478 P x y).
Proof. exact (MK_COMB (@lem7663039 _140476 _140477 _140478 P) (@lem7663038 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663041 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term138 _140476 _140477 _140478 P x) = (term139 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7663040 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663042 {_140476 _140478 : Type'} : (@ex (cart _140476 _140478)) = (@ex (cart _140476 _140478)).
Proof. exact (eq_refl (@ex (cart _140476 _140478))). Qed.
Lemma lem7663043 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term131 _140476 _140477 _140478 P x) = (term140 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663042 _140476 _140478) (@lem7663041 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663044 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : ((term130 _140476 _140477 _140478 P x) = (term131 _140476 _140477 _140478 P x)) = ((term126 _140476 _140477 _140478 P x) = (term140 _140476 _140477 _140478 P x)).
Proof. exact (MK_COMB (@lem7663037 _140476 _140477 _140478 P x) (@lem7663043 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663045 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term126 _140476 _140477 _140478 P x) = (term140 _140476 _140477 _140478 P x).
Proof. exact (EQ_MP (@lem7663044 _140476 _140477 _140478 P x) (@lem7663029 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663046 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term128 _140476 _140477 _140478 P) = (term141 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663045 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663047 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7663048 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term129 _140476 _140477 _140478 P) = (term142 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663047 _140476 _140477) (@lem7663046 _140476 _140477 _140478 P)). Qed.
Lemma lem7663049 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term101 _140476 _140477 _140478 P) = (term142 _140476 _140477 _140478 P).
Proof. exact (TRANS (@lem7663025 _140476 _140477 _140478 P) (@lem7663048 _140476 _140477 _140478 P)). Qed.
Lemma lem7663050 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term108 _140476 _140477 _140478 P) = (term143 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663005 _140476 _140477 _140478 P) (@lem7663049 _140476 _140477 _140478 P)). Qed.
Lemma lem7663054 {A : Type'} (P : A -> Prop) (Q : Prop) : (term144 A P Q) = (term145 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7663055 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (Q : Prop) : (term146 _140476 _140477 _140478 P Q) = (term147 _140476 _140477 _140478 P Q).
Proof. exact (@lem7663054 (type2 _140476 _140477 _140478) P Q). Qed.
Lemma lem7663056 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term148 _140476 _140477 _140478 P) = (term149 _140476 _140477 _140478 P).
Proof. exact (@lem7663055 _140476 _140477 _140478 (term150 _140476 _140477 _140478 P) (term142 _140476 _140477 _140478 P)). Qed.
Lemma lem7663057 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term151 _140476 _140477 _140478 P p) = (term152 _140476 _140477 _140478 p P).
Proof. exact (eq_refl (term151 _140476 _140477 _140478 P p)). Qed.
Lemma lem7663058 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term153 _140476 _140477 _140478 P) = (term150 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7663057 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663059 {_140476 _140477 _140478 : Type'} : (@ex (cart _140476 (finite_sum _140477 _140478))) = (@ex (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@ex (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663060 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term154 _140476 _140477 _140478 P) = (term113 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663059 _140476 _140477 _140478) (@lem7663058 _140476 _140477 _140478 P)). Qed.
Lemma lem7663061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7663062 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term155 _140476 _140477 _140478 P) = (term114 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663061) (@lem7663060 _140476 _140477 _140478 P)). Qed.
Lemma lem7663063 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term142 _140476 _140477 _140478 P) = (term142 _140476 _140477 _140478 P).
Proof. exact (eq_refl (term142 _140476 _140477 _140478 P)). Qed.
Lemma lem7663064 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term148 _140476 _140477 _140478 P) = (term143 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663062 _140476 _140477 _140478 P) (@lem7663063 _140476 _140477 _140478 P)). Qed.
Lemma lem7663065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7663066 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term156 _140476 _140477 _140478 P) = (term157 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663065) (@lem7663064 _140476 _140477 _140478 P)). Qed.
Lemma lem7663067 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term151 _140476 _140477 _140478 P p) = (term152 _140476 _140477 _140478 p P).
Proof. exact (eq_refl (term151 _140476 _140477 _140478 P p)). Qed.
Lemma lem7663068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7663069 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term158 _140476 _140477 _140478 P p) = (term159 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663068) (@lem7663067 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663070 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term142 _140476 _140477 _140478 P) = (term142 _140476 _140477 _140478 P).
Proof. exact (eq_refl (term142 _140476 _140477 _140478 P)). Qed.
Lemma lem7663071 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term160 _140476 _140477 _140478 p P) = (term161 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663069 _140476 _140477 _140478 p P) (@lem7663070 _140476 _140477 _140478 P)). Qed.
Lemma lem7663072 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term162 _140476 _140477 _140478 P) = (term163 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7663071 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663073 {_140476 _140477 _140478 : Type'} : (@ex (cart _140476 (finite_sum _140477 _140478))) = (@ex (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@ex (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663074 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term149 _140476 _140477 _140478 P) = (term164 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663073 _140476 _140477 _140478) (@lem7663072 _140476 _140477 _140478 P)). Qed.
Lemma lem7663075 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : ((term148 _140476 _140477 _140478 P) = (term149 _140476 _140477 _140478 P)) = ((term143 _140476 _140477 _140478 P) = (term164 _140476 _140477 _140478 P)).
Proof. exact (MK_COMB (@lem7663066 _140476 _140477 _140478 P) (@lem7663074 _140476 _140477 _140478 P)). Qed.
Lemma lem7663076 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term143 _140476 _140477 _140478 P) = (term164 _140476 _140477 _140478 P).
Proof. exact (EQ_MP (@lem7663075 _140476 _140477 _140478 P) (@lem7663056 _140476 _140477 _140478 P)). Qed.
Lemma lem7663078 {A : Type'} (P : Prop) (Q : A -> Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7663079 {_140476 _140477 : Type'} (P : Prop) (Q : type24 _140476 _140477) : (term167 _140476 _140477 P Q) = (term168 _140476 _140477 P Q).
Proof. exact (@lem7663078 (cart _140476 _140477) P Q). Qed.
Lemma lem7663080 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term169 _140476 _140477 _140478 p P) = (term170 _140476 _140477 _140478 p P).
Proof. exact (@lem7663079 _140476 _140477 (term152 _140476 _140477 _140478 p P) (term141 _140476 _140477 _140478 P)). Qed.
Lemma lem7663081 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term171 _140476 _140477 _140478 P x) = (term140 _140476 _140477 _140478 P x).
Proof. exact (eq_refl (term171 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663082 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term172 _140476 _140477 _140478 P) = (term141 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663081 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663083 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7663084 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term173 _140476 _140477 _140478 P) = (term142 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663083 _140476 _140477) (@lem7663082 _140476 _140477 _140478 P)). Qed.
Lemma lem7663085 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term159 _140476 _140477 _140478 p P) = (term159 _140476 _140477 _140478 p P).
Proof. exact (eq_refl (term159 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663086 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term169 _140476 _140477 _140478 p P) = (term161 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663085 _140476 _140477 _140478 p P) (@lem7663084 _140476 _140477 _140478 P)). Qed.
Lemma lem7663087 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7663088 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term174 _140476 _140477 _140478 p P) = (term175 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663087) (@lem7663086 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663089 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term171 _140476 _140477 _140478 P x) = (term140 _140476 _140477 _140478 P x).
Proof. exact (eq_refl (term171 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663090 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term159 _140476 _140477 _140478 p P) = (term159 _140476 _140477 _140478 p P).
Proof. exact (eq_refl (term159 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663091 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term176 _140476 _140477 _140478 p P x) = (term177 _140476 _140477 _140478 p P x).
Proof. exact (MK_COMB (@lem7663090 _140476 _140477 _140478 p P) (@lem7663089 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663092 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term178 _140476 _140477 _140478 p P) = (term179 _140476 _140477 _140478 p P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663091 _140476 _140477 _140478 p P x)). Qed.
Lemma lem7663093 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7663094 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term170 _140476 _140477 _140478 p P) = (term180 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663093 _140476 _140477) (@lem7663092 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663095 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : ((term169 _140476 _140477 _140478 p P) = (term170 _140476 _140477 _140478 p P)) = ((term161 _140476 _140477 _140478 p P) = (term180 _140476 _140477 _140478 p P)).
Proof. exact (MK_COMB (@lem7663088 _140476 _140477 _140478 p P) (@lem7663094 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663096 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term161 _140476 _140477 _140478 p P) = (term180 _140476 _140477 _140478 p P).
Proof. exact (EQ_MP (@lem7663095 _140476 _140477 _140478 p P) (@lem7663080 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663098 {A : Type'} (P : Prop) (Q : A -> Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7663099 {_140476 _140478 : Type'} (P : Prop) (Q : type24 _140476 _140478) : (term167 _140476 _140478 P Q) = (term168 _140476 _140478 P Q).
Proof. exact (@lem7663098 (cart _140476 _140478) P Q). Qed.
Lemma lem7663100 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term181 _140476 _140477 _140478 p P x) = (term182 _140476 _140477 _140478 p P x).
Proof. exact (@lem7663099 _140476 _140478 (term152 _140476 _140477 _140478 p P) (term139 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663101 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term183 _140476 _140477 _140478 P x y) = (term137 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term183 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663102 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term184 _140476 _140477 _140478 P x) = (term139 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7663101 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663103 {_140476 _140478 : Type'} : (@ex (cart _140476 _140478)) = (@ex (cart _140476 _140478)).
Proof. exact (eq_refl (@ex (cart _140476 _140478))). Qed.
Lemma lem7663104 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term185 _140476 _140477 _140478 P x) = (term140 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663103 _140476 _140478) (@lem7663102 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663105 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term159 _140476 _140477 _140478 p P) = (term159 _140476 _140477 _140478 p P).
Proof. exact (eq_refl (term159 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663106 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term181 _140476 _140477 _140478 p P x) = (term177 _140476 _140477 _140478 p P x).
Proof. exact (MK_COMB (@lem7663105 _140476 _140477 _140478 p P) (@lem7663104 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7663108 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term186 _140476 _140477 _140478 p P x) = (term187 _140476 _140477 _140478 p P x).
Proof. exact (MK_COMB (@lem7663107) (@lem7663106 _140476 _140477 _140478 p P x)). Qed.
Lemma lem7663109 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term183 _140476 _140477 _140478 P x y) = (term137 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term183 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663110 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term159 _140476 _140477 _140478 p P) = (term159 _140476 _140477 _140478 p P).
Proof. exact (eq_refl (term159 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663111 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term188 _140476 _140477 _140478 p P x y) = (term189 _140476 _140477 _140478 p P x y).
Proof. exact (MK_COMB (@lem7663110 _140476 _140477 _140478 p P) (@lem7663109 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663112 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term190 _140476 _140477 _140478 p P x) = (term191 _140476 _140477 _140478 p P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7663111 _140476 _140477 _140478 p P x y)). Qed.
Lemma lem7663113 {_140476 _140478 : Type'} : (@ex (cart _140476 _140478)) = (@ex (cart _140476 _140478)).
Proof. exact (eq_refl (@ex (cart _140476 _140478))). Qed.
Lemma lem7663114 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term182 _140476 _140477 _140478 p P x) = (term192 _140476 _140477 _140478 p P x).
Proof. exact (MK_COMB (@lem7663113 _140476 _140478) (@lem7663112 _140476 _140477 _140478 p P x)). Qed.
Lemma lem7663115 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : ((term181 _140476 _140477 _140478 p P x) = (term182 _140476 _140477 _140478 p P x)) = ((term177 _140476 _140477 _140478 p P x) = (term192 _140476 _140477 _140478 p P x)).
Proof. exact (MK_COMB (@lem7663108 _140476 _140477 _140478 p P x) (@lem7663114 _140476 _140477 _140478 p P x)). Qed.
Lemma lem7663116 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term177 _140476 _140477 _140478 p P x) = (term192 _140476 _140477 _140478 p P x).
Proof. exact (EQ_MP (@lem7663115 _140476 _140477 _140478 p P x) (@lem7663100 _140476 _140477 _140478 p P x)). Qed.
Lemma lem7663117 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term179 _140476 _140477 _140478 p P) = (term193 _140476 _140477 _140478 p P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663116 _140476 _140477 _140478 p P x)). Qed.
Lemma lem7663118 {_140476 _140477 : Type'} : (@ex (cart _140476 _140477)) = (@ex (cart _140476 _140477)).
Proof. exact (eq_refl (@ex (cart _140476 _140477))). Qed.
Lemma lem7663119 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term180 _140476 _140477 _140478 p P) = (term194 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663118 _140476 _140477) (@lem7663117 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663120 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term161 _140476 _140477 _140478 p P) = (term194 _140476 _140477 _140478 p P).
Proof. exact (TRANS (@lem7663096 _140476 _140477 _140478 p P) (@lem7663119 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663121 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term163 _140476 _140477 _140478 P) = (term195 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7663120 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663122 {_140476 _140477 _140478 : Type'} : (@ex (cart _140476 (finite_sum _140477 _140478))) = (@ex (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@ex (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663123 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term164 _140476 _140477 _140478 P) = (term196 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663122 _140476 _140477 _140478) (@lem7663121 _140476 _140477 _140478 P)). Qed.
Lemma lem7663124 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term143 _140476 _140477 _140478 P) = (term196 _140476 _140477 _140478 P).
Proof. exact (TRANS (@lem7663076 _140476 _140477 _140478 P) (@lem7663123 _140476 _140477 _140478 P)). Qed.
Lemma lem7663126 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term108 _140476 _140477 _140478 P) = (term196 _140476 _140477 _140478 P).
Proof. exact (TRANS (@lem7663050 _140476 _140477 _140478 P) (@lem7663124 _140476 _140477 _140478 P)). Qed.
Lemma lem7663127 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term0 _140476 _140477 _140478 P) = (term196 _140476 _140477 _140478 P).
Proof. exact (TRANS (@lem7662974 _140476 _140477 _140478 P) (@lem7663126 _140476 _140477 _140478 P)). Qed.
Lemma lem7663128 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term196 _140476 _140477 _140478 P.
Proof. exact (EQ_MP (@lem7663127 _140476 _140477 _140478 P) (@lem7662913 _140476 _140477 _140478 P h1)). Qed.
Lemma lem7663249 {_140476 _140477 _140478 : Type'} (z : type2 _140476 _140477 _140478) : ((term38 _140476 _140477 _140478 z) = z) = ((term38 _140476 _140477 _140478 z) = z).
Proof. exact (eq_refl ((term38 _140476 _140477 _140478 z) = z)). Qed.
Lemma lem7663250 {_140476 _140477 _140478 : Type'} : (term39 _140476 _140477 _140478) = (term39 _140476 _140477 _140478).
Proof. exact (fun_ext (fun z : type2 _140476 _140477 _140478 => @lem7663249 _140476 _140477 _140478 z)). Qed.
Lemma lem7663251 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663260 {_140476 _140477 _140478 : Type'} : (term1 _140476 _140477 _140478) = (term1 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7663251 _140476 _140477 _140478) (@lem7663250 _140476 _140477 _140478)). Qed.
Lemma lem7663261 {_140476 _140477 _140478 : Type'} (h1 : term1 _140476 _140477 _140478) : term1 _140476 _140477 _140478.
Proof. exact (EQ_MP (@lem7663260 _140476 _140477 _140478) (@lem7662920 _140476 _140477 _140478 h1)). Qed.
Lemma lem7663262 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term194 _140476 _140477 _140478 p P) : term194 _140476 _140477 _140478 p P.
Proof. exact (h1). Qed.
Lemma lem7663263 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (h1 : term192 _140476 _140477 _140478 p P x) : term192 _140476 _140477 _140478 p P x.
Proof. exact (h1). Qed.
Lemma lem7663264 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term189 _140476 _140477 _140478 p P x y) : term189 _140476 _140477 _140478 p P x y.
Proof. exact (h1). Qed.
Lemma lem7663385 {_140476 _140477 _140478 : Type'} (z : type2 _140476 _140477 _140478) : ((term38 _140476 _140477 _140478 z) = z) = ((term38 _140476 _140477 _140478 z) = z).
Proof. exact (eq_refl ((term38 _140476 _140477 _140478 z) = z)). Qed.
Lemma lem7663386 {_140476 _140477 _140478 : Type'} : (term39 _140476 _140477 _140478) = (term39 _140476 _140477 _140478).
Proof. exact (fun_ext (fun z : type2 _140476 _140477 _140478 => @lem7663385 _140476 _140477 _140478 z)). Qed.
Lemma lem7663387 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663388 {_140476 _140477 _140478 : Type'} : (term1 _140476 _140477 _140478) = (term1 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7663387 _140476 _140477 _140478) (@lem7663386 _140476 _140477 _140478)). Qed.
Lemma lem7663389 {_140476 _140477 _140478 : Type'} (h1 : term1 _140476 _140477 _140478) : term1 _140476 _140477 _140478.
Proof. exact (EQ_MP (@lem7663388 _140476 _140477 _140478) (@lem7663261 _140476 _140477 _140478 h1)). Qed.
Lemma lem7663396 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term64 _140476 _140477 _140478 P x y) = (term64 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term64 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663401 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (term78 _140476 _140477 _140478 P p) = (term78 _140476 _140477 _140478 P p).
Proof. exact (eq_refl (term78 _140476 _140477 _140478 P p)). Qed.
Lemma lem7663402 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term80 _140476 _140477 _140478 P) = (term80 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7663401 _140476 _140477 _140478 P p)). Qed.
Lemma lem7663403 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663404 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term73 _140476 _140477 _140478 P) = (term73 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663403 _140476 _140477 _140478) (@lem7663402 _140476 _140477 _140478 P)). Qed.
Lemma lem7663405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7663406 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term99 _140476 _140477 _140478 P) = (term99 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663405) (@lem7663404 _140476 _140477 _140478 P)). Qed.
Lemma lem7663407 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term137 _140476 _140477 _140478 P x y) = (term137 _140476 _140477 _140478 P x y).
Proof. exact (MK_COMB (@lem7663406 _140476 _140477 _140478 P) (@lem7663396 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663416 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term87 _140476 _140477 _140478 P x y) = (term87 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term87 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663417 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term89 _140476 _140477 _140478 P x) = (term89 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7663416 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663418 {_140476 _140478 : Type'} : (@all (cart _140476 _140478)) = (@all (cart _140476 _140478)).
Proof. exact (eq_refl (@all (cart _140476 _140478))). Qed.
Lemma lem7663419 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term90 _140476 _140477 _140478 P x) = (term90 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663418 _140476 _140478) (@lem7663417 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663420 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term96 _140476 _140477 _140478 P) = (term96 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663419 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663421 {_140476 _140477 : Type'} : (@all (cart _140476 _140477)) = (@all (cart _140476 _140477)).
Proof. exact (eq_refl (@all (cart _140476 _140477))). Qed.
Lemma lem7663422 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term97 _140476 _140477 _140478 P) = (term97 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663421 _140476 _140477) (@lem7663420 _140476 _140477 _140478 P)). Qed.
Lemma lem7663427 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (term197 _140476 _140477 _140478 P p) = (term197 _140476 _140477 _140478 P p).
Proof. exact (eq_refl (term197 _140476 _140477 _140478 P p)). Qed.
Lemma lem7663428 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term152 _140476 _140477 _140478 p P) = (term152 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663427 _140476 _140477 _140478 P p) (@lem7663422 _140476 _140477 _140478 P)). Qed.
Lemma lem7663429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7663430 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) : (term159 _140476 _140477 _140478 p P) = (term159 _140476 _140477 _140478 p P).
Proof. exact (MK_COMB (@lem7663429) (@lem7663428 _140476 _140477 _140478 p P)). Qed.
Lemma lem7663431 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term189 _140476 _140477 _140478 p P x y) = (term189 _140476 _140477 _140478 p P x y).
Proof. exact (MK_COMB (@lem7663430 _140476 _140477 _140478 p P) (@lem7663407 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663432 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term189 _140476 _140477 _140478 p P x y) : term189 _140476 _140477 _140478 p P x y.
Proof. exact (EQ_MP (@lem7663431 _140476 _140477 _140478 p P x y) (@lem7663264 _140476 _140477 _140478 p P x y h1)). Qed.
Lemma lem7663433 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term152 _140476 _140477 _140478 p P.
Proof. exact (h1). Qed.
Lemma lem7663434 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term137 _140476 _140477 _140478 P x y.
Proof. exact (h1). Qed.
Lemma lem7663435 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term97 _140476 _140477 _140478 P.
Proof. exact (proj2 (@lem7663433 _140476 _140477 _140478 p P h1)). Qed.
Lemma lem7663438 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term73 _140476 _140477 _140478 P.
Proof. exact (proj1 (@lem7663434 _140476 _140477 _140478 P x y h1)). Qed.
Lemma lem7663500 {_140476 _140477 _140478 : Type'} (z : type2 _140476 _140477 _140478) : ((term38 _140476 _140477 _140478 z) = z) = ((term38 _140476 _140477 _140478 z) = z).
Proof. exact (eq_refl ((term38 _140476 _140477 _140478 z) = z)). Qed.
Lemma lem7663501 {_140476 _140477 _140478 : Type'} : (term39 _140476 _140477 _140478) = (term39 _140476 _140477 _140478).
Proof. exact (fun_ext (fun z : type2 _140476 _140477 _140478 => @lem7663500 _140476 _140477 _140478 z)). Qed.
Lemma lem7663502 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663504 {_140476 _140477 _140478 : Type'} : (term1 _140476 _140477 _140478) = (term1 _140476 _140477 _140478).
Proof. exact (MK_COMB (@lem7663502 _140476 _140477 _140478) (@lem7663501 _140476 _140477 _140478)). Qed.
Lemma lem7663505 {_140476 _140477 _140478 : Type'} (h1 : term1 _140476 _140477 _140478) : term1 _140476 _140477 _140478.
Proof. exact (EQ_MP (@lem7663504 _140476 _140477 _140478) (@lem7663389 _140476 _140477 _140478 h1)). Qed.
Lemma lem7663511 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term87 _140476 _140477 _140478 P x y) = (term87 _140476 _140477 _140478 P x y).
Proof. exact (eq_refl (term87 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663512 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term89 _140476 _140477 _140478 P x) = (term89 _140476 _140477 _140478 P x).
Proof. exact (fun_ext (fun y : cart _140476 _140478 => @lem7663511 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7663513 {_140476 _140478 : Type'} : (@all (cart _140476 _140478)) = (@all (cart _140476 _140478)).
Proof. exact (eq_refl (@all (cart _140476 _140478))). Qed.
Lemma lem7663514 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) : (term90 _140476 _140477 _140478 P x) = (term90 _140476 _140477 _140478 P x).
Proof. exact (MK_COMB (@lem7663513 _140476 _140478) (@lem7663512 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663515 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term96 _140476 _140477 _140478 P) = (term96 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun x : cart _140476 _140477 => @lem7663514 _140476 _140477 _140478 P x)). Qed.
Lemma lem7663516 {_140476 _140477 : Type'} : (@all (cart _140476 _140477)) = (@all (cart _140476 _140477)).
Proof. exact (eq_refl (@all (cart _140476 _140477))). Qed.
Lemma lem7663518 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term97 _140476 _140477 _140478 P) = (term97 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663516 _140476 _140477) (@lem7663515 _140476 _140477 _140478 P)). Qed.
Lemma lem7663519 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term97 _140476 _140477 _140478 P.
Proof. exact (EQ_MP (@lem7663518 _140476 _140477 _140478 P) (@lem7663435 _140476 _140477 _140478 p P h1)). Qed.
Lemma lem7663588 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (term78 _140476 _140477 _140478 P p) = (term78 _140476 _140477 _140478 P p).
Proof. exact (eq_refl (term78 _140476 _140477 _140478 P p)). Qed.
Lemma lem7663589 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term80 _140476 _140477 _140478 P) = (term80 _140476 _140477 _140478 P).
Proof. exact (fun_ext (fun p : type2 _140476 _140477 _140478 => @lem7663588 _140476 _140477 _140478 P p)). Qed.
Lemma lem7663590 {_140476 _140477 _140478 : Type'} : (@all (cart _140476 (finite_sum _140477 _140478))) = (@all (cart _140476 (finite_sum _140477 _140478))).
Proof. exact (eq_refl (@all (cart _140476 (finite_sum _140477 _140478)))). Qed.
Lemma lem7663592 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : (term73 _140476 _140477 _140478 P) = (term73 _140476 _140477 _140478 P).
Proof. exact (MK_COMB (@lem7663590 _140476 _140477 _140478) (@lem7663589 _140476 _140477 _140478 P)). Qed.
Lemma lem7663593 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term73 _140476 _140477 _140478 P.
Proof. exact (EQ_MP (@lem7663592 _140476 _140477 _140478 P) (@lem7663438 _140476 _140477 _140478 P x y h1)). Qed.
Lemma lem7663634 {_140476 _140477 _140478 : Type'} (_98692 : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : term198 _140476 _140477 _140478 _98692.
Proof. exact (@lem7663505 _140476 _140477 _140478 h1 _98692). Qed.
Lemma lem7663635 {_140476 _140477 _140478 : Type'} (_98692 : type2 _140476 _140477 _140478) : (term198 _140476 _140477 _140478 _98692) = ((term38 _140476 _140477 _140478 _98692) = _98692).
Proof. exact (eq_refl (term198 _140476 _140477 _140478 _98692)). Qed.
Lemma lem7663637 {_140476 _140477 _140478 : Type'} (_98693 : cart _140476 _140477) (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term199 _140476 _140477 _140478 P _98693.
Proof. exact (@lem7663519 _140476 _140477 _140478 p P h1 _98693). Qed.
Lemma lem7663638 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98693 : cart _140476 _140477) : (term199 _140476 _140477 _140478 P _98693) = (term90 _140476 _140477 _140478 P _98693).
Proof. exact (eq_refl (term199 _140476 _140477 _140478 P _98693)). Qed.
Lemma lem7663639 {_140476 _140477 _140478 : Type'} (_98693 : cart _140476 _140477) (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term90 _140476 _140477 _140478 P _98693.
Proof. exact (EQ_MP (@lem7663638 _140476 _140477 _140478 P _98693) (@lem7663637 _140476 _140477 _140478 _98693 p P h1)). Qed.
Lemma lem7663640 {_140476 _140477 _140478 : Type'} (_98693 : cart _140476 _140477) (_98694 : cart _140476 _140478) (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term200 _140476 _140477 _140478 P _98693 _98694.
Proof. exact (@lem7663639 _140476 _140477 _140478 _98693 p P h1 _98694). Qed.
Lemma lem7663641 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98693 : cart _140476 _140477) (_98694 : cart _140476 _140478) : (term200 _140476 _140477 _140478 P _98693 _98694) = (term87 _140476 _140477 _140478 P _98693 _98694).
Proof. exact (eq_refl (term200 _140476 _140477 _140478 P _98693 _98694)). Qed.
Lemma lem7663682 {_140476 _140477 _140478 : Type'} (_98708 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term201 _140476 _140477 _140478 P _98708.
Proof. exact (@lem7663593 _140476 _140477 _140478 P x y h1 _98708). Qed.
Lemma lem7663683 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98708 : type2 _140476 _140477 _140478) : (term201 _140476 _140477 _140478 P _98708) = (term78 _140476 _140477 _140478 P _98708).
Proof. exact (eq_refl (term201 _140476 _140477 _140478 P _98708)). Qed.
Lemma lem7663702 {_140476 _140477 _140478 : Type'} (_98693 : cart _140476 _140477) (_98694 : cart _140476 _140478) (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term87 _140476 _140477 _140478 P _98693 _98694.
Proof. exact (EQ_MP (@lem7663641 _140476 _140477 _140478 P _98693 _98694) (@lem7663640 _140476 _140477 _140478 _98693 _98694 p P h1)). Qed.
Lemma lem7663718 {_140476 _140477 _140478 : Type'} (_98708 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term78 _140476 _140477 _140478 P _98708.
Proof. exact (EQ_MP (@lem7663683 _140476 _140477 _140478 P _98708) (@lem7663682 _140476 _140477 _140478 _98708 P x y h1)). Qed.
Lemma lem7663721 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem7663722 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) (h1 : _98709 = _98710) : _98709 = _98710.
Proof. exact (h1). Qed.
Lemma lem7663723 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) (h1 : _98709 = _98710) : (P _98709) = (P _98710).
Proof. exact (MK_COMB (@lem7663721 _140476 _140477 _140478 P) (@lem7663722 _140476 _140477 _140478 _98709 _98710 h1)). Qed.
Lemma lem7663725 (b : Prop) (a : Prop) : term202 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem7663726 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : term203 _140476 _140477 _140478 _98710 P _98709.
Proof. exact (@lem7663725 (P _98710) (P _98709)). Qed.
Lemma lem7663727 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) (h1 : _98709 = _98710) : term204 _140476 _140477 _140478 _98710 P _98709.
Proof. exact (@lem7663726 _140476 _140477 _140478 _98710 P _98709 (@lem7663723 _140476 _140477 _140478 P _98709 _98710 h1)). Qed.
Lemma lem7663728 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : term205 _140476 _140477 _140478 _98710 P _98709.
Proof. exact (fun h0 : _98709 = _98710 => @lem7663727 _140476 _140477 _140478 P _98709 _98710 h0). Qed.
Lemma lem7663730 (a : Prop) (b : Prop) : (a -> b) = (term206 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem7663731 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term205 _140476 _140477 _140478 _98710 P _98709) = (term207 _140476 _140477 _140478 _98710 P _98709).
Proof. exact (@lem7663730 (_98709 = _98710) (term204 _140476 _140477 _140478 _98710 P _98709)). Qed.
Lemma lem7663732 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : term207 _140476 _140477 _140478 _98710 P _98709.
Proof. exact (EQ_MP (@lem7663731 _140476 _140477 _140478 _98710 P _98709) (@lem7663728 _140476 _140477 _140478 _98710 P _98709)). Qed.
Lemma lem7663844 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : term208 _140476 _140477 _140478 x y z.
Proof. exact (@lem21385 (type2 _140476 _140477 _140478) x y z). Qed.
Lemma lem7663858 {_140476 _140477 _140478 : Type'} (_98692 : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : (term38 _140476 _140477 _140478 _98692) = _98692.
Proof. exact (EQ_MP (@lem7663635 _140476 _140477 _140478 _98692) (@lem7663634 _140476 _140477 _140478 _98692 h1)). Qed.
Lemma lem7663859 {_140476 _140477 _140478 : Type'} (_98692 : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : (term38 _140476 _140477 _140478 _98692) = _98692.
Proof. exact (@lem7663858 _140476 _140477 _140478 _98692 h1). Qed.
Lemma lem7663860 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : (term38 _140476 _140477 _140478 p) = p.
Proof. exact (@lem7663859 _140476 _140477 _140478 p h1). Qed.
Lemma lem7663861 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : term209 _140476 _140477 _140478 p.
Proof. exact (fun h0 : term210 _140476 _140477 _140478 p => @lem7663860 _140476 _140477 _140478 p h1). Qed.
Lemma lem7663863 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7663864 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) : (term209 _140476 _140477 _140478 p) = ((term38 _140476 _140477 _140478 p) = p).
Proof. exact (@lem7663863 ((term38 _140476 _140477 _140478 p) = p)). Qed.
Lemma lem7663865 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : (term38 _140476 _140477 _140478 p) = p.
Proof. exact (EQ_MP (@lem7663864 _140476 _140477 _140478 p) (@lem7663861 _140476 _140477 _140478 p h1)). Qed.
Lemma lem7663867 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) : x = x.
Proof. exact (@lem21386 (type2 _140476 _140477 _140478) x). Qed.
Lemma lem7663868 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) : x = x.
Proof. exact (@lem7663867 _140476 _140477 _140478 x). Qed.
Lemma lem7663869 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) : (term38 _140476 _140477 _140478 p) = (term38 _140476 _140477 _140478 p).
Proof. exact (@lem7663868 _140476 _140477 _140478 (term38 _140476 _140477 _140478 p)). Qed.
Lemma lem7663870 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) : term212 _140476 _140477 _140478 p.
Proof. exact (fun h0 : term213 _140476 _140477 _140478 p => @lem7663869 _140476 _140477 _140478 p). Qed.
Lemma lem7663872 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7663873 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) : (term212 _140476 _140477 _140478 p) = ((term38 _140476 _140477 _140478 p) = (term38 _140476 _140477 _140478 p)).
Proof. exact (@lem7663872 ((term38 _140476 _140477 _140478 p) = (term38 _140476 _140477 _140478 p))). Qed.
Lemma lem7663874 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) : (term38 _140476 _140477 _140478 p) = (term38 _140476 _140477 _140478 p).
Proof. exact (EQ_MP (@lem7663873 _140476 _140477 _140478 p) (@lem7663870 _140476 _140477 _140478 p)). Qed.
Lemma lem7663892 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7663893 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term214 _140476 _140477 _140478 x y z) = (term215 _140476 _140477 _140478 y x z).
Proof. exact (@lem7663892 (y = z) (term216 _140476 _140477 _140478 x z)). Qed.
Lemma lem7663903 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) : (term217 _140476 _140477 _140478 x y) = (term217 _140476 _140477 _140478 x y).
Proof. exact (eq_refl (term217 _140476 _140477 _140478 x y)). Qed.
Lemma lem7663904 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term208 _140476 _140477 _140478 x y z) = (term218 _140476 _140477 _140478 y x z).
Proof. exact (MK_COMB (@lem7663903 _140476 _140477 _140478 x y) (@lem7663893 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663908 (q : Prop) (p : Prop) (r : Prop) : (term219 p q r) = (term219 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7663909 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term218 _140476 _140477 _140478 y x z) = (term220 _140476 _140477 _140478 y x z).
Proof. exact (@lem7663908 (y = z) (term216 _140476 _140477 _140478 x y) (term216 _140476 _140477 _140478 x z)). Qed.
Lemma lem7663931 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term208 _140476 _140477 _140478 x y z) = (term220 _140476 _140477 _140478 y x z).
Proof. exact (TRANS (@lem7663904 _140476 _140477 _140478 y x z) (@lem7663909 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7663933 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term221 _140476 _140477 _140478 x y z) = (term222 _140476 _140477 _140478 y x z).
Proof. exact (MK_COMB (@lem7663932) (@lem7663931 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663955 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term220 _140476 _140477 _140478 y x z) = (term220 _140476 _140477 _140478 y x z).
Proof. exact (eq_refl (term220 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663956 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : ((term208 _140476 _140477 _140478 x y z) = (term220 _140476 _140477 _140478 y x z)) = ((term220 _140476 _140477 _140478 y x z) = (term220 _140476 _140477 _140478 y x z)).
Proof. exact (MK_COMB (@lem7663933 _140476 _140477 _140478 y x z) (@lem7663955 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663958 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7663959 (x : Prop) : (x = x) = True.
Proof. exact (@lem7663958 Prop x). Qed.
Lemma lem7663960 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : ((term220 _140476 _140477 _140478 y x z) = (term220 _140476 _140477 _140478 y x z)) = True.
Proof. exact (@lem7663959 (term220 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663961 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : ((term208 _140476 _140477 _140478 x y z) = (term220 _140476 _140477 _140478 y x z)) = True.
Proof. exact (TRANS (@lem7663956 _140476 _140477 _140478 y x z) (@lem7663960 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663962 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : True = ((term208 _140476 _140477 _140478 x y z) = (term220 _140476 _140477 _140478 y x z)).
Proof. exact (SYM (@lem7663961 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663963 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term208 _140476 _140477 _140478 x y z) = (term220 _140476 _140477 _140478 y x z).
Proof. exact (EQ_MP (@lem7663962 _140476 _140477 _140478 y x z) (@lem0)). Qed.
Lemma lem7663964 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : term220 _140476 _140477 _140478 y x z.
Proof. exact (EQ_MP (@lem7663963 _140476 _140477 _140478 y x z) (@lem7663844 _140476 _140477 _140478 x y z)). Qed.
Lemma lem7663966 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7663967 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term220 _140476 _140477 _140478 y x z) = (term224 _140476 _140477 _140478 x y z).
Proof. exact (@lem7663966 (term225 _140476 _140477 _140478 y x z) (y = z)). Qed.
Lemma lem7663969 (a : Prop) (b : Prop) : (term226 a b) = (term227 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7663970 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term228 _140476 _140477 _140478 y x z) = (term229 _140476 _140477 _140478 y x z).
Proof. exact (@lem7663969 (term216 _140476 _140477 _140478 x y) (term216 _140476 _140477 _140478 x z)). Qed.
Lemma lem7663972 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7663973 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) : (term231 _140476 _140477 _140478 x y) = (x = y).
Proof. exact (@lem7663972 (x = y)). Qed.
Lemma lem7663974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7663975 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) : (term232 _140476 _140477 _140478 x y) = (term233 _140476 _140477 _140478 x y).
Proof. exact (MK_COMB (@lem7663974) (@lem7663973 _140476 _140477 _140478 x y)). Qed.
Lemma lem7663977 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7663978 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term231 _140476 _140477 _140478 x z) = (x = z).
Proof. exact (@lem7663977 (x = z)). Qed.
Lemma lem7663979 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term229 _140476 _140477 _140478 y x z) = (term234 _140476 _140477 _140478 y x z).
Proof. exact (MK_COMB (@lem7663975 _140476 _140477 _140478 x y) (@lem7663978 _140476 _140477 _140478 x z)). Qed.
Lemma lem7663980 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term228 _140476 _140477 _140478 y x z) = (term234 _140476 _140477 _140478 y x z).
Proof. exact (TRANS (@lem7663970 _140476 _140477 _140478 y x z) (@lem7663979 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663981 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7663982 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (x : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term235 _140476 _140477 _140478 y x z) = (term236 _140476 _140477 _140478 y x z).
Proof. exact (MK_COMB (@lem7663981) (@lem7663980 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663983 {_140476 _140477 _140478 : Type'} (y : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem7663984 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term224 _140476 _140477 _140478 x y z) = (term237 _140476 _140477 _140478 x y z).
Proof. exact (MK_COMB (@lem7663982 _140476 _140477 _140478 y x z) (@lem7663983 _140476 _140477 _140478 y z)). Qed.
Lemma lem7663985 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : (term220 _140476 _140477 _140478 y x z) = (term237 _140476 _140477 _140478 x y z).
Proof. exact (TRANS (@lem7663967 _140476 _140477 _140478 x y z) (@lem7663984 _140476 _140477 _140478 x y z)). Qed.
Lemma lem7663987 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : term238 _140476 _140477 _140478 p.
Proof. exact (conj (@lem7663865 _140476 _140477 _140478 p h1) (@lem7663874 _140476 _140477 _140478 p)). Qed.
Lemma lem7663989 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : term237 _140476 _140477 _140478 x y z.
Proof. exact (EQ_MP (@lem7663985 _140476 _140477 _140478 x y z) (@lem7663964 _140476 _140477 _140478 y x z)). Qed.
Lemma lem7663990 {_140476 _140477 _140478 : Type'} (x : type2 _140476 _140477 _140478) (y : type2 _140476 _140477 _140478) (z : type2 _140476 _140477 _140478) : term237 _140476 _140477 _140478 x y z.
Proof. exact (@lem7663989 _140476 _140477 _140478 x y z). Qed.
Lemma lem7663991 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) : term239 _140476 _140477 _140478 p.
Proof. exact (@lem7663990 _140476 _140477 _140478 (term38 _140476 _140477 _140478 p) p (term38 _140476 _140477 _140478 p)). Qed.
Lemma lem7663994 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : p = (term38 _140476 _140477 _140478 p).
Proof. exact (@lem7663991 _140476 _140477 _140478 p (@lem7663987 _140476 _140477 _140478 p h1)). Qed.
Lemma lem7663995 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : p = (term38 _140476 _140477 _140478 p).
Proof. exact (@lem7663994 _140476 _140477 _140478 p h1). Qed.
Lemma lem7663996 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : term240 _140476 _140477 _140478 p.
Proof. exact (fun h0 : term241 _140476 _140477 _140478 p => @lem7663995 _140476 _140477 _140478 p h1). Qed.
Lemma lem7663998 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7663999 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) : (term240 _140476 _140477 _140478 p) = (p = (term38 _140476 _140477 _140478 p)).
Proof. exact (@lem7663998 (p = (term38 _140476 _140477 _140478 p))). Qed.
Lemma lem7664000 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) : p = (term38 _140476 _140477 _140478 p).
Proof. exact (EQ_MP (@lem7663999 _140476 _140477 _140478 p) (@lem7663996 _140476 _140477 _140478 p h1)). Qed.
Lemma lem7664002 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : P p.
Proof. exact (proj1 (@lem7663433 _140476 _140477 _140478 p P h1)). Qed.
Lemma lem7664003 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term242 _140476 _140477 _140478 P p.
Proof. exact (fun h0 : term78 _140476 _140477 _140478 P p => @lem7664002 _140476 _140477 _140478 p P h1). Qed.
Lemma lem7664005 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7664006 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (term242 _140476 _140477 _140478 P p) = (P p).
Proof. exact (@lem7664005 (P p)). Qed.
Lemma lem7664007 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : P p.
Proof. exact (EQ_MP (@lem7664006 _140476 _140477 _140478 P p) (@lem7664003 _140476 _140477 _140478 p P h1)). Qed.
Lemma lem7664013 (q : Prop) (p : Prop) (r : Prop) : (term219 p q r) = (term219 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem7664014 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term207 _140476 _140477 _140478 _98710 P _98709) = (term243 _140476 _140477 _140478 _98710 P _98709).
Proof. exact (@lem7664013 (P _98710) (term216 _140476 _140477 _140478 _98709 _98710) (term78 _140476 _140477 _140478 P _98709)). Qed.
Lemma lem7664028 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7664029 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term244 _140476 _140477 _140478 _98710 P _98709) = (term245 _140476 _140477 _140478 P _98709 _98710).
Proof. exact (@lem7664028 (term78 _140476 _140477 _140478 P _98709) (term216 _140476 _140477 _140478 _98709 _98710)). Qed.
Lemma lem7664037 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term246 _140476 _140477 _140478 P _98710) = (term246 _140476 _140477 _140478 P _98710).
Proof. exact (eq_refl (term246 _140476 _140477 _140478 P _98710)). Qed.
Lemma lem7664038 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term243 _140476 _140477 _140478 _98710 P _98709) = (term247 _140476 _140477 _140478 P _98709 _98710).
Proof. exact (MK_COMB (@lem7664037 _140476 _140477 _140478 P _98710) (@lem7664029 _140476 _140477 _140478 P _98709 _98710)). Qed.
Lemma lem7664049 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term207 _140476 _140477 _140478 _98710 P _98709) = (term247 _140476 _140477 _140478 P _98709 _98710).
Proof. exact (TRANS (@lem7664014 _140476 _140477 _140478 _98710 P _98709) (@lem7664038 _140476 _140477 _140478 P _98709 _98710)). Qed.
Lemma lem7664050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7664051 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term248 _140476 _140477 _140478 _98710 P _98709) = (term249 _140476 _140477 _140478 P _98709 _98710).
Proof. exact (MK_COMB (@lem7664050) (@lem7664049 _140476 _140477 _140478 P _98709 _98710)). Qed.
Lemma lem7664065 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7664066 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term244 _140476 _140477 _140478 _98710 P _98709) = (term245 _140476 _140477 _140478 P _98709 _98710).
Proof. exact (@lem7664065 (term78 _140476 _140477 _140478 P _98709) (term216 _140476 _140477 _140478 _98709 _98710)). Qed.
Lemma lem7664074 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term246 _140476 _140477 _140478 P _98710) = (term246 _140476 _140477 _140478 P _98710).
Proof. exact (eq_refl (term246 _140476 _140477 _140478 P _98710)). Qed.
Lemma lem7664075 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term243 _140476 _140477 _140478 _98710 P _98709) = (term247 _140476 _140477 _140478 P _98709 _98710).
Proof. exact (MK_COMB (@lem7664074 _140476 _140477 _140478 P _98710) (@lem7664066 _140476 _140477 _140478 P _98709 _98710)). Qed.
Lemma lem7664086 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : ((term207 _140476 _140477 _140478 _98710 P _98709) = (term243 _140476 _140477 _140478 _98710 P _98709)) = ((term247 _140476 _140477 _140478 P _98709 _98710) = (term247 _140476 _140477 _140478 P _98709 _98710)).
Proof. exact (MK_COMB (@lem7664051 _140476 _140477 _140478 P _98709 _98710) (@lem7664075 _140476 _140477 _140478 P _98709 _98710)). Qed.
Lemma lem7664088 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7664089 (x : Prop) : (x = x) = True.
Proof. exact (@lem7664088 Prop x). Qed.
Lemma lem7664090 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : ((term247 _140476 _140477 _140478 P _98709 _98710) = (term247 _140476 _140477 _140478 P _98709 _98710)) = True.
Proof. exact (@lem7664089 (term247 _140476 _140477 _140478 P _98709 _98710)). Qed.
Lemma lem7664091 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : ((term207 _140476 _140477 _140478 _98710 P _98709) = (term243 _140476 _140477 _140478 _98710 P _98709)) = True.
Proof. exact (TRANS (@lem7664086 _140476 _140477 _140478 P _98709 _98710) (@lem7664090 _140476 _140477 _140478 P _98709 _98710)). Qed.
Lemma lem7664092 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : True = ((term207 _140476 _140477 _140478 _98710 P _98709) = (term243 _140476 _140477 _140478 _98710 P _98709)).
Proof. exact (SYM (@lem7664091 _140476 _140477 _140478 _98710 P _98709)). Qed.
Lemma lem7664093 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term207 _140476 _140477 _140478 _98710 P _98709) = (term243 _140476 _140477 _140478 _98710 P _98709).
Proof. exact (EQ_MP (@lem7664092 _140476 _140477 _140478 _98710 P _98709) (@lem0)). Qed.
Lemma lem7664094 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : term243 _140476 _140477 _140478 _98710 P _98709.
Proof. exact (EQ_MP (@lem7664093 _140476 _140477 _140478 _98710 P _98709) (@lem7663732 _140476 _140477 _140478 _98710 P _98709)). Qed.
Lemma lem7664096 (b : Prop) (a : Prop) : (a \/ b) = (term223 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7664097 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term243 _140476 _140477 _140478 _98710 P _98709) = (term250 _140476 _140477 _140478 _98709 P _98710).
Proof. exact (@lem7664096 (term244 _140476 _140477 _140478 _98710 P _98709) (P _98710)). Qed.
Lemma lem7664099 (a : Prop) (b : Prop) : (term226 a b) = (term227 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem7664100 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term251 _140476 _140477 _140478 _98710 P _98709) = (term252 _140476 _140477 _140478 _98710 P _98709).
Proof. exact (@lem7664099 (term216 _140476 _140477 _140478 _98709 _98710) (term78 _140476 _140477 _140478 P _98709)). Qed.
Lemma lem7664102 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7664103 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term231 _140476 _140477 _140478 _98709 _98710) = (_98709 = _98710).
Proof. exact (@lem7664102 (_98709 = _98710)). Qed.
Lemma lem7664104 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664105 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term232 _140476 _140477 _140478 _98709 _98710) = (term233 _140476 _140477 _140478 _98709 _98710).
Proof. exact (MK_COMB (@lem7664104) (@lem7664103 _140476 _140477 _140478 _98709 _98710)). Qed.
Lemma lem7664107 (a : Prop) : (term230 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7664108 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term253 _140476 _140477 _140478 P _98709) = (P _98709).
Proof. exact (@lem7664107 (P _98709)). Qed.
Lemma lem7664109 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term252 _140476 _140477 _140478 _98710 P _98709) = (term254 _140476 _140477 _140478 _98710 P _98709).
Proof. exact (MK_COMB (@lem7664105 _140476 _140477 _140478 _98709 _98710) (@lem7664108 _140476 _140477 _140478 P _98709)). Qed.
Lemma lem7664110 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term251 _140476 _140477 _140478 _98710 P _98709) = (term254 _140476 _140477 _140478 _98710 P _98709).
Proof. exact (TRANS (@lem7664100 _140476 _140477 _140478 _98710 P _98709) (@lem7664109 _140476 _140477 _140478 _98710 P _98709)). Qed.
Lemma lem7664111 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7664112 {_140476 _140477 _140478 : Type'} (_98710 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98709 : type2 _140476 _140477 _140478) : (term255 _140476 _140477 _140478 _98710 P _98709) = (term256 _140476 _140477 _140478 _98710 P _98709).
Proof. exact (MK_COMB (@lem7664111) (@lem7664110 _140476 _140477 _140478 _98710 P _98709)). Qed.
Lemma lem7664113 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (P _98710) = (P _98710).
Proof. exact (eq_refl (P _98710)). Qed.
Lemma lem7664114 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term250 _140476 _140477 _140478 _98709 P _98710) = (term257 _140476 _140477 _140478 _98709 P _98710).
Proof. exact (MK_COMB (@lem7664112 _140476 _140477 _140478 _98710 P _98709) (@lem7664113 _140476 _140477 _140478 P _98710)). Qed.
Lemma lem7664115 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : (term243 _140476 _140477 _140478 _98710 P _98709) = (term257 _140476 _140477 _140478 _98709 P _98710).
Proof. exact (TRANS (@lem7664097 _140476 _140477 _140478 _98709 P _98710) (@lem7664114 _140476 _140477 _140478 _98709 P _98710)). Qed.
Lemma lem7664117 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : term258 _140476 _140477 _140478 P p.
Proof. exact (conj (@lem7664000 _140476 _140477 _140478 p h1) (@lem7664007 _140476 _140477 _140478 p P h2)). Qed.
Lemma lem7664119 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : term257 _140476 _140477 _140478 _98709 P _98710.
Proof. exact (EQ_MP (@lem7664115 _140476 _140477 _140478 _98709 P _98710) (@lem7664094 _140476 _140477 _140478 _98710 P _98709)). Qed.
Lemma lem7664120 {_140476 _140477 _140478 : Type'} (_98709 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (_98710 : type2 _140476 _140477 _140478) : term257 _140476 _140477 _140478 _98709 P _98710.
Proof. exact (@lem7664119 _140476 _140477 _140478 _98709 P _98710). Qed.
Lemma lem7664121 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : term259 _140476 _140477 _140478 P p.
Proof. exact (@lem7664120 _140476 _140477 _140478 p P (term38 _140476 _140477 _140478 p)). Qed.
Lemma lem7664124 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : term260 _140476 _140477 _140478 P p.
Proof. exact (@lem7664121 _140476 _140477 _140478 P p (@lem7664117 _140476 _140477 _140478 p P h1 h2)). Qed.
Lemma lem7664125 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : term261 _140476 _140477 _140478 P p.
Proof. exact (fun h0 : term262 _140476 _140477 _140478 P p => @lem7664124 _140476 _140477 _140478 p P h1 h2). Qed.
Lemma lem7664127 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7664128 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (p : type2 _140476 _140477 _140478) : (term261 _140476 _140477 _140478 P p) = (term260 _140476 _140477 _140478 P p).
Proof. exact (@lem7664127 (term260 _140476 _140477 _140478 P p)). Qed.
Lemma lem7664129 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : term260 _140476 _140477 _140478 P p.
Proof. exact (EQ_MP (@lem7664128 _140476 _140477 _140478 P p) (@lem7664125 _140476 _140477 _140478 p P h1 h2)). Qed.
Lemma lem7664132 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7664134 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98693 : cart _140476 _140477) (_98694 : cart _140476 _140478) : (term87 _140476 _140477 _140478 P _98693 _98694) = (term263 _140476 _140477 _140478 P _98693 _98694).
Proof. exact (@lem7664132 (term64 _140476 _140477 _140478 P _98693 _98694)). Qed.
Lemma lem7664137 {_140476 _140477 _140478 : Type'} (_98693 : cart _140476 _140477) (_98694 : cart _140476 _140478) (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term263 _140476 _140477 _140478 P _98693 _98694.
Proof. exact (EQ_MP (@lem7664134 _140476 _140477 _140478 P _98693 _98694) (@lem7663702 _140476 _140477 _140478 _98693 _98694 p P h1)). Qed.
Lemma lem7664138 {_140476 _140477 _140478 : Type'} (_98693 : cart _140476 _140477) (_98694 : cart _140476 _140478) (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term263 _140476 _140477 _140478 P _98693 _98694.
Proof. exact (@lem7664137 _140476 _140477 _140478 _98693 _98694 p P h1). Qed.
Lemma lem7664139 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term152 _140476 _140477 _140478 p P) : term264 _140476 _140477 _140478 P p.
Proof. exact (@lem7664138 _140476 _140477 _140478 (@fstcart _140476 _140477 _140478 p) (@sndcart _140476 _140477 _140478 p) p P h1). Qed.
Lemma lem7664142 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : False.
Proof. exact (@lem7664139 _140476 _140477 _140478 p P h2 (@lem7664129 _140476 _140477 _140478 p P h1 h2)). Qed.
Lemma lem7664143 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : term265.
Proof. exact (fun h0 : ~ False => @lem7664142 _140476 _140477 _140478 p P h1 h2). Qed.
Lemma lem7664145 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7664146 : term265 = False.
Proof. exact (@lem7664145 False). Qed.
Lemma lem7664147 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : False.
Proof. exact (EQ_MP (@lem7664146) (@lem7664143 _140476 _140477 _140478 p P h1 h2)). Qed.
Lemma lem7664285 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term64 _140476 _140477 _140478 P x y.
Proof. exact (proj2 (@lem7663434 _140476 _140477 _140478 P x y h1)). Qed.
Lemma lem7664286 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term266 _140476 _140477 _140478 P x y.
Proof. exact (fun h0 : term87 _140476 _140477 _140478 P x y => @lem7664285 _140476 _140477 _140478 P x y h1). Qed.
Lemma lem7664288 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7664289 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) : (term266 _140476 _140477 _140478 P x y) = (term64 _140476 _140477 _140478 P x y).
Proof. exact (@lem7664288 (term64 _140476 _140477 _140478 P x y)). Qed.
Lemma lem7664290 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term64 _140476 _140477 _140478 P x y.
Proof. exact (EQ_MP (@lem7664289 _140476 _140477 _140478 P x y) (@lem7664286 _140476 _140477 _140478 P x y h1)). Qed.
Lemma lem7664293 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7664295 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (_98708 : type2 _140476 _140477 _140478) : (term78 _140476 _140477 _140478 P _98708) = (term267 _140476 _140477 _140478 P _98708).
Proof. exact (@lem7664293 (P _98708)). Qed.
Lemma lem7664298 {_140476 _140477 _140478 : Type'} (_98708 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term267 _140476 _140477 _140478 P _98708.
Proof. exact (EQ_MP (@lem7664295 _140476 _140477 _140478 P _98708) (@lem7663718 _140476 _140477 _140478 _98708 P x y h1)). Qed.
Lemma lem7664299 {_140476 _140477 _140478 : Type'} (_98708 : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term267 _140476 _140477 _140478 P _98708.
Proof. exact (@lem7664298 _140476 _140477 _140478 _98708 P x y h1). Qed.
Lemma lem7664300 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term263 _140476 _140477 _140478 P x y.
Proof. exact (@lem7664299 _140476 _140477 _140478 (@pastecart _140476 _140477 _140478 x y) P x y h1). Qed.
Lemma lem7664303 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : False.
Proof. exact (@lem7664300 _140476 _140477 _140478 P x y h1 (@lem7664290 _140476 _140477 _140478 P x y h1)). Qed.
Lemma lem7664304 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : term265.
Proof. exact (fun h0 : ~ False => @lem7664303 _140476 _140477 _140478 P x y h1). Qed.
Lemma lem7664306 (p : Prop) : (term211 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7664307 : term265 = False.
Proof. exact (@lem7664306 False). Qed.
Lemma lem7664308 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term137 _140476 _140477 _140478 P x y) : False.
Proof. exact (EQ_MP (@lem7664307) (@lem7664304 _140476 _140477 _140478 P x y h1)). Qed.
Lemma lem7664309 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : (term1 _140476 _140477 _140478) = False.
Proof. exact (prop_ext (fun h3 : term1 _140476 _140477 _140478 => @lem7664147 _140476 _140477 _140478 p P h1 h2) (fun h3 : False => @lem7663505 _140476 _140477 _140478 h1)). Qed.
Lemma lem7664310 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term152 _140476 _140477 _140478 p P) : False.
Proof. exact (EQ_MP (@lem7664309 _140476 _140477 _140478 p P h1 h2) (@lem7663505 _140476 _140477 _140478 h1)). Qed.
Lemma lem7664311 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term189 _140476 _140477 _140478 p P x y) : False.
Proof. exact (or_elim (@lem7663432 _140476 _140477 _140478 p P x y h2) (fun h0 : term152 _140476 _140477 _140478 p P => @lem7664310 _140476 _140477 _140478 p P h1 h0) (fun h0 : term137 _140476 _140477 _140478 P x y => @lem7664308 _140476 _140477 _140478 P x y h0)). Qed.
Lemma lem7664312 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term189 _140476 _140477 _140478 p P x y) : (term189 _140476 _140477 _140478 p P x y) = False.
Proof. exact (prop_ext (fun h3 : term189 _140476 _140477 _140478 p P x y => @lem7664311 _140476 _140477 _140478 p P x y h1 h2) (fun h3 : False => @lem7663432 _140476 _140477 _140478 p P x y h2)). Qed.
Lemma lem7664313 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term189 _140476 _140477 _140478 p P x y) : False.
Proof. exact (EQ_MP (@lem7664312 _140476 _140477 _140478 p P x y h1 h2) (@lem7663432 _140476 _140477 _140478 p P x y h2)). Qed.
Lemma lem7664314 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term189 _140476 _140477 _140478 p P x y) : (term1 _140476 _140477 _140478) = False.
Proof. exact (prop_ext (fun h3 : term1 _140476 _140477 _140478 => @lem7664313 _140476 _140477 _140478 p P x y h1 h2) (fun h3 : False => @lem7663389 _140476 _140477 _140478 h1)). Qed.
Lemma lem7664315 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (y : cart _140476 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term189 _140476 _140477 _140478 p P x y) : False.
Proof. exact (EQ_MP (@lem7664314 _140476 _140477 _140478 p P x y h1 h2) (@lem7663389 _140476 _140477 _140478 h1)). Qed.
Lemma lem7664316 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (x : cart _140476 _140477) (h1 : term1 _140476 _140477 _140478) (h2 : term192 _140476 _140477 _140478 p P x) : False.
Proof. exact (ex_elim (@lem7663263 _140476 _140477 _140478 p P x h2) (fun y : cart _140476 _140478 => fun h0 : term191 _140476 _140477 _140478 p P x y => @lem7664315 _140476 _140477 _140478 p P x y h1 h0)). Qed.
Lemma lem7664317 {_140476 _140477 _140478 : Type'} (p : type2 _140476 _140477 _140478) (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term194 _140476 _140477 _140478 p P) : False.
Proof. exact (ex_elim (@lem7663262 _140476 _140477 _140478 p P h2) (fun x : cart _140476 _140477 => fun h0 : term193 _140476 _140477 _140478 p P x => @lem7664316 _140476 _140477 _140478 p P x h1 h0)). Qed.
Lemma lem7664318 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term0 _140476 _140477 _140478 P) : False.
Proof. exact (ex_elim (@lem7663128 _140476 _140477 _140478 P h2) (fun p : type2 _140476 _140477 _140478 => fun h0 : term195 _140476 _140477 _140478 P p => @lem7664317 _140476 _140477 _140478 p P h1 h0)). Qed.
Lemma lem7664319 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term0 _140476 _140477 _140478 P) : (term1 _140476 _140477 _140478) = False.
Proof. exact (prop_ext (fun h3 : term1 _140476 _140477 _140478 => @lem7664318 _140476 _140477 _140478 P h1 h2) (fun h3 : False => @lem7663261 _140476 _140477 _140478 h1)). Qed.
Lemma lem7664320 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term1 _140476 _140477 _140478) (h2 : term0 _140476 _140477 _140478 P) : False.
Proof. exact (EQ_MP (@lem7664319 _140476 _140477 _140478 P h1 h2) (@lem7663261 _140476 _140477 _140478 h1)). Qed.
Lemma lem7664321 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term12 _140476 _140477 _140478.
Proof. exact (fun h0 : term1 _140476 _140477 _140478 => @lem7664320 _140476 _140477 _140478 P h0 h1). Qed.
Lemma lem7664322 {_140476 _140477 _140478 : Type'} : (term12 _140476 _140477 _140478) = (term13 _140476 _140477 _140478).
Proof. exact (@lem69 (term1 _140476 _140477 _140478)). Qed.
Lemma lem7664323 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term13 _140476 _140477 _140478.
Proof. exact (EQ_MP (@lem7664322 _140476 _140477 _140478) (@lem7664321 _140476 _140477 _140478 P h1)). Qed.
Lemma lem7664324 {_140476 _140477 _140478 N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term16 _140476 _140477 _140478 N.
Proof. exact (fun h0 : term2 _140476 _140477 _140478 N => @lem7664323 _140476 _140477 _140478 P h1). Qed.
Lemma lem7664325 {_140476 _140477 _140478 N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term19 _140476 _140477 _140478 N.
Proof. exact (fun h0 : term3 _140476 _140477 _140478 => @lem7664324 _140476 _140477 _140478 N P h1). Qed.
Lemma lem7664326 {_140476 _140477 _140478 N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term22 _140476 _140477 _140478 N.
Proof. exact (fun h0 : term7 _140476 _140477 _140478 N => @lem7664325 _140476 _140477 _140478 N P h1). Qed.
Lemma lem7664327 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term25 _140476 _140477 _140478 M N.
Proof. exact (fun h0 : term4 _140476 _140477 _140478 M => @lem7664326 _140476 _140477 _140478 N P h1). Qed.
Lemma lem7664328 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term28 _140476 _140477 _140478 M N.
Proof. exact (fun h0 : term5 _140476 _140477 M => @lem7664327 _140476 _140477 _140478 M N P h1). Qed.
Lemma lem7664329 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term31 _140476 _140477 _140478 M N.
Proof. exact (fun h0 : term6 _140476 _140477 _140478 => @lem7664328 _140476 _140477 _140478 M N P h1). Qed.
Lemma lem7664330 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term33 _140476 _140477 _140478 M N P.
Proof. exact (fun h0 : term0 _140476 _140477 _140478 P => @lem7664329 _140476 _140477 _140478 M N P h0). Qed.
Lemma lem7664335 {_140476 _140477 _140478 M N : Type'} : term37 _140476 _140477 _140478 M N.
Proof. exact (fun P : type16 _140476 _140477 _140478 => @lem7664330 _140476 _140477 _140478 M N P). Qed.
Lemma lem7664336 {_140476 _140477 _140478 M N : Type'} : term36 _140476 _140477 _140478 M N.
Proof. exact (EQ_MP (@lem7662912 _140476 _140477 _140478 M N) (@lem7664335 _140476 _140477 _140478 M N)). Qed.
Lemma lem7664337 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term268 _140476 _140477 _140478 M N P.
Proof. exact (@lem7664336 _140476 _140477 _140478 M N P). Qed.
Lemma lem7664338 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : (term268 _140476 _140477 _140478 M N P) = (term8 _140476 _140477 _140478 M N P).
Proof. exact (eq_refl (term268 _140476 _140477 _140478 M N P)). Qed.
Lemma lem7664339 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term8 _140476 _140477 _140478 M N P.
Proof. exact (EQ_MP (@lem7664338 _140476 _140477 _140478 M N P) (@lem7664337 _140476 _140477 _140478 M N P)). Qed.
Lemma lem7664341 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) : term8 _140476 _140477 _140478 M N P.
Proof. exact (@lem7662580 _140476 _140477 _140478 M N P (@lem7664339 _140476 _140477 _140478 M N P)). Qed.
Lemma lem7664342 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term30 _140476 _140477 _140478 M N.
Proof. exact (@lem7664341 _140476 _140477 _140478 M N P (@lem7662555 _140476 _140477 _140478 P h1)). Qed.
Lemma lem7664343 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term27 _140476 _140477 _140478 M N.
Proof. exact (@lem7664342 _140476 _140477 _140478 M N P h1 (@lem7662562 _140476 _140477 _140478)). Qed.
Lemma lem7664344 {_140476 _140477 _140478 M N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term24 _140476 _140477 _140478 M N.
Proof. exact (@lem7664343 _140476 _140477 _140478 M N P h1 (@lem7662561 _140476 _140477 M)). Qed.
Lemma lem7664345 {_140476 _140477 _140478 N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term21 _140476 _140477 _140478 N.
Proof. exact (@lem7664344 _140476 _140477 _140478 Prop N P h1 (@lem7662560 _140476 _140477 _140478 Prop)). Qed.
Lemma lem7664346 {_140476 _140477 _140478 N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term18 _140476 _140477 _140478 N.
Proof. exact (@lem7664345 _140476 _140477 _140478 N P h1 (@lem7662564 _140476 _140477 _140478 N)). Qed.
Lemma lem7664347 {_140476 _140477 _140478 N : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term15 _140476 _140477 _140478 N.
Proof. exact (@lem7664346 _140476 _140477 _140478 N P h1 (@lem7662558 _140476 _140477 _140478)). Qed.
Lemma lem7664348 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : term12 _140476 _140477 _140478.
Proof. exact (@lem7664347 _140476 _140477 _140478 Prop P h1 (@lem7662557 _140476 _140477 _140478 Prop)). Qed.
Lemma lem7664349 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : False.
Proof. exact (@lem7664348 _140476 _140477 _140478 P h1 (@lem7662556 _140476 _140477 _140478)). Qed.
Lemma lem7664350 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : (term0 _140476 _140477 _140478 P) = False.
Proof. exact (prop_ext (fun h2 : term0 _140476 _140477 _140478 P => @lem7664349 _140476 _140477 _140478 P h1) (fun h2 : False => @lem7662555 _140476 _140477 _140478 P h1)). Qed.
Lemma lem7664351 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) (h1 : term0 _140476 _140477 _140478 P) : False.
Proof. exact (EQ_MP (@lem7664350 _140476 _140477 _140478 P h1) (@lem7662555 _140476 _140477 _140478 P h1)). Qed.
Lemma lem7664352 {_140476 _140477 _140478 : Type'} (P : type16 _140476 _140477 _140478) : term269 _140476 _140477 _140478 P.
Proof. exact (fun h0 : term0 _140476 _140477 _140478 P => @lem7664351 _140476 _140477 _140478 P h0). Qed.
