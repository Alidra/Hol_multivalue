Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110669_term_abbrevs.
Require Import thm1110222_spec.
Require Import thm1110612_spec.
Lemma lem1110613 {A : Type'} : (term0 A) = (term1 A).
Proof. exact (eq_refl (term0 A)). Qed.
Lemma lem1110614 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem1110613 A) (@lem1110222 A)). Qed.
Lemma lem1110615 {A : Type'} : term2 A.
Proof. exact (@lem1110614 A term3). Qed.
Lemma lem1110616 {A : Type'} : (term2 A) = (term4 A).
Proof. exact (eq_refl (term2 A)). Qed.
Lemma lem1110617 {A : Type'} : term4 A.
Proof. exact (EQ_MP (@lem1110616 A) (@lem1110615 A)). Qed.
Lemma lem1110618 {A : Type'} (h1 : (@List.ForallOrdPairs A) = (term5 A)) : (@List.ForallOrdPairs A) = (term5 A).
Proof. exact (h1). Qed.
Lemma lem1110619 {A : Type'} (h1 : (@List.ForallOrdPairs A) = (term5 A)) : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (SYM (@lem1110618 A h1)). Qed.
Lemma lem1110620 {A : Type'} (h1 : (term5 A) = (@List.ForallOrdPairs A)) : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (h1). Qed.
Lemma lem1110621 {A : Type'} (h1 : (term5 A) = (@List.ForallOrdPairs A)) : (@List.ForallOrdPairs A) = (term5 A).
Proof. exact (SYM (@lem1110620 A h1)). Qed.
Lemma lem1110622 {A : Type'} : ((@List.ForallOrdPairs A) = (term5 A)) = ((term5 A) = (@List.ForallOrdPairs A)).
Proof. exact (prop_ext (fun h1 : (@List.ForallOrdPairs A) = (term5 A) => @lem1110619 A h1) (fun h1 : (term5 A) = (@List.ForallOrdPairs A) => @lem1110621 A h1)). Qed.
Lemma lem1110625 {A : Type'} : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (EQ_MP (@lem1110622 A) (@lem1110612 A)). Qed.
Lemma lem1110626 {A : Type'} : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (@lem1110625 A). Qed.
Lemma lem1110627 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110628 {A : Type'} (r : type1402 A) : (term6 A r) = (@List.ForallOrdPairs A r).
Proof. exact (MK_COMB (@lem1110626 A) (@lem1110627 A r)). Qed.
Lemma lem1110629 {A : Type'} : (@nil A) = (@nil A).
Proof. exact (eq_refl (@nil A)). Qed.
Lemma lem1110630 {A : Type'} (r : type1402 A) : (term7 A r) = (@List.ForallOrdPairs A r (@nil A)).
Proof. exact (MK_COMB (@lem1110628 A r) (@lem1110629 A)). Qed.
Lemma lem1110631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110632 {A : Type'} (r : type1402 A) : (term8 A r) = (term9 A r).
Proof. exact (MK_COMB (@lem1110631) (@lem1110630 A r)). Qed.
Lemma lem1110633 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem1110634 {A : Type'} (r : type1402 A) : ((term7 A r) = True) = ((@List.ForallOrdPairs A r (@nil A)) = True).
Proof. exact (MK_COMB (@lem1110632 A r) (@lem1110633)). Qed.
Lemma lem1110635 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (fun_ext (fun r : type1402 A => @lem1110634 A r)). Qed.
Lemma lem1110636 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1110637 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (MK_COMB (@lem1110636 A) (@lem1110635 A)). Qed.
Lemma lem1110638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1110639 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem1110638) (@lem1110637 A)). Qed.
Lemma lem1110641 {A : Type'} : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (EQ_MP (@lem1110622 A) (@lem1110612 A)). Qed.
Lemma lem1110642 {A : Type'} : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (@lem1110641 A). Qed.
Lemma lem1110643 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110644 {A : Type'} (r : type1402 A) : (term6 A r) = (@List.ForallOrdPairs A r).
Proof. exact (MK_COMB (@lem1110642 A) (@lem1110643 A r)). Qed.
Lemma lem1110645 {A : Type'} (h : A) (t : list A) : (@cons A h t) = (@cons A h t).
Proof. exact (eq_refl (@cons A h t)). Qed.
Lemma lem1110646 {A : Type'} (r : type1402 A) (h : A) (t : list A) : (term16 A r h t) = (term17 A r h t).
Proof. exact (MK_COMB (@lem1110644 A r) (@lem1110645 A h t)). Qed.
Lemma lem1110647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1110648 {A : Type'} (r : type1402 A) (h : A) (t : list A) : (term18 A r h t) = (term19 A r h t).
Proof. exact (MK_COMB (@lem1110647) (@lem1110646 A r h t)). Qed.
Lemma lem1110650 {A : Type'} : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (EQ_MP (@lem1110622 A) (@lem1110612 A)). Qed.
Lemma lem1110651 {A : Type'} : (term5 A) = (@List.ForallOrdPairs A).
Proof. exact (@lem1110650 A). Qed.
Lemma lem1110652 {A : Type'} (r : type1402 A) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem1110653 {A : Type'} (r : type1402 A) : (term6 A r) = (@List.ForallOrdPairs A r).
Proof. exact (MK_COMB (@lem1110651 A) (@lem1110652 A r)). Qed.
Lemma lem1110654 {A : Type'} (t : list A) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1110655 {A : Type'} (r : type1402 A) (t : list A) : (term20 A r t) = (@List.ForallOrdPairs A r t).
Proof. exact (MK_COMB (@lem1110653 A r) (@lem1110654 A t)). Qed.
Lemma lem1110656 {A : Type'} (r : type1402 A) (h : A) (t : list A) : (term21 A r h t) = (term21 A r h t).
Proof. exact (eq_refl (term21 A r h t)). Qed.
Lemma lem1110657 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term22 A h r t) = (term23 A h r t).
Proof. exact (MK_COMB (@lem1110656 A r h t) (@lem1110655 A r t)). Qed.
Lemma lem1110658 {A : Type'} (h : A) (r : type1402 A) (t : list A) : ((term16 A r h t) = (term22 A h r t)) = ((term17 A r h t) = (term23 A h r t)).
Proof. exact (MK_COMB (@lem1110648 A r h t) (@lem1110657 A h r t)). Qed.
Lemma lem1110659 {A : Type'} (h : A) (r : type1402 A) : (term24 A h r) = (term25 A h r).
Proof. exact (fun_ext (fun t : list A => @lem1110658 A h r t)). Qed.
Lemma lem1110660 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1110661 {A : Type'} (h : A) (r : type1402 A) : (term26 A h r) = (term27 A h r).
Proof. exact (MK_COMB (@lem1110660 A) (@lem1110659 A h r)). Qed.
Lemma lem1110662 {A : Type'} (h : A) : (term28 A h) = (term29 A h).
Proof. exact (fun_ext (fun r : type1402 A => @lem1110661 A h r)). Qed.
Lemma lem1110663 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1110664 {A : Type'} (h : A) : (term30 A h) = (term31 A h).
Proof. exact (MK_COMB (@lem1110663 A) (@lem1110662 A h)). Qed.
Lemma lem1110665 {A : Type'} : (term32 A) = (term33 A).
Proof. exact (fun_ext (fun h : A => @lem1110664 A h)). Qed.
Lemma lem1110666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1110667 {A : Type'} : (term34 A) = (term35 A).
Proof. exact (MK_COMB (@lem1110666 A) (@lem1110665 A)). Qed.
Lemma lem1110668 {A : Type'} : (term4 A) = (term36 A).
Proof. exact (MK_COMB (@lem1110639 A) (@lem1110667 A)). Qed.
Lemma lem1110669 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem1110668 A) (@lem1110617 A)). Qed.
