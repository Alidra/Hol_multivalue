Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_INTERS_term_abbrevs.
Require Import DISJ_ACI_spec.
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
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3458971_spec.
Require Import thm3458974_spec.
Lemma lem3470580 {_89520 _89534 : Type'} : term0 _89520 _89534.
Proof. exact (EQ_MP (@lem3458974 _89520 _89534) (@lem3458971 _89520 _89534)). Qed.
Lemma lem3470581 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term1 _89520 _89534 P.
Proof. exact (@lem3470580 _89520 _89534 P). Qed.
Lemma lem3470582 {_89520 _89534 : Type'} (P : _89534 -> Prop) : (term1 _89520 _89534 P) = (term2 _89520 _89534 P).
Proof. exact (eq_refl (term1 _89520 _89534 P)). Qed.
Lemma lem3470583 {_89520 _89534 : Type'} (P : _89534 -> Prop) : term2 _89520 _89534 P.
Proof. exact (EQ_MP (@lem3470582 _89520 _89534 P) (@lem3470581 _89520 _89534 P)). Qed.
Lemma lem3470584 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : term3 _89520 _89534 P f.
Proof. exact (@lem3470583 _89520 _89534 P f). Qed.
Lemma lem3470585 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term3 _89520 _89534 P f) = ((term4 _89520 _89534 P f) = (term5 _89520 _89534 P f)).
Proof. exact (eq_refl (term3 _89520 _89534 P f)). Qed.
Lemma lem3470598 {_89520 _89534 : Type'} (P : _89534 -> Prop) (f : type1470 _89520 _89534) : (term4 _89520 _89534 P f) = (term5 _89520 _89534 P f).
Proof. exact (EQ_MP (@lem3470585 _89520 _89534 P f) (@lem3470584 _89520 _89534 P f)). Qed.
Lemma lem3470599 {_90037 : Type'} (P : type686 _90037) (f : type672 _90037) : (term6 _90037 P f) = (term7 _90037 P f).
Proof. exact (@lem3470598 _90037 (_90037 -> Prop) P f). Qed.
Lemma lem3470600 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term8 _90037 s u) = (term9 _90037 s u).
Proof. exact (@lem3470599 _90037 (term10 _90037 s) (term11 _90037 u)). Qed.
Lemma lem3470601 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) : (term12 _90037 s t) = (@IN (_90037 -> Prop) t s).
Proof. exact (eq_refl (term12 _90037 s t)). Qed.
Lemma lem3470602 {_90037 : Type'} (GEN_PVAR_64 : _90037 -> Prop) : (@SETSPEC (_90037 -> Prop) GEN_PVAR_64) = (@SETSPEC (_90037 -> Prop) GEN_PVAR_64).
Proof. exact (eq_refl (@SETSPEC (_90037 -> Prop) GEN_PVAR_64)). Qed.
Lemma lem3470603 {_90037 : Type'} (GEN_PVAR_64 : _90037 -> Prop) (t : _90037 -> Prop) (s : type686 _90037) : (term13 _90037 GEN_PVAR_64 s t) = (term14 _90037 GEN_PVAR_64 t s).
Proof. exact (MK_COMB (@lem3470602 _90037 GEN_PVAR_64) (@lem3470601 _90037 t s)). Qed.
Lemma lem3470604 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) : (term15 _90037 u t) = (@DIFF _90037 u t).
Proof. exact (eq_refl (term15 _90037 u t)). Qed.
Lemma lem3470605 {_90037 : Type'} (GEN_PVAR_64 : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) : (term16 _90037 GEN_PVAR_64 s u t) = (term17 _90037 GEN_PVAR_64 s u t).
Proof. exact (MK_COMB (@lem3470603 _90037 GEN_PVAR_64 t s) (@lem3470604 _90037 u t)). Qed.
Lemma lem3470606 {_90037 : Type'} (GEN_PVAR_64 : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) : (term18 _90037 GEN_PVAR_64 s u) = (term19 _90037 GEN_PVAR_64 s u).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3470605 _90037 GEN_PVAR_64 s u t)). Qed.
Lemma lem3470607 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3470608 {_90037 : Type'} (GEN_PVAR_64 : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) : (term20 _90037 GEN_PVAR_64 s u) = (term21 _90037 GEN_PVAR_64 s u).
Proof. exact (MK_COMB (@lem3470607 _90037) (@lem3470606 _90037 GEN_PVAR_64 s u)). Qed.
Lemma lem3470609 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term22 _90037 s u) = (term23 _90037 s u).
Proof. exact (fun_ext (fun GEN_PVAR_64 : _90037 -> Prop => @lem3470608 _90037 GEN_PVAR_64 s u)). Qed.
Lemma lem3470610 {_90037 : Type'} : (@GSPEC (_90037 -> Prop)) = (@GSPEC (_90037 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_90037 -> Prop))). Qed.
Lemma lem3470611 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term24 _90037 s u) = (term25 _90037 s u).
Proof. exact (MK_COMB (@lem3470610 _90037) (@lem3470609 _90037 s u)). Qed.
Lemma lem3470612 {_90037 : Type'} : (@UNIONS _90037) = (@UNIONS _90037).
Proof. exact (eq_refl (@UNIONS _90037)). Qed.
Lemma lem3470613 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term8 _90037 s u) = (term26 _90037 s u).
Proof. exact (MK_COMB (@lem3470612 _90037) (@lem3470611 _90037 s u)). Qed.
Lemma lem3470614 {_90037 : Type'} : (@eq (_90037 -> Prop)) = (@eq (_90037 -> Prop)).
Proof. exact (eq_refl (@eq (_90037 -> Prop))). Qed.
Lemma lem3470615 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term27 _90037 s u) = (term28 _90037 s u).
Proof. exact (MK_COMB (@lem3470614 _90037) (@lem3470613 _90037 s u)). Qed.
Lemma lem3470616 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) : (term12 _90037 s t) = (@IN (_90037 -> Prop) t s).
Proof. exact (eq_refl (term12 _90037 s t)). Qed.
Lemma lem3470617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470618 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) : (term29 _90037 s t) = (term30 _90037 t s).
Proof. exact (MK_COMB (@lem3470617) (@lem3470616 _90037 t s)). Qed.
Lemma lem3470619 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) : (term15 _90037 u t) = (@DIFF _90037 u t).
Proof. exact (eq_refl (term15 _90037 u t)). Qed.
Lemma lem3470620 {_90037 : Type'} (a : _90037) : (@IN _90037 a) = (@IN _90037 a).
Proof. exact (eq_refl (@IN _90037 a)). Qed.
Lemma lem3470621 {_90037 : Type'} (a : _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) : (term31 _90037 a u t) = (term32 _90037 a u t).
Proof. exact (MK_COMB (@lem3470620 _90037 a) (@lem3470619 _90037 u t)). Qed.
Lemma lem3470622 {_90037 : Type'} (s : type686 _90037) (a : _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) : (term33 _90037 s a u t) = (term34 _90037 s a u t).
Proof. exact (MK_COMB (@lem3470618 _90037 t s) (@lem3470621 _90037 a u t)). Qed.
Lemma lem3470623 {_90037 : Type'} (s : type686 _90037) (a : _90037) (u : _90037 -> Prop) : (term35 _90037 s a u) = (term36 _90037 s a u).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3470622 _90037 s a u t)). Qed.
Lemma lem3470624 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3470625 {_90037 : Type'} (s : type686 _90037) (a : _90037) (u : _90037 -> Prop) : (term37 _90037 s a u) = (term38 _90037 s a u).
Proof. exact (MK_COMB (@lem3470624 _90037) (@lem3470623 _90037 s a u)). Qed.
Lemma lem3470626 {_90037 : Type'} (GEN_PVAR_50 : _90037) : (@SETSPEC _90037 GEN_PVAR_50) = (@SETSPEC _90037 GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC _90037 GEN_PVAR_50)). Qed.
Lemma lem3470627 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (a : _90037) (u : _90037 -> Prop) : (term39 _90037 GEN_PVAR_50 s a u) = (term40 _90037 GEN_PVAR_50 s a u).
Proof. exact (MK_COMB (@lem3470626 _90037 GEN_PVAR_50) (@lem3470625 _90037 s a u)). Qed.
Lemma lem3470628 {_90037 : Type'} (a : _90037) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3470629 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (u : _90037 -> Prop) (a : _90037) : (term41 _90037 GEN_PVAR_50 s u a) = (term42 _90037 GEN_PVAR_50 s u a).
Proof. exact (MK_COMB (@lem3470627 _90037 GEN_PVAR_50 s a u) (@lem3470628 _90037 a)). Qed.
Lemma lem3470630 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (u : _90037 -> Prop) : (term43 _90037 GEN_PVAR_50 s u) = (term44 _90037 GEN_PVAR_50 s u).
Proof. exact (fun_ext (fun a : _90037 => @lem3470629 _90037 GEN_PVAR_50 s u a)). Qed.
Lemma lem3470631 {_90037 : Type'} : (@ex _90037) = (@ex _90037).
Proof. exact (eq_refl (@ex _90037)). Qed.
Lemma lem3470632 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (u : _90037 -> Prop) : (term45 _90037 GEN_PVAR_50 s u) = (term46 _90037 GEN_PVAR_50 s u).
Proof. exact (MK_COMB (@lem3470631 _90037) (@lem3470630 _90037 GEN_PVAR_50 s u)). Qed.
Lemma lem3470633 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term47 _90037 s u) = (term48 _90037 s u).
Proof. exact (fun_ext (fun GEN_PVAR_50 : _90037 => @lem3470632 _90037 GEN_PVAR_50 s u)). Qed.
Lemma lem3470634 {_90037 : Type'} : (@GSPEC _90037) = (@GSPEC _90037).
Proof. exact (eq_refl (@GSPEC _90037)). Qed.
Lemma lem3470635 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term9 _90037 s u) = (term49 _90037 s u).
Proof. exact (MK_COMB (@lem3470634 _90037) (@lem3470633 _90037 s u)). Qed.
Lemma lem3470636 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : ((term8 _90037 s u) = (term9 _90037 s u)) = ((term26 _90037 s u) = (term49 _90037 s u)).
Proof. exact (MK_COMB (@lem3470615 _90037 s u) (@lem3470635 _90037 s u)). Qed.
Lemma lem3470637 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term26 _90037 s u) = (term49 _90037 s u).
Proof. exact (EQ_MP (@lem3470636 _90037 s u) (@lem3470600 _90037 s u)). Qed.
Lemma lem3470648 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) : (term50 _90037 u s) = (term50 _90037 u s).
Proof. exact (eq_refl (term50 _90037 u s)). Qed.
Lemma lem3470649 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : ((term51 _90037 u s) = (term26 _90037 s u)) = ((term51 _90037 u s) = (term49 _90037 s u)).
Proof. exact (MK_COMB (@lem3470648 _90037 u s) (@lem3470637 _90037 s u)). Qed.
Lemma lem3470652 {_90037 : Type'} (u : _90037 -> Prop) : (term52 _90037 u) = (term53 _90037 u).
Proof. exact (fun_ext (fun s : type686 _90037 => @lem3470649 _90037 s u)). Qed.
Lemma lem3470653 {_90037 : Type'} : (@all ((_90037 -> Prop) -> Prop)) = (@all ((_90037 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90037 -> Prop) -> Prop))). Qed.
Lemma lem3470654 {_90037 : Type'} (u : _90037 -> Prop) : (term54 _90037 u) = (term55 _90037 u).
Proof. exact (MK_COMB (@lem3470653 _90037) (@lem3470652 _90037 u)). Qed.
Lemma lem3470659 {_90037 : Type'} : (term56 _90037) = (term57 _90037).
Proof. exact (fun_ext (fun u : _90037 -> Prop => @lem3470654 _90037 u)). Qed.
Lemma lem3470660 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3470661 {_90037 : Type'} : (term58 _90037) = (term59 _90037).
Proof. exact (MK_COMB (@lem3470660 _90037) (@lem3470659 _90037)). Qed.
Lemma lem3470666 {_90037 : Type'} : (term59 _90037) = (term58 _90037).
Proof. exact (SYM (@lem3470661 _90037)). Qed.
Lemma lem3470678 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term60 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3470679 {_90037 : Type'} (s : _90037 -> Prop) (t : _90037 -> Prop) : (s = t) = (term60 _90037 s t).
Proof. exact (@lem3470678 _90037 s t). Qed.
Lemma lem3470680 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : ((term51 _90037 u s) = (term49 _90037 s u)) = (term61 _90037 s u).
Proof. exact (@lem3470679 _90037 (term51 _90037 u s) (term49 _90037 s u)). Qed.
Lemma lem3470699 {_90037 : Type'} (u : _90037 -> Prop) : (term53 _90037 u) = (term62 _90037 u).
Proof. exact (fun_ext (fun s : type686 _90037 => @lem3470680 _90037 s u)). Qed.
Lemma lem3470700 {_90037 : Type'} : (@all ((_90037 -> Prop) -> Prop)) = (@all ((_90037 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90037 -> Prop) -> Prop))). Qed.
Lemma lem3470701 {_90037 : Type'} (u : _90037 -> Prop) : (term55 _90037 u) = (term63 _90037 u).
Proof. exact (MK_COMB (@lem3470700 _90037) (@lem3470699 _90037 u)). Qed.
Lemma lem3470706 {_90037 : Type'} : (term57 _90037) = (term64 _90037).
Proof. exact (fun_ext (fun u : _90037 -> Prop => @lem3470701 _90037 u)). Qed.
Lemma lem3470707 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3470708 {_90037 : Type'} : (term59 _90037) = (term65 _90037).
Proof. exact (MK_COMB (@lem3470707 _90037) (@lem3470706 _90037)). Qed.
Lemma lem3470713 {_90037 : Type'} : (term65 _90037) = (term59 _90037).
Proof. exact (SYM (@lem3470708 _90037)). Qed.
Lemma lem3470729 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term66 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3470730 {_90037 : Type'} (s : _90037 -> Prop) (x : _90037) (t : _90037 -> Prop) : (term32 _90037 x s t) = (term66 _90037 s x t).
Proof. exact (@lem3470729 _90037 s x t). Qed.
Lemma lem3470731 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) : (term67 _90037 x u s) = (term68 _90037 u x s).
Proof. exact (@lem3470730 _90037 u x (@INTERS _90037 s)). Qed.
Lemma lem3470735 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3470736 {_90037 : Type'} (P : _90037 -> Prop) (x : _90037) : (@IN _90037 x P) = (P x).
Proof. exact (@lem3470735 _90037 P x). Qed.
Lemma lem3470737 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (@IN _90037 x u) = (u x).
Proof. exact (@lem3470736 _90037 u x). Qed.
Lemma lem3470738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470739 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term69 _90037 x u) = (term70 _90037 u x).
Proof. exact (MK_COMB (@lem3470738) (@lem3470737 _90037 u x)). Qed.
Lemma lem3470741 {A : Type'} (s : type686 A) (x : A) : (term71 A x s) = (term72 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3470742 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term71 _90037 x s) = (term72 _90037 s x).
Proof. exact (@lem3470741 _90037 s x). Qed.
Lemma lem3470750 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3470751 {_90037 : Type'} (P : type686 _90037) (x : _90037 -> Prop) : (@IN (_90037 -> Prop) x P) = (P x).
Proof. exact (@lem3470750 (_90037 -> Prop) P x). Qed.
Lemma lem3470752 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (@IN (_90037 -> Prop) t s) = (s t).
Proof. exact (@lem3470751 _90037 s t). Qed.
Lemma lem3470753 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3470754 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term73 _90037 t s) = (term74 _90037 s t).
Proof. exact (MK_COMB (@lem3470753) (@lem3470752 _90037 s t)). Qed.
Lemma lem3470756 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3470757 {_90037 : Type'} (P : _90037 -> Prop) (x : _90037) : (@IN _90037 x P) = (P x).
Proof. exact (@lem3470756 _90037 P x). Qed.
Lemma lem3470758 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (@IN _90037 x t) = (t x).
Proof. exact (@lem3470757 _90037 t x). Qed.
Lemma lem3470759 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term75 _90037 s x t) = (term76 _90037 s t x).
Proof. exact (MK_COMB (@lem3470754 _90037 s t) (@lem3470758 _90037 t x)). Qed.
Lemma lem3470762 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term77 _90037 s x) = (term78 _90037 s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3470759 _90037 s t x)). Qed.
Lemma lem3470763 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3470764 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term72 _90037 s x) = (term79 _90037 s x).
Proof. exact (MK_COMB (@lem3470763 _90037) (@lem3470762 _90037 s x)). Qed.
Lemma lem3470769 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term71 _90037 x s) = (term79 _90037 s x).
Proof. exact (TRANS (@lem3470742 _90037 s x) (@lem3470764 _90037 s x)). Qed.
Lemma lem3470770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3470771 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term80 _90037 x s) = (term81 _90037 s x).
Proof. exact (MK_COMB (@lem3470770) (@lem3470769 _90037 s x)). Qed.
Lemma lem3470772 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term68 _90037 u x s) = (term82 _90037 u s x).
Proof. exact (MK_COMB (@lem3470739 _90037 u x) (@lem3470771 _90037 s x)). Qed.
Lemma lem3470775 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term67 _90037 x u s) = (term82 _90037 u s x).
Proof. exact (TRANS (@lem3470731 _90037 u x s) (@lem3470772 _90037 u s x)). Qed.
Lemma lem3470776 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3470777 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term83 _90037 x u s) = (term84 _90037 u s x).
Proof. exact (MK_COMB (@lem3470776) (@lem3470775 _90037 u s x)). Qed.
Lemma lem3470779 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term85 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3470780 {_90037 : Type'} (p : _90037 -> Prop) (x : _90037) : (term85 _90037 x p) = (p x).
Proof. exact (@lem3470779 _90037 p x). Qed.
Lemma lem3470781 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term86 _90037 x s u) = (term87 _90037 s u x).
Proof. exact (@lem3470780 _90037 (term88 _90037 s u) x). Qed.
Lemma lem3470782 {_90037 : Type'} (s : type686 _90037) (a : _90037) (u : _90037 -> Prop) : (term87 _90037 s u a) = (term38 _90037 s a u).
Proof. exact (eq_refl (term87 _90037 s u a)). Qed.
Lemma lem3470783 {_90037 : Type'} (GEN_PVAR_50 : _90037) : (@SETSPEC _90037 GEN_PVAR_50) = (@SETSPEC _90037 GEN_PVAR_50).
Proof. exact (eq_refl (@SETSPEC _90037 GEN_PVAR_50)). Qed.
Lemma lem3470784 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (a : _90037) (u : _90037 -> Prop) : (term89 _90037 GEN_PVAR_50 s u a) = (term40 _90037 GEN_PVAR_50 s a u).
Proof. exact (MK_COMB (@lem3470783 _90037 GEN_PVAR_50) (@lem3470782 _90037 s a u)). Qed.
Lemma lem3470785 {_90037 : Type'} (a : _90037) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3470786 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (u : _90037 -> Prop) (a : _90037) : (term90 _90037 GEN_PVAR_50 s u a) = (term42 _90037 GEN_PVAR_50 s u a).
Proof. exact (MK_COMB (@lem3470784 _90037 GEN_PVAR_50 s a u) (@lem3470785 _90037 a)). Qed.
Lemma lem3470787 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (u : _90037 -> Prop) : (term91 _90037 GEN_PVAR_50 s u) = (term44 _90037 GEN_PVAR_50 s u).
Proof. exact (fun_ext (fun a : _90037 => @lem3470786 _90037 GEN_PVAR_50 s u a)). Qed.
Lemma lem3470788 {_90037 : Type'} : (@ex _90037) = (@ex _90037).
Proof. exact (eq_refl (@ex _90037)). Qed.
Lemma lem3470789 {_90037 : Type'} (GEN_PVAR_50 : _90037) (s : type686 _90037) (u : _90037 -> Prop) : (term92 _90037 GEN_PVAR_50 s u) = (term46 _90037 GEN_PVAR_50 s u).
Proof. exact (MK_COMB (@lem3470788 _90037) (@lem3470787 _90037 GEN_PVAR_50 s u)). Qed.
Lemma lem3470790 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term93 _90037 s u) = (term48 _90037 s u).
Proof. exact (fun_ext (fun GEN_PVAR_50 : _90037 => @lem3470789 _90037 GEN_PVAR_50 s u)). Qed.
Lemma lem3470791 {_90037 : Type'} : (@GSPEC _90037) = (@GSPEC _90037).
Proof. exact (eq_refl (@GSPEC _90037)). Qed.
Lemma lem3470792 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term94 _90037 s u) = (term49 _90037 s u).
Proof. exact (MK_COMB (@lem3470791 _90037) (@lem3470790 _90037 s u)). Qed.
Lemma lem3470793 {_90037 : Type'} (x : _90037) : (@IN _90037 x) = (@IN _90037 x).
Proof. exact (eq_refl (@IN _90037 x)). Qed.
Lemma lem3470794 {_90037 : Type'} (x : _90037) (s : type686 _90037) (u : _90037 -> Prop) : (term86 _90037 x s u) = (term95 _90037 x s u).
Proof. exact (MK_COMB (@lem3470793 _90037 x) (@lem3470792 _90037 s u)). Qed.
Lemma lem3470795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3470796 {_90037 : Type'} (x : _90037) (s : type686 _90037) (u : _90037 -> Prop) : (term96 _90037 x s u) = (term97 _90037 x s u).
Proof. exact (MK_COMB (@lem3470795) (@lem3470794 _90037 x s u)). Qed.
Lemma lem3470797 {_90037 : Type'} (s : type686 _90037) (x : _90037) (u : _90037 -> Prop) : (term87 _90037 s u x) = (term38 _90037 s x u).
Proof. exact (eq_refl (term87 _90037 s u x)). Qed.
Lemma lem3470798 {_90037 : Type'} (s : type686 _90037) (x : _90037) (u : _90037 -> Prop) : ((term86 _90037 x s u) = (term87 _90037 s u x)) = ((term95 _90037 x s u) = (term38 _90037 s x u)).
Proof. exact (MK_COMB (@lem3470796 _90037 x s u) (@lem3470797 _90037 s x u)). Qed.
Lemma lem3470799 {_90037 : Type'} (s : type686 _90037) (x : _90037) (u : _90037 -> Prop) : (term95 _90037 x s u) = (term38 _90037 s x u).
Proof. exact (EQ_MP (@lem3470798 _90037 s x u) (@lem3470781 _90037 s u x)). Qed.
Lemma lem3470807 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3470808 {_90037 : Type'} (P : type686 _90037) (x : _90037 -> Prop) : (@IN (_90037 -> Prop) x P) = (P x).
Proof. exact (@lem3470807 (_90037 -> Prop) P x). Qed.
Lemma lem3470809 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (@IN (_90037 -> Prop) t s) = (s t).
Proof. exact (@lem3470808 _90037 s t). Qed.
Lemma lem3470810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470811 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term30 _90037 t s) = (term98 _90037 s t).
Proof. exact (MK_COMB (@lem3470810) (@lem3470809 _90037 s t)). Qed.
Lemma lem3470813 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term66 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3470814 {_90037 : Type'} (s : _90037 -> Prop) (x : _90037) (t : _90037 -> Prop) : (term32 _90037 x s t) = (term66 _90037 s x t).
Proof. exact (@lem3470813 _90037 s x t). Qed.
Lemma lem3470815 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (t : _90037 -> Prop) : (term32 _90037 x u t) = (term66 _90037 u x t).
Proof. exact (@lem3470814 _90037 u x t). Qed.
Lemma lem3470819 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3470820 {_90037 : Type'} (P : _90037 -> Prop) (x : _90037) : (@IN _90037 x P) = (P x).
Proof. exact (@lem3470819 _90037 P x). Qed.
Lemma lem3470821 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (@IN _90037 x u) = (u x).
Proof. exact (@lem3470820 _90037 u x). Qed.
Lemma lem3470822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3470823 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term69 _90037 x u) = (term70 _90037 u x).
Proof. exact (MK_COMB (@lem3470822) (@lem3470821 _90037 u x)). Qed.
Lemma lem3470825 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3470826 {_90037 : Type'} (P : _90037 -> Prop) (x : _90037) : (@IN _90037 x P) = (P x).
Proof. exact (@lem3470825 _90037 P x). Qed.
Lemma lem3470827 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (@IN _90037 x t) = (t x).
Proof. exact (@lem3470826 _90037 t x). Qed.
Lemma lem3470828 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3470829 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term99 _90037 x t) = (term100 _90037 t x).
Proof. exact (MK_COMB (@lem3470828) (@lem3470827 _90037 t x)). Qed.
Lemma lem3470830 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term66 _90037 u x t) = (term101 _90037 u t x).
Proof. exact (MK_COMB (@lem3470823 _90037 u x) (@lem3470829 _90037 t x)). Qed.
Lemma lem3470833 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term32 _90037 x u t) = (term101 _90037 u t x).
Proof. exact (TRANS (@lem3470815 _90037 u x t) (@lem3470830 _90037 u t x)). Qed.
Lemma lem3470834 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term34 _90037 s x u t) = (term102 _90037 s u t x).
Proof. exact (MK_COMB (@lem3470811 _90037 s t) (@lem3470833 _90037 u t x)). Qed.
Lemma lem3470837 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term36 _90037 s x u) = (term103 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3470834 _90037 s u t x)). Qed.
Lemma lem3470838 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3470839 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term38 _90037 s x u) = (term104 _90037 s u x).
Proof. exact (MK_COMB (@lem3470838 _90037) (@lem3470837 _90037 s u x)). Qed.
Lemma lem3470844 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term95 _90037 x s u) = (term104 _90037 s u x).
Proof. exact (TRANS (@lem3470799 _90037 s x u) (@lem3470839 _90037 s u x)). Qed.
Lemma lem3470845 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : ((term67 _90037 x u s) = (term95 _90037 x s u)) = ((term82 _90037 u s x) = (term104 _90037 s u x)).
Proof. exact (MK_COMB (@lem3470777 _90037 u s x) (@lem3470844 _90037 s u x)). Qed.
Lemma lem3470848 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term105 _90037 s u) = (term106 _90037 s u).
Proof. exact (fun_ext (fun x : _90037 => @lem3470845 _90037 s u x)). Qed.
Lemma lem3470849 {_90037 : Type'} : (@all _90037) = (@all _90037).
Proof. exact (eq_refl (@all _90037)). Qed.
Lemma lem3470850 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term61 _90037 s u) = (term107 _90037 s u).
Proof. exact (MK_COMB (@lem3470849 _90037) (@lem3470848 _90037 s u)). Qed.
Lemma lem3470855 {_90037 : Type'} (u : _90037 -> Prop) : (term62 _90037 u) = (term108 _90037 u).
Proof. exact (fun_ext (fun s : type686 _90037 => @lem3470850 _90037 s u)). Qed.
Lemma lem3470856 {_90037 : Type'} : (@all ((_90037 -> Prop) -> Prop)) = (@all ((_90037 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90037 -> Prop) -> Prop))). Qed.
Lemma lem3470857 {_90037 : Type'} (u : _90037 -> Prop) : (term63 _90037 u) = (term109 _90037 u).
Proof. exact (MK_COMB (@lem3470856 _90037) (@lem3470855 _90037 u)). Qed.
Lemma lem3470862 {_90037 : Type'} : (term64 _90037) = (term110 _90037).
Proof. exact (fun_ext (fun u : _90037 -> Prop => @lem3470857 _90037 u)). Qed.
Lemma lem3470863 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3470864 {_90037 : Type'} : (term65 _90037) = (term111 _90037).
Proof. exact (MK_COMB (@lem3470863 _90037) (@lem3470862 _90037)). Qed.
Lemma lem3470869 {_90037 : Type'} : (term111 _90037) = (term65 _90037).
Proof. exact (SYM (@lem3470864 _90037)). Qed.
Lemma lem3470871 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3470872 {_90037 : Type'} : (term111 _90037) = (term113 _90037).
Proof. exact (@lem3470871 (term111 _90037)). Qed.
Lemma lem3470873 {_90037 : Type'} : (term113 _90037) = (term111 _90037).
Proof. exact (SYM (@lem3470872 _90037)). Qed.
Lemma lem3470874 {_90037 : Type'} (h1 : term114 _90037) : term114 _90037.
Proof. exact (h1). Qed.
Lemma lem3470877 {_90037 : Type'} (h1 : term113 _90037) : term113 _90037.
Proof. exact (h1). Qed.
Lemma lem3470878 {_90037 : Type'} : term115 _90037.
Proof. exact (fun h0 : term113 _90037 => @lem3470877 _90037 h0). Qed.
Lemma lem3470879 {_90037 : Type'} (h1 : term115 _90037) : term115 _90037.
Proof. exact (h1). Qed.
Lemma lem3470880 {_90037 : Type'} (h1 : term113 _90037) : term113 _90037.
Proof. exact (h1). Qed.
Lemma lem3470881 {_90037 : Type'} (h1 : term113 _90037) (h2 : term115 _90037) : term113 _90037.
Proof. exact (@lem3470879 _90037 h2 (@lem3470880 _90037 h1)). Qed.
Lemma lem3470882 {_90037 : Type'} (h1 : term113 _90037) : term116 _90037.
Proof. exact (fun h0 : term115 _90037 => @lem3470881 _90037 h1 h0). Qed.
Lemma lem3470883 {_90037 : Type'} (h1 : term115 _90037) : term115 _90037.
Proof. exact (h1). Qed.
Lemma lem3470884 {_90037 : Type'} (h1 : term113 _90037) (h2 : term115 _90037) : term113 _90037.
Proof. exact (@lem3470882 _90037 h1 (@lem3470883 _90037 h2)). Qed.
Lemma lem3470885 {_90037 : Type'} (h1 : term115 _90037) : term115 _90037.
Proof. exact (fun h0 : term113 _90037 => @lem3470884 _90037 h0 h1). Qed.
Lemma lem3470886 {_90037 : Type'} : term117 _90037.
Proof. exact (fun h0 : term115 _90037 => @lem3470885 _90037 h0). Qed.
Lemma lem3470889 {_90037 : Type'} : term115 _90037.
Proof. exact (@lem3470886 _90037 (@lem3470878 _90037)). Qed.
Lemma lem3470890 {_90037 : Type'} : term115 _90037.
Proof. exact (@lem3470889 _90037). Qed.
Lemma lem3470892 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3470893 {_90037 : Type'} : (term113 _90037) = (term118 _90037).
Proof. exact (@lem3470892 (term114 _90037)). Qed.
Lemma lem3470895 (t : Prop) : (term119 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3470896 {_90037 : Type'} : (term118 _90037) = (term111 _90037).
Proof. exact (@lem3470895 (term111 _90037)). Qed.
Lemma lem3470953 {_90037 : Type'} : (term113 _90037) = (term111 _90037).
Proof. exact (TRANS (@lem3470893 _90037) (@lem3470896 _90037)). Qed.
Lemma lem3470964 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term102 _90037 s u t x) = (term102 _90037 s u t x).
Proof. exact (eq_refl (term102 _90037 s u t x)). Qed.
Lemma lem3470965 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term103 _90037 s u x) = (term103 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3470964 _90037 s u t x)). Qed.
Lemma lem3470966 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3470967 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term104 _90037 s u x) = (term104 _90037 s u x).
Proof. exact (MK_COMB (@lem3470966 _90037) (@lem3470965 _90037 s u x)). Qed.
Lemma lem3470972 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term76 _90037 s t x) = (term76 _90037 s t x).
Proof. exact (eq_refl (term76 _90037 s t x)). Qed.
Lemma lem3470973 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term78 _90037 s x) = (term78 _90037 s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3470972 _90037 s t x)). Qed.
Lemma lem3470974 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3470975 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term79 _90037 s x) = (term79 _90037 s x).
Proof. exact (MK_COMB (@lem3470974 _90037) (@lem3470973 _90037 s x)). Qed.
Lemma lem3470976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3470977 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term81 _90037 s x) = (term81 _90037 s x).
Proof. exact (MK_COMB (@lem3470976) (@lem3470975 _90037 s x)). Qed.
Lemma lem3470980 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term70 _90037 u x) = (term70 _90037 u x).
Proof. exact (eq_refl (term70 _90037 u x)). Qed.
Lemma lem3470981 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term82 _90037 u s x) = (term82 _90037 u s x).
Proof. exact (MK_COMB (@lem3470980 _90037 u x) (@lem3470977 _90037 s x)). Qed.
Lemma lem3470982 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3470983 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term84 _90037 u s x) = (term84 _90037 u s x).
Proof. exact (MK_COMB (@lem3470982) (@lem3470981 _90037 u s x)). Qed.
Lemma lem3470984 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : ((term82 _90037 u s x) = (term104 _90037 s u x)) = ((term82 _90037 u s x) = (term104 _90037 s u x)).
Proof. exact (MK_COMB (@lem3470983 _90037 u s x) (@lem3470967 _90037 s u x)). Qed.
Lemma lem3470985 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term106 _90037 s u) = (term106 _90037 s u).
Proof. exact (fun_ext (fun x : _90037 => @lem3470984 _90037 s u x)). Qed.
Lemma lem3470986 {_90037 : Type'} : (@all _90037) = (@all _90037).
Proof. exact (eq_refl (@all _90037)). Qed.
Lemma lem3470987 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : (term107 _90037 s u) = (term107 _90037 s u).
Proof. exact (MK_COMB (@lem3470986 _90037) (@lem3470985 _90037 s u)). Qed.
Lemma lem3470988 {_90037 : Type'} (u : _90037 -> Prop) : (term108 _90037 u) = (term108 _90037 u).
Proof. exact (fun_ext (fun s : type686 _90037 => @lem3470987 _90037 s u)). Qed.
Lemma lem3470989 {_90037 : Type'} : (@all ((_90037 -> Prop) -> Prop)) = (@all ((_90037 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90037 -> Prop) -> Prop))). Qed.
Lemma lem3470990 {_90037 : Type'} (u : _90037 -> Prop) : (term109 _90037 u) = (term109 _90037 u).
Proof. exact (MK_COMB (@lem3470989 _90037) (@lem3470988 _90037 u)). Qed.
Lemma lem3470991 {_90037 : Type'} : (term110 _90037) = (term110 _90037).
Proof. exact (fun_ext (fun u : _90037 -> Prop => @lem3470990 _90037 u)). Qed.
Lemma lem3470992 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3470993 {_90037 : Type'} : (term111 _90037) = (term111 _90037).
Proof. exact (MK_COMB (@lem3470992 _90037) (@lem3470991 _90037)). Qed.
Lemma lem3471034 {_90037 : Type'} : (term113 _90037) = (term111 _90037).
Proof. exact (TRANS (@lem3470953 _90037) (@lem3470993 _90037)). Qed.
Lemma lem3471035 {_90037 : Type'} : (term111 _90037) = (term113 _90037).
Proof. exact (SYM (@lem3471034 _90037)). Qed.
Lemma lem3471037 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3471038 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : ((term82 _90037 u s x) = (term104 _90037 s u x)) = (term120 _90037 s u x).
Proof. exact (@lem3471037 ((term82 _90037 u s x) = (term104 _90037 s u x))). Qed.
Lemma lem3471039 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term120 _90037 s u x) = ((term82 _90037 u s x) = (term104 _90037 s u x)).
Proof. exact (SYM (@lem3471038 _90037 s u x)). Qed.
Lemma lem3471040 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term121 _90037 s u x) : term121 _90037 s u x.
Proof. exact (h1). Qed.
Lemma lem3471051 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term122 _90037 s t x) = (term123 _90037 s t x).
Proof. exact (@lem17362 (s t) (t x)). Qed.
Lemma lem3471056 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term76 _90037 s t x) = (term124 _90037 s t x).
Proof. exact (@lem17265 (s t) (t x)). Qed.
Lemma lem3471057 {_90037 : Type'} (P : type686 _90037) : (term125 _90037 P) = (term126 _90037 P).
Proof. exact (@lem18392 (_90037 -> Prop) P). Qed.
Lemma lem3471058 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term81 _90037 s x) = (term127 _90037 s x).
Proof. exact (@lem3471057 _90037 (term78 _90037 s x)). Qed.
Lemma lem3471059 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term128 _90037 s x t) = (term76 _90037 s t x).
Proof. exact (eq_refl (term128 _90037 s x t)). Qed.
Lemma lem3471060 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471061 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term129 _90037 s x t) = (term122 _90037 s t x).
Proof. exact (MK_COMB (@lem3471060) (@lem3471059 _90037 s t x)). Qed.
Lemma lem3471062 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term129 _90037 s x t) = (term123 _90037 s t x).
Proof. exact (TRANS (@lem3471061 _90037 s t x) (@lem3471051 _90037 s t x)). Qed.
Lemma lem3471063 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term130 _90037 s x) = (term131 _90037 s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471062 _90037 s t x)). Qed.
Lemma lem3471064 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471065 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term127 _90037 s x) = (term132 _90037 s x).
Proof. exact (MK_COMB (@lem3471064 _90037) (@lem3471063 _90037 s x)). Qed.
Lemma lem3471066 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term81 _90037 s x) = (term132 _90037 s x).
Proof. exact (TRANS (@lem3471058 _90037 s x) (@lem3471065 _90037 s x)). Qed.
Lemma lem3471067 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term78 _90037 s x) = (term133 _90037 s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471056 _90037 s t x)). Qed.
Lemma lem3471068 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3471069 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term79 _90037 s x) = (term134 _90037 s x).
Proof. exact (MK_COMB (@lem3471068 _90037) (@lem3471067 _90037 s x)). Qed.
Lemma lem3471070 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term135 _90037 s x) = (term79 _90037 s x).
Proof. exact (@lem16933 (term79 _90037 s x)). Qed.
Lemma lem3471071 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term135 _90037 s x) = (term134 _90037 s x).
Proof. exact (TRANS (@lem3471070 _90037 s x) (@lem3471069 _90037 s x)). Qed.
Lemma lem3471073 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term136 _90037 u x) = (term136 _90037 u x).
Proof. exact (eq_refl (term136 _90037 u x)). Qed.
Lemma lem3471074 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term137 _90037 u s x) = (term138 _90037 u s x).
Proof. exact (MK_COMB (@lem3471073 _90037 u x) (@lem3471071 _90037 s x)). Qed.
Lemma lem3471075 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term139 _90037 u s x) = (term137 _90037 u s x).
Proof. exact (@lem17045 (u x) (term81 _90037 s x)). Qed.
Lemma lem3471076 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term139 _90037 u s x) = (term138 _90037 u s x).
Proof. exact (TRANS (@lem3471075 _90037 u s x) (@lem3471074 _90037 u s x)). Qed.
Lemma lem3471078 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term70 _90037 u x) = (term70 _90037 u x).
Proof. exact (eq_refl (term70 _90037 u x)). Qed.
Lemma lem3471079 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term82 _90037 u s x) = (term140 _90037 u s x).
Proof. exact (MK_COMB (@lem3471078 _90037 u x) (@lem3471066 _90037 s x)). Qed.
Lemma lem3471087 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term141 _90037 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3471089 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term136 _90037 u x) = (term136 _90037 u x).
Proof. exact (eq_refl (term136 _90037 u x)). Qed.
Lemma lem3471090 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term142 _90037 u t x) = (term143 _90037 u t x).
Proof. exact (MK_COMB (@lem3471089 _90037 u x) (@lem3471087 _90037 t x)). Qed.
Lemma lem3471091 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term144 _90037 u t x) = (term142 _90037 u t x).
Proof. exact (@lem17045 (u x) (term100 _90037 t x)). Qed.
Lemma lem3471092 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term144 _90037 u t x) = (term143 _90037 u t x).
Proof. exact (TRANS (@lem3471091 _90037 u t x) (@lem3471090 _90037 u t x)). Qed.
Lemma lem3471097 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term145 _90037 s t) = (term145 _90037 s t).
Proof. exact (eq_refl (term145 _90037 s t)). Qed.
Lemma lem3471098 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term146 _90037 s u t x) = (term147 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471097 _90037 s t) (@lem3471092 _90037 u t x)). Qed.
Lemma lem3471099 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term148 _90037 s u t x) = (term146 _90037 s u t x).
Proof. exact (@lem17045 (s t) (term101 _90037 u t x)). Qed.
Lemma lem3471100 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term148 _90037 s u t x) = (term147 _90037 s u t x).
Proof. exact (TRANS (@lem3471099 _90037 s u t x) (@lem3471098 _90037 s u t x)). Qed.
Lemma lem3471103 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term102 _90037 s u t x) = (term102 _90037 s u t x).
Proof. exact (eq_refl (term102 _90037 s u t x)). Qed.
Lemma lem3471104 {_90037 : Type'} (P : type686 _90037) : (term149 _90037 P) = (term150 _90037 P).
Proof. exact (@lem18394 (_90037 -> Prop) P). Qed.
Lemma lem3471105 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term151 _90037 s u x) = (term152 _90037 s u x).
Proof. exact (@lem3471104 _90037 (term103 _90037 s u x)). Qed.
Lemma lem3471106 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term153 _90037 s u x t) = (term102 _90037 s u t x).
Proof. exact (eq_refl (term153 _90037 s u x t)). Qed.
Lemma lem3471107 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471108 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term154 _90037 s u x t) = (term148 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471107) (@lem3471106 _90037 s u t x)). Qed.
Lemma lem3471109 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term154 _90037 s u x t) = (term147 _90037 s u t x).
Proof. exact (TRANS (@lem3471108 _90037 s u t x) (@lem3471100 _90037 s u t x)). Qed.
Lemma lem3471110 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term155 _90037 s u x) = (term156 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471109 _90037 s u t x)). Qed.
Lemma lem3471111 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3471112 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term152 _90037 s u x) = (term157 _90037 s u x).
Proof. exact (MK_COMB (@lem3471111 _90037) (@lem3471110 _90037 s u x)). Qed.
Lemma lem3471113 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term151 _90037 s u x) = (term157 _90037 s u x).
Proof. exact (TRANS (@lem3471105 _90037 s u x) (@lem3471112 _90037 s u x)). Qed.
Lemma lem3471114 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term103 _90037 s u x) = (term103 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471103 _90037 s u t x)). Qed.
Lemma lem3471115 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471116 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term104 _90037 s u x) = (term104 _90037 s u x).
Proof. exact (MK_COMB (@lem3471115 _90037) (@lem3471114 _90037 s u x)). Qed.
Lemma lem3471117 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471118 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term158 _90037 u s x) = (term159 _90037 u s x).
Proof. exact (MK_COMB (@lem3471117) (@lem3471076 _90037 u s x)). Qed.
Lemma lem3471119 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term160 _90037 s u x) = (term161 _90037 s u x).
Proof. exact (MK_COMB (@lem3471118 _90037 u s x) (@lem3471116 _90037 s u x)). Qed.
Lemma lem3471120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471121 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term162 _90037 u s x) = (term163 _90037 u s x).
Proof. exact (MK_COMB (@lem3471120) (@lem3471079 _90037 u s x)). Qed.
Lemma lem3471122 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term164 _90037 s u x) = (term165 _90037 s u x).
Proof. exact (MK_COMB (@lem3471121 _90037 u s x) (@lem3471113 _90037 s u x)). Qed.
Lemma lem3471123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471124 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term166 _90037 s u x) = (term167 _90037 s u x).
Proof. exact (MK_COMB (@lem3471123) (@lem3471122 _90037 s u x)). Qed.
Lemma lem3471125 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term168 _90037 s u x) = (term169 _90037 s u x).
Proof. exact (MK_COMB (@lem3471124 _90037 s u x) (@lem3471119 _90037 s u x)). Qed.
Lemma lem3471126 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term121 _90037 s u x) = (term168 _90037 s u x).
Proof. exact (@lem17646 (term82 _90037 u s x) (term104 _90037 s u x)). Qed.
Lemma lem3471127 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term121 _90037 s u x) = (term169 _90037 s u x).
Proof. exact (TRANS (@lem3471126 _90037 s u x) (@lem3471125 _90037 s u x)). Qed.
Lemma lem3471282 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3471283 {_90037 : Type'} (P : Prop) (Q : type686 _90037) : (term172 _90037 P Q) = (term173 _90037 P Q).
Proof. exact (@lem3471282 (_90037 -> Prop) P Q). Qed.
Lemma lem3471284 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term174 _90037 u s x) = (term175 _90037 u s x).
Proof. exact (@lem3471283 _90037 (u x) (term131 _90037 s x)). Qed.
Lemma lem3471285 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term176 _90037 s x t) = (term123 _90037 s t x).
Proof. exact (eq_refl (term176 _90037 s x t)). Qed.
Lemma lem3471286 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term177 _90037 s x) = (term131 _90037 s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471285 _90037 s t x)). Qed.
Lemma lem3471287 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471288 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term178 _90037 s x) = (term132 _90037 s x).
Proof. exact (MK_COMB (@lem3471287 _90037) (@lem3471286 _90037 s x)). Qed.
Lemma lem3471289 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term70 _90037 u x) = (term70 _90037 u x).
Proof. exact (eq_refl (term70 _90037 u x)). Qed.
Lemma lem3471290 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term174 _90037 u s x) = (term140 _90037 u s x).
Proof. exact (MK_COMB (@lem3471289 _90037 u x) (@lem3471288 _90037 s x)). Qed.
Lemma lem3471291 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3471292 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term179 _90037 u s x) = (term180 _90037 u s x).
Proof. exact (MK_COMB (@lem3471291) (@lem3471290 _90037 u s x)). Qed.
Lemma lem3471293 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term176 _90037 s x t) = (term123 _90037 s t x).
Proof. exact (eq_refl (term176 _90037 s x t)). Qed.
Lemma lem3471294 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term70 _90037 u x) = (term70 _90037 u x).
Proof. exact (eq_refl (term70 _90037 u x)). Qed.
Lemma lem3471295 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term181 _90037 u s x t) = (term182 _90037 u s t x).
Proof. exact (MK_COMB (@lem3471294 _90037 u x) (@lem3471293 _90037 s t x)). Qed.
Lemma lem3471296 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term183 _90037 u s x) = (term184 _90037 u s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471295 _90037 u s t x)). Qed.
Lemma lem3471297 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471298 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term175 _90037 u s x) = (term185 _90037 u s x).
Proof. exact (MK_COMB (@lem3471297 _90037) (@lem3471296 _90037 u s x)). Qed.
Lemma lem3471299 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : ((term174 _90037 u s x) = (term175 _90037 u s x)) = ((term140 _90037 u s x) = (term185 _90037 u s x)).
Proof. exact (MK_COMB (@lem3471292 _90037 u s x) (@lem3471298 _90037 u s x)). Qed.
Lemma lem3471300 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term140 _90037 u s x) = (term185 _90037 u s x).
Proof. exact (EQ_MP (@lem3471299 _90037 u s x) (@lem3471284 _90037 u s x)). Qed.
Lemma lem3471301 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471302 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term163 _90037 u s x) = (term186 _90037 u s x).
Proof. exact (MK_COMB (@lem3471301) (@lem3471300 _90037 u s x)). Qed.
Lemma lem3471303 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term157 _90037 s u x) = (term157 _90037 s u x).
Proof. exact (eq_refl (term157 _90037 s u x)). Qed.
Lemma lem3471304 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term165 _90037 s u x) = (term187 _90037 s u x).
Proof. exact (MK_COMB (@lem3471302 _90037 u s x) (@lem3471303 _90037 s u x)). Qed.
Lemma lem3471306 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3471307 {_90037 : Type'} (P : type686 _90037) (Q : Prop) : (term190 _90037 P Q) = (term191 _90037 P Q).
Proof. exact (@lem3471306 (_90037 -> Prop) P Q). Qed.
Lemma lem3471308 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term192 _90037 s u x) = (term193 _90037 s u x).
Proof. exact (@lem3471307 _90037 (term184 _90037 u s x) (term157 _90037 s u x)). Qed.
Lemma lem3471309 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term194 _90037 u s x t) = (term182 _90037 u s t x).
Proof. exact (eq_refl (term194 _90037 u s x t)). Qed.
Lemma lem3471310 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term195 _90037 u s x) = (term184 _90037 u s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471309 _90037 u s t x)). Qed.
Lemma lem3471311 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471312 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term196 _90037 u s x) = (term185 _90037 u s x).
Proof. exact (MK_COMB (@lem3471311 _90037) (@lem3471310 _90037 u s x)). Qed.
Lemma lem3471313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471314 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term197 _90037 u s x) = (term186 _90037 u s x).
Proof. exact (MK_COMB (@lem3471313) (@lem3471312 _90037 u s x)). Qed.
Lemma lem3471315 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term157 _90037 s u x) = (term157 _90037 s u x).
Proof. exact (eq_refl (term157 _90037 s u x)). Qed.
Lemma lem3471316 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term192 _90037 s u x) = (term187 _90037 s u x).
Proof. exact (MK_COMB (@lem3471314 _90037 u s x) (@lem3471315 _90037 s u x)). Qed.
Lemma lem3471317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3471318 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term198 _90037 s u x) = (term199 _90037 s u x).
Proof. exact (MK_COMB (@lem3471317) (@lem3471316 _90037 s u x)). Qed.
Lemma lem3471319 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term194 _90037 u s x t) = (term182 _90037 u s t x).
Proof. exact (eq_refl (term194 _90037 u s x t)). Qed.
Lemma lem3471320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471321 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term200 _90037 u s x t) = (term201 _90037 u s t x).
Proof. exact (MK_COMB (@lem3471320) (@lem3471319 _90037 u s t x)). Qed.
Lemma lem3471322 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term157 _90037 s u x) = (term157 _90037 s u x).
Proof. exact (eq_refl (term157 _90037 s u x)). Qed.
Lemma lem3471323 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term202 _90037 t s u x) = (term203 _90037 t s u x).
Proof. exact (MK_COMB (@lem3471321 _90037 u s t x) (@lem3471322 _90037 s u x)). Qed.
Lemma lem3471324 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term204 _90037 s u x) = (term205 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471323 _90037 t s u x)). Qed.
Lemma lem3471325 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471326 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term193 _90037 s u x) = (term206 _90037 s u x).
Proof. exact (MK_COMB (@lem3471325 _90037) (@lem3471324 _90037 s u x)). Qed.
Lemma lem3471327 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : ((term192 _90037 s u x) = (term193 _90037 s u x)) = ((term187 _90037 s u x) = (term206 _90037 s u x)).
Proof. exact (MK_COMB (@lem3471318 _90037 s u x) (@lem3471326 _90037 s u x)). Qed.
Lemma lem3471328 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term187 _90037 s u x) = (term206 _90037 s u x).
Proof. exact (EQ_MP (@lem3471327 _90037 s u x) (@lem3471308 _90037 s u x)). Qed.
Lemma lem3471329 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term165 _90037 s u x) = (term206 _90037 s u x).
Proof. exact (TRANS (@lem3471304 _90037 s u x) (@lem3471328 _90037 s u x)). Qed.
Lemma lem3471330 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471331 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term167 _90037 s u x) = (term207 _90037 s u x).
Proof. exact (MK_COMB (@lem3471330) (@lem3471329 _90037 s u x)). Qed.
Lemma lem3471333 {A : Type'} (P : Prop) (Q : A -> Prop) : (term170 A P Q) = (term171 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3471334 {_90037 : Type'} (P : Prop) (Q : type686 _90037) : (term172 _90037 P Q) = (term173 _90037 P Q).
Proof. exact (@lem3471333 (_90037 -> Prop) P Q). Qed.
Lemma lem3471335 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term208 _90037 s u x) = (term209 _90037 s u x).
Proof. exact (@lem3471334 _90037 (term138 _90037 u s x) (term103 _90037 s u x)). Qed.
Lemma lem3471336 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term153 _90037 s u x t) = (term102 _90037 s u t x).
Proof. exact (eq_refl (term153 _90037 s u x t)). Qed.
Lemma lem3471337 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term210 _90037 s u x) = (term103 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471336 _90037 s u t x)). Qed.
Lemma lem3471338 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471339 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term211 _90037 s u x) = (term104 _90037 s u x).
Proof. exact (MK_COMB (@lem3471338 _90037) (@lem3471337 _90037 s u x)). Qed.
Lemma lem3471340 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term159 _90037 u s x) = (term159 _90037 u s x).
Proof. exact (eq_refl (term159 _90037 u s x)). Qed.
Lemma lem3471341 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term208 _90037 s u x) = (term161 _90037 s u x).
Proof. exact (MK_COMB (@lem3471340 _90037 u s x) (@lem3471339 _90037 s u x)). Qed.
Lemma lem3471342 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3471343 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term212 _90037 s u x) = (term213 _90037 s u x).
Proof. exact (MK_COMB (@lem3471342) (@lem3471341 _90037 s u x)). Qed.
Lemma lem3471344 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term153 _90037 s u x t) = (term102 _90037 s u t x).
Proof. exact (eq_refl (term153 _90037 s u x t)). Qed.
Lemma lem3471345 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term159 _90037 u s x) = (term159 _90037 u s x).
Proof. exact (eq_refl (term159 _90037 u s x)). Qed.
Lemma lem3471346 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term214 _90037 s u x t) = (term215 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471345 _90037 u s x) (@lem3471344 _90037 s u t x)). Qed.
Lemma lem3471347 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term216 _90037 s u x) = (term217 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471346 _90037 s u t x)). Qed.
Lemma lem3471348 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471349 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term209 _90037 s u x) = (term218 _90037 s u x).
Proof. exact (MK_COMB (@lem3471348 _90037) (@lem3471347 _90037 s u x)). Qed.
Lemma lem3471350 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : ((term208 _90037 s u x) = (term209 _90037 s u x)) = ((term161 _90037 s u x) = (term218 _90037 s u x)).
Proof. exact (MK_COMB (@lem3471343 _90037 s u x) (@lem3471349 _90037 s u x)). Qed.
Lemma lem3471351 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term161 _90037 s u x) = (term218 _90037 s u x).
Proof. exact (EQ_MP (@lem3471350 _90037 s u x) (@lem3471335 _90037 s u x)). Qed.
Lemma lem3471352 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term169 _90037 s u x) = (term219 _90037 s u x).
Proof. exact (MK_COMB (@lem3471331 _90037 s u x) (@lem3471351 _90037 s u x)). Qed.
Lemma lem3471354 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term220 A P Q) = (term221 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3471355 {_90037 : Type'} (P : type686 _90037) (Q : type686 _90037) : (term222 _90037 P Q) = (term223 _90037 P Q).
Proof. exact (@lem3471354 (_90037 -> Prop) P Q). Qed.
Lemma lem3471356 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term224 _90037 s u x) = (term225 _90037 s u x).
Proof. exact (@lem3471355 _90037 (term205 _90037 s u x) (term217 _90037 s u x)). Qed.
Lemma lem3471357 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term226 _90037 s u x t) = (term203 _90037 t s u x).
Proof. exact (eq_refl (term226 _90037 s u x t)). Qed.
Lemma lem3471358 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term227 _90037 s u x) = (term205 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471357 _90037 t s u x)). Qed.
Lemma lem3471359 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471360 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term228 _90037 s u x) = (term206 _90037 s u x).
Proof. exact (MK_COMB (@lem3471359 _90037) (@lem3471358 _90037 s u x)). Qed.
Lemma lem3471361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471362 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term229 _90037 s u x) = (term207 _90037 s u x).
Proof. exact (MK_COMB (@lem3471361) (@lem3471360 _90037 s u x)). Qed.
Lemma lem3471363 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term230 _90037 s u x t) = (term215 _90037 s u t x).
Proof. exact (eq_refl (term230 _90037 s u x t)). Qed.
Lemma lem3471364 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term231 _90037 s u x) = (term217 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471363 _90037 s u t x)). Qed.
Lemma lem3471365 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471366 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term232 _90037 s u x) = (term218 _90037 s u x).
Proof. exact (MK_COMB (@lem3471365 _90037) (@lem3471364 _90037 s u x)). Qed.
Lemma lem3471367 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term224 _90037 s u x) = (term219 _90037 s u x).
Proof. exact (MK_COMB (@lem3471362 _90037 s u x) (@lem3471366 _90037 s u x)). Qed.
Lemma lem3471368 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3471369 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term233 _90037 s u x) = (term234 _90037 s u x).
Proof. exact (MK_COMB (@lem3471368) (@lem3471367 _90037 s u x)). Qed.
Lemma lem3471370 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term226 _90037 s u x t) = (term203 _90037 t s u x).
Proof. exact (eq_refl (term226 _90037 s u x t)). Qed.
Lemma lem3471371 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471372 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term235 _90037 s u x t) = (term236 _90037 t s u x).
Proof. exact (MK_COMB (@lem3471371) (@lem3471370 _90037 t s u x)). Qed.
Lemma lem3471373 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term230 _90037 s u x t) = (term215 _90037 s u t x).
Proof. exact (eq_refl (term230 _90037 s u x t)). Qed.
Lemma lem3471374 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term237 _90037 s u x t) = (term238 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471372 _90037 t s u x) (@lem3471373 _90037 s u t x)). Qed.
Lemma lem3471375 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term239 _90037 s u x) = (term240 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471374 _90037 s u t x)). Qed.
Lemma lem3471376 {_90037 : Type'} : (@ex (_90037 -> Prop)) = (@ex (_90037 -> Prop)).
Proof. exact (eq_refl (@ex (_90037 -> Prop))). Qed.
Lemma lem3471377 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term225 _90037 s u x) = (term241 _90037 s u x).
Proof. exact (MK_COMB (@lem3471376 _90037) (@lem3471375 _90037 s u x)). Qed.
Lemma lem3471378 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : ((term224 _90037 s u x) = (term225 _90037 s u x)) = ((term219 _90037 s u x) = (term241 _90037 s u x)).
Proof. exact (MK_COMB (@lem3471369 _90037 s u x) (@lem3471377 _90037 s u x)). Qed.
Lemma lem3471379 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term219 _90037 s u x) = (term241 _90037 s u x).
Proof. exact (EQ_MP (@lem3471378 _90037 s u x) (@lem3471356 _90037 s u x)). Qed.
Lemma lem3471381 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term169 _90037 s u x) = (term241 _90037 s u x).
Proof. exact (TRANS (@lem3471352 _90037 s u x) (@lem3471379 _90037 s u x)). Qed.
Lemma lem3471382 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term121 _90037 s u x) = (term241 _90037 s u x).
Proof. exact (TRANS (@lem3471127 _90037 s u x) (@lem3471381 _90037 s u x)). Qed.
Lemma lem3471383 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term121 _90037 s u x) : term241 _90037 s u x.
Proof. exact (EQ_MP (@lem3471382 _90037 s u x) (@lem3471040 _90037 s u x h1)). Qed.
Lemma lem3471384 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term238 _90037 s u t x) : term238 _90037 s u t x.
Proof. exact (h1). Qed.
Lemma lem3471385 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471390 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471391 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471390 _90037 Prop f x). Qed.
Lemma lem3471393 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (t x) = (@I (_90037 -> Prop) t x).
Proof. exact (@lem3471391 _90037 t x). Qed.
Lemma lem3471394 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term100 _90037 t x) = (term242 _90037 t x).
Proof. exact (MK_COMB (@lem3471385) (@lem3471393 _90037 t x)). Qed.
Lemma lem3471399 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471400 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471399 _90037 Prop f x). Qed.
Lemma lem3471402 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (u x) = (@I (_90037 -> Prop) u x).
Proof. exact (@lem3471400 _90037 u x). Qed.
Lemma lem3471403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471404 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term70 _90037 u x) = (term243 _90037 u x).
Proof. exact (MK_COMB (@lem3471403) (@lem3471402 _90037 u x)). Qed.
Lemma lem3471405 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term101 _90037 u t x) = (term244 _90037 u t x).
Proof. exact (MK_COMB (@lem3471404 _90037 u x) (@lem3471394 _90037 t x)). Qed.
Lemma lem3471410 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471411 {_90037 : Type'} (f : type686 _90037) (x : _90037 -> Prop) : (f x) = (@I ((_90037 -> Prop) -> Prop) f x).
Proof. exact (@lem3471410 (_90037 -> Prop) Prop f x). Qed.
Lemma lem3471413 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (s t) = (@I ((_90037 -> Prop) -> Prop) s t).
Proof. exact (@lem3471411 _90037 s t). Qed.
Lemma lem3471414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471415 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term98 _90037 s t) = (term245 _90037 s t).
Proof. exact (MK_COMB (@lem3471414) (@lem3471413 _90037 s t)). Qed.
Lemma lem3471416 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term102 _90037 s u t x) = (term246 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471415 _90037 s t) (@lem3471405 _90037 u t x)). Qed.
Lemma lem3471421 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471422 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471421 _90037 Prop f x). Qed.
Lemma lem3471424 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (t x) = (@I (_90037 -> Prop) t x).
Proof. exact (@lem3471422 _90037 t x). Qed.
Lemma lem3471425 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471430 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471431 {_90037 : Type'} (f : type686 _90037) (x : _90037 -> Prop) : (f x) = (@I ((_90037 -> Prop) -> Prop) f x).
Proof. exact (@lem3471430 (_90037 -> Prop) Prop f x). Qed.
Lemma lem3471433 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (s t) = (@I ((_90037 -> Prop) -> Prop) s t).
Proof. exact (@lem3471431 _90037 s t). Qed.
Lemma lem3471434 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term247 _90037 s t) = (term248 _90037 s t).
Proof. exact (MK_COMB (@lem3471425) (@lem3471433 _90037 s t)). Qed.
Lemma lem3471435 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471436 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term145 _90037 s t) = (term249 _90037 s t).
Proof. exact (MK_COMB (@lem3471435) (@lem3471434 _90037 s t)). Qed.
Lemma lem3471437 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term124 _90037 s t x) = (term250 _90037 s t x).
Proof. exact (MK_COMB (@lem3471436 _90037 s t) (@lem3471424 _90037 t x)). Qed.
Lemma lem3471438 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term133 _90037 s x) = (term251 _90037 s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471437 _90037 s t x)). Qed.
Lemma lem3471439 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3471440 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term134 _90037 s x) = (term252 _90037 s x).
Proof. exact (MK_COMB (@lem3471439 _90037) (@lem3471438 _90037 s x)). Qed.
Lemma lem3471441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471446 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471447 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471446 _90037 Prop f x). Qed.
Lemma lem3471449 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (u x) = (@I (_90037 -> Prop) u x).
Proof. exact (@lem3471447 _90037 u x). Qed.
Lemma lem3471450 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term100 _90037 u x) = (term242 _90037 u x).
Proof. exact (MK_COMB (@lem3471441) (@lem3471449 _90037 u x)). Qed.
Lemma lem3471451 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471452 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term136 _90037 u x) = (term253 _90037 u x).
Proof. exact (MK_COMB (@lem3471451) (@lem3471450 _90037 u x)). Qed.
Lemma lem3471453 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term138 _90037 u s x) = (term254 _90037 u s x).
Proof. exact (MK_COMB (@lem3471452 _90037 u x) (@lem3471440 _90037 s x)). Qed.
Lemma lem3471454 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471455 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (x : _90037) : (term159 _90037 u s x) = (term255 _90037 u s x).
Proof. exact (MK_COMB (@lem3471454) (@lem3471453 _90037 u s x)). Qed.
Lemma lem3471456 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term215 _90037 s u t x) = (term256 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471455 _90037 u s x) (@lem3471416 _90037 s u t x)). Qed.
Lemma lem3471461 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471462 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471461 _90037 Prop f x). Qed.
Lemma lem3471464 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (t x) = (@I (_90037 -> Prop) t x).
Proof. exact (@lem3471462 _90037 t x). Qed.
Lemma lem3471465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471470 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471471 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471470 _90037 Prop f x). Qed.
Lemma lem3471473 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (u x) = (@I (_90037 -> Prop) u x).
Proof. exact (@lem3471471 _90037 u x). Qed.
Lemma lem3471474 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term100 _90037 u x) = (term242 _90037 u x).
Proof. exact (MK_COMB (@lem3471465) (@lem3471473 _90037 u x)). Qed.
Lemma lem3471475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471476 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term136 _90037 u x) = (term253 _90037 u x).
Proof. exact (MK_COMB (@lem3471475) (@lem3471474 _90037 u x)). Qed.
Lemma lem3471477 {_90037 : Type'} (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term143 _90037 u t x) = (term257 _90037 u t x).
Proof. exact (MK_COMB (@lem3471476 _90037 u x) (@lem3471464 _90037 t x)). Qed.
Lemma lem3471478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471483 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471484 {_90037 : Type'} (f : type686 _90037) (x : _90037 -> Prop) : (f x) = (@I ((_90037 -> Prop) -> Prop) f x).
Proof. exact (@lem3471483 (_90037 -> Prop) Prop f x). Qed.
Lemma lem3471486 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (s t) = (@I ((_90037 -> Prop) -> Prop) s t).
Proof. exact (@lem3471484 _90037 s t). Qed.
Lemma lem3471487 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term247 _90037 s t) = (term248 _90037 s t).
Proof. exact (MK_COMB (@lem3471478) (@lem3471486 _90037 s t)). Qed.
Lemma lem3471488 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471489 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term145 _90037 s t) = (term249 _90037 s t).
Proof. exact (MK_COMB (@lem3471488) (@lem3471487 _90037 s t)). Qed.
Lemma lem3471490 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term147 _90037 s u t x) = (term258 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471489 _90037 s t) (@lem3471477 _90037 u t x)). Qed.
Lemma lem3471491 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term156 _90037 s u x) = (term259 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471490 _90037 s u t x)). Qed.
Lemma lem3471492 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3471493 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term157 _90037 s u x) = (term260 _90037 s u x).
Proof. exact (MK_COMB (@lem3471492 _90037) (@lem3471491 _90037 s u x)). Qed.
Lemma lem3471494 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3471499 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471500 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471499 _90037 Prop f x). Qed.
Lemma lem3471502 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (t x) = (@I (_90037 -> Prop) t x).
Proof. exact (@lem3471500 _90037 t x). Qed.
Lemma lem3471503 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term100 _90037 t x) = (term242 _90037 t x).
Proof. exact (MK_COMB (@lem3471494) (@lem3471502 _90037 t x)). Qed.
Lemma lem3471508 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471509 {_90037 : Type'} (f : type686 _90037) (x : _90037 -> Prop) : (f x) = (@I ((_90037 -> Prop) -> Prop) f x).
Proof. exact (@lem3471508 (_90037 -> Prop) Prop f x). Qed.
Lemma lem3471511 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (s t) = (@I ((_90037 -> Prop) -> Prop) s t).
Proof. exact (@lem3471509 _90037 s t). Qed.
Lemma lem3471512 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471513 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term98 _90037 s t) = (term245 _90037 s t).
Proof. exact (MK_COMB (@lem3471512) (@lem3471511 _90037 s t)). Qed.
Lemma lem3471514 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term123 _90037 s t x) = (term261 _90037 s t x).
Proof. exact (MK_COMB (@lem3471513 _90037 s t) (@lem3471503 _90037 t x)). Qed.
Lemma lem3471519 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3471520 {_90037 : Type'} (f : _90037 -> Prop) (x : _90037) : (f x) = (@I (_90037 -> Prop) f x).
Proof. exact (@lem3471519 _90037 Prop f x). Qed.
Lemma lem3471522 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (u x) = (@I (_90037 -> Prop) u x).
Proof. exact (@lem3471520 _90037 u x). Qed.
Lemma lem3471523 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471524 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term70 _90037 u x) = (term243 _90037 u x).
Proof. exact (MK_COMB (@lem3471523) (@lem3471522 _90037 u x)). Qed.
Lemma lem3471525 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term182 _90037 u s t x) = (term262 _90037 u s t x).
Proof. exact (MK_COMB (@lem3471524 _90037 u x) (@lem3471514 _90037 s t x)). Qed.
Lemma lem3471526 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471527 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term201 _90037 u s t x) = (term263 _90037 u s t x).
Proof. exact (MK_COMB (@lem3471526) (@lem3471525 _90037 u s t x)). Qed.
Lemma lem3471528 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term203 _90037 t s u x) = (term264 _90037 t s u x).
Proof. exact (MK_COMB (@lem3471527 _90037 u s t x) (@lem3471493 _90037 s u x)). Qed.
Lemma lem3471529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3471530 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term236 _90037 t s u x) = (term265 _90037 t s u x).
Proof. exact (MK_COMB (@lem3471529) (@lem3471528 _90037 t s u x)). Qed.
Lemma lem3471531 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term238 _90037 s u t x) = (term266 _90037 s u t x).
Proof. exact (MK_COMB (@lem3471530 _90037 t s u x) (@lem3471456 _90037 s u t x)). Qed.
Lemma lem3471532 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term238 _90037 s u t x) : term266 _90037 s u t x.
Proof. exact (EQ_MP (@lem3471531 _90037 s u t x) (@lem3471384 _90037 s u t x h1)). Qed.
Lemma lem3471533 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term264 _90037 t s u x.
Proof. exact (h1). Qed.
Lemma lem3471534 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term256 _90037 s u t x.
Proof. exact (h1). Qed.
Lemma lem3471535 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term260 _90037 s u x.
Proof. exact (proj2 (@lem3471533 _90037 t s u x h1)). Qed.
Lemma lem3471536 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term262 _90037 u s t x.
Proof. exact (proj1 (@lem3471533 _90037 t s u x h1)). Qed.
Lemma lem3471537 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term261 _90037 s t x.
Proof. exact (proj2 (@lem3471536 _90037 t s u x h1)). Qed.
Lemma lem3471541 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term246 _90037 s u t x.
Proof. exact (proj2 (@lem3471534 _90037 s u t x h1)). Qed.
Lemma lem3471542 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term254 _90037 u s x.
Proof. exact (proj1 (@lem3471534 _90037 s u t x h1)). Qed.
Lemma lem3471543 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term244 _90037 u t x.
Proof. exact (proj2 (@lem3471541 _90037 s u t x h1)). Qed.
Lemma lem3471548 {_90037 : Type'} (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term252 _90037 s x.
Proof. exact (h1). Qed.
Lemma lem3471562 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) : (term258 _90037 s u t x) = (term258 _90037 s u t x).
Proof. exact (eq_refl (term258 _90037 s u t x)). Qed.
Lemma lem3471563 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term259 _90037 s u x) = (term259 _90037 s u x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471562 _90037 s u t x)). Qed.
Lemma lem3471564 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3471566 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term260 _90037 s u x) = (term260 _90037 s u x).
Proof. exact (MK_COMB (@lem3471564 _90037) (@lem3471563 _90037 s u x)). Qed.
Lemma lem3471567 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term260 _90037 s u x.
Proof. exact (EQ_MP (@lem3471566 _90037 s u x) (@lem3471535 _90037 t s u x h1)). Qed.
Lemma lem3471595 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) : term242 _90037 u x.
Proof. exact (h1). Qed.
Lemma lem3471615 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) (x : _90037) : (term250 _90037 s t x) = (term250 _90037 s t x).
Proof. exact (eq_refl (term250 _90037 s t x)). Qed.
Lemma lem3471616 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term251 _90037 s x) = (term251 _90037 s x).
Proof. exact (fun_ext (fun t : _90037 -> Prop => @lem3471615 _90037 s t x)). Qed.
Lemma lem3471617 {_90037 : Type'} : (@all (_90037 -> Prop)) = (@all (_90037 -> Prop)).
Proof. exact (eq_refl (@all (_90037 -> Prop))). Qed.
Lemma lem3471619 {_90037 : Type'} (s : type686 _90037) (x : _90037) : (term252 _90037 s x) = (term252 _90037 s x).
Proof. exact (MK_COMB (@lem3471617 _90037) (@lem3471616 _90037 s x)). Qed.
Lemma lem3471620 {_90037 : Type'} (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term252 _90037 s x.
Proof. exact (EQ_MP (@lem3471619 _90037 s x) (@lem3471548 _90037 s x h1)). Qed.
Lemma lem3471621 {_90037 : Type'} (_36669 : _90037 -> Prop) (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term267 _90037 s u x _36669.
Proof. exact (@lem3471567 _90037 t s u x h1 _36669). Qed.
Lemma lem3471622 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (_36669 : _90037 -> Prop) (x : _90037) : (term267 _90037 s u x _36669) = (term258 _90037 s u _36669 x).
Proof. exact (eq_refl (term267 _90037 s u x _36669)). Qed.
Lemma lem3471624 {_90037 : Type'} (_36670 : _90037 -> Prop) (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term268 _90037 s x _36670.
Proof. exact (@lem3471620 _90037 s x h1 _36670). Qed.
Lemma lem3471625 {_90037 : Type'} (s : type686 _90037) (_36670 : _90037 -> Prop) (x : _90037) : (term268 _90037 s x _36670) = (term250 _90037 s _36670 x).
Proof. exact (eq_refl (term268 _90037 s x _36670)). Qed.
Lemma lem3471636 {_90037 : Type'} (_36669 : _90037 -> Prop) (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term258 _90037 s u _36669 x.
Proof. exact (EQ_MP (@lem3471622 _90037 s u _36669 x) (@lem3471621 _90037 _36669 t s u x h1)). Qed.
Lemma lem3471642 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term242 _90037 t x.
Proof. exact (proj2 (@lem3471537 _90037 t s u x h1)). Qed.
Lemma lem3471650 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) : term242 _90037 u x.
Proof. exact (h1). Qed.
Lemma lem3471656 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term242 _90037 t x.
Proof. exact (proj2 (@lem3471543 _90037 s u t x h1)). Qed.
Lemma lem3471662 {_90037 : Type'} (_36670 : _90037 -> Prop) (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term250 _90037 s _36670 x.
Proof. exact (EQ_MP (@lem3471625 _90037 s _36670 x) (@lem3471624 _90037 _36670 s x h1)). Qed.
Lemma lem3471664 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : @I ((_90037 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3471537 _90037 t s u x h1)). Qed.
Lemma lem3471665 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term269 _90037 s t.
Proof. exact (fun h0 : term248 _90037 s t => @lem3471664 _90037 t s u x h1). Qed.
Lemma lem3471667 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471668 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term269 _90037 s t) = (@I ((_90037 -> Prop) -> Prop) s t).
Proof. exact (@lem3471667 (@I ((_90037 -> Prop) -> Prop) s t)). Qed.
Lemma lem3471669 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : @I ((_90037 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3471668 _90037 s t) (@lem3471665 _90037 t s u x h1)). Qed.
Lemma lem3471671 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : @I (_90037 -> Prop) u x.
Proof. exact (proj1 (@lem3471536 _90037 t s u x h1)). Qed.
Lemma lem3471672 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term271 _90037 u x.
Proof. exact (fun h0 : term242 _90037 u x => @lem3471671 _90037 t s u x h1). Qed.
Lemma lem3471674 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471675 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term271 _90037 u x) = (@I (_90037 -> Prop) u x).
Proof. exact (@lem3471674 (@I (_90037 -> Prop) u x)). Qed.
Lemma lem3471676 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : @I (_90037 -> Prop) u x.
Proof. exact (EQ_MP (@lem3471675 _90037 u x) (@lem3471672 _90037 t s u x h1)). Qed.
Lemma lem3471682 (q : Prop) (p : Prop) (r : Prop) : (term272 p q r) = (term272 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3471683 {_90037 : Type'} (u : _90037 -> Prop) (s : type686 _90037) (_36669 : _90037 -> Prop) (x : _90037) : (term258 _90037 s u _36669 x) = (term273 _90037 u s _36669 x).
Proof. exact (@lem3471682 (term242 _90037 u x) (term248 _90037 s _36669) (@I (_90037 -> Prop) _36669 x)). Qed.
Lemma lem3471697 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3471698 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term250 _90037 s _36669 x) = (term274 _90037 x s _36669).
Proof. exact (@lem3471697 (@I (_90037 -> Prop) _36669 x) (term248 _90037 s _36669)). Qed.
Lemma lem3471704 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term253 _90037 u x) = (term253 _90037 u x).
Proof. exact (eq_refl (term253 _90037 u x)). Qed.
Lemma lem3471705 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term273 _90037 u s _36669 x) = (term275 _90037 u x s _36669).
Proof. exact (MK_COMB (@lem3471704 _90037 u x) (@lem3471698 _90037 x s _36669)). Qed.
Lemma lem3471709 (q : Prop) (p : Prop) (r : Prop) : (term272 p q r) = (term272 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3471710 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term275 _90037 u x s _36669) = (term276 _90037 u x s _36669).
Proof. exact (@lem3471709 (@I (_90037 -> Prop) _36669 x) (term242 _90037 u x) (term248 _90037 s _36669)). Qed.
Lemma lem3471726 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term273 _90037 u s _36669 x) = (term276 _90037 u x s _36669).
Proof. exact (TRANS (@lem3471705 _90037 u x s _36669) (@lem3471710 _90037 u x s _36669)). Qed.
Lemma lem3471727 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term258 _90037 s u _36669 x) = (term276 _90037 u x s _36669).
Proof. exact (TRANS (@lem3471683 _90037 u s _36669 x) (@lem3471726 _90037 u x s _36669)). Qed.
Lemma lem3471728 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3471729 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term277 _90037 s u _36669 x) = (term278 _90037 u x s _36669).
Proof. exact (MK_COMB (@lem3471728) (@lem3471727 _90037 u x s _36669)). Qed.
Lemma lem3471743 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3471744 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term279 _90037 s _36669 u x) = (term280 _90037 u x s _36669).
Proof. exact (@lem3471743 (term242 _90037 u x) (term248 _90037 s _36669)). Qed.
Lemma lem3471750 {_90037 : Type'} (_36669 : _90037 -> Prop) (x : _90037) : (term281 _90037 _36669 x) = (term281 _90037 _36669 x).
Proof. exact (eq_refl (term281 _90037 _36669 x)). Qed.
Lemma lem3471751 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : (term282 _90037 s _36669 u x) = (term276 _90037 u x s _36669).
Proof. exact (MK_COMB (@lem3471750 _90037 _36669 x) (@lem3471744 _90037 u x s _36669)). Qed.
Lemma lem3471762 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : ((term258 _90037 s u _36669 x) = (term282 _90037 s _36669 u x)) = ((term276 _90037 u x s _36669) = (term276 _90037 u x s _36669)).
Proof. exact (MK_COMB (@lem3471729 _90037 u x s _36669) (@lem3471751 _90037 u x s _36669)). Qed.
Lemma lem3471764 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3471765 (x : Prop) : (x = x) = True.
Proof. exact (@lem3471764 Prop x). Qed.
Lemma lem3471766 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (s : type686 _90037) (_36669 : _90037 -> Prop) : ((term276 _90037 u x s _36669) = (term276 _90037 u x s _36669)) = True.
Proof. exact (@lem3471765 (term276 _90037 u x s _36669)). Qed.
Lemma lem3471767 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) (u : _90037 -> Prop) (x : _90037) : ((term258 _90037 s u _36669 x) = (term282 _90037 s _36669 u x)) = True.
Proof. exact (TRANS (@lem3471762 _90037 u x s _36669) (@lem3471766 _90037 u x s _36669)). Qed.
Lemma lem3471768 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) (u : _90037 -> Prop) (x : _90037) : True = ((term258 _90037 s u _36669 x) = (term282 _90037 s _36669 u x)).
Proof. exact (SYM (@lem3471767 _90037 s _36669 u x)). Qed.
Lemma lem3471769 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) (u : _90037 -> Prop) (x : _90037) : (term258 _90037 s u _36669 x) = (term282 _90037 s _36669 u x).
Proof. exact (EQ_MP (@lem3471768 _90037 s _36669 u x) (@lem0)). Qed.
Lemma lem3471770 {_90037 : Type'} (_36669 : _90037 -> Prop) (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term282 _90037 s _36669 u x.
Proof. exact (EQ_MP (@lem3471769 _90037 s _36669 u x) (@lem3471636 _90037 _36669 t s u x h1)). Qed.
Lemma lem3471772 (b : Prop) (a : Prop) : (a \/ b) = (term283 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3471773 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (_36669 : _90037 -> Prop) (x : _90037) : (term282 _90037 s _36669 u x) = (term284 _90037 s u _36669 x).
Proof. exact (@lem3471772 (term279 _90037 s _36669 u x) (@I (_90037 -> Prop) _36669 x)). Qed.
Lemma lem3471775 (a : Prop) (b : Prop) : (term285 a b) = (term286 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3471776 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) (u : _90037 -> Prop) (x : _90037) : (term287 _90037 s _36669 u x) = (term288 _90037 s _36669 u x).
Proof. exact (@lem3471775 (term248 _90037 s _36669) (term242 _90037 u x)). Qed.
Lemma lem3471778 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3471779 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) : (term289 _90037 s _36669) = (@I ((_90037 -> Prop) -> Prop) s _36669).
Proof. exact (@lem3471778 (@I ((_90037 -> Prop) -> Prop) s _36669)). Qed.
Lemma lem3471780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3471781 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) : (term290 _90037 s _36669) = (term245 _90037 s _36669).
Proof. exact (MK_COMB (@lem3471780) (@lem3471779 _90037 s _36669)). Qed.
Lemma lem3471783 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3471784 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term291 _90037 u x) = (@I (_90037 -> Prop) u x).
Proof. exact (@lem3471783 (@I (_90037 -> Prop) u x)). Qed.
Lemma lem3471785 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) (u : _90037 -> Prop) (x : _90037) : (term288 _90037 s _36669 u x) = (term292 _90037 s _36669 u x).
Proof. exact (MK_COMB (@lem3471781 _90037 s _36669) (@lem3471784 _90037 u x)). Qed.
Lemma lem3471786 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) (u : _90037 -> Prop) (x : _90037) : (term287 _90037 s _36669 u x) = (term292 _90037 s _36669 u x).
Proof. exact (TRANS (@lem3471776 _90037 s _36669 u x) (@lem3471785 _90037 s _36669 u x)). Qed.
Lemma lem3471787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3471788 {_90037 : Type'} (s : type686 _90037) (_36669 : _90037 -> Prop) (u : _90037 -> Prop) (x : _90037) : (term293 _90037 s _36669 u x) = (term294 _90037 s _36669 u x).
Proof. exact (MK_COMB (@lem3471787) (@lem3471786 _90037 s _36669 u x)). Qed.
Lemma lem3471789 {_90037 : Type'} (_36669 : _90037 -> Prop) (x : _90037) : (@I (_90037 -> Prop) _36669 x) = (@I (_90037 -> Prop) _36669 x).
Proof. exact (eq_refl (@I (_90037 -> Prop) _36669 x)). Qed.
Lemma lem3471790 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (_36669 : _90037 -> Prop) (x : _90037) : (term284 _90037 s u _36669 x) = (term295 _90037 s u _36669 x).
Proof. exact (MK_COMB (@lem3471788 _90037 s _36669 u x) (@lem3471789 _90037 _36669 x)). Qed.
Lemma lem3471791 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (_36669 : _90037 -> Prop) (x : _90037) : (term282 _90037 s _36669 u x) = (term295 _90037 s u _36669 x).
Proof. exact (TRANS (@lem3471773 _90037 s u _36669 x) (@lem3471790 _90037 s u _36669 x)). Qed.
Lemma lem3471793 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term292 _90037 s t u x.
Proof. exact (conj (@lem3471669 _90037 t s u x h1) (@lem3471676 _90037 t s u x h1)). Qed.
Lemma lem3471795 {_90037 : Type'} (_36669 : _90037 -> Prop) (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term295 _90037 s u _36669 x.
Proof. exact (EQ_MP (@lem3471791 _90037 s u _36669 x) (@lem3471770 _90037 _36669 t s u x h1)). Qed.
Lemma lem3471796 {_90037 : Type'} (_36669 : _90037 -> Prop) (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term295 _90037 s u _36669 x.
Proof. exact (@lem3471795 _90037 _36669 t s u x h1). Qed.
Lemma lem3471797 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term295 _90037 s u t x.
Proof. exact (@lem3471796 _90037 t t s u x h1). Qed.
Lemma lem3471800 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : @I (_90037 -> Prop) t x.
Proof. exact (@lem3471797 _90037 t s u x h1 (@lem3471793 _90037 t s u x h1)). Qed.
Lemma lem3471801 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term271 _90037 t x.
Proof. exact (fun h0 : term242 _90037 t x => @lem3471800 _90037 t s u x h1). Qed.
Lemma lem3471803 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471804 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term271 _90037 t x) = (@I (_90037 -> Prop) t x).
Proof. exact (@lem3471803 (@I (_90037 -> Prop) t x)). Qed.
Lemma lem3471805 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : @I (_90037 -> Prop) t x.
Proof. exact (EQ_MP (@lem3471804 _90037 t x) (@lem3471801 _90037 t s u x h1)). Qed.
Lemma lem3471808 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3471810 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term242 _90037 t x) = (term296 _90037 t x).
Proof. exact (@lem3471808 (@I (_90037 -> Prop) t x)). Qed.
Lemma lem3471813 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term296 _90037 t x.
Proof. exact (EQ_MP (@lem3471810 _90037 t x) (@lem3471642 _90037 t s u x h1)). Qed.
Lemma lem3471816 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : False.
Proof. exact (@lem3471813 _90037 t s u x h1 (@lem3471805 _90037 t s u x h1)). Qed.
Lemma lem3471817 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : term297.
Proof. exact (fun h0 : ~ False => @lem3471816 _90037 t s u x h1). Qed.
Lemma lem3471819 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471820 : term297 = False.
Proof. exact (@lem3471819 False). Qed.
Lemma lem3471821 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term264 _90037 t s u x) : False.
Proof. exact (EQ_MP (@lem3471820) (@lem3471817 _90037 t s u x h1)). Qed.
Lemma lem3471823 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : @I (_90037 -> Prop) u x.
Proof. exact (proj1 (@lem3471543 _90037 s u t x h1)). Qed.
Lemma lem3471824 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term271 _90037 u x.
Proof. exact (fun h0 : term242 _90037 u x => @lem3471823 _90037 s u t x h1). Qed.
Lemma lem3471826 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471827 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term271 _90037 u x) = (@I (_90037 -> Prop) u x).
Proof. exact (@lem3471826 (@I (_90037 -> Prop) u x)). Qed.
Lemma lem3471828 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : @I (_90037 -> Prop) u x.
Proof. exact (EQ_MP (@lem3471827 _90037 u x) (@lem3471824 _90037 s u t x h1)). Qed.
Lemma lem3471831 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3471833 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) : (term242 _90037 u x) = (term296 _90037 u x).
Proof. exact (@lem3471831 (@I (_90037 -> Prop) u x)). Qed.
Lemma lem3471836 {_90037 : Type'} (u : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) : term296 _90037 u x.
Proof. exact (EQ_MP (@lem3471833 _90037 u x) (@lem3471650 _90037 u x h1)). Qed.
Lemma lem3471839 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (@lem3471836 _90037 u x h1 (@lem3471828 _90037 s u t x h2)). Qed.
Lemma lem3471840 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : term297.
Proof. exact (fun h0 : ~ False => @lem3471839 _90037 s u t x h1 h2). Qed.
Lemma lem3471842 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471843 : term297 = False.
Proof. exact (@lem3471842 False). Qed.
Lemma lem3471844 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (EQ_MP (@lem3471843) (@lem3471840 _90037 s u t x h1 h2)). Qed.
Lemma lem3471846 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : @I ((_90037 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3471541 _90037 s u t x h1)). Qed.
Lemma lem3471847 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term269 _90037 s t.
Proof. exact (fun h0 : term248 _90037 s t => @lem3471846 _90037 s u t x h1). Qed.
Lemma lem3471849 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471850 {_90037 : Type'} (s : type686 _90037) (t : _90037 -> Prop) : (term269 _90037 s t) = (@I ((_90037 -> Prop) -> Prop) s t).
Proof. exact (@lem3471849 (@I ((_90037 -> Prop) -> Prop) s t)). Qed.
Lemma lem3471851 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : @I ((_90037 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3471850 _90037 s t) (@lem3471847 _90037 s u t x h1)). Qed.
Lemma lem3471857 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3471858 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : (term250 _90037 s _36670 x) = (term274 _90037 x s _36670).
Proof. exact (@lem3471857 (@I (_90037 -> Prop) _36670 x) (term248 _90037 s _36670)). Qed.
Lemma lem3471864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3471865 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : (term298 _90037 s _36670 x) = (term299 _90037 x s _36670).
Proof. exact (MK_COMB (@lem3471864) (@lem3471858 _90037 x s _36670)). Qed.
Lemma lem3471871 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : (term274 _90037 x s _36670) = (term274 _90037 x s _36670).
Proof. exact (eq_refl (term274 _90037 x s _36670)). Qed.
Lemma lem3471872 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : ((term250 _90037 s _36670 x) = (term274 _90037 x s _36670)) = ((term274 _90037 x s _36670) = (term274 _90037 x s _36670)).
Proof. exact (MK_COMB (@lem3471865 _90037 x s _36670) (@lem3471871 _90037 x s _36670)). Qed.
Lemma lem3471874 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3471875 (x : Prop) : (x = x) = True.
Proof. exact (@lem3471874 Prop x). Qed.
Lemma lem3471876 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : ((term274 _90037 x s _36670) = (term274 _90037 x s _36670)) = True.
Proof. exact (@lem3471875 (term274 _90037 x s _36670)). Qed.
Lemma lem3471877 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : ((term250 _90037 s _36670 x) = (term274 _90037 x s _36670)) = True.
Proof. exact (TRANS (@lem3471872 _90037 x s _36670) (@lem3471876 _90037 x s _36670)). Qed.
Lemma lem3471878 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : True = ((term250 _90037 s _36670 x) = (term274 _90037 x s _36670)).
Proof. exact (SYM (@lem3471877 _90037 x s _36670)). Qed.
Lemma lem3471879 {_90037 : Type'} (x : _90037) (s : type686 _90037) (_36670 : _90037 -> Prop) : (term250 _90037 s _36670 x) = (term274 _90037 x s _36670).
Proof. exact (EQ_MP (@lem3471878 _90037 x s _36670) (@lem0)). Qed.
Lemma lem3471880 {_90037 : Type'} (_36670 : _90037 -> Prop) (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term274 _90037 x s _36670.
Proof. exact (EQ_MP (@lem3471879 _90037 x s _36670) (@lem3471662 _90037 _36670 s x h1)). Qed.
Lemma lem3471882 (b : Prop) (a : Prop) : (a \/ b) = (term283 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3471883 {_90037 : Type'} (s : type686 _90037) (_36670 : _90037 -> Prop) (x : _90037) : (term274 _90037 x s _36670) = (term300 _90037 s _36670 x).
Proof. exact (@lem3471882 (term248 _90037 s _36670) (@I (_90037 -> Prop) _36670 x)). Qed.
Lemma lem3471885 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3471886 {_90037 : Type'} (s : type686 _90037) (_36670 : _90037 -> Prop) : (term289 _90037 s _36670) = (@I ((_90037 -> Prop) -> Prop) s _36670).
Proof. exact (@lem3471885 (@I ((_90037 -> Prop) -> Prop) s _36670)). Qed.
Lemma lem3471887 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3471888 {_90037 : Type'} (s : type686 _90037) (_36670 : _90037 -> Prop) : (term301 _90037 s _36670) = (term302 _90037 s _36670).
Proof. exact (MK_COMB (@lem3471887) (@lem3471886 _90037 s _36670)). Qed.
Lemma lem3471889 {_90037 : Type'} (_36670 : _90037 -> Prop) (x : _90037) : (@I (_90037 -> Prop) _36670 x) = (@I (_90037 -> Prop) _36670 x).
Proof. exact (eq_refl (@I (_90037 -> Prop) _36670 x)). Qed.
Lemma lem3471890 {_90037 : Type'} (s : type686 _90037) (_36670 : _90037 -> Prop) (x : _90037) : (term300 _90037 s _36670 x) = (term303 _90037 s _36670 x).
Proof. exact (MK_COMB (@lem3471888 _90037 s _36670) (@lem3471889 _90037 _36670 x)). Qed.
Lemma lem3471891 {_90037 : Type'} (s : type686 _90037) (_36670 : _90037 -> Prop) (x : _90037) : (term274 _90037 x s _36670) = (term303 _90037 s _36670 x).
Proof. exact (TRANS (@lem3471883 _90037 s _36670 x) (@lem3471890 _90037 s _36670 x)). Qed.
Lemma lem3471894 {_90037 : Type'} (_36670 : _90037 -> Prop) (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term303 _90037 s _36670 x.
Proof. exact (EQ_MP (@lem3471891 _90037 s _36670 x) (@lem3471880 _90037 _36670 s x h1)). Qed.
Lemma lem3471895 {_90037 : Type'} (_36670 : _90037 -> Prop) (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term303 _90037 s _36670 x.
Proof. exact (@lem3471894 _90037 _36670 s x h1). Qed.
Lemma lem3471896 {_90037 : Type'} (t : _90037 -> Prop) (s : type686 _90037) (x : _90037) (h1 : term252 _90037 s x) : term303 _90037 s t x.
Proof. exact (@lem3471895 _90037 t s x h1). Qed.
Lemma lem3471899 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : @I (_90037 -> Prop) t x.
Proof. exact (@lem3471896 _90037 t s x h1 (@lem3471851 _90037 s u t x h2)). Qed.
Lemma lem3471900 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : term271 _90037 t x.
Proof. exact (fun h0 : term242 _90037 t x => @lem3471899 _90037 s u t x h1 h2). Qed.
Lemma lem3471902 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471903 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term271 _90037 t x) = (@I (_90037 -> Prop) t x).
Proof. exact (@lem3471902 (@I (_90037 -> Prop) t x)). Qed.
Lemma lem3471904 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : @I (_90037 -> Prop) t x.
Proof. exact (EQ_MP (@lem3471903 _90037 t x) (@lem3471900 _90037 s u t x h1 h2)). Qed.
Lemma lem3471907 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3471909 {_90037 : Type'} (t : _90037 -> Prop) (x : _90037) : (term242 _90037 t x) = (term296 _90037 t x).
Proof. exact (@lem3471907 (@I (_90037 -> Prop) t x)). Qed.
Lemma lem3471912 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : term296 _90037 t x.
Proof. exact (EQ_MP (@lem3471909 _90037 t x) (@lem3471656 _90037 s u t x h1)). Qed.
Lemma lem3471915 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (@lem3471912 _90037 s u t x h2 (@lem3471904 _90037 s u t x h1 h2)). Qed.
Lemma lem3471916 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : term297.
Proof. exact (fun h0 : ~ False => @lem3471915 _90037 s u t x h1 h2). Qed.
Lemma lem3471918 (p : Prop) : (term270 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3471919 : term297 = False.
Proof. exact (@lem3471918 False). Qed.
Lemma lem3471920 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (EQ_MP (@lem3471919) (@lem3471916 _90037 s u t x h1 h2)). Qed.
Lemma lem3471921 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : (term242 _90037 u x) = False.
Proof. exact (prop_ext (fun h3 : term242 _90037 u x => @lem3471844 _90037 s u t x h1 h2) (fun h3 : False => @lem3471650 _90037 u x h1)). Qed.
Lemma lem3471922 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (EQ_MP (@lem3471921 _90037 s u t x h1 h2) (@lem3471650 _90037 u x h1)). Qed.
Lemma lem3471923 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : (term242 _90037 u x) = False.
Proof. exact (prop_ext (fun h3 : term242 _90037 u x => @lem3471922 _90037 s u t x h1 h2) (fun h3 : False => @lem3471595 _90037 u x h1)). Qed.
Lemma lem3471924 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (EQ_MP (@lem3471923 _90037 s u t x h1 h2) (@lem3471595 _90037 u x h1)). Qed.
Lemma lem3471925 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : (term252 _90037 s x) = False.
Proof. exact (prop_ext (fun h3 : term252 _90037 s x => @lem3471920 _90037 s u t x h1 h2) (fun h3 : False => @lem3471620 _90037 s x h1)). Qed.
Lemma lem3471926 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term252 _90037 s x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (EQ_MP (@lem3471925 _90037 s u t x h1 h2) (@lem3471620 _90037 s x h1)). Qed.
Lemma lem3471927 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : (term242 _90037 u x) = False.
Proof. exact (prop_ext (fun h3 : term242 _90037 u x => @lem3471924 _90037 s u t x h1 h2) (fun h3 : False => @lem3471595 _90037 u x h1)). Qed.
Lemma lem3471928 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term242 _90037 u x) (h2 : term256 _90037 s u t x) : False.
Proof. exact (EQ_MP (@lem3471927 _90037 s u t x h1 h2) (@lem3471595 _90037 u x h1)). Qed.
Lemma lem3471929 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term256 _90037 s u t x) : False.
Proof. exact (or_elim (@lem3471542 _90037 s u t x h1) (fun h0 : term242 _90037 u x => @lem3471928 _90037 s u t x h0 h1) (fun h0 : term252 _90037 s x => @lem3471926 _90037 s u t x h0 h1)). Qed.
Lemma lem3471930 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (t : _90037 -> Prop) (x : _90037) (h1 : term238 _90037 s u t x) : False.
Proof. exact (or_elim (@lem3471532 _90037 s u t x h1) (fun h0 : term264 _90037 t s u x => @lem3471821 _90037 t s u x h0) (fun h0 : term256 _90037 s u t x => @lem3471929 _90037 s u t x h0)). Qed.
Lemma lem3471931 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term121 _90037 s u x) : False.
Proof. exact (ex_elim (@lem3471383 _90037 s u x h1) (fun t : _90037 -> Prop => fun h0 : term240 _90037 s u x t => @lem3471930 _90037 s u t x h0)). Qed.
Lemma lem3471932 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term121 _90037 s u x) : (term121 _90037 s u x) = False.
Proof. exact (prop_ext (fun h2 : term121 _90037 s u x => @lem3471931 _90037 s u x h1) (fun h2 : False => @lem3471040 _90037 s u x h1)). Qed.
Lemma lem3471933 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) (h1 : term121 _90037 s u x) : False.
Proof. exact (EQ_MP (@lem3471932 _90037 s u x h1) (@lem3471040 _90037 s u x h1)). Qed.
Lemma lem3471934 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : term120 _90037 s u x.
Proof. exact (fun h0 : term121 _90037 s u x => @lem3471933 _90037 s u x h0). Qed.
Lemma lem3471935 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) (x : _90037) : (term82 _90037 u s x) = (term104 _90037 s u x).
Proof. exact (EQ_MP (@lem3471039 _90037 s u x) (@lem3471934 _90037 s u x)). Qed.
Lemma lem3471940 {_90037 : Type'} (s : type686 _90037) (u : _90037 -> Prop) : term107 _90037 s u.
Proof. exact (fun x : _90037 => @lem3471935 _90037 s u x). Qed.
Lemma lem3471945 {_90037 : Type'} (u : _90037 -> Prop) : term109 _90037 u.
Proof. exact (fun s : type686 _90037 => @lem3471940 _90037 s u). Qed.
Lemma lem3471950 {_90037 : Type'} : term111 _90037.
Proof. exact (fun u : _90037 -> Prop => @lem3471945 _90037 u). Qed.
Lemma lem3471951 {_90037 : Type'} : term113 _90037.
Proof. exact (EQ_MP (@lem3471035 _90037) (@lem3471950 _90037)). Qed.
Lemma lem3471953 {_90037 : Type'} : term113 _90037.
Proof. exact (@lem3470890 _90037 (@lem3471951 _90037)). Qed.
Lemma lem3471954 {_90037 : Type'} (h1 : term114 _90037) : False.
Proof. exact (@lem3471953 _90037 (@lem3470874 _90037 h1)). Qed.
Lemma lem3471955 {_90037 : Type'} (h1 : term114 _90037) : (term114 _90037) = False.
Proof. exact (prop_ext (fun h2 : term114 _90037 => @lem3471954 _90037 h1) (fun h2 : False => @lem3470874 _90037 h1)). Qed.
Lemma lem3471956 {_90037 : Type'} (h1 : term114 _90037) : False.
Proof. exact (EQ_MP (@lem3471955 _90037 h1) (@lem3470874 _90037 h1)). Qed.
Lemma lem3471957 {_90037 : Type'} : term113 _90037.
Proof. exact (fun h0 : term114 _90037 => @lem3471956 _90037 h0). Qed.
Lemma lem3471958 {_90037 : Type'} : term111 _90037.
Proof. exact (EQ_MP (@lem3470873 _90037) (@lem3471957 _90037)). Qed.
Lemma lem3471959 {_90037 : Type'} : term65 _90037.
Proof. exact (EQ_MP (@lem3470869 _90037) (@lem3471958 _90037)). Qed.
Lemma lem3471960 {_90037 : Type'} : term59 _90037.
Proof. exact (EQ_MP (@lem3470713 _90037) (@lem3471959 _90037)). Qed.
Lemma lem3471961 {_90037 : Type'} : term58 _90037.
Proof. exact (EQ_MP (@lem3470666 _90037) (@lem3471960 _90037)). Qed.
