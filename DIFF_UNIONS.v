Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIFF_UNIONS_term_abbrevs.
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
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211640_spec.
Require Import thm3211641_spec.
Require Import thm3211662_spec.
Require Import thm3211663_spec.
Require Import thm3211701_spec.
Require Import thm3211702_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm3464405_spec.
Require Import thm3464408_spec.
Lemma lem3474680 {_89711 _89725 : Type'} : term0 _89711 _89725.
Proof. exact (EQ_MP (@lem3464408 _89711 _89725) (@lem3464405 _89711 _89725)). Qed.
Lemma lem3474681 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term1 _89711 _89725 P.
Proof. exact (@lem3474680 _89711 _89725 P). Qed.
Lemma lem3474682 {_89711 _89725 : Type'} (P : _89725 -> Prop) : (term1 _89711 _89725 P) = (term2 _89711 _89725 P).
Proof. exact (eq_refl (term1 _89711 _89725 P)). Qed.
Lemma lem3474683 {_89711 _89725 : Type'} (P : _89725 -> Prop) : term2 _89711 _89725 P.
Proof. exact (EQ_MP (@lem3474682 _89711 _89725 P) (@lem3474681 _89711 _89725 P)). Qed.
Lemma lem3474684 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : term3 _89711 _89725 P f.
Proof. exact (@lem3474683 _89711 _89725 P f). Qed.
Lemma lem3474685 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term3 _89711 _89725 P f) = ((term4 _89711 _89725 P f) = (term5 _89711 _89725 P f)).
Proof. exact (eq_refl (term3 _89711 _89725 P f)). Qed.
Lemma lem3474698 {_89711 _89725 : Type'} (P : _89725 -> Prop) (f : type1470 _89711 _89725) : (term4 _89711 _89725 P f) = (term5 _89711 _89725 P f).
Proof. exact (EQ_MP (@lem3474685 _89711 _89725 P f) (@lem3474684 _89711 _89725 P f)). Qed.
Lemma lem3474699 {_90184 : Type'} (P : type686 _90184) (f : type672 _90184) : (term6 _90184 P f) = (term7 _90184 P f).
Proof. exact (@lem3474698 _90184 (_90184 -> Prop) P f). Qed.
Lemma lem3474700 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term8 _90184 s u) = (term9 _90184 s u).
Proof. exact (@lem3474699 _90184 (term10 _90184 s) (term11 _90184 u)). Qed.
Lemma lem3474701 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) : (term12 _90184 s t) = (@IN (_90184 -> Prop) t s).
Proof. exact (eq_refl (term12 _90184 s t)). Qed.
Lemma lem3474702 {_90184 : Type'} (GEN_PVAR_68 : _90184 -> Prop) : (@SETSPEC (_90184 -> Prop) GEN_PVAR_68) = (@SETSPEC (_90184 -> Prop) GEN_PVAR_68).
Proof. exact (eq_refl (@SETSPEC (_90184 -> Prop) GEN_PVAR_68)). Qed.
Lemma lem3474703 {_90184 : Type'} (GEN_PVAR_68 : _90184 -> Prop) (t : _90184 -> Prop) (s : type686 _90184) : (term13 _90184 GEN_PVAR_68 s t) = (term14 _90184 GEN_PVAR_68 t s).
Proof. exact (MK_COMB (@lem3474702 _90184 GEN_PVAR_68) (@lem3474701 _90184 t s)). Qed.
Lemma lem3474704 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) : (term15 _90184 u t) = (@DIFF _90184 u t).
Proof. exact (eq_refl (term15 _90184 u t)). Qed.
Lemma lem3474705 {_90184 : Type'} (GEN_PVAR_68 : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) : (term16 _90184 GEN_PVAR_68 s u t) = (term17 _90184 GEN_PVAR_68 s u t).
Proof. exact (MK_COMB (@lem3474703 _90184 GEN_PVAR_68 t s) (@lem3474704 _90184 u t)). Qed.
Lemma lem3474706 {_90184 : Type'} (GEN_PVAR_68 : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) : (term18 _90184 GEN_PVAR_68 s u) = (term19 _90184 GEN_PVAR_68 s u).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3474705 _90184 GEN_PVAR_68 s u t)). Qed.
Lemma lem3474707 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3474708 {_90184 : Type'} (GEN_PVAR_68 : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) : (term20 _90184 GEN_PVAR_68 s u) = (term21 _90184 GEN_PVAR_68 s u).
Proof. exact (MK_COMB (@lem3474707 _90184) (@lem3474706 _90184 GEN_PVAR_68 s u)). Qed.
Lemma lem3474709 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term22 _90184 s u) = (term23 _90184 s u).
Proof. exact (fun_ext (fun GEN_PVAR_68 : _90184 -> Prop => @lem3474708 _90184 GEN_PVAR_68 s u)). Qed.
Lemma lem3474710 {_90184 : Type'} : (@GSPEC (_90184 -> Prop)) = (@GSPEC (_90184 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_90184 -> Prop))). Qed.
Lemma lem3474711 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term24 _90184 s u) = (term25 _90184 s u).
Proof. exact (MK_COMB (@lem3474710 _90184) (@lem3474709 _90184 s u)). Qed.
Lemma lem3474712 {_90184 : Type'} : (@INTERS _90184) = (@INTERS _90184).
Proof. exact (eq_refl (@INTERS _90184)). Qed.
Lemma lem3474713 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term8 _90184 s u) = (term26 _90184 s u).
Proof. exact (MK_COMB (@lem3474712 _90184) (@lem3474711 _90184 s u)). Qed.
Lemma lem3474714 {_90184 : Type'} : (@eq (_90184 -> Prop)) = (@eq (_90184 -> Prop)).
Proof. exact (eq_refl (@eq (_90184 -> Prop))). Qed.
Lemma lem3474715 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term27 _90184 s u) = (term28 _90184 s u).
Proof. exact (MK_COMB (@lem3474714 _90184) (@lem3474713 _90184 s u)). Qed.
Lemma lem3474716 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) : (term12 _90184 s t) = (@IN (_90184 -> Prop) t s).
Proof. exact (eq_refl (term12 _90184 s t)). Qed.
Lemma lem3474717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3474718 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) : (term29 _90184 s t) = (term30 _90184 t s).
Proof. exact (MK_COMB (@lem3474717) (@lem3474716 _90184 t s)). Qed.
Lemma lem3474719 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) : (term15 _90184 u t) = (@DIFF _90184 u t).
Proof. exact (eq_refl (term15 _90184 u t)). Qed.
Lemma lem3474720 {_90184 : Type'} (a : _90184) : (@IN _90184 a) = (@IN _90184 a).
Proof. exact (eq_refl (@IN _90184 a)). Qed.
Lemma lem3474721 {_90184 : Type'} (a : _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) : (term31 _90184 a u t) = (term32 _90184 a u t).
Proof. exact (MK_COMB (@lem3474720 _90184 a) (@lem3474719 _90184 u t)). Qed.
Lemma lem3474722 {_90184 : Type'} (s : type686 _90184) (a : _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) : (term33 _90184 s a u t) = (term34 _90184 s a u t).
Proof. exact (MK_COMB (@lem3474718 _90184 t s) (@lem3474721 _90184 a u t)). Qed.
Lemma lem3474723 {_90184 : Type'} (s : type686 _90184) (a : _90184) (u : _90184 -> Prop) : (term35 _90184 s a u) = (term36 _90184 s a u).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3474722 _90184 s a u t)). Qed.
Lemma lem3474724 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3474725 {_90184 : Type'} (s : type686 _90184) (a : _90184) (u : _90184 -> Prop) : (term37 _90184 s a u) = (term38 _90184 s a u).
Proof. exact (MK_COMB (@lem3474724 _90184) (@lem3474723 _90184 s a u)). Qed.
Lemma lem3474726 {_90184 : Type'} (GEN_PVAR_56 : _90184) : (@SETSPEC _90184 GEN_PVAR_56) = (@SETSPEC _90184 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _90184 GEN_PVAR_56)). Qed.
Lemma lem3474727 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (a : _90184) (u : _90184 -> Prop) : (term39 _90184 GEN_PVAR_56 s a u) = (term40 _90184 GEN_PVAR_56 s a u).
Proof. exact (MK_COMB (@lem3474726 _90184 GEN_PVAR_56) (@lem3474725 _90184 s a u)). Qed.
Lemma lem3474728 {_90184 : Type'} (a : _90184) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3474729 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (u : _90184 -> Prop) (a : _90184) : (term41 _90184 GEN_PVAR_56 s u a) = (term42 _90184 GEN_PVAR_56 s u a).
Proof. exact (MK_COMB (@lem3474727 _90184 GEN_PVAR_56 s a u) (@lem3474728 _90184 a)). Qed.
Lemma lem3474730 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (u : _90184 -> Prop) : (term43 _90184 GEN_PVAR_56 s u) = (term44 _90184 GEN_PVAR_56 s u).
Proof. exact (fun_ext (fun a : _90184 => @lem3474729 _90184 GEN_PVAR_56 s u a)). Qed.
Lemma lem3474731 {_90184 : Type'} : (@ex _90184) = (@ex _90184).
Proof. exact (eq_refl (@ex _90184)). Qed.
Lemma lem3474732 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (u : _90184 -> Prop) : (term45 _90184 GEN_PVAR_56 s u) = (term46 _90184 GEN_PVAR_56 s u).
Proof. exact (MK_COMB (@lem3474731 _90184) (@lem3474730 _90184 GEN_PVAR_56 s u)). Qed.
Lemma lem3474733 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term47 _90184 s u) = (term48 _90184 s u).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _90184 => @lem3474732 _90184 GEN_PVAR_56 s u)). Qed.
Lemma lem3474734 {_90184 : Type'} : (@GSPEC _90184) = (@GSPEC _90184).
Proof. exact (eq_refl (@GSPEC _90184)). Qed.
Lemma lem3474735 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term9 _90184 s u) = (term49 _90184 s u).
Proof. exact (MK_COMB (@lem3474734 _90184) (@lem3474733 _90184 s u)). Qed.
Lemma lem3474736 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : ((term8 _90184 s u) = (term9 _90184 s u)) = ((term26 _90184 s u) = (term49 _90184 s u)).
Proof. exact (MK_COMB (@lem3474715 _90184 s u) (@lem3474735 _90184 s u)). Qed.
Lemma lem3474737 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term26 _90184 s u) = (term49 _90184 s u).
Proof. exact (EQ_MP (@lem3474736 _90184 s u) (@lem3474700 _90184 s u)). Qed.
Lemma lem3474748 {_90184 : Type'} (u : _90184 -> Prop) : (@INTER _90184 u) = (@INTER _90184 u).
Proof. exact (eq_refl (@INTER _90184 u)). Qed.
Lemma lem3474749 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term50 _90184 s u) = (term51 _90184 s u).
Proof. exact (MK_COMB (@lem3474748 _90184 u) (@lem3474737 _90184 s u)). Qed.
Lemma lem3474750 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) : (term52 _90184 u s) = (term52 _90184 u s).
Proof. exact (eq_refl (term52 _90184 u s)). Qed.
Lemma lem3474751 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : ((term53 _90184 u s) = (term50 _90184 s u)) = ((term53 _90184 u s) = (term51 _90184 s u)).
Proof. exact (MK_COMB (@lem3474750 _90184 u s) (@lem3474749 _90184 s u)). Qed.
Lemma lem3474754 {_90184 : Type'} (u : _90184 -> Prop) : (term54 _90184 u) = (term55 _90184 u).
Proof. exact (fun_ext (fun s : type686 _90184 => @lem3474751 _90184 s u)). Qed.
Lemma lem3474755 {_90184 : Type'} : (@all ((_90184 -> Prop) -> Prop)) = (@all ((_90184 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90184 -> Prop) -> Prop))). Qed.
Lemma lem3474756 {_90184 : Type'} (u : _90184 -> Prop) : (term56 _90184 u) = (term57 _90184 u).
Proof. exact (MK_COMB (@lem3474755 _90184) (@lem3474754 _90184 u)). Qed.
Lemma lem3474761 {_90184 : Type'} : (term58 _90184) = (term59 _90184).
Proof. exact (fun_ext (fun u : _90184 -> Prop => @lem3474756 _90184 u)). Qed.
Lemma lem3474762 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3474763 {_90184 : Type'} : (term60 _90184) = (term61 _90184).
Proof. exact (MK_COMB (@lem3474762 _90184) (@lem3474761 _90184)). Qed.
Lemma lem3474768 {_90184 : Type'} : (term61 _90184) = (term60 _90184).
Proof. exact (SYM (@lem3474763 _90184)). Qed.
Lemma lem3474780 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term62 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3474781 {_90184 : Type'} (s : _90184 -> Prop) (t : _90184 -> Prop) : (s = t) = (term62 _90184 s t).
Proof. exact (@lem3474780 _90184 s t). Qed.
Lemma lem3474782 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : ((term53 _90184 u s) = (term51 _90184 s u)) = (term63 _90184 s u).
Proof. exact (@lem3474781 _90184 (term53 _90184 u s) (term51 _90184 s u)). Qed.
Lemma lem3474801 {_90184 : Type'} (u : _90184 -> Prop) : (term55 _90184 u) = (term64 _90184 u).
Proof. exact (fun_ext (fun s : type686 _90184 => @lem3474782 _90184 s u)). Qed.
Lemma lem3474802 {_90184 : Type'} : (@all ((_90184 -> Prop) -> Prop)) = (@all ((_90184 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90184 -> Prop) -> Prop))). Qed.
Lemma lem3474803 {_90184 : Type'} (u : _90184 -> Prop) : (term57 _90184 u) = (term65 _90184 u).
Proof. exact (MK_COMB (@lem3474802 _90184) (@lem3474801 _90184 u)). Qed.
Lemma lem3474808 {_90184 : Type'} : (term59 _90184) = (term66 _90184).
Proof. exact (fun_ext (fun u : _90184 -> Prop => @lem3474803 _90184 u)). Qed.
Lemma lem3474809 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3474810 {_90184 : Type'} : (term61 _90184) = (term67 _90184).
Proof. exact (MK_COMB (@lem3474809 _90184) (@lem3474808 _90184)). Qed.
Lemma lem3474815 {_90184 : Type'} : (term67 _90184) = (term61 _90184).
Proof. exact (SYM (@lem3474810 _90184)). Qed.
Lemma lem3474831 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term68 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3474832 {_90184 : Type'} (s : _90184 -> Prop) (x : _90184) (t : _90184 -> Prop) : (term32 _90184 x s t) = (term68 _90184 s x t).
Proof. exact (@lem3474831 _90184 s x t). Qed.
Lemma lem3474833 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (s : type686 _90184) : (term69 _90184 x u s) = (term70 _90184 u x s).
Proof. exact (@lem3474832 _90184 u x (@UNIONS _90184 s)). Qed.
Lemma lem3474837 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3474838 {_90184 : Type'} (P : _90184 -> Prop) (x : _90184) : (@IN _90184 x P) = (P x).
Proof. exact (@lem3474837 _90184 P x). Qed.
Lemma lem3474839 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (@IN _90184 x u) = (u x).
Proof. exact (@lem3474838 _90184 u x). Qed.
Lemma lem3474840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474841 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term71 _90184 x u) = (term72 _90184 u x).
Proof. exact (MK_COMB (@lem3474840) (@lem3474839 _90184 u x)). Qed.
Lemma lem3474843 {A : Type'} (s : type686 A) (x : A) : (term73 A x s) = (term74 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem3474844 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term73 _90184 x s) = (term74 _90184 s x).
Proof. exact (@lem3474843 _90184 s x). Qed.
Lemma lem3474852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3474853 {_90184 : Type'} (P : type686 _90184) (x : _90184 -> Prop) : (@IN (_90184 -> Prop) x P) = (P x).
Proof. exact (@lem3474852 (_90184 -> Prop) P x). Qed.
Lemma lem3474854 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (@IN (_90184 -> Prop) t s) = (s t).
Proof. exact (@lem3474853 _90184 s t). Qed.
Lemma lem3474855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474856 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term75 _90184 t s) = (term76 _90184 s t).
Proof. exact (MK_COMB (@lem3474855) (@lem3474854 _90184 s t)). Qed.
Lemma lem3474858 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3474859 {_90184 : Type'} (P : _90184 -> Prop) (x : _90184) : (@IN _90184 x P) = (P x).
Proof. exact (@lem3474858 _90184 P x). Qed.
Lemma lem3474860 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (@IN _90184 x t) = (t x).
Proof. exact (@lem3474859 _90184 t x). Qed.
Lemma lem3474861 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term77 _90184 s x t) = (term78 _90184 s t x).
Proof. exact (MK_COMB (@lem3474856 _90184 s t) (@lem3474860 _90184 t x)). Qed.
Lemma lem3474864 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term79 _90184 s x) = (term80 _90184 s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3474861 _90184 s t x)). Qed.
Lemma lem3474865 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3474866 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term74 _90184 s x) = (term81 _90184 s x).
Proof. exact (MK_COMB (@lem3474865 _90184) (@lem3474864 _90184 s x)). Qed.
Lemma lem3474871 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term73 _90184 x s) = (term81 _90184 s x).
Proof. exact (TRANS (@lem3474844 _90184 s x) (@lem3474866 _90184 s x)). Qed.
Lemma lem3474872 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474873 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term82 _90184 x s) = (term83 _90184 s x).
Proof. exact (MK_COMB (@lem3474872) (@lem3474871 _90184 s x)). Qed.
Lemma lem3474874 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term70 _90184 u x s) = (term84 _90184 u s x).
Proof. exact (MK_COMB (@lem3474841 _90184 u x) (@lem3474873 _90184 s x)). Qed.
Lemma lem3474877 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term69 _90184 x u s) = (term84 _90184 u s x).
Proof. exact (TRANS (@lem3474833 _90184 u x s) (@lem3474874 _90184 u s x)). Qed.
Lemma lem3474878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474879 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term85 _90184 x u s) = (term86 _90184 u s x).
Proof. exact (MK_COMB (@lem3474878) (@lem3474877 _90184 u s x)). Qed.
Lemma lem3474881 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term87 A x s t) = (term88 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3474882 {_90184 : Type'} (s : _90184 -> Prop) (x : _90184) (t : _90184 -> Prop) : (term87 _90184 x s t) = (term88 _90184 s x t).
Proof. exact (@lem3474881 _90184 s x t). Qed.
Lemma lem3474883 {_90184 : Type'} (x : _90184) (s : type686 _90184) (u : _90184 -> Prop) : (term89 _90184 x s u) = (term90 _90184 x s u).
Proof. exact (@lem3474882 _90184 u x (term49 _90184 s u)). Qed.
Lemma lem3474887 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3474888 {_90184 : Type'} (P : _90184 -> Prop) (x : _90184) : (@IN _90184 x P) = (P x).
Proof. exact (@lem3474887 _90184 P x). Qed.
Lemma lem3474889 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (@IN _90184 x u) = (u x).
Proof. exact (@lem3474888 _90184 u x). Qed.
Lemma lem3474890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474891 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term71 _90184 x u) = (term72 _90184 u x).
Proof. exact (MK_COMB (@lem3474890) (@lem3474889 _90184 u x)). Qed.
Lemma lem3474893 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term91 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem3474894 {_90184 : Type'} (p : _90184 -> Prop) (x : _90184) : (term91 _90184 x p) = (p x).
Proof. exact (@lem3474893 _90184 p x). Qed.
Lemma lem3474895 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term92 _90184 x s u) = (term93 _90184 s u x).
Proof. exact (@lem3474894 _90184 (term94 _90184 s u) x). Qed.
Lemma lem3474896 {_90184 : Type'} (s : type686 _90184) (a : _90184) (u : _90184 -> Prop) : (term93 _90184 s u a) = (term38 _90184 s a u).
Proof. exact (eq_refl (term93 _90184 s u a)). Qed.
Lemma lem3474897 {_90184 : Type'} (GEN_PVAR_56 : _90184) : (@SETSPEC _90184 GEN_PVAR_56) = (@SETSPEC _90184 GEN_PVAR_56).
Proof. exact (eq_refl (@SETSPEC _90184 GEN_PVAR_56)). Qed.
Lemma lem3474898 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (a : _90184) (u : _90184 -> Prop) : (term95 _90184 GEN_PVAR_56 s u a) = (term40 _90184 GEN_PVAR_56 s a u).
Proof. exact (MK_COMB (@lem3474897 _90184 GEN_PVAR_56) (@lem3474896 _90184 s a u)). Qed.
Lemma lem3474899 {_90184 : Type'} (a : _90184) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3474900 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (u : _90184 -> Prop) (a : _90184) : (term96 _90184 GEN_PVAR_56 s u a) = (term42 _90184 GEN_PVAR_56 s u a).
Proof. exact (MK_COMB (@lem3474898 _90184 GEN_PVAR_56 s a u) (@lem3474899 _90184 a)). Qed.
Lemma lem3474901 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (u : _90184 -> Prop) : (term97 _90184 GEN_PVAR_56 s u) = (term44 _90184 GEN_PVAR_56 s u).
Proof. exact (fun_ext (fun a : _90184 => @lem3474900 _90184 GEN_PVAR_56 s u a)). Qed.
Lemma lem3474902 {_90184 : Type'} : (@ex _90184) = (@ex _90184).
Proof. exact (eq_refl (@ex _90184)). Qed.
Lemma lem3474903 {_90184 : Type'} (GEN_PVAR_56 : _90184) (s : type686 _90184) (u : _90184 -> Prop) : (term98 _90184 GEN_PVAR_56 s u) = (term46 _90184 GEN_PVAR_56 s u).
Proof. exact (MK_COMB (@lem3474902 _90184) (@lem3474901 _90184 GEN_PVAR_56 s u)). Qed.
Lemma lem3474904 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term99 _90184 s u) = (term48 _90184 s u).
Proof. exact (fun_ext (fun GEN_PVAR_56 : _90184 => @lem3474903 _90184 GEN_PVAR_56 s u)). Qed.
Lemma lem3474905 {_90184 : Type'} : (@GSPEC _90184) = (@GSPEC _90184).
Proof. exact (eq_refl (@GSPEC _90184)). Qed.
Lemma lem3474906 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term100 _90184 s u) = (term49 _90184 s u).
Proof. exact (MK_COMB (@lem3474905 _90184) (@lem3474904 _90184 s u)). Qed.
Lemma lem3474907 {_90184 : Type'} (x : _90184) : (@IN _90184 x) = (@IN _90184 x).
Proof. exact (eq_refl (@IN _90184 x)). Qed.
Lemma lem3474908 {_90184 : Type'} (x : _90184) (s : type686 _90184) (u : _90184 -> Prop) : (term92 _90184 x s u) = (term101 _90184 x s u).
Proof. exact (MK_COMB (@lem3474907 _90184 x) (@lem3474906 _90184 s u)). Qed.
Lemma lem3474909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3474910 {_90184 : Type'} (x : _90184) (s : type686 _90184) (u : _90184 -> Prop) : (term102 _90184 x s u) = (term103 _90184 x s u).
Proof. exact (MK_COMB (@lem3474909) (@lem3474908 _90184 x s u)). Qed.
Lemma lem3474911 {_90184 : Type'} (s : type686 _90184) (x : _90184) (u : _90184 -> Prop) : (term93 _90184 s u x) = (term38 _90184 s x u).
Proof. exact (eq_refl (term93 _90184 s u x)). Qed.
Lemma lem3474912 {_90184 : Type'} (s : type686 _90184) (x : _90184) (u : _90184 -> Prop) : ((term92 _90184 x s u) = (term93 _90184 s u x)) = ((term101 _90184 x s u) = (term38 _90184 s x u)).
Proof. exact (MK_COMB (@lem3474910 _90184 x s u) (@lem3474911 _90184 s x u)). Qed.
Lemma lem3474913 {_90184 : Type'} (s : type686 _90184) (x : _90184) (u : _90184 -> Prop) : (term101 _90184 x s u) = (term38 _90184 s x u).
Proof. exact (EQ_MP (@lem3474912 _90184 s x u) (@lem3474895 _90184 s u x)). Qed.
Lemma lem3474921 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3474922 {_90184 : Type'} (P : type686 _90184) (x : _90184 -> Prop) : (@IN (_90184 -> Prop) x P) = (P x).
Proof. exact (@lem3474921 (_90184 -> Prop) P x). Qed.
Lemma lem3474923 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (@IN (_90184 -> Prop) t s) = (s t).
Proof. exact (@lem3474922 _90184 s t). Qed.
Lemma lem3474924 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3474925 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term30 _90184 t s) = (term104 _90184 s t).
Proof. exact (MK_COMB (@lem3474924) (@lem3474923 _90184 s t)). Qed.
Lemma lem3474927 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term32 A x s t) = (term68 A s x t).
Proof. exact (EQ_MP (@lem3211702 A s x t) (@lem3211701 A s t x)). Qed.
Lemma lem3474928 {_90184 : Type'} (s : _90184 -> Prop) (x : _90184) (t : _90184 -> Prop) : (term32 _90184 x s t) = (term68 _90184 s x t).
Proof. exact (@lem3474927 _90184 s x t). Qed.
Lemma lem3474929 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (t : _90184 -> Prop) : (term32 _90184 x u t) = (term68 _90184 u x t).
Proof. exact (@lem3474928 _90184 u x t). Qed.
Lemma lem3474933 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3474934 {_90184 : Type'} (P : _90184 -> Prop) (x : _90184) : (@IN _90184 x P) = (P x).
Proof. exact (@lem3474933 _90184 P x). Qed.
Lemma lem3474935 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (@IN _90184 x u) = (u x).
Proof. exact (@lem3474934 _90184 u x). Qed.
Lemma lem3474936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3474937 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term71 _90184 x u) = (term72 _90184 u x).
Proof. exact (MK_COMB (@lem3474936) (@lem3474935 _90184 u x)). Qed.
Lemma lem3474939 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3474940 {_90184 : Type'} (P : _90184 -> Prop) (x : _90184) : (@IN _90184 x P) = (P x).
Proof. exact (@lem3474939 _90184 P x). Qed.
Lemma lem3474941 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (@IN _90184 x t) = (t x).
Proof. exact (@lem3474940 _90184 t x). Qed.
Lemma lem3474942 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3474943 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (term105 _90184 x t) = (term106 _90184 t x).
Proof. exact (MK_COMB (@lem3474942) (@lem3474941 _90184 t x)). Qed.
Lemma lem3474944 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term68 _90184 u x t) = (term107 _90184 u t x).
Proof. exact (MK_COMB (@lem3474937 _90184 u x) (@lem3474943 _90184 t x)). Qed.
Lemma lem3474947 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term32 _90184 x u t) = (term107 _90184 u t x).
Proof. exact (TRANS (@lem3474929 _90184 u x t) (@lem3474944 _90184 u t x)). Qed.
Lemma lem3474948 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term34 _90184 s x u t) = (term108 _90184 s u t x).
Proof. exact (MK_COMB (@lem3474925 _90184 s t) (@lem3474947 _90184 u t x)). Qed.
Lemma lem3474951 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term36 _90184 s x u) = (term109 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3474948 _90184 s u t x)). Qed.
Lemma lem3474952 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3474953 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term38 _90184 s x u) = (term110 _90184 s u x).
Proof. exact (MK_COMB (@lem3474952 _90184) (@lem3474951 _90184 s u x)). Qed.
Lemma lem3474958 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term101 _90184 x s u) = (term110 _90184 s u x).
Proof. exact (TRANS (@lem3474913 _90184 s x u) (@lem3474953 _90184 s u x)). Qed.
Lemma lem3474959 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term90 _90184 x s u) = (term111 _90184 s u x).
Proof. exact (MK_COMB (@lem3474891 _90184 u x) (@lem3474958 _90184 s u x)). Qed.
Lemma lem3474962 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term89 _90184 x s u) = (term111 _90184 s u x).
Proof. exact (TRANS (@lem3474883 _90184 x s u) (@lem3474959 _90184 s u x)). Qed.
Lemma lem3474963 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : ((term69 _90184 x u s) = (term89 _90184 x s u)) = ((term84 _90184 u s x) = (term111 _90184 s u x)).
Proof. exact (MK_COMB (@lem3474879 _90184 u s x) (@lem3474962 _90184 s u x)). Qed.
Lemma lem3474966 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term112 _90184 s u) = (term113 _90184 s u).
Proof. exact (fun_ext (fun x : _90184 => @lem3474963 _90184 s u x)). Qed.
Lemma lem3474967 {_90184 : Type'} : (@all _90184) = (@all _90184).
Proof. exact (eq_refl (@all _90184)). Qed.
Lemma lem3474968 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term63 _90184 s u) = (term114 _90184 s u).
Proof. exact (MK_COMB (@lem3474967 _90184) (@lem3474966 _90184 s u)). Qed.
Lemma lem3474973 {_90184 : Type'} (u : _90184 -> Prop) : (term64 _90184 u) = (term115 _90184 u).
Proof. exact (fun_ext (fun s : type686 _90184 => @lem3474968 _90184 s u)). Qed.
Lemma lem3474974 {_90184 : Type'} : (@all ((_90184 -> Prop) -> Prop)) = (@all ((_90184 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90184 -> Prop) -> Prop))). Qed.
Lemma lem3474975 {_90184 : Type'} (u : _90184 -> Prop) : (term65 _90184 u) = (term116 _90184 u).
Proof. exact (MK_COMB (@lem3474974 _90184) (@lem3474973 _90184 u)). Qed.
Lemma lem3474980 {_90184 : Type'} : (term66 _90184) = (term117 _90184).
Proof. exact (fun_ext (fun u : _90184 -> Prop => @lem3474975 _90184 u)). Qed.
Lemma lem3474981 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3474982 {_90184 : Type'} : (term67 _90184) = (term118 _90184).
Proof. exact (MK_COMB (@lem3474981 _90184) (@lem3474980 _90184)). Qed.
Lemma lem3474987 {_90184 : Type'} : (term118 _90184) = (term67 _90184).
Proof. exact (SYM (@lem3474982 _90184)). Qed.
Lemma lem3474989 (p : Prop) : p = (term119 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3474990 {_90184 : Type'} : (term118 _90184) = (term120 _90184).
Proof. exact (@lem3474989 (term118 _90184)). Qed.
Lemma lem3474991 {_90184 : Type'} : (term120 _90184) = (term118 _90184).
Proof. exact (SYM (@lem3474990 _90184)). Qed.
Lemma lem3474992 {_90184 : Type'} (h1 : term121 _90184) : term121 _90184.
Proof. exact (h1). Qed.
Lemma lem3474995 {_90184 : Type'} (h1 : term120 _90184) : term120 _90184.
Proof. exact (h1). Qed.
Lemma lem3474996 {_90184 : Type'} : term122 _90184.
Proof. exact (fun h0 : term120 _90184 => @lem3474995 _90184 h0). Qed.
Lemma lem3474997 {_90184 : Type'} (h1 : term122 _90184) : term122 _90184.
Proof. exact (h1). Qed.
Lemma lem3474998 {_90184 : Type'} (h1 : term120 _90184) : term120 _90184.
Proof. exact (h1). Qed.
Lemma lem3474999 {_90184 : Type'} (h1 : term120 _90184) (h2 : term122 _90184) : term120 _90184.
Proof. exact (@lem3474997 _90184 h2 (@lem3474998 _90184 h1)). Qed.
Lemma lem3475000 {_90184 : Type'} (h1 : term120 _90184) : term123 _90184.
Proof. exact (fun h0 : term122 _90184 => @lem3474999 _90184 h1 h0). Qed.
Lemma lem3475001 {_90184 : Type'} (h1 : term122 _90184) : term122 _90184.
Proof. exact (h1). Qed.
Lemma lem3475002 {_90184 : Type'} (h1 : term120 _90184) (h2 : term122 _90184) : term120 _90184.
Proof. exact (@lem3475000 _90184 h1 (@lem3475001 _90184 h2)). Qed.
Lemma lem3475003 {_90184 : Type'} (h1 : term122 _90184) : term122 _90184.
Proof. exact (fun h0 : term120 _90184 => @lem3475002 _90184 h0 h1). Qed.
Lemma lem3475004 {_90184 : Type'} : term124 _90184.
Proof. exact (fun h0 : term122 _90184 => @lem3475003 _90184 h0). Qed.
Lemma lem3475007 {_90184 : Type'} : term122 _90184.
Proof. exact (@lem3475004 _90184 (@lem3474996 _90184)). Qed.
Lemma lem3475008 {_90184 : Type'} : term122 _90184.
Proof. exact (@lem3475007 _90184). Qed.
Lemma lem3475010 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3475011 {_90184 : Type'} : (term120 _90184) = (term125 _90184).
Proof. exact (@lem3475010 (term121 _90184)). Qed.
Lemma lem3475013 (t : Prop) : (term126 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3475014 {_90184 : Type'} : (term125 _90184) = (term118 _90184).
Proof. exact (@lem3475013 (term118 _90184)). Qed.
Lemma lem3475073 {_90184 : Type'} : (term120 _90184) = (term118 _90184).
Proof. exact (TRANS (@lem3475011 _90184) (@lem3475014 _90184)). Qed.
Lemma lem3475084 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term108 _90184 s u t x) = (term108 _90184 s u t x).
Proof. exact (eq_refl (term108 _90184 s u t x)). Qed.
Lemma lem3475085 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term109 _90184 s u x) = (term109 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475084 _90184 s u t x)). Qed.
Lemma lem3475086 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475087 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term110 _90184 s u x) = (term110 _90184 s u x).
Proof. exact (MK_COMB (@lem3475086 _90184) (@lem3475085 _90184 s u x)). Qed.
Lemma lem3475090 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term72 _90184 u x) = (term72 _90184 u x).
Proof. exact (eq_refl (term72 _90184 u x)). Qed.
Lemma lem3475091 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term111 _90184 s u x) = (term111 _90184 s u x).
Proof. exact (MK_COMB (@lem3475090 _90184 u x) (@lem3475087 _90184 s u x)). Qed.
Lemma lem3475096 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term78 _90184 s t x) = (term78 _90184 s t x).
Proof. exact (eq_refl (term78 _90184 s t x)). Qed.
Lemma lem3475097 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term80 _90184 s x) = (term80 _90184 s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475096 _90184 s t x)). Qed.
Lemma lem3475098 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475099 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term81 _90184 s x) = (term81 _90184 s x).
Proof. exact (MK_COMB (@lem3475098 _90184) (@lem3475097 _90184 s x)). Qed.
Lemma lem3475100 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475101 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term83 _90184 s x) = (term83 _90184 s x).
Proof. exact (MK_COMB (@lem3475100) (@lem3475099 _90184 s x)). Qed.
Lemma lem3475104 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term72 _90184 u x) = (term72 _90184 u x).
Proof. exact (eq_refl (term72 _90184 u x)). Qed.
Lemma lem3475105 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term84 _90184 u s x) = (term84 _90184 u s x).
Proof. exact (MK_COMB (@lem3475104 _90184 u x) (@lem3475101 _90184 s x)). Qed.
Lemma lem3475106 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3475107 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term86 _90184 u s x) = (term86 _90184 u s x).
Proof. exact (MK_COMB (@lem3475106) (@lem3475105 _90184 u s x)). Qed.
Lemma lem3475108 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : ((term84 _90184 u s x) = (term111 _90184 s u x)) = ((term84 _90184 u s x) = (term111 _90184 s u x)).
Proof. exact (MK_COMB (@lem3475107 _90184 u s x) (@lem3475091 _90184 s u x)). Qed.
Lemma lem3475109 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term113 _90184 s u) = (term113 _90184 s u).
Proof. exact (fun_ext (fun x : _90184 => @lem3475108 _90184 s u x)). Qed.
Lemma lem3475110 {_90184 : Type'} : (@all _90184) = (@all _90184).
Proof. exact (eq_refl (@all _90184)). Qed.
Lemma lem3475111 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : (term114 _90184 s u) = (term114 _90184 s u).
Proof. exact (MK_COMB (@lem3475110 _90184) (@lem3475109 _90184 s u)). Qed.
Lemma lem3475112 {_90184 : Type'} (u : _90184 -> Prop) : (term115 _90184 u) = (term115 _90184 u).
Proof. exact (fun_ext (fun s : type686 _90184 => @lem3475111 _90184 s u)). Qed.
Lemma lem3475113 {_90184 : Type'} : (@all ((_90184 -> Prop) -> Prop)) = (@all ((_90184 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_90184 -> Prop) -> Prop))). Qed.
Lemma lem3475114 {_90184 : Type'} (u : _90184 -> Prop) : (term116 _90184 u) = (term116 _90184 u).
Proof. exact (MK_COMB (@lem3475113 _90184) (@lem3475112 _90184 u)). Qed.
Lemma lem3475115 {_90184 : Type'} : (term117 _90184) = (term117 _90184).
Proof. exact (fun_ext (fun u : _90184 -> Prop => @lem3475114 _90184 u)). Qed.
Lemma lem3475116 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475117 {_90184 : Type'} : (term118 _90184) = (term118 _90184).
Proof. exact (MK_COMB (@lem3475116 _90184) (@lem3475115 _90184)). Qed.
Lemma lem3475160 {_90184 : Type'} : (term120 _90184) = (term118 _90184).
Proof. exact (TRANS (@lem3475073 _90184) (@lem3475117 _90184)). Qed.
Lemma lem3475161 {_90184 : Type'} : (term118 _90184) = (term120 _90184).
Proof. exact (SYM (@lem3475160 _90184)). Qed.
Lemma lem3475163 (p : Prop) : p = (term119 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3475164 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : ((term84 _90184 u s x) = (term111 _90184 s u x)) = (term127 _90184 s u x).
Proof. exact (@lem3475163 ((term84 _90184 u s x) = (term111 _90184 s u x))). Qed.
Lemma lem3475165 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term127 _90184 s u x) = ((term84 _90184 u s x) = (term111 _90184 s u x)).
Proof. exact (SYM (@lem3475164 _90184 s u x)). Qed.
Lemma lem3475166 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term128 _90184 s u x) : term128 _90184 s u x.
Proof. exact (h1). Qed.
Lemma lem3475177 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term129 _90184 s t x) = (term130 _90184 s t x).
Proof. exact (@lem17045 (s t) (t x)). Qed.
Lemma lem3475180 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term78 _90184 s t x) = (term78 _90184 s t x).
Proof. exact (eq_refl (term78 _90184 s t x)). Qed.
Lemma lem3475181 {_90184 : Type'} (P : type686 _90184) : (term131 _90184 P) = (term132 _90184 P).
Proof. exact (@lem18394 (_90184 -> Prop) P). Qed.
Lemma lem3475182 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term83 _90184 s x) = (term133 _90184 s x).
Proof. exact (@lem3475181 _90184 (term80 _90184 s x)). Qed.
Lemma lem3475183 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term134 _90184 s x t) = (term78 _90184 s t x).
Proof. exact (eq_refl (term134 _90184 s x t)). Qed.
Lemma lem3475184 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475185 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term135 _90184 s x t) = (term129 _90184 s t x).
Proof. exact (MK_COMB (@lem3475184) (@lem3475183 _90184 s t x)). Qed.
Lemma lem3475186 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term135 _90184 s x t) = (term130 _90184 s t x).
Proof. exact (TRANS (@lem3475185 _90184 s t x) (@lem3475177 _90184 s t x)). Qed.
Lemma lem3475187 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term136 _90184 s x) = (term137 _90184 s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475186 _90184 s t x)). Qed.
Lemma lem3475188 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475189 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term133 _90184 s x) = (term138 _90184 s x).
Proof. exact (MK_COMB (@lem3475188 _90184) (@lem3475187 _90184 s x)). Qed.
Lemma lem3475190 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term83 _90184 s x) = (term138 _90184 s x).
Proof. exact (TRANS (@lem3475182 _90184 s x) (@lem3475189 _90184 s x)). Qed.
Lemma lem3475191 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term80 _90184 s x) = (term80 _90184 s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475180 _90184 s t x)). Qed.
Lemma lem3475192 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475193 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term81 _90184 s x) = (term81 _90184 s x).
Proof. exact (MK_COMB (@lem3475192 _90184) (@lem3475191 _90184 s x)). Qed.
Lemma lem3475194 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term139 _90184 s x) = (term81 _90184 s x).
Proof. exact (@lem16933 (term81 _90184 s x)). Qed.
Lemma lem3475195 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term139 _90184 s x) = (term81 _90184 s x).
Proof. exact (TRANS (@lem3475194 _90184 s x) (@lem3475193 _90184 s x)). Qed.
Lemma lem3475197 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term140 _90184 u x).
Proof. exact (eq_refl (term140 _90184 u x)). Qed.
Lemma lem3475198 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term141 _90184 u s x) = (term142 _90184 u s x).
Proof. exact (MK_COMB (@lem3475197 _90184 u x) (@lem3475195 _90184 s x)). Qed.
Lemma lem3475199 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term143 _90184 u s x) = (term141 _90184 u s x).
Proof. exact (@lem17045 (u x) (term83 _90184 s x)). Qed.
Lemma lem3475200 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term143 _90184 u s x) = (term142 _90184 u s x).
Proof. exact (TRANS (@lem3475199 _90184 u s x) (@lem3475198 _90184 u s x)). Qed.
Lemma lem3475202 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term72 _90184 u x) = (term72 _90184 u x).
Proof. exact (eq_refl (term72 _90184 u x)). Qed.
Lemma lem3475203 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term84 _90184 u s x) = (term144 _90184 u s x).
Proof. exact (MK_COMB (@lem3475202 _90184 u x) (@lem3475190 _90184 s x)). Qed.
Lemma lem3475213 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (term145 _90184 t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem3475215 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term140 _90184 u x).
Proof. exact (eq_refl (term140 _90184 u x)). Qed.
Lemma lem3475216 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term146 _90184 u t x) = (term147 _90184 u t x).
Proof. exact (MK_COMB (@lem3475215 _90184 u x) (@lem3475213 _90184 t x)). Qed.
Lemma lem3475217 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term148 _90184 u t x) = (term146 _90184 u t x).
Proof. exact (@lem17045 (u x) (term106 _90184 t x)). Qed.
Lemma lem3475218 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term148 _90184 u t x) = (term147 _90184 u t x).
Proof. exact (TRANS (@lem3475217 _90184 u t x) (@lem3475216 _90184 u t x)). Qed.
Lemma lem3475223 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term76 _90184 s t) = (term76 _90184 s t).
Proof. exact (eq_refl (term76 _90184 s t)). Qed.
Lemma lem3475224 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term149 _90184 s u t x) = (term150 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475223 _90184 s t) (@lem3475218 _90184 u t x)). Qed.
Lemma lem3475225 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term151 _90184 s u t x) = (term149 _90184 s u t x).
Proof. exact (@lem17362 (s t) (term107 _90184 u t x)). Qed.
Lemma lem3475226 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term151 _90184 s u t x) = (term150 _90184 s u t x).
Proof. exact (TRANS (@lem3475225 _90184 s u t x) (@lem3475224 _90184 s u t x)). Qed.
Lemma lem3475231 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term108 _90184 s u t x) = (term152 _90184 s u t x).
Proof. exact (@lem17265 (s t) (term107 _90184 u t x)). Qed.
Lemma lem3475232 {_90184 : Type'} (P : type686 _90184) : (term153 _90184 P) = (term154 _90184 P).
Proof. exact (@lem18392 (_90184 -> Prop) P). Qed.
Lemma lem3475233 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term155 _90184 s u x) = (term156 _90184 s u x).
Proof. exact (@lem3475232 _90184 (term109 _90184 s u x)). Qed.
Lemma lem3475234 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term157 _90184 s u x t) = (term108 _90184 s u t x).
Proof. exact (eq_refl (term157 _90184 s u x t)). Qed.
Lemma lem3475235 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475236 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term158 _90184 s u x t) = (term151 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475235) (@lem3475234 _90184 s u t x)). Qed.
Lemma lem3475237 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term158 _90184 s u x t) = (term150 _90184 s u t x).
Proof. exact (TRANS (@lem3475236 _90184 s u t x) (@lem3475226 _90184 s u t x)). Qed.
Lemma lem3475238 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term159 _90184 s u x) = (term160 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475237 _90184 s u t x)). Qed.
Lemma lem3475239 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475240 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term156 _90184 s u x) = (term161 _90184 s u x).
Proof. exact (MK_COMB (@lem3475239 _90184) (@lem3475238 _90184 s u x)). Qed.
Lemma lem3475241 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term155 _90184 s u x) = (term161 _90184 s u x).
Proof. exact (TRANS (@lem3475233 _90184 s u x) (@lem3475240 _90184 s u x)). Qed.
Lemma lem3475242 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term109 _90184 s u x) = (term162 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475231 _90184 s u t x)). Qed.
Lemma lem3475243 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475244 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term110 _90184 s u x) = (term163 _90184 s u x).
Proof. exact (MK_COMB (@lem3475243 _90184) (@lem3475242 _90184 s u x)). Qed.
Lemma lem3475246 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term140 _90184 u x).
Proof. exact (eq_refl (term140 _90184 u x)). Qed.
Lemma lem3475247 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term164 _90184 s u x) = (term165 _90184 s u x).
Proof. exact (MK_COMB (@lem3475246 _90184 u x) (@lem3475241 _90184 s u x)). Qed.
Lemma lem3475248 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term166 _90184 s u x) = (term164 _90184 s u x).
Proof. exact (@lem17045 (u x) (term110 _90184 s u x)). Qed.
Lemma lem3475249 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term166 _90184 s u x) = (term165 _90184 s u x).
Proof. exact (TRANS (@lem3475248 _90184 s u x) (@lem3475247 _90184 s u x)). Qed.
Lemma lem3475251 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term72 _90184 u x) = (term72 _90184 u x).
Proof. exact (eq_refl (term72 _90184 u x)). Qed.
Lemma lem3475252 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term111 _90184 s u x) = (term167 _90184 s u x).
Proof. exact (MK_COMB (@lem3475251 _90184 u x) (@lem3475244 _90184 s u x)). Qed.
Lemma lem3475253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475254 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term168 _90184 u s x) = (term169 _90184 u s x).
Proof. exact (MK_COMB (@lem3475253) (@lem3475200 _90184 u s x)). Qed.
Lemma lem3475255 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term170 _90184 s u x) = (term171 _90184 s u x).
Proof. exact (MK_COMB (@lem3475254 _90184 u s x) (@lem3475252 _90184 s u x)). Qed.
Lemma lem3475256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475257 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term172 _90184 u s x) = (term173 _90184 u s x).
Proof. exact (MK_COMB (@lem3475256) (@lem3475203 _90184 u s x)). Qed.
Lemma lem3475258 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term174 _90184 s u x) = (term175 _90184 s u x).
Proof. exact (MK_COMB (@lem3475257 _90184 u s x) (@lem3475249 _90184 s u x)). Qed.
Lemma lem3475259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475260 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term176 _90184 s u x) = (term177 _90184 s u x).
Proof. exact (MK_COMB (@lem3475259) (@lem3475258 _90184 s u x)). Qed.
Lemma lem3475261 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term178 _90184 s u x) = (term179 _90184 s u x).
Proof. exact (MK_COMB (@lem3475260 _90184 s u x) (@lem3475255 _90184 s u x)). Qed.
Lemma lem3475262 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term128 _90184 s u x) = (term178 _90184 s u x).
Proof. exact (@lem17646 (term84 _90184 u s x) (term111 _90184 s u x)). Qed.
Lemma lem3475263 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term128 _90184 s u x) = (term179 _90184 s u x).
Proof. exact (TRANS (@lem3475262 _90184 s u x) (@lem3475261 _90184 s u x)). Qed.
Lemma lem3475418 {A : Type'} (P : Prop) (Q : A -> Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3475419 {_90184 : Type'} (P : Prop) (Q : type686 _90184) : (term182 _90184 P Q) = (term183 _90184 P Q).
Proof. exact (@lem3475418 (_90184 -> Prop) P Q). Qed.
Lemma lem3475420 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term184 _90184 s u x) = (term185 _90184 s u x).
Proof. exact (@lem3475419 _90184 (term106 _90184 u x) (term160 _90184 s u x)). Qed.
Lemma lem3475421 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term186 _90184 s u x t) = (term150 _90184 s u t x).
Proof. exact (eq_refl (term186 _90184 s u x t)). Qed.
Lemma lem3475422 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term187 _90184 s u x) = (term160 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475421 _90184 s u t x)). Qed.
Lemma lem3475423 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475424 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term188 _90184 s u x) = (term161 _90184 s u x).
Proof. exact (MK_COMB (@lem3475423 _90184) (@lem3475422 _90184 s u x)). Qed.
Lemma lem3475425 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term140 _90184 u x).
Proof. exact (eq_refl (term140 _90184 u x)). Qed.
Lemma lem3475426 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term184 _90184 s u x) = (term165 _90184 s u x).
Proof. exact (MK_COMB (@lem3475425 _90184 u x) (@lem3475424 _90184 s u x)). Qed.
Lemma lem3475427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3475428 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term189 _90184 s u x) = (term190 _90184 s u x).
Proof. exact (MK_COMB (@lem3475427) (@lem3475426 _90184 s u x)). Qed.
Lemma lem3475429 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term186 _90184 s u x t) = (term150 _90184 s u t x).
Proof. exact (eq_refl (term186 _90184 s u x t)). Qed.
Lemma lem3475430 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term140 _90184 u x).
Proof. exact (eq_refl (term140 _90184 u x)). Qed.
Lemma lem3475431 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term191 _90184 s u x t) = (term192 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475430 _90184 u x) (@lem3475429 _90184 s u t x)). Qed.
Lemma lem3475432 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term193 _90184 s u x) = (term194 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475431 _90184 s u t x)). Qed.
Lemma lem3475433 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475434 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term185 _90184 s u x) = (term195 _90184 s u x).
Proof. exact (MK_COMB (@lem3475433 _90184) (@lem3475432 _90184 s u x)). Qed.
Lemma lem3475435 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : ((term184 _90184 s u x) = (term185 _90184 s u x)) = ((term165 _90184 s u x) = (term195 _90184 s u x)).
Proof. exact (MK_COMB (@lem3475428 _90184 s u x) (@lem3475434 _90184 s u x)). Qed.
Lemma lem3475436 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term165 _90184 s u x) = (term195 _90184 s u x).
Proof. exact (EQ_MP (@lem3475435 _90184 s u x) (@lem3475420 _90184 s u x)). Qed.
Lemma lem3475437 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term173 _90184 u s x) = (term173 _90184 u s x).
Proof. exact (eq_refl (term173 _90184 u s x)). Qed.
Lemma lem3475438 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term175 _90184 s u x) = (term196 _90184 s u x).
Proof. exact (MK_COMB (@lem3475437 _90184 u s x) (@lem3475436 _90184 s u x)). Qed.
Lemma lem3475440 {A : Type'} (P : Prop) (Q : A -> Prop) : (term197 A P Q) = (term198 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3475441 {_90184 : Type'} (P : Prop) (Q : type686 _90184) : (term199 _90184 P Q) = (term200 _90184 P Q).
Proof. exact (@lem3475440 (_90184 -> Prop) P Q). Qed.
Lemma lem3475442 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term201 _90184 s u x) = (term202 _90184 s u x).
Proof. exact (@lem3475441 _90184 (term144 _90184 u s x) (term194 _90184 s u x)). Qed.
Lemma lem3475443 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term203 _90184 s u x t) = (term192 _90184 s u t x).
Proof. exact (eq_refl (term203 _90184 s u x t)). Qed.
Lemma lem3475444 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term204 _90184 s u x) = (term194 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475443 _90184 s u t x)). Qed.
Lemma lem3475445 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475446 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term205 _90184 s u x) = (term195 _90184 s u x).
Proof. exact (MK_COMB (@lem3475445 _90184) (@lem3475444 _90184 s u x)). Qed.
Lemma lem3475447 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term173 _90184 u s x) = (term173 _90184 u s x).
Proof. exact (eq_refl (term173 _90184 u s x)). Qed.
Lemma lem3475448 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term201 _90184 s u x) = (term196 _90184 s u x).
Proof. exact (MK_COMB (@lem3475447 _90184 u s x) (@lem3475446 _90184 s u x)). Qed.
Lemma lem3475449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3475450 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term206 _90184 s u x) = (term207 _90184 s u x).
Proof. exact (MK_COMB (@lem3475449) (@lem3475448 _90184 s u x)). Qed.
Lemma lem3475451 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term203 _90184 s u x t) = (term192 _90184 s u t x).
Proof. exact (eq_refl (term203 _90184 s u x t)). Qed.
Lemma lem3475452 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term173 _90184 u s x) = (term173 _90184 u s x).
Proof. exact (eq_refl (term173 _90184 u s x)). Qed.
Lemma lem3475453 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term208 _90184 s u x t) = (term209 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475452 _90184 u s x) (@lem3475451 _90184 s u t x)). Qed.
Lemma lem3475454 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term210 _90184 s u x) = (term211 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475453 _90184 s u t x)). Qed.
Lemma lem3475455 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475456 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term202 _90184 s u x) = (term212 _90184 s u x).
Proof. exact (MK_COMB (@lem3475455 _90184) (@lem3475454 _90184 s u x)). Qed.
Lemma lem3475457 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : ((term201 _90184 s u x) = (term202 _90184 s u x)) = ((term196 _90184 s u x) = (term212 _90184 s u x)).
Proof. exact (MK_COMB (@lem3475450 _90184 s u x) (@lem3475456 _90184 s u x)). Qed.
Lemma lem3475458 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term196 _90184 s u x) = (term212 _90184 s u x).
Proof. exact (EQ_MP (@lem3475457 _90184 s u x) (@lem3475442 _90184 s u x)). Qed.
Lemma lem3475459 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term175 _90184 s u x) = (term212 _90184 s u x).
Proof. exact (TRANS (@lem3475438 _90184 s u x) (@lem3475458 _90184 s u x)). Qed.
Lemma lem3475460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475461 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term177 _90184 s u x) = (term213 _90184 s u x).
Proof. exact (MK_COMB (@lem3475460) (@lem3475459 _90184 s u x)). Qed.
Lemma lem3475463 {A : Type'} (P : Prop) (Q : A -> Prop) : (term180 A P Q) = (term181 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3475464 {_90184 : Type'} (P : Prop) (Q : type686 _90184) : (term182 _90184 P Q) = (term183 _90184 P Q).
Proof. exact (@lem3475463 (_90184 -> Prop) P Q). Qed.
Lemma lem3475465 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term214 _90184 u s x) = (term215 _90184 u s x).
Proof. exact (@lem3475464 _90184 (term106 _90184 u x) (term80 _90184 s x)). Qed.
Lemma lem3475466 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term134 _90184 s x t) = (term78 _90184 s t x).
Proof. exact (eq_refl (term134 _90184 s x t)). Qed.
Lemma lem3475467 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term216 _90184 s x) = (term80 _90184 s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475466 _90184 s t x)). Qed.
Lemma lem3475468 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475469 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term217 _90184 s x) = (term81 _90184 s x).
Proof. exact (MK_COMB (@lem3475468 _90184) (@lem3475467 _90184 s x)). Qed.
Lemma lem3475470 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term140 _90184 u x).
Proof. exact (eq_refl (term140 _90184 u x)). Qed.
Lemma lem3475471 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term214 _90184 u s x) = (term142 _90184 u s x).
Proof. exact (MK_COMB (@lem3475470 _90184 u x) (@lem3475469 _90184 s x)). Qed.
Lemma lem3475472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3475473 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term218 _90184 u s x) = (term219 _90184 u s x).
Proof. exact (MK_COMB (@lem3475472) (@lem3475471 _90184 u s x)). Qed.
Lemma lem3475474 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term134 _90184 s x t) = (term78 _90184 s t x).
Proof. exact (eq_refl (term134 _90184 s x t)). Qed.
Lemma lem3475475 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term140 _90184 u x).
Proof. exact (eq_refl (term140 _90184 u x)). Qed.
Lemma lem3475476 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term220 _90184 u s x t) = (term221 _90184 u s t x).
Proof. exact (MK_COMB (@lem3475475 _90184 u x) (@lem3475474 _90184 s t x)). Qed.
Lemma lem3475477 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term222 _90184 u s x) = (term223 _90184 u s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475476 _90184 u s t x)). Qed.
Lemma lem3475478 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475479 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term215 _90184 u s x) = (term224 _90184 u s x).
Proof. exact (MK_COMB (@lem3475478 _90184) (@lem3475477 _90184 u s x)). Qed.
Lemma lem3475480 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : ((term214 _90184 u s x) = (term215 _90184 u s x)) = ((term142 _90184 u s x) = (term224 _90184 u s x)).
Proof. exact (MK_COMB (@lem3475473 _90184 u s x) (@lem3475479 _90184 u s x)). Qed.
Lemma lem3475481 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term142 _90184 u s x) = (term224 _90184 u s x).
Proof. exact (EQ_MP (@lem3475480 _90184 u s x) (@lem3475465 _90184 u s x)). Qed.
Lemma lem3475482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475483 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term169 _90184 u s x) = (term225 _90184 u s x).
Proof. exact (MK_COMB (@lem3475482) (@lem3475481 _90184 u s x)). Qed.
Lemma lem3475484 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term167 _90184 s u x) = (term167 _90184 s u x).
Proof. exact (eq_refl (term167 _90184 s u x)). Qed.
Lemma lem3475485 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term171 _90184 s u x) = (term226 _90184 s u x).
Proof. exact (MK_COMB (@lem3475483 _90184 u s x) (@lem3475484 _90184 s u x)). Qed.
Lemma lem3475487 {A : Type'} (P : A -> Prop) (Q : Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3475488 {_90184 : Type'} (P : type686 _90184) (Q : Prop) : (term229 _90184 P Q) = (term230 _90184 P Q).
Proof. exact (@lem3475487 (_90184 -> Prop) P Q). Qed.
Lemma lem3475489 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term231 _90184 s u x) = (term232 _90184 s u x).
Proof. exact (@lem3475488 _90184 (term223 _90184 u s x) (term167 _90184 s u x)). Qed.
Lemma lem3475490 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term233 _90184 u s x t) = (term221 _90184 u s t x).
Proof. exact (eq_refl (term233 _90184 u s x t)). Qed.
Lemma lem3475491 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term234 _90184 u s x) = (term223 _90184 u s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475490 _90184 u s t x)). Qed.
Lemma lem3475492 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475493 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term235 _90184 u s x) = (term224 _90184 u s x).
Proof. exact (MK_COMB (@lem3475492 _90184) (@lem3475491 _90184 u s x)). Qed.
Lemma lem3475494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475495 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term236 _90184 u s x) = (term225 _90184 u s x).
Proof. exact (MK_COMB (@lem3475494) (@lem3475493 _90184 u s x)). Qed.
Lemma lem3475496 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term167 _90184 s u x) = (term167 _90184 s u x).
Proof. exact (eq_refl (term167 _90184 s u x)). Qed.
Lemma lem3475497 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term231 _90184 s u x) = (term226 _90184 s u x).
Proof. exact (MK_COMB (@lem3475495 _90184 u s x) (@lem3475496 _90184 s u x)). Qed.
Lemma lem3475498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3475499 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term237 _90184 s u x) = (term238 _90184 s u x).
Proof. exact (MK_COMB (@lem3475498) (@lem3475497 _90184 s u x)). Qed.
Lemma lem3475500 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term233 _90184 u s x t) = (term221 _90184 u s t x).
Proof. exact (eq_refl (term233 _90184 u s x t)). Qed.
Lemma lem3475501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475502 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term239 _90184 u s x t) = (term240 _90184 u s t x).
Proof. exact (MK_COMB (@lem3475501) (@lem3475500 _90184 u s t x)). Qed.
Lemma lem3475503 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term167 _90184 s u x) = (term167 _90184 s u x).
Proof. exact (eq_refl (term167 _90184 s u x)). Qed.
Lemma lem3475504 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term241 _90184 t s u x) = (term242 _90184 t s u x).
Proof. exact (MK_COMB (@lem3475502 _90184 u s t x) (@lem3475503 _90184 s u x)). Qed.
Lemma lem3475505 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term243 _90184 s u x) = (term244 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475504 _90184 t s u x)). Qed.
Lemma lem3475506 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475507 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term232 _90184 s u x) = (term245 _90184 s u x).
Proof. exact (MK_COMB (@lem3475506 _90184) (@lem3475505 _90184 s u x)). Qed.
Lemma lem3475508 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : ((term231 _90184 s u x) = (term232 _90184 s u x)) = ((term226 _90184 s u x) = (term245 _90184 s u x)).
Proof. exact (MK_COMB (@lem3475499 _90184 s u x) (@lem3475507 _90184 s u x)). Qed.
Lemma lem3475509 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term226 _90184 s u x) = (term245 _90184 s u x).
Proof. exact (EQ_MP (@lem3475508 _90184 s u x) (@lem3475489 _90184 s u x)). Qed.
Lemma lem3475510 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term171 _90184 s u x) = (term245 _90184 s u x).
Proof. exact (TRANS (@lem3475485 _90184 s u x) (@lem3475509 _90184 s u x)). Qed.
Lemma lem3475511 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term179 _90184 s u x) = (term246 _90184 s u x).
Proof. exact (MK_COMB (@lem3475461 _90184 s u x) (@lem3475510 _90184 s u x)). Qed.
Lemma lem3475513 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term247 A P Q) = (term248 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3475514 {_90184 : Type'} (P : type686 _90184) (Q : type686 _90184) : (term249 _90184 P Q) = (term250 _90184 P Q).
Proof. exact (@lem3475513 (_90184 -> Prop) P Q). Qed.
Lemma lem3475515 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term251 _90184 s u x) = (term252 _90184 s u x).
Proof. exact (@lem3475514 _90184 (term211 _90184 s u x) (term244 _90184 s u x)). Qed.
Lemma lem3475516 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term253 _90184 s u x t) = (term209 _90184 s u t x).
Proof. exact (eq_refl (term253 _90184 s u x t)). Qed.
Lemma lem3475517 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term254 _90184 s u x) = (term211 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475516 _90184 s u t x)). Qed.
Lemma lem3475518 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475519 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term255 _90184 s u x) = (term212 _90184 s u x).
Proof. exact (MK_COMB (@lem3475518 _90184) (@lem3475517 _90184 s u x)). Qed.
Lemma lem3475520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475521 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term256 _90184 s u x) = (term213 _90184 s u x).
Proof. exact (MK_COMB (@lem3475520) (@lem3475519 _90184 s u x)). Qed.
Lemma lem3475522 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term257 _90184 s u x t) = (term242 _90184 t s u x).
Proof. exact (eq_refl (term257 _90184 s u x t)). Qed.
Lemma lem3475523 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term258 _90184 s u x) = (term244 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475522 _90184 t s u x)). Qed.
Lemma lem3475524 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475525 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term259 _90184 s u x) = (term245 _90184 s u x).
Proof. exact (MK_COMB (@lem3475524 _90184) (@lem3475523 _90184 s u x)). Qed.
Lemma lem3475526 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term251 _90184 s u x) = (term246 _90184 s u x).
Proof. exact (MK_COMB (@lem3475521 _90184 s u x) (@lem3475525 _90184 s u x)). Qed.
Lemma lem3475527 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3475528 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term260 _90184 s u x) = (term261 _90184 s u x).
Proof. exact (MK_COMB (@lem3475527) (@lem3475526 _90184 s u x)). Qed.
Lemma lem3475529 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term253 _90184 s u x t) = (term209 _90184 s u t x).
Proof. exact (eq_refl (term253 _90184 s u x t)). Qed.
Lemma lem3475530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475531 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term262 _90184 s u x t) = (term263 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475530) (@lem3475529 _90184 s u t x)). Qed.
Lemma lem3475532 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term257 _90184 s u x t) = (term242 _90184 t s u x).
Proof. exact (eq_refl (term257 _90184 s u x t)). Qed.
Lemma lem3475533 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term264 _90184 s u x t) = (term265 _90184 t s u x).
Proof. exact (MK_COMB (@lem3475531 _90184 s u t x) (@lem3475532 _90184 t s u x)). Qed.
Lemma lem3475534 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term266 _90184 s u x) = (term267 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475533 _90184 t s u x)). Qed.
Lemma lem3475535 {_90184 : Type'} : (@ex (_90184 -> Prop)) = (@ex (_90184 -> Prop)).
Proof. exact (eq_refl (@ex (_90184 -> Prop))). Qed.
Lemma lem3475536 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term252 _90184 s u x) = (term268 _90184 s u x).
Proof. exact (MK_COMB (@lem3475535 _90184) (@lem3475534 _90184 s u x)). Qed.
Lemma lem3475537 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : ((term251 _90184 s u x) = (term252 _90184 s u x)) = ((term246 _90184 s u x) = (term268 _90184 s u x)).
Proof. exact (MK_COMB (@lem3475528 _90184 s u x) (@lem3475536 _90184 s u x)). Qed.
Lemma lem3475538 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term246 _90184 s u x) = (term268 _90184 s u x).
Proof. exact (EQ_MP (@lem3475537 _90184 s u x) (@lem3475515 _90184 s u x)). Qed.
Lemma lem3475540 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term179 _90184 s u x) = (term268 _90184 s u x).
Proof. exact (TRANS (@lem3475511 _90184 s u x) (@lem3475538 _90184 s u x)). Qed.
Lemma lem3475541 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term128 _90184 s u x) = (term268 _90184 s u x).
Proof. exact (TRANS (@lem3475263 _90184 s u x) (@lem3475540 _90184 s u x)). Qed.
Lemma lem3475542 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term128 _90184 s u x) : term268 _90184 s u x.
Proof. exact (EQ_MP (@lem3475541 _90184 s u x) (@lem3475166 _90184 s u x h1)). Qed.
Lemma lem3475543 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term265 _90184 t s u x) : term265 _90184 t s u x.
Proof. exact (h1). Qed.
Lemma lem3475544 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475549 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475550 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475549 _90184 Prop f x). Qed.
Lemma lem3475552 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (t x) = (@I (_90184 -> Prop) t x).
Proof. exact (@lem3475550 _90184 t x). Qed.
Lemma lem3475553 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (term106 _90184 t x) = (term269 _90184 t x).
Proof. exact (MK_COMB (@lem3475544) (@lem3475552 _90184 t x)). Qed.
Lemma lem3475558 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475559 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475558 _90184 Prop f x). Qed.
Lemma lem3475561 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475559 _90184 u x). Qed.
Lemma lem3475562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475563 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term72 _90184 u x) = (term270 _90184 u x).
Proof. exact (MK_COMB (@lem3475562) (@lem3475561 _90184 u x)). Qed.
Lemma lem3475564 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term107 _90184 u t x) = (term271 _90184 u t x).
Proof. exact (MK_COMB (@lem3475563 _90184 u x) (@lem3475553 _90184 t x)). Qed.
Lemma lem3475565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475570 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475571 {_90184 : Type'} (f : type686 _90184) (x : _90184 -> Prop) : (f x) = (@I ((_90184 -> Prop) -> Prop) f x).
Proof. exact (@lem3475570 (_90184 -> Prop) Prop f x). Qed.
Lemma lem3475573 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (s t) = (@I ((_90184 -> Prop) -> Prop) s t).
Proof. exact (@lem3475571 _90184 s t). Qed.
Lemma lem3475574 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term272 _90184 s t) = (term273 _90184 s t).
Proof. exact (MK_COMB (@lem3475565) (@lem3475573 _90184 s t)). Qed.
Lemma lem3475575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475576 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term274 _90184 s t) = (term275 _90184 s t).
Proof. exact (MK_COMB (@lem3475575) (@lem3475574 _90184 s t)). Qed.
Lemma lem3475577 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term152 _90184 s u t x) = (term276 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475576 _90184 s t) (@lem3475564 _90184 u t x)). Qed.
Lemma lem3475578 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term162 _90184 s u x) = (term277 _90184 s u x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475577 _90184 s u t x)). Qed.
Lemma lem3475579 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475580 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term163 _90184 s u x) = (term278 _90184 s u x).
Proof. exact (MK_COMB (@lem3475579 _90184) (@lem3475578 _90184 s u x)). Qed.
Lemma lem3475585 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475586 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475585 _90184 Prop f x). Qed.
Lemma lem3475588 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475586 _90184 u x). Qed.
Lemma lem3475589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475590 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term72 _90184 u x) = (term270 _90184 u x).
Proof. exact (MK_COMB (@lem3475589) (@lem3475588 _90184 u x)). Qed.
Lemma lem3475591 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term167 _90184 s u x) = (term279 _90184 s u x).
Proof. exact (MK_COMB (@lem3475590 _90184 u x) (@lem3475580 _90184 s u x)). Qed.
Lemma lem3475596 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475597 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475596 _90184 Prop f x). Qed.
Lemma lem3475599 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (t x) = (@I (_90184 -> Prop) t x).
Proof. exact (@lem3475597 _90184 t x). Qed.
Lemma lem3475604 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475605 {_90184 : Type'} (f : type686 _90184) (x : _90184 -> Prop) : (f x) = (@I ((_90184 -> Prop) -> Prop) f x).
Proof. exact (@lem3475604 (_90184 -> Prop) Prop f x). Qed.
Lemma lem3475607 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (s t) = (@I ((_90184 -> Prop) -> Prop) s t).
Proof. exact (@lem3475605 _90184 s t). Qed.
Lemma lem3475608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475609 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term76 _90184 s t) = (term280 _90184 s t).
Proof. exact (MK_COMB (@lem3475608) (@lem3475607 _90184 s t)). Qed.
Lemma lem3475610 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term78 _90184 s t x) = (term281 _90184 s t x).
Proof. exact (MK_COMB (@lem3475609 _90184 s t) (@lem3475599 _90184 t x)). Qed.
Lemma lem3475611 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475616 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475617 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475616 _90184 Prop f x). Qed.
Lemma lem3475619 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475617 _90184 u x). Qed.
Lemma lem3475620 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term106 _90184 u x) = (term269 _90184 u x).
Proof. exact (MK_COMB (@lem3475611) (@lem3475619 _90184 u x)). Qed.
Lemma lem3475621 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475622 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term282 _90184 u x).
Proof. exact (MK_COMB (@lem3475621) (@lem3475620 _90184 u x)). Qed.
Lemma lem3475623 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term221 _90184 u s t x) = (term283 _90184 u s t x).
Proof. exact (MK_COMB (@lem3475622 _90184 u x) (@lem3475610 _90184 s t x)). Qed.
Lemma lem3475624 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475625 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term240 _90184 u s t x) = (term284 _90184 u s t x).
Proof. exact (MK_COMB (@lem3475624) (@lem3475623 _90184 u s t x)). Qed.
Lemma lem3475626 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term242 _90184 t s u x) = (term285 _90184 t s u x).
Proof. exact (MK_COMB (@lem3475625 _90184 u s t x) (@lem3475591 _90184 s u x)). Qed.
Lemma lem3475631 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475632 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475631 _90184 Prop f x). Qed.
Lemma lem3475634 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (t x) = (@I (_90184 -> Prop) t x).
Proof. exact (@lem3475632 _90184 t x). Qed.
Lemma lem3475635 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475640 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475641 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475640 _90184 Prop f x). Qed.
Lemma lem3475643 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475641 _90184 u x). Qed.
Lemma lem3475644 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term106 _90184 u x) = (term269 _90184 u x).
Proof. exact (MK_COMB (@lem3475635) (@lem3475643 _90184 u x)). Qed.
Lemma lem3475645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475646 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term282 _90184 u x).
Proof. exact (MK_COMB (@lem3475645) (@lem3475644 _90184 u x)). Qed.
Lemma lem3475647 {_90184 : Type'} (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term147 _90184 u t x) = (term286 _90184 u t x).
Proof. exact (MK_COMB (@lem3475646 _90184 u x) (@lem3475634 _90184 t x)). Qed.
Lemma lem3475652 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475653 {_90184 : Type'} (f : type686 _90184) (x : _90184 -> Prop) : (f x) = (@I ((_90184 -> Prop) -> Prop) f x).
Proof. exact (@lem3475652 (_90184 -> Prop) Prop f x). Qed.
Lemma lem3475655 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (s t) = (@I ((_90184 -> Prop) -> Prop) s t).
Proof. exact (@lem3475653 _90184 s t). Qed.
Lemma lem3475656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475657 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term76 _90184 s t) = (term280 _90184 s t).
Proof. exact (MK_COMB (@lem3475656) (@lem3475655 _90184 s t)). Qed.
Lemma lem3475658 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term150 _90184 s u t x) = (term287 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475657 _90184 s t) (@lem3475647 _90184 u t x)). Qed.
Lemma lem3475659 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475664 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475665 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475664 _90184 Prop f x). Qed.
Lemma lem3475667 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475665 _90184 u x). Qed.
Lemma lem3475668 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term106 _90184 u x) = (term269 _90184 u x).
Proof. exact (MK_COMB (@lem3475659) (@lem3475667 _90184 u x)). Qed.
Lemma lem3475669 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475670 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term140 _90184 u x) = (term282 _90184 u x).
Proof. exact (MK_COMB (@lem3475669) (@lem3475668 _90184 u x)). Qed.
Lemma lem3475671 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term192 _90184 s u t x) = (term288 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475670 _90184 u x) (@lem3475658 _90184 s u t x)). Qed.
Lemma lem3475672 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475677 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475678 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475677 _90184 Prop f x). Qed.
Lemma lem3475680 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (t x) = (@I (_90184 -> Prop) t x).
Proof. exact (@lem3475678 _90184 t x). Qed.
Lemma lem3475681 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (term106 _90184 t x) = (term269 _90184 t x).
Proof. exact (MK_COMB (@lem3475672) (@lem3475680 _90184 t x)). Qed.
Lemma lem3475682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3475687 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475688 {_90184 : Type'} (f : type686 _90184) (x : _90184 -> Prop) : (f x) = (@I ((_90184 -> Prop) -> Prop) f x).
Proof. exact (@lem3475687 (_90184 -> Prop) Prop f x). Qed.
Lemma lem3475690 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (s t) = (@I ((_90184 -> Prop) -> Prop) s t).
Proof. exact (@lem3475688 _90184 s t). Qed.
Lemma lem3475691 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term272 _90184 s t) = (term273 _90184 s t).
Proof. exact (MK_COMB (@lem3475682) (@lem3475690 _90184 s t)). Qed.
Lemma lem3475692 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475693 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term274 _90184 s t) = (term275 _90184 s t).
Proof. exact (MK_COMB (@lem3475692) (@lem3475691 _90184 s t)). Qed.
Lemma lem3475694 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term130 _90184 s t x) = (term289 _90184 s t x).
Proof. exact (MK_COMB (@lem3475693 _90184 s t) (@lem3475681 _90184 t x)). Qed.
Lemma lem3475695 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term137 _90184 s x) = (term290 _90184 s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475694 _90184 s t x)). Qed.
Lemma lem3475696 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475697 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term138 _90184 s x) = (term291 _90184 s x).
Proof. exact (MK_COMB (@lem3475696 _90184) (@lem3475695 _90184 s x)). Qed.
Lemma lem3475702 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3475703 {_90184 : Type'} (f : _90184 -> Prop) (x : _90184) : (f x) = (@I (_90184 -> Prop) f x).
Proof. exact (@lem3475702 _90184 Prop f x). Qed.
Lemma lem3475705 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475703 _90184 u x). Qed.
Lemma lem3475706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475707 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term72 _90184 u x) = (term270 _90184 u x).
Proof. exact (MK_COMB (@lem3475706) (@lem3475705 _90184 u x)). Qed.
Lemma lem3475708 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term144 _90184 u s x) = (term292 _90184 u s x).
Proof. exact (MK_COMB (@lem3475707 _90184 u x) (@lem3475697 _90184 s x)). Qed.
Lemma lem3475709 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3475710 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term173 _90184 u s x) = (term293 _90184 u s x).
Proof. exact (MK_COMB (@lem3475709) (@lem3475708 _90184 u s x)). Qed.
Lemma lem3475711 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term209 _90184 s u t x) = (term294 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475710 _90184 u s x) (@lem3475671 _90184 s u t x)). Qed.
Lemma lem3475712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3475713 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) : (term263 _90184 s u t x) = (term295 _90184 s u t x).
Proof. exact (MK_COMB (@lem3475712) (@lem3475711 _90184 s u t x)). Qed.
Lemma lem3475714 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term265 _90184 t s u x) = (term296 _90184 t s u x).
Proof. exact (MK_COMB (@lem3475713 _90184 s u t x) (@lem3475626 _90184 t s u x)). Qed.
Lemma lem3475715 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term265 _90184 t s u x) : term296 _90184 t s u x.
Proof. exact (EQ_MP (@lem3475714 _90184 t s u x) (@lem3475543 _90184 t s u x h1)). Qed.
Lemma lem3475716 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term294 _90184 s u t x.
Proof. exact (h1). Qed.
Lemma lem3475717 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term285 _90184 t s u x.
Proof. exact (h1). Qed.
Lemma lem3475718 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term288 _90184 s u t x.
Proof. exact (proj2 (@lem3475716 _90184 s u t x h1)). Qed.
Lemma lem3475719 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term292 _90184 u s x.
Proof. exact (proj1 (@lem3475716 _90184 s u t x h1)). Qed.
Lemma lem3475720 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term291 _90184 s x.
Proof. exact (proj2 (@lem3475719 _90184 s u t x h1)). Qed.
Lemma lem3475723 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term287 _90184 s u t x) : term287 _90184 s u t x.
Proof. exact (h1). Qed.
Lemma lem3475724 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term287 _90184 s u t x) : term286 _90184 u t x.
Proof. exact (proj2 (@lem3475723 _90184 s u t x h1)). Qed.
Lemma lem3475728 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term279 _90184 s u x.
Proof. exact (proj2 (@lem3475717 _90184 t s u x h1)). Qed.
Lemma lem3475729 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term283 _90184 u s t x.
Proof. exact (proj1 (@lem3475717 _90184 t s u x h1)). Qed.
Lemma lem3475730 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term278 _90184 s u x.
Proof. exact (proj2 (@lem3475728 _90184 t s u x h1)). Qed.
Lemma lem3475733 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : term281 _90184 s t x.
Proof. exact (h1). Qed.
Lemma lem3475756 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term269 _90184 u x.
Proof. exact (h1). Qed.
Lemma lem3475781 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term269 _90184 u x.
Proof. exact (h1). Qed.
Lemma lem3475793 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term289 _90184 s t x) = (term289 _90184 s t x).
Proof. exact (eq_refl (term289 _90184 s t x)). Qed.
Lemma lem3475794 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term290 _90184 s x) = (term290 _90184 s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475793 _90184 s t x)). Qed.
Lemma lem3475795 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475797 {_90184 : Type'} (s : type686 _90184) (x : _90184) : (term291 _90184 s x) = (term291 _90184 s x).
Proof. exact (MK_COMB (@lem3475795 _90184) (@lem3475794 _90184 s x)). Qed.
Lemma lem3475798 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term291 _90184 s x.
Proof. exact (EQ_MP (@lem3475797 _90184 s x) (@lem3475720 _90184 s u t x h1)). Qed.
Lemma lem3475806 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) (h1 : @I (_90184 -> Prop) t x) : @I (_90184 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3475837 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term269 _90184 u x.
Proof. exact (h1). Qed.
Lemma lem3475859 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) : (term276 _90184 s u t x) = (term297 _90184 u s t x).
Proof. exact (@lem19490 (@I (_90184 -> Prop) u x) (term273 _90184 s t) (term269 _90184 t x)). Qed.
Lemma lem3475860 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term277 _90184 s u x) = (term298 _90184 u s x).
Proof. exact (fun_ext (fun t : _90184 -> Prop => @lem3475859 _90184 u s t x)). Qed.
Lemma lem3475861 {_90184 : Type'} : (@all (_90184 -> Prop)) = (@all (_90184 -> Prop)).
Proof. exact (eq_refl (@all (_90184 -> Prop))). Qed.
Lemma lem3475863 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (x : _90184) : (term278 _90184 s u x) = (term299 _90184 u s x).
Proof. exact (MK_COMB (@lem3475861 _90184) (@lem3475860 _90184 u s x)). Qed.
Lemma lem3475864 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term299 _90184 u s x.
Proof. exact (EQ_MP (@lem3475863 _90184 u s x) (@lem3475730 _90184 t s u x h1)). Qed.
Lemma lem3475879 {_90184 : Type'} (_36679 : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term300 _90184 s x _36679.
Proof. exact (@lem3475798 _90184 s u t x h1 _36679). Qed.
Lemma lem3475880 {_90184 : Type'} (s : type686 _90184) (_36679 : _90184 -> Prop) (x : _90184) : (term300 _90184 s x _36679) = (term289 _90184 s _36679 x).
Proof. exact (eq_refl (term300 _90184 s x _36679)). Qed.
Lemma lem3475885 {_90184 : Type'} (_36681 : _90184 -> Prop) (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term301 _90184 u s x _36681.
Proof. exact (@lem3475864 _90184 t s u x h1 _36681). Qed.
Lemma lem3475886 {_90184 : Type'} (u : _90184 -> Prop) (s : type686 _90184) (_36681 : _90184 -> Prop) (x : _90184) : (term301 _90184 u s x _36681) = (term297 _90184 u s _36681 x).
Proof. exact (eq_refl (term301 _90184 u s x _36681)). Qed.
Lemma lem3475887 {_90184 : Type'} (_36681 : _90184 -> Prop) (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term297 _90184 u s _36681 x.
Proof. exact (EQ_MP (@lem3475886 _90184 u s _36681 x) (@lem3475885 _90184 _36681 t s u x h1)). Qed.
Lemma lem3475901 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term269 _90184 u x.
Proof. exact (h1). Qed.
Lemma lem3475913 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term269 _90184 u x.
Proof. exact (h1). Qed.
Lemma lem3475921 {_90184 : Type'} (_36679 : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term289 _90184 s _36679 x.
Proof. exact (EQ_MP (@lem3475880 _90184 s _36679 x) (@lem3475879 _90184 _36679 s u t x h1)). Qed.
Lemma lem3475925 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) (h1 : @I (_90184 -> Prop) t x) : @I (_90184 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3475929 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term269 _90184 u x.
Proof. exact (h1). Qed.
Lemma lem3475959 {_90184 : Type'} (_36681 : _90184 -> Prop) (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term289 _90184 s _36681 x.
Proof. exact (proj2 (@lem3475887 _90184 _36681 t s u x h1)). Qed.
Lemma lem3475961 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : @I (_90184 -> Prop) u x.
Proof. exact (proj1 (@lem3475719 _90184 s u t x h1)). Qed.
Lemma lem3475962 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term302 _90184 u x.
Proof. exact (fun h0 : term269 _90184 u x => @lem3475961 _90184 s u t x h1). Qed.
Lemma lem3475964 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3475965 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term302 _90184 u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475964 (@I (_90184 -> Prop) u x)). Qed.
Lemma lem3475966 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : @I (_90184 -> Prop) u x.
Proof. exact (EQ_MP (@lem3475965 _90184 u x) (@lem3475962 _90184 s u t x h1)). Qed.
Lemma lem3475969 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3475971 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term269 _90184 u x) = (term304 _90184 u x).
Proof. exact (@lem3475969 (@I (_90184 -> Prop) u x)). Qed.
Lemma lem3475974 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term304 _90184 u x.
Proof. exact (EQ_MP (@lem3475971 _90184 u x) (@lem3475901 _90184 u x h1)). Qed.
Lemma lem3475977 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (@lem3475974 _90184 u x h1 (@lem3475966 _90184 s u t x h2)). Qed.
Lemma lem3475978 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : term305.
Proof. exact (fun h0 : ~ False => @lem3475977 _90184 s u t x h1 h2). Qed.
Lemma lem3475980 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3475981 : term305 = False.
Proof. exact (@lem3475980 False). Qed.
Lemma lem3475982 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3475981) (@lem3475978 _90184 s u t x h1 h2)). Qed.
Lemma lem3475984 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : @I (_90184 -> Prop) u x.
Proof. exact (proj1 (@lem3475719 _90184 s u t x h1)). Qed.
Lemma lem3475985 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term302 _90184 u x.
Proof. exact (fun h0 : term269 _90184 u x => @lem3475984 _90184 s u t x h1). Qed.
Lemma lem3475987 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3475988 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term302 _90184 u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3475987 (@I (_90184 -> Prop) u x)). Qed.
Lemma lem3475989 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : @I (_90184 -> Prop) u x.
Proof. exact (EQ_MP (@lem3475988 _90184 u x) (@lem3475985 _90184 s u t x h1)). Qed.
Lemma lem3475992 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3475994 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term269 _90184 u x) = (term304 _90184 u x).
Proof. exact (@lem3475992 (@I (_90184 -> Prop) u x)). Qed.
Lemma lem3475997 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term304 _90184 u x.
Proof. exact (EQ_MP (@lem3475994 _90184 u x) (@lem3475913 _90184 u x h1)). Qed.
Lemma lem3476000 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (@lem3475997 _90184 u x h1 (@lem3475989 _90184 s u t x h2)). Qed.
Lemma lem3476001 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : term305.
Proof. exact (fun h0 : ~ False => @lem3476000 _90184 s u t x h1 h2). Qed.
Lemma lem3476003 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476004 : term305 = False.
Proof. exact (@lem3476003 False). Qed.
Lemma lem3476005 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3476004) (@lem3476001 _90184 s u t x h1 h2)). Qed.
Lemma lem3476007 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term287 _90184 s u t x) : @I ((_90184 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3475723 _90184 s u t x h1)). Qed.
Lemma lem3476008 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term287 _90184 s u t x) : term306 _90184 s t.
Proof. exact (fun h0 : term273 _90184 s t => @lem3476007 _90184 s u t x h1). Qed.
Lemma lem3476010 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476011 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term306 _90184 s t) = (@I ((_90184 -> Prop) -> Prop) s t).
Proof. exact (@lem3476010 (@I ((_90184 -> Prop) -> Prop) s t)). Qed.
Lemma lem3476012 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term287 _90184 s u t x) : @I ((_90184 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3476011 _90184 s t) (@lem3476008 _90184 s u t x h1)). Qed.
Lemma lem3476014 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) (h1 : @I (_90184 -> Prop) t x) : @I (_90184 -> Prop) t x.
Proof. exact (h1). Qed.
Lemma lem3476015 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) (h1 : @I (_90184 -> Prop) t x) : term302 _90184 t x.
Proof. exact (fun h0 : term269 _90184 t x => @lem3476014 _90184 t x h1). Qed.
Lemma lem3476017 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476018 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (term302 _90184 t x) = (@I (_90184 -> Prop) t x).
Proof. exact (@lem3476017 (@I (_90184 -> Prop) t x)). Qed.
Lemma lem3476019 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) (h1 : @I (_90184 -> Prop) t x) : @I (_90184 -> Prop) t x.
Proof. exact (EQ_MP (@lem3476018 _90184 t x) (@lem3476015 _90184 t x h1)). Qed.
Lemma lem3476021 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3476022 {_90184 : Type'} (s : type686 _90184) (_36679 : _90184 -> Prop) (x : _90184) : (term289 _90184 s _36679 x) = (term309 _90184 s _36679 x).
Proof. exact (@lem3476021 (@I ((_90184 -> Prop) -> Prop) s _36679) (@I (_90184 -> Prop) _36679 x)). Qed.
Lemma lem3476024 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3476025 {_90184 : Type'} (s : type686 _90184) (_36679 : _90184 -> Prop) (x : _90184) : (term309 _90184 s _36679 x) = (term310 _90184 s _36679 x).
Proof. exact (@lem3476024 (term281 _90184 s _36679 x)). Qed.
Lemma lem3476026 {_90184 : Type'} (s : type686 _90184) (_36679 : _90184 -> Prop) (x : _90184) : (term289 _90184 s _36679 x) = (term310 _90184 s _36679 x).
Proof. exact (TRANS (@lem3476022 _90184 s _36679 x) (@lem3476025 _90184 s _36679 x)). Qed.
Lemma lem3476028 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term287 _90184 s u t x) (h2 : @I (_90184 -> Prop) t x) : term281 _90184 s t x.
Proof. exact (conj (@lem3476012 _90184 s u t x h1) (@lem3476019 _90184 t x h2)). Qed.
Lemma lem3476030 {_90184 : Type'} (_36679 : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term310 _90184 s _36679 x.
Proof. exact (EQ_MP (@lem3476026 _90184 s _36679 x) (@lem3475921 _90184 _36679 s u t x h1)). Qed.
Lemma lem3476031 {_90184 : Type'} (_36679 : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term310 _90184 s _36679 x.
Proof. exact (@lem3476030 _90184 _36679 s u t x h1). Qed.
Lemma lem3476032 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : term310 _90184 s t x.
Proof. exact (@lem3476031 _90184 t s u t x h1). Qed.
Lemma lem3476035 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : False.
Proof. exact (@lem3476032 _90184 s u t x h1 (@lem3476028 _90184 s u t x h2 h3)). Qed.
Lemma lem3476036 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : term305.
Proof. exact (fun h0 : ~ False => @lem3476035 _90184 s u t x h1 h2 h3). Qed.
Lemma lem3476038 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476039 : term305 = False.
Proof. exact (@lem3476038 False). Qed.
Lemma lem3476040 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3476039) (@lem3476036 _90184 s u t x h1 h2 h3)). Qed.
Lemma lem3476042 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : @I (_90184 -> Prop) u x.
Proof. exact (proj1 (@lem3475728 _90184 t s u x h1)). Qed.
Lemma lem3476043 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term302 _90184 u x.
Proof. exact (fun h0 : term269 _90184 u x => @lem3476042 _90184 t s u x h1). Qed.
Lemma lem3476045 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476046 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term302 _90184 u x) = (@I (_90184 -> Prop) u x).
Proof. exact (@lem3476045 (@I (_90184 -> Prop) u x)). Qed.
Lemma lem3476047 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : @I (_90184 -> Prop) u x.
Proof. exact (EQ_MP (@lem3476046 _90184 u x) (@lem3476043 _90184 t s u x h1)). Qed.
Lemma lem3476050 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3476052 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) : (term269 _90184 u x) = (term304 _90184 u x).
Proof. exact (@lem3476050 (@I (_90184 -> Prop) u x)). Qed.
Lemma lem3476055 {_90184 : Type'} (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) : term304 _90184 u x.
Proof. exact (EQ_MP (@lem3476052 _90184 u x) (@lem3475929 _90184 u x h1)). Qed.
Lemma lem3476058 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : False.
Proof. exact (@lem3476055 _90184 u x h1 (@lem3476047 _90184 t s u x h2)). Qed.
Lemma lem3476059 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : term305.
Proof. exact (fun h0 : ~ False => @lem3476058 _90184 t s u x h1 h2). Qed.
Lemma lem3476061 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476062 : term305 = False.
Proof. exact (@lem3476061 False). Qed.
Lemma lem3476063 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : False.
Proof. exact (EQ_MP (@lem3476062) (@lem3476059 _90184 t s u x h1 h2)). Qed.
Lemma lem3476065 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : @I ((_90184 -> Prop) -> Prop) s t.
Proof. exact (proj1 (@lem3475733 _90184 s t x h1)). Qed.
Lemma lem3476066 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : term306 _90184 s t.
Proof. exact (fun h0 : term273 _90184 s t => @lem3476065 _90184 s t x h1). Qed.
Lemma lem3476068 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476069 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) : (term306 _90184 s t) = (@I ((_90184 -> Prop) -> Prop) s t).
Proof. exact (@lem3476068 (@I ((_90184 -> Prop) -> Prop) s t)). Qed.
Lemma lem3476070 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : @I ((_90184 -> Prop) -> Prop) s t.
Proof. exact (EQ_MP (@lem3476069 _90184 s t) (@lem3476066 _90184 s t x h1)). Qed.
Lemma lem3476072 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : @I (_90184 -> Prop) t x.
Proof. exact (proj2 (@lem3475733 _90184 s t x h1)). Qed.
Lemma lem3476073 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : term302 _90184 t x.
Proof. exact (fun h0 : term269 _90184 t x => @lem3476072 _90184 s t x h1). Qed.
Lemma lem3476075 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476076 {_90184 : Type'} (t : _90184 -> Prop) (x : _90184) : (term302 _90184 t x) = (@I (_90184 -> Prop) t x).
Proof. exact (@lem3476075 (@I (_90184 -> Prop) t x)). Qed.
Lemma lem3476077 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : @I (_90184 -> Prop) t x.
Proof. exact (EQ_MP (@lem3476076 _90184 t x) (@lem3476073 _90184 s t x h1)). Qed.
Lemma lem3476079 (a : Prop) (b : Prop) : (term307 a b) = (term308 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3476080 {_90184 : Type'} (s : type686 _90184) (_36681 : _90184 -> Prop) (x : _90184) : (term289 _90184 s _36681 x) = (term309 _90184 s _36681 x).
Proof. exact (@lem3476079 (@I ((_90184 -> Prop) -> Prop) s _36681) (@I (_90184 -> Prop) _36681 x)). Qed.
Lemma lem3476082 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3476083 {_90184 : Type'} (s : type686 _90184) (_36681 : _90184 -> Prop) (x : _90184) : (term309 _90184 s _36681 x) = (term310 _90184 s _36681 x).
Proof. exact (@lem3476082 (term281 _90184 s _36681 x)). Qed.
Lemma lem3476084 {_90184 : Type'} (s : type686 _90184) (_36681 : _90184 -> Prop) (x : _90184) : (term289 _90184 s _36681 x) = (term310 _90184 s _36681 x).
Proof. exact (TRANS (@lem3476080 _90184 s _36681 x) (@lem3476083 _90184 s _36681 x)). Qed.
Lemma lem3476086 {_90184 : Type'} (s : type686 _90184) (t : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) : term281 _90184 s t x.
Proof. exact (conj (@lem3476070 _90184 s t x h1) (@lem3476077 _90184 s t x h1)). Qed.
Lemma lem3476088 {_90184 : Type'} (_36681 : _90184 -> Prop) (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term310 _90184 s _36681 x.
Proof. exact (EQ_MP (@lem3476084 _90184 s _36681 x) (@lem3475959 _90184 _36681 t s u x h1)). Qed.
Lemma lem3476089 {_90184 : Type'} (_36681 : _90184 -> Prop) (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term310 _90184 s _36681 x.
Proof. exact (@lem3476088 _90184 _36681 t s u x h1). Qed.
Lemma lem3476090 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : term310 _90184 s t x.
Proof. exact (@lem3476089 _90184 t t s u x h1). Qed.
Lemma lem3476093 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) (h2 : term285 _90184 t s u x) : False.
Proof. exact (@lem3476090 _90184 t s u x h2 (@lem3476086 _90184 s t x h1)). Qed.
Lemma lem3476094 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) (h2 : term285 _90184 t s u x) : term305.
Proof. exact (fun h0 : ~ False => @lem3476093 _90184 t s u x h1 h2). Qed.
Lemma lem3476096 (p : Prop) : (term303 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3476097 : term305 = False.
Proof. exact (@lem3476096 False). Qed.
Lemma lem3476098 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term281 _90184 s t x) (h2 : term285 _90184 t s u x) : False.
Proof. exact (EQ_MP (@lem3476097) (@lem3476094 _90184 t s u x h1 h2)). Qed.
Lemma lem3476099 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476063 _90184 t s u x h1 h2) (fun h3 : False => @lem3475929 _90184 u x h1)). Qed.
Lemma lem3476100 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : False.
Proof. exact (EQ_MP (@lem3476099 _90184 t s u x h1 h2) (@lem3475929 _90184 u x h1)). Qed.
Lemma lem3476101 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : (@I (_90184 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (_90184 -> Prop) t x => @lem3476040 _90184 s u t x h1 h2 h3) (fun h4 : False => @lem3475925 _90184 t x h3)). Qed.
Lemma lem3476102 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3476101 _90184 s u t x h1 h2 h3) (@lem3475925 _90184 t x h3)). Qed.
Lemma lem3476103 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476005 _90184 s u t x h1 h2) (fun h3 : False => @lem3475913 _90184 u x h1)). Qed.
Lemma lem3476104 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3476103 _90184 s u t x h1 h2) (@lem3475913 _90184 u x h1)). Qed.
Lemma lem3476105 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3475982 _90184 s u t x h1 h2) (fun h3 : False => @lem3475901 _90184 u x h1)). Qed.
Lemma lem3476106 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3476105 _90184 s u t x h1 h2) (@lem3475901 _90184 u x h1)). Qed.
Lemma lem3476107 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476100 _90184 t s u x h1 h2) (fun h3 : False => @lem3475837 _90184 u x h1)). Qed.
Lemma lem3476108 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : False.
Proof. exact (EQ_MP (@lem3476107 _90184 t s u x h1 h2) (@lem3475837 _90184 u x h1)). Qed.
Lemma lem3476109 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : (@I (_90184 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (_90184 -> Prop) t x => @lem3476102 _90184 s u t x h1 h2 h3) (fun h4 : False => @lem3475806 _90184 t x h3)). Qed.
Lemma lem3476110 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3476109 _90184 s u t x h1 h2 h3) (@lem3475806 _90184 t x h3)). Qed.
Lemma lem3476111 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476104 _90184 s u t x h1 h2) (fun h3 : False => @lem3475781 _90184 u x h1)). Qed.
Lemma lem3476112 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3476111 _90184 s u t x h1 h2) (@lem3475781 _90184 u x h1)). Qed.
Lemma lem3476113 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476106 _90184 s u t x h1 h2) (fun h3 : False => @lem3475756 _90184 u x h1)). Qed.
Lemma lem3476114 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3476113 _90184 s u t x h1 h2) (@lem3475756 _90184 u x h1)). Qed.
Lemma lem3476115 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476108 _90184 t s u x h1 h2) (fun h3 : False => @lem3475837 _90184 u x h1)). Qed.
Lemma lem3476116 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term285 _90184 t s u x) : False.
Proof. exact (EQ_MP (@lem3476115 _90184 t s u x h1 h2) (@lem3475837 _90184 u x h1)). Qed.
Lemma lem3476117 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : (@I (_90184 -> Prop) t x) = False.
Proof. exact (prop_ext (fun h4 : @I (_90184 -> Prop) t x => @lem3476110 _90184 s u t x h1 h2 h3) (fun h4 : False => @lem3475806 _90184 t x h3)). Qed.
Lemma lem3476118 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) (h3 : @I (_90184 -> Prop) t x) : False.
Proof. exact (EQ_MP (@lem3476117 _90184 s u t x h1 h2 h3) (@lem3475806 _90184 t x h3)). Qed.
Lemma lem3476119 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476112 _90184 s u t x h1 h2) (fun h3 : False => @lem3475781 _90184 u x h1)). Qed.
Lemma lem3476120 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3476119 _90184 s u t x h1 h2) (@lem3475781 _90184 u x h1)). Qed.
Lemma lem3476121 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : (term269 _90184 u x) = False.
Proof. exact (prop_ext (fun h3 : term269 _90184 u x => @lem3476114 _90184 s u t x h1 h2) (fun h3 : False => @lem3475756 _90184 u x h1)). Qed.
Lemma lem3476122 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term269 _90184 u x) (h2 : term294 _90184 s u t x) : False.
Proof. exact (EQ_MP (@lem3476121 _90184 s u t x h1 h2) (@lem3475756 _90184 u x h1)). Qed.
Lemma lem3476123 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term285 _90184 t s u x) : False.
Proof. exact (or_elim (@lem3475729 _90184 t s u x h1) (fun h0 : term269 _90184 u x => @lem3476116 _90184 t s u x h0 h1) (fun h0 : term281 _90184 s t x => @lem3476098 _90184 t s u x h0 h1)). Qed.
Lemma lem3476124 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) (h2 : term287 _90184 s u t x) : False.
Proof. exact (or_elim (@lem3475724 _90184 s u t x h2) (fun h0 : term269 _90184 u x => @lem3476120 _90184 s u t x h0 h1) (fun h0 : @I (_90184 -> Prop) t x => @lem3476118 _90184 s u t x h1 h2 h0)). Qed.
Lemma lem3476125 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (t : _90184 -> Prop) (x : _90184) (h1 : term294 _90184 s u t x) : False.
Proof. exact (or_elim (@lem3475718 _90184 s u t x h1) (fun h0 : term269 _90184 u x => @lem3476122 _90184 s u t x h0 h1) (fun h0 : term287 _90184 s u t x => @lem3476124 _90184 s u t x h1 h0)). Qed.
Lemma lem3476126 {_90184 : Type'} (t : _90184 -> Prop) (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term265 _90184 t s u x) : False.
Proof. exact (or_elim (@lem3475715 _90184 t s u x h1) (fun h0 : term294 _90184 s u t x => @lem3476125 _90184 s u t x h0) (fun h0 : term285 _90184 t s u x => @lem3476123 _90184 t s u x h0)). Qed.
Lemma lem3476127 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term128 _90184 s u x) : False.
Proof. exact (ex_elim (@lem3475542 _90184 s u x h1) (fun t : _90184 -> Prop => fun h0 : term267 _90184 s u x t => @lem3476126 _90184 t s u x h0)). Qed.
Lemma lem3476128 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term128 _90184 s u x) : (term128 _90184 s u x) = False.
Proof. exact (prop_ext (fun h2 : term128 _90184 s u x => @lem3476127 _90184 s u x h1) (fun h2 : False => @lem3475166 _90184 s u x h1)). Qed.
Lemma lem3476129 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) (h1 : term128 _90184 s u x) : False.
Proof. exact (EQ_MP (@lem3476128 _90184 s u x h1) (@lem3475166 _90184 s u x h1)). Qed.
Lemma lem3476130 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : term127 _90184 s u x.
Proof. exact (fun h0 : term128 _90184 s u x => @lem3476129 _90184 s u x h0). Qed.
Lemma lem3476131 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) (x : _90184) : (term84 _90184 u s x) = (term111 _90184 s u x).
Proof. exact (EQ_MP (@lem3475165 _90184 s u x) (@lem3476130 _90184 s u x)). Qed.
Lemma lem3476136 {_90184 : Type'} (s : type686 _90184) (u : _90184 -> Prop) : term114 _90184 s u.
Proof. exact (fun x : _90184 => @lem3476131 _90184 s u x). Qed.
Lemma lem3476141 {_90184 : Type'} (u : _90184 -> Prop) : term116 _90184 u.
Proof. exact (fun s : type686 _90184 => @lem3476136 _90184 s u). Qed.
Lemma lem3476146 {_90184 : Type'} : term118 _90184.
Proof. exact (fun u : _90184 -> Prop => @lem3476141 _90184 u). Qed.
Lemma lem3476147 {_90184 : Type'} : term120 _90184.
Proof. exact (EQ_MP (@lem3475161 _90184) (@lem3476146 _90184)). Qed.
Lemma lem3476149 {_90184 : Type'} : term120 _90184.
Proof. exact (@lem3475008 _90184 (@lem3476147 _90184)). Qed.
Lemma lem3476150 {_90184 : Type'} (h1 : term121 _90184) : False.
Proof. exact (@lem3476149 _90184 (@lem3474992 _90184 h1)). Qed.
Lemma lem3476151 {_90184 : Type'} (h1 : term121 _90184) : (term121 _90184) = False.
Proof. exact (prop_ext (fun h2 : term121 _90184 => @lem3476150 _90184 h1) (fun h2 : False => @lem3474992 _90184 h1)). Qed.
Lemma lem3476152 {_90184 : Type'} (h1 : term121 _90184) : False.
Proof. exact (EQ_MP (@lem3476151 _90184 h1) (@lem3474992 _90184 h1)). Qed.
Lemma lem3476153 {_90184 : Type'} : term120 _90184.
Proof. exact (fun h0 : term121 _90184 => @lem3476152 _90184 h0). Qed.
Lemma lem3476154 {_90184 : Type'} : term118 _90184.
Proof. exact (EQ_MP (@lem3474991 _90184) (@lem3476153 _90184)). Qed.
Lemma lem3476155 {_90184 : Type'} : term67 _90184.
Proof. exact (EQ_MP (@lem3474987 _90184) (@lem3476154 _90184)). Qed.
Lemma lem3476156 {_90184 : Type'} : term61 _90184.
Proof. exact (EQ_MP (@lem3474815 _90184) (@lem3476155 _90184)). Qed.
Lemma lem3476157 {_90184 : Type'} : term60 _90184.
Proof. exact (EQ_MP (@lem3474768 _90184) (@lem3476156 _90184)). Qed.
