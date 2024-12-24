Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3355403_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Lemma lem3354731 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem3354732 {_87240 : Type'} (s : type686 _87240) (x : _87240) : (term0 _87240 x s) = (term1 _87240 s x).
Proof. exact (@lem3354731 _87240 s x). Qed.
Lemma lem3354733 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term2 _87240 x s) = (term3 _87240 s x).
Proof. exact (@lem3354732 _87240 (@INSERT (_87240 -> Prop) s (@EMPTY (_87240 -> Prop))) x). Qed.
Lemma lem3354741 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term4 A x y s) = (term5 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3354742 {_87240 : Type'} (y : _87240 -> Prop) (x : _87240 -> Prop) (s : type686 _87240) : (term6 _87240 x y s) = (term7 _87240 y x s).
Proof. exact (@lem3354741 (_87240 -> Prop) y x s). Qed.
Lemma lem3354743 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) : (term8 _87240 t s) = (term9 _87240 s t).
Proof. exact (@lem3354742 _87240 s t (@EMPTY (_87240 -> Prop))). Qed.
Lemma lem3354749 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3354750 {_87240 : Type'} (x : _87240 -> Prop) : (@IN (_87240 -> Prop) x (@EMPTY (_87240 -> Prop))) = False.
Proof. exact (@lem3354749 (_87240 -> Prop) x). Qed.
Lemma lem3354751 {_87240 : Type'} (t : _87240 -> Prop) : (@IN (_87240 -> Prop) t (@EMPTY (_87240 -> Prop))) = False.
Proof. exact (@lem3354750 _87240 t). Qed.
Lemma lem3354752 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term10 _87240 t s) = (term10 _87240 t s).
Proof. exact (eq_refl (term10 _87240 t s)). Qed.
Lemma lem3354753 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term9 _87240 s t) = (term11 _87240 t s).
Proof. exact (MK_COMB (@lem3354752 _87240 t s) (@lem3354751 _87240 t)). Qed.
Lemma lem3354755 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem3354756 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term11 _87240 t s) = (t = s).
Proof. exact (@lem3354755 (t = s)). Qed.
Lemma lem3354759 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term9 _87240 s t) = (t = s).
Proof. exact (TRANS (@lem3354753 _87240 t s) (@lem3354756 _87240 t s)). Qed.
Lemma lem3354760 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term8 _87240 t s) = (t = s).
Proof. exact (TRANS (@lem3354743 _87240 s t) (@lem3354759 _87240 t s)). Qed.
Lemma lem3354761 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3354762 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term12 _87240 t s) = (term13 _87240 t s).
Proof. exact (MK_COMB (@lem3354761) (@lem3354760 _87240 t s)). Qed.
Lemma lem3354764 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3354765 {_87240 : Type'} (P : _87240 -> Prop) (x : _87240) : (@IN _87240 x P) = (P x).
Proof. exact (@lem3354764 _87240 P x). Qed.
Lemma lem3354766 {_87240 : Type'} (t : _87240 -> Prop) (x : _87240) : (@IN _87240 x t) = (t x).
Proof. exact (@lem3354765 _87240 t x). Qed.
Lemma lem3354767 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term14 _87240 s x t) = (term15 _87240 s t x).
Proof. exact (MK_COMB (@lem3354762 _87240 t s) (@lem3354766 _87240 t x)). Qed.
Lemma lem3354772 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term16 _87240 s x) = (term17 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3354767 _87240 s t x)). Qed.
Lemma lem3354773 {_87240 : Type'} : (@all (_87240 -> Prop)) = (@all (_87240 -> Prop)).
Proof. exact (eq_refl (@all (_87240 -> Prop))). Qed.
Lemma lem3354774 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term3 _87240 s x) = (term18 _87240 s x).
Proof. exact (MK_COMB (@lem3354773 _87240) (@lem3354772 _87240 s x)). Qed.
Lemma lem3354779 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term2 _87240 x s) = (term18 _87240 s x).
Proof. exact (TRANS (@lem3354733 _87240 s x) (@lem3354774 _87240 s x)). Qed.
Lemma lem3354780 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3354781 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term19 _87240 x s) = (term20 _87240 s x).
Proof. exact (MK_COMB (@lem3354780) (@lem3354779 _87240 s x)). Qed.
Lemma lem3354783 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3354784 {_87240 : Type'} (P : _87240 -> Prop) (x : _87240) : (@IN _87240 x P) = (P x).
Proof. exact (@lem3354783 _87240 P x). Qed.
Lemma lem3354785 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (@IN _87240 x s) = (s x).
Proof. exact (@lem3354784 _87240 s x). Qed.
Lemma lem3354786 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : ((term2 _87240 x s) = (@IN _87240 x s)) = ((term18 _87240 s x) = (s x)).
Proof. exact (MK_COMB (@lem3354781 _87240 s x) (@lem3354785 _87240 s x)). Qed.
Lemma lem3354789 {_87240 : Type'} (s : _87240 -> Prop) : (term21 _87240 s) = (term22 _87240 s).
Proof. exact (fun_ext (fun x : _87240 => @lem3354786 _87240 s x)). Qed.
Lemma lem3354790 {_87240 : Type'} : (@all _87240) = (@all _87240).
Proof. exact (eq_refl (@all _87240)). Qed.
Lemma lem3354791 {_87240 : Type'} (s : _87240 -> Prop) : (term23 _87240 s) = (term24 _87240 s).
Proof. exact (MK_COMB (@lem3354790 _87240) (@lem3354789 _87240 s)). Qed.
Lemma lem3354796 {_87240 : Type'} (s : _87240 -> Prop) : (term24 _87240 s) = (term23 _87240 s).
Proof. exact (SYM (@lem3354791 _87240 s)). Qed.
Lemma lem3354798 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3354799 {_87240 : Type'} (s : _87240 -> Prop) : (term24 _87240 s) = (term26 _87240 s).
Proof. exact (@lem3354798 (term24 _87240 s)). Qed.
Lemma lem3354800 {_87240 : Type'} (s : _87240 -> Prop) : (term26 _87240 s) = (term24 _87240 s).
Proof. exact (SYM (@lem3354799 _87240 s)). Qed.
Lemma lem3354801 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term27 _87240 s) : term27 _87240 s.
Proof. exact (h1). Qed.
Lemma lem3354804 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term26 _87240 s) : term26 _87240 s.
Proof. exact (h1). Qed.
Lemma lem3354805 {_87240 : Type'} (s : _87240 -> Prop) : term28 _87240 s.
Proof. exact (fun h0 : term26 _87240 s => @lem3354804 _87240 s h0). Qed.
Lemma lem3354806 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term28 _87240 s) : term28 _87240 s.
Proof. exact (h1). Qed.
Lemma lem3354807 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term26 _87240 s) : term26 _87240 s.
Proof. exact (h1). Qed.
Lemma lem3354808 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term26 _87240 s) (h2 : term28 _87240 s) : term26 _87240 s.
Proof. exact (@lem3354806 _87240 s h2 (@lem3354807 _87240 s h1)). Qed.
Lemma lem3354809 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term26 _87240 s) : term29 _87240 s.
Proof. exact (fun h0 : term28 _87240 s => @lem3354808 _87240 s h1 h0). Qed.
Lemma lem3354810 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term28 _87240 s) : term28 _87240 s.
Proof. exact (h1). Qed.
Lemma lem3354811 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term26 _87240 s) (h2 : term28 _87240 s) : term26 _87240 s.
Proof. exact (@lem3354809 _87240 s h1 (@lem3354810 _87240 s h2)). Qed.
Lemma lem3354812 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term28 _87240 s) : term28 _87240 s.
Proof. exact (fun h0 : term26 _87240 s => @lem3354811 _87240 s h0 h1). Qed.
Lemma lem3354813 {_87240 : Type'} (s : _87240 -> Prop) : term30 _87240 s.
Proof. exact (fun h0 : term28 _87240 s => @lem3354812 _87240 s h0). Qed.
Lemma lem3354816 {_87240 : Type'} (s : _87240 -> Prop) : term28 _87240 s.
Proof. exact (@lem3354813 _87240 s (@lem3354805 _87240 s)). Qed.
Lemma lem3354817 {_87240 : Type'} (s : _87240 -> Prop) : term28 _87240 s.
Proof. exact (@lem3354816 _87240 s). Qed.
Lemma lem3354823 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3354824 {_87240 : Type'} (s : _87240 -> Prop) : (term26 _87240 s) = (term31 _87240 s).
Proof. exact (@lem3354823 (term27 _87240 s)). Qed.
Lemma lem3354826 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3354827 {_87240 : Type'} (s : _87240 -> Prop) : (term31 _87240 s) = (term24 _87240 s).
Proof. exact (@lem3354826 (term24 _87240 s)). Qed.
Lemma lem3354832 {_87240 : Type'} (s : _87240 -> Prop) : (term26 _87240 s) = (term24 _87240 s).
Proof. exact (TRANS (@lem3354824 _87240 s) (@lem3354827 _87240 s)). Qed.
Lemma lem3354839 {_87240 : Type'} : (term33 _87240) = (term34 _87240).
Proof. exact (fun_ext (fun s : _87240 -> Prop => @lem3354832 _87240 s)). Qed.
Lemma lem3354840 {_87240 : Type'} : (@all (_87240 -> Prop)) = (@all (_87240 -> Prop)).
Proof. exact (eq_refl (@all (_87240 -> Prop))). Qed.
Lemma lem3354849 {_87240 : Type'} : (term35 _87240) = (term36 _87240).
Proof. exact (MK_COMB (@lem3354840 _87240) (@lem3354839 _87240)). Qed.
Lemma lem3354850 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3354855 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term15 _87240 s t x) = (term15 _87240 s t x).
Proof. exact (eq_refl (term15 _87240 s t x)). Qed.
Lemma lem3354856 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term17 _87240 s x) = (term17 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3354855 _87240 s t x)). Qed.
Lemma lem3354857 {_87240 : Type'} : (@all (_87240 -> Prop)) = (@all (_87240 -> Prop)).
Proof. exact (eq_refl (@all (_87240 -> Prop))). Qed.
Lemma lem3354858 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term18 _87240 s x) = (term18 _87240 s x).
Proof. exact (MK_COMB (@lem3354857 _87240) (@lem3354856 _87240 s x)). Qed.
Lemma lem3354859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3354860 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term20 _87240 s x) = (term20 _87240 s x).
Proof. exact (MK_COMB (@lem3354859) (@lem3354858 _87240 s x)). Qed.
Lemma lem3354861 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : ((term18 _87240 s x) = (s x)) = ((term18 _87240 s x) = (s x)).
Proof. exact (MK_COMB (@lem3354860 _87240 s x) (@lem3354850 _87240 s x)). Qed.
Lemma lem3354862 {_87240 : Type'} (s : _87240 -> Prop) : (term22 _87240 s) = (term22 _87240 s).
Proof. exact (fun_ext (fun x : _87240 => @lem3354861 _87240 s x)). Qed.
Lemma lem3354863 {_87240 : Type'} : (@all _87240) = (@all _87240).
Proof. exact (eq_refl (@all _87240)). Qed.
Lemma lem3354864 {_87240 : Type'} (s : _87240 -> Prop) : (term24 _87240 s) = (term24 _87240 s).
Proof. exact (MK_COMB (@lem3354863 _87240) (@lem3354862 _87240 s)). Qed.
Lemma lem3354865 {_87240 : Type'} : (term34 _87240) = (term34 _87240).
Proof. exact (fun_ext (fun s : _87240 -> Prop => @lem3354864 _87240 s)). Qed.
Lemma lem3354866 {_87240 : Type'} : (@all (_87240 -> Prop)) = (@all (_87240 -> Prop)).
Proof. exact (eq_refl (@all (_87240 -> Prop))). Qed.
Lemma lem3354867 {_87240 : Type'} : (term36 _87240) = (term36 _87240).
Proof. exact (MK_COMB (@lem3354866 _87240) (@lem3354865 _87240)). Qed.
Lemma lem3354890 {_87240 : Type'} : (term35 _87240) = (term36 _87240).
Proof. exact (TRANS (@lem3354849 _87240) (@lem3354867 _87240)). Qed.
Lemma lem3354891 {_87240 : Type'} : (term36 _87240) = (term35 _87240).
Proof. exact (SYM (@lem3354890 _87240)). Qed.
Lemma lem3354893 (p : Prop) : p = (term25 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3354894 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : ((term18 _87240 s x) = (s x)) = (term37 _87240 s x).
Proof. exact (@lem3354893 ((term18 _87240 s x) = (s x))). Qed.
Lemma lem3354895 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term37 _87240 s x) = ((term18 _87240 s x) = (s x)).
Proof. exact (SYM (@lem3354894 _87240 s x)). Qed.
Lemma lem3354896 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term38 _87240 s x) : term38 _87240 s x.
Proof. exact (h1). Qed.
Lemma lem3354905 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term39 _87240 s t x) = (term40 _87240 s t x).
Proof. exact (@lem17362 (t = s) (t x)). Qed.
Lemma lem3354910 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term15 _87240 s t x) = (term41 _87240 s t x).
Proof. exact (@lem17265 (t = s) (t x)). Qed.
Lemma lem3354911 {_87240 : Type'} (P : type686 _87240) : (term42 _87240 P) = (term43 _87240 P).
Proof. exact (@lem18392 (_87240 -> Prop) P). Qed.
Lemma lem3354912 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term44 _87240 s x) = (term45 _87240 s x).
Proof. exact (@lem3354911 _87240 (term17 _87240 s x)). Qed.
Lemma lem3354913 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term46 _87240 s x t) = (term15 _87240 s t x).
Proof. exact (eq_refl (term46 _87240 s x t)). Qed.
Lemma lem3354914 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3354915 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term47 _87240 s x t) = (term39 _87240 s t x).
Proof. exact (MK_COMB (@lem3354914) (@lem3354913 _87240 s t x)). Qed.
Lemma lem3354916 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term47 _87240 s x t) = (term40 _87240 s t x).
Proof. exact (TRANS (@lem3354915 _87240 s t x) (@lem3354905 _87240 s t x)). Qed.
Lemma lem3354917 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term48 _87240 s x) = (term49 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3354916 _87240 s t x)). Qed.
Lemma lem3354918 {_87240 : Type'} : (@ex (_87240 -> Prop)) = (@ex (_87240 -> Prop)).
Proof. exact (eq_refl (@ex (_87240 -> Prop))). Qed.
Lemma lem3354919 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term45 _87240 s x) = (term50 _87240 s x).
Proof. exact (MK_COMB (@lem3354918 _87240) (@lem3354917 _87240 s x)). Qed.
Lemma lem3354920 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term44 _87240 s x) = (term50 _87240 s x).
Proof. exact (TRANS (@lem3354912 _87240 s x) (@lem3354919 _87240 s x)). Qed.
Lemma lem3354921 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term17 _87240 s x) = (term51 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3354910 _87240 s t x)). Qed.
Lemma lem3354922 {_87240 : Type'} : (@all (_87240 -> Prop)) = (@all (_87240 -> Prop)).
Proof. exact (eq_refl (@all (_87240 -> Prop))). Qed.
Lemma lem3354923 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term18 _87240 s x) = (term52 _87240 s x).
Proof. exact (MK_COMB (@lem3354922 _87240) (@lem3354921 _87240 s x)). Qed.
Lemma lem3354924 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term53 _87240 s x) = (term53 _87240 s x).
Proof. exact (eq_refl (term53 _87240 s x)). Qed.
Lemma lem3354925 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3354926 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3354927 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term54 _87240 s x) = (term55 _87240 s x).
Proof. exact (MK_COMB (@lem3354926) (@lem3354920 _87240 s x)). Qed.
Lemma lem3354928 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term56 _87240 s x) = (term57 _87240 s x).
Proof. exact (MK_COMB (@lem3354927 _87240 s x) (@lem3354925 _87240 s x)). Qed.
Lemma lem3354929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3354930 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term58 _87240 s x) = (term59 _87240 s x).
Proof. exact (MK_COMB (@lem3354929) (@lem3354923 _87240 s x)). Qed.
Lemma lem3354931 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term60 _87240 s x) = (term61 _87240 s x).
Proof. exact (MK_COMB (@lem3354930 _87240 s x) (@lem3354924 _87240 s x)). Qed.
Lemma lem3354932 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3354933 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term62 _87240 s x) = (term63 _87240 s x).
Proof. exact (MK_COMB (@lem3354932) (@lem3354931 _87240 s x)). Qed.
Lemma lem3354934 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term64 _87240 s x) = (term65 _87240 s x).
Proof. exact (MK_COMB (@lem3354933 _87240 s x) (@lem3354928 _87240 s x)). Qed.
Lemma lem3354935 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term38 _87240 s x) = (term64 _87240 s x).
Proof. exact (@lem17646 (term18 _87240 s x) (s x)). Qed.
Lemma lem3354936 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term38 _87240 s x) = (term65 _87240 s x).
Proof. exact (TRANS (@lem3354935 _87240 s x) (@lem3354934 _87240 s x)). Qed.
Lemma lem3355035 {A : Type'} (P : A -> Prop) (Q : Prop) : (term66 A P Q) = (term67 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3355036 {_87240 : Type'} (P : type686 _87240) (Q : Prop) : (term68 _87240 P Q) = (term69 _87240 P Q).
Proof. exact (@lem3355035 (_87240 -> Prop) P Q). Qed.
Lemma lem3355037 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term70 _87240 s x) = (term71 _87240 s x).
Proof. exact (@lem3355036 _87240 (term49 _87240 s x) (s x)). Qed.
Lemma lem3355038 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term72 _87240 s x t) = (term40 _87240 s t x).
Proof. exact (eq_refl (term72 _87240 s x t)). Qed.
Lemma lem3355039 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term73 _87240 s x) = (term49 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3355038 _87240 s t x)). Qed.
Lemma lem3355040 {_87240 : Type'} : (@ex (_87240 -> Prop)) = (@ex (_87240 -> Prop)).
Proof. exact (eq_refl (@ex (_87240 -> Prop))). Qed.
Lemma lem3355041 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term74 _87240 s x) = (term50 _87240 s x).
Proof. exact (MK_COMB (@lem3355040 _87240) (@lem3355039 _87240 s x)). Qed.
Lemma lem3355042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355043 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term75 _87240 s x) = (term55 _87240 s x).
Proof. exact (MK_COMB (@lem3355042) (@lem3355041 _87240 s x)). Qed.
Lemma lem3355044 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3355045 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term70 _87240 s x) = (term57 _87240 s x).
Proof. exact (MK_COMB (@lem3355043 _87240 s x) (@lem3355044 _87240 s x)). Qed.
Lemma lem3355046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355047 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term76 _87240 s x) = (term77 _87240 s x).
Proof. exact (MK_COMB (@lem3355046) (@lem3355045 _87240 s x)). Qed.
Lemma lem3355048 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term72 _87240 s x t) = (term40 _87240 s t x).
Proof. exact (eq_refl (term72 _87240 s x t)). Qed.
Lemma lem3355049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355050 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term78 _87240 s x t) = (term79 _87240 s t x).
Proof. exact (MK_COMB (@lem3355049) (@lem3355048 _87240 s t x)). Qed.
Lemma lem3355051 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3355052 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : (term80 _87240 t s x) = (term81 _87240 t s x).
Proof. exact (MK_COMB (@lem3355050 _87240 s t x) (@lem3355051 _87240 s x)). Qed.
Lemma lem3355053 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term82 _87240 s x) = (term83 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3355052 _87240 t s x)). Qed.
Lemma lem3355054 {_87240 : Type'} : (@ex (_87240 -> Prop)) = (@ex (_87240 -> Prop)).
Proof. exact (eq_refl (@ex (_87240 -> Prop))). Qed.
Lemma lem3355055 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term71 _87240 s x) = (term84 _87240 s x).
Proof. exact (MK_COMB (@lem3355054 _87240) (@lem3355053 _87240 s x)). Qed.
Lemma lem3355056 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : ((term70 _87240 s x) = (term71 _87240 s x)) = ((term57 _87240 s x) = (term84 _87240 s x)).
Proof. exact (MK_COMB (@lem3355047 _87240 s x) (@lem3355055 _87240 s x)). Qed.
Lemma lem3355057 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term57 _87240 s x) = (term84 _87240 s x).
Proof. exact (EQ_MP (@lem3355056 _87240 s x) (@lem3355037 _87240 s x)). Qed.
Lemma lem3355058 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term63 _87240 s x) = (term63 _87240 s x).
Proof. exact (eq_refl (term63 _87240 s x)). Qed.
Lemma lem3355059 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term65 _87240 s x) = (term85 _87240 s x).
Proof. exact (MK_COMB (@lem3355058 _87240 s x) (@lem3355057 _87240 s x)). Qed.
Lemma lem3355061 {A : Type'} (P : Prop) (Q : A -> Prop) : (term86 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3355062 {_87240 : Type'} (P : Prop) (Q : type686 _87240) : (term88 _87240 P Q) = (term89 _87240 P Q).
Proof. exact (@lem3355061 (_87240 -> Prop) P Q). Qed.
Lemma lem3355063 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term90 _87240 s x) = (term91 _87240 s x).
Proof. exact (@lem3355062 _87240 (term61 _87240 s x) (term83 _87240 s x)). Qed.
Lemma lem3355064 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : (term92 _87240 s x t) = (term81 _87240 t s x).
Proof. exact (eq_refl (term92 _87240 s x t)). Qed.
Lemma lem3355065 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term93 _87240 s x) = (term83 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3355064 _87240 t s x)). Qed.
Lemma lem3355066 {_87240 : Type'} : (@ex (_87240 -> Prop)) = (@ex (_87240 -> Prop)).
Proof. exact (eq_refl (@ex (_87240 -> Prop))). Qed.
Lemma lem3355067 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term94 _87240 s x) = (term84 _87240 s x).
Proof. exact (MK_COMB (@lem3355066 _87240) (@lem3355065 _87240 s x)). Qed.
Lemma lem3355068 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term63 _87240 s x) = (term63 _87240 s x).
Proof. exact (eq_refl (term63 _87240 s x)). Qed.
Lemma lem3355069 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term90 _87240 s x) = (term85 _87240 s x).
Proof. exact (MK_COMB (@lem3355068 _87240 s x) (@lem3355067 _87240 s x)). Qed.
Lemma lem3355070 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355071 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term95 _87240 s x) = (term96 _87240 s x).
Proof. exact (MK_COMB (@lem3355070) (@lem3355069 _87240 s x)). Qed.
Lemma lem3355072 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : (term92 _87240 s x t) = (term81 _87240 t s x).
Proof. exact (eq_refl (term92 _87240 s x t)). Qed.
Lemma lem3355073 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term63 _87240 s x) = (term63 _87240 s x).
Proof. exact (eq_refl (term63 _87240 s x)). Qed.
Lemma lem3355074 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : (term97 _87240 s x t) = (term98 _87240 t s x).
Proof. exact (MK_COMB (@lem3355073 _87240 s x) (@lem3355072 _87240 t s x)). Qed.
Lemma lem3355075 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term99 _87240 s x) = (term100 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3355074 _87240 t s x)). Qed.
Lemma lem3355076 {_87240 : Type'} : (@ex (_87240 -> Prop)) = (@ex (_87240 -> Prop)).
Proof. exact (eq_refl (@ex (_87240 -> Prop))). Qed.
Lemma lem3355077 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term91 _87240 s x) = (term101 _87240 s x).
Proof. exact (MK_COMB (@lem3355076 _87240) (@lem3355075 _87240 s x)). Qed.
Lemma lem3355078 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : ((term90 _87240 s x) = (term91 _87240 s x)) = ((term85 _87240 s x) = (term101 _87240 s x)).
Proof. exact (MK_COMB (@lem3355071 _87240 s x) (@lem3355077 _87240 s x)). Qed.
Lemma lem3355079 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term85 _87240 s x) = (term101 _87240 s x).
Proof. exact (EQ_MP (@lem3355078 _87240 s x) (@lem3355063 _87240 s x)). Qed.
Lemma lem3355081 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term65 _87240 s x) = (term101 _87240 s x).
Proof. exact (TRANS (@lem3355059 _87240 s x) (@lem3355079 _87240 s x)). Qed.
Lemma lem3355082 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term38 _87240 s x) = (term101 _87240 s x).
Proof. exact (TRANS (@lem3354936 _87240 s x) (@lem3355081 _87240 s x)). Qed.
Lemma lem3355083 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term38 _87240 s x) : term101 _87240 s x.
Proof. exact (EQ_MP (@lem3355082 _87240 s x) (@lem3354896 _87240 s x h1)). Qed.
Lemma lem3355084 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term98 _87240 t s x) : term98 _87240 t s x.
Proof. exact (h1). Qed.
Lemma lem3355089 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355090 {_87240 : Type'} (f : _87240 -> Prop) (x : _87240) : (f x) = (@I (_87240 -> Prop) f x).
Proof. exact (@lem3355089 _87240 Prop f x). Qed.
Lemma lem3355092 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (s x) = (@I (_87240 -> Prop) s x).
Proof. exact (@lem3355090 _87240 s x). Qed.
Lemma lem3355093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3355098 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355099 {_87240 : Type'} (f : _87240 -> Prop) (x : _87240) : (f x) = (@I (_87240 -> Prop) f x).
Proof. exact (@lem3355098 _87240 Prop f x). Qed.
Lemma lem3355101 {_87240 : Type'} (t : _87240 -> Prop) (x : _87240) : (t x) = (@I (_87240 -> Prop) t x).
Proof. exact (@lem3355099 _87240 t x). Qed.
Lemma lem3355102 {_87240 : Type'} (t : _87240 -> Prop) (x : _87240) : (term53 _87240 t x) = (term102 _87240 t x).
Proof. exact (MK_COMB (@lem3355093) (@lem3355101 _87240 t x)). Qed.
Lemma lem3355109 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term103 _87240 t s) = (term103 _87240 t s).
Proof. exact (eq_refl (term103 _87240 t s)). Qed.
Lemma lem3355110 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term40 _87240 s t x) = (term104 _87240 s t x).
Proof. exact (MK_COMB (@lem3355109 _87240 t s) (@lem3355102 _87240 t x)). Qed.
Lemma lem3355111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355112 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term79 _87240 s t x) = (term105 _87240 s t x).
Proof. exact (MK_COMB (@lem3355111) (@lem3355110 _87240 s t x)). Qed.
Lemma lem3355113 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : (term81 _87240 t s x) = (term106 _87240 t s x).
Proof. exact (MK_COMB (@lem3355112 _87240 s t x) (@lem3355092 _87240 s x)). Qed.
Lemma lem3355114 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3355119 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355120 {_87240 : Type'} (f : _87240 -> Prop) (x : _87240) : (f x) = (@I (_87240 -> Prop) f x).
Proof. exact (@lem3355119 _87240 Prop f x). Qed.
Lemma lem3355122 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (s x) = (@I (_87240 -> Prop) s x).
Proof. exact (@lem3355120 _87240 s x). Qed.
Lemma lem3355123 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term53 _87240 s x) = (term102 _87240 s x).
Proof. exact (MK_COMB (@lem3355114) (@lem3355122 _87240 s x)). Qed.
Lemma lem3355128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem3355129 {_87240 : Type'} (f : _87240 -> Prop) (x : _87240) : (f x) = (@I (_87240 -> Prop) f x).
Proof. exact (@lem3355128 _87240 Prop f x). Qed.
Lemma lem3355131 {_87240 : Type'} (t : _87240 -> Prop) (x : _87240) : (t x) = (@I (_87240 -> Prop) t x).
Proof. exact (@lem3355129 _87240 t x). Qed.
Lemma lem3355140 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) : (term107 _87240 t s) = (term107 _87240 t s).
Proof. exact (eq_refl (term107 _87240 t s)). Qed.
Lemma lem3355141 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term41 _87240 s t x) = (term108 _87240 s t x).
Proof. exact (MK_COMB (@lem3355140 _87240 t s) (@lem3355131 _87240 t x)). Qed.
Lemma lem3355142 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term51 _87240 s x) = (term109 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3355141 _87240 s t x)). Qed.
Lemma lem3355143 {_87240 : Type'} : (@all (_87240 -> Prop)) = (@all (_87240 -> Prop)).
Proof. exact (eq_refl (@all (_87240 -> Prop))). Qed.
Lemma lem3355144 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term52 _87240 s x) = (term110 _87240 s x).
Proof. exact (MK_COMB (@lem3355143 _87240) (@lem3355142 _87240 s x)). Qed.
Lemma lem3355145 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3355146 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term59 _87240 s x) = (term111 _87240 s x).
Proof. exact (MK_COMB (@lem3355145) (@lem3355144 _87240 s x)). Qed.
Lemma lem3355147 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term61 _87240 s x) = (term112 _87240 s x).
Proof. exact (MK_COMB (@lem3355146 _87240 s x) (@lem3355123 _87240 s x)). Qed.
Lemma lem3355148 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3355149 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term63 _87240 s x) = (term113 _87240 s x).
Proof. exact (MK_COMB (@lem3355148) (@lem3355147 _87240 s x)). Qed.
Lemma lem3355150 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : (term98 _87240 t s x) = (term114 _87240 t s x).
Proof. exact (MK_COMB (@lem3355149 _87240 s x) (@lem3355113 _87240 t s x)). Qed.
Lemma lem3355151 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term98 _87240 t s x) : term114 _87240 t s x.
Proof. exact (EQ_MP (@lem3355150 _87240 t s x) (@lem3355084 _87240 t s x h1)). Qed.
Lemma lem3355152 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term112 _87240 s x.
Proof. exact (h1). Qed.
Lemma lem3355153 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : term106 _87240 t s x.
Proof. exact (h1). Qed.
Lemma lem3355155 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term110 _87240 s x.
Proof. exact (proj1 (@lem3355152 _87240 s x h1)). Qed.
Lemma lem3355157 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : term104 _87240 s t x.
Proof. exact (proj1 (@lem3355153 _87240 t s x h1)). Qed.
Lemma lem3355167 {_87240 : Type'} (s : _87240 -> Prop) (t : _87240 -> Prop) (x : _87240) : (term108 _87240 s t x) = (term108 _87240 s t x).
Proof. exact (eq_refl (term108 _87240 s t x)). Qed.
Lemma lem3355168 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term109 _87240 s x) = (term109 _87240 s x).
Proof. exact (fun_ext (fun t : _87240 -> Prop => @lem3355167 _87240 s t x)). Qed.
Lemma lem3355169 {_87240 : Type'} : (@all (_87240 -> Prop)) = (@all (_87240 -> Prop)).
Proof. exact (eq_refl (@all (_87240 -> Prop))). Qed.
Lemma lem3355171 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term110 _87240 s x) = (term110 _87240 s x).
Proof. exact (MK_COMB (@lem3355169 _87240) (@lem3355168 _87240 s x)). Qed.
Lemma lem3355172 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term110 _87240 s x.
Proof. exact (EQ_MP (@lem3355171 _87240 s x) (@lem3355155 _87240 s x h1)). Qed.
Lemma lem3355189 {_87240 : Type'} (_34996 : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term115 _87240 s x _34996.
Proof. exact (@lem3355172 _87240 s x h1 _34996). Qed.
Lemma lem3355190 {_87240 : Type'} (s : _87240 -> Prop) (_34996 : _87240 -> Prop) (x : _87240) : (term115 _87240 s x _34996) = (term108 _87240 s _34996 x).
Proof. exact (eq_refl (term115 _87240 s x _34996)). Qed.
Lemma lem3355197 {_87240 : Type'} (_34996 : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term108 _87240 s _34996 x.
Proof. exact (EQ_MP (@lem3355190 _87240 s _34996 x) (@lem3355189 _87240 _34996 s x h1)). Qed.
Lemma lem3355199 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term102 _87240 s x.
Proof. exact (proj2 (@lem3355152 _87240 s x h1)). Qed.
Lemma lem3355203 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : t = s.
Proof. exact (proj1 (@lem3355157 _87240 t s x h1)). Qed.
Lemma lem3355205 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : term102 _87240 t x.
Proof. exact (proj2 (@lem3355157 _87240 t s x h1)). Qed.
Lemma lem3355234 {_87240 : Type'} (x : _87240) : (term116 _87240 x) = (term116 _87240 x).
Proof. exact (eq_refl (term116 _87240 x)). Qed.
Lemma lem3355235 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : (term117 _87240 x t) = (term117 _87240 x s).
Proof. exact (MK_COMB (@lem3355234 _87240 x) (@lem3355203 _87240 t s x h1)). Qed.
Lemma lem3355236 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term117 _87240 x s) = (term102 _87240 s x).
Proof. exact (eq_refl (term117 _87240 x s)). Qed.
Lemma lem3355237 {_87240 : Type'} (x : _87240) (t : _87240 -> Prop) : (term118 _87240 x t) = (term118 _87240 x t).
Proof. exact (eq_refl (term118 _87240 x t)). Qed.
Lemma lem3355238 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : ((term117 _87240 x t) = (term117 _87240 x s)) = ((term117 _87240 x t) = (term102 _87240 s x)).
Proof. exact (MK_COMB (@lem3355237 _87240 x t) (@lem3355236 _87240 s x)). Qed.
Lemma lem3355239 {_87240 : Type'} (t : _87240 -> Prop) (x : _87240) : (term117 _87240 x t) = (term102 _87240 t x).
Proof. exact (eq_refl (term117 _87240 x t)). Qed.
Lemma lem3355240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355241 {_87240 : Type'} (t : _87240 -> Prop) (x : _87240) : (term118 _87240 x t) = (term119 _87240 t x).
Proof. exact (MK_COMB (@lem3355240) (@lem3355239 _87240 t x)). Qed.
Lemma lem3355242 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term102 _87240 s x) = (term102 _87240 s x).
Proof. exact (eq_refl (term102 _87240 s x)). Qed.
Lemma lem3355243 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : ((term117 _87240 x t) = (term102 _87240 s x)) = ((term102 _87240 t x) = (term102 _87240 s x)).
Proof. exact (MK_COMB (@lem3355241 _87240 t x) (@lem3355242 _87240 s x)). Qed.
Lemma lem3355244 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) : ((term117 _87240 x t) = (term117 _87240 x s)) = ((term102 _87240 t x) = (term102 _87240 s x)).
Proof. exact (TRANS (@lem3355238 _87240 t s x) (@lem3355243 _87240 t s x)). Qed.
Lemma lem3355245 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : (term102 _87240 t x) = (term102 _87240 s x).
Proof. exact (EQ_MP (@lem3355244 _87240 t s x) (@lem3355235 _87240 t s x h1)). Qed.
Lemma lem3355246 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : term102 _87240 s x.
Proof. exact (EQ_MP (@lem3355245 _87240 t s x h1) (@lem3355205 _87240 t s x h1)). Qed.
Lemma lem3355271 {_87240 : Type'} (x : _87240 -> Prop) : x = x.
Proof. exact (@lem21386 (_87240 -> Prop) x). Qed.
Lemma lem3355272 {_87240 : Type'} (x : _87240 -> Prop) : x = x.
Proof. exact (@lem3355271 _87240 x). Qed.
Lemma lem3355273 {_87240 : Type'} (s : _87240 -> Prop) : s = s.
Proof. exact (@lem3355272 _87240 s). Qed.
Lemma lem3355274 {_87240 : Type'} (s : _87240 -> Prop) : term120 _87240 s.
Proof. exact (fun h0 : term121 _87240 s => @lem3355273 _87240 s). Qed.
Lemma lem3355276 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3355277 {_87240 : Type'} (s : _87240 -> Prop) : (term120 _87240 s) = (s = s).
Proof. exact (@lem3355276 (s = s)). Qed.
Lemma lem3355278 {_87240 : Type'} (s : _87240 -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3355277 _87240 s) (@lem3355274 _87240 s)). Qed.
Lemma lem3355284 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3355285 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : (term108 _87240 s _34996 x) = (term123 _87240 x _34996 s).
Proof. exact (@lem3355284 (@I (_87240 -> Prop) _34996 x) (term124 _87240 _34996 s)). Qed.
Lemma lem3355293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3355294 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : (term125 _87240 s _34996 x) = (term126 _87240 x _34996 s).
Proof. exact (MK_COMB (@lem3355293) (@lem3355285 _87240 x _34996 s)). Qed.
Lemma lem3355302 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : (term123 _87240 x _34996 s) = (term123 _87240 x _34996 s).
Proof. exact (eq_refl (term123 _87240 x _34996 s)). Qed.
Lemma lem3355303 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : ((term108 _87240 s _34996 x) = (term123 _87240 x _34996 s)) = ((term123 _87240 x _34996 s) = (term123 _87240 x _34996 s)).
Proof. exact (MK_COMB (@lem3355294 _87240 x _34996 s) (@lem3355302 _87240 x _34996 s)). Qed.
Lemma lem3355305 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3355306 (x : Prop) : (x = x) = True.
Proof. exact (@lem3355305 Prop x). Qed.
Lemma lem3355307 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : ((term123 _87240 x _34996 s) = (term123 _87240 x _34996 s)) = True.
Proof. exact (@lem3355306 (term123 _87240 x _34996 s)). Qed.
Lemma lem3355308 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : ((term108 _87240 s _34996 x) = (term123 _87240 x _34996 s)) = True.
Proof. exact (TRANS (@lem3355303 _87240 x _34996 s) (@lem3355307 _87240 x _34996 s)). Qed.
Lemma lem3355309 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : True = ((term108 _87240 s _34996 x) = (term123 _87240 x _34996 s)).
Proof. exact (SYM (@lem3355308 _87240 x _34996 s)). Qed.
Lemma lem3355310 {_87240 : Type'} (x : _87240) (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : (term108 _87240 s _34996 x) = (term123 _87240 x _34996 s).
Proof. exact (EQ_MP (@lem3355309 _87240 x _34996 s) (@lem0)). Qed.
Lemma lem3355311 {_87240 : Type'} (_34996 : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term123 _87240 x _34996 s.
Proof. exact (EQ_MP (@lem3355310 _87240 x _34996 s) (@lem3355197 _87240 _34996 s x h1)). Qed.
Lemma lem3355313 (b : Prop) (a : Prop) : (a \/ b) = (term127 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3355314 {_87240 : Type'} (s : _87240 -> Prop) (_34996 : _87240 -> Prop) (x : _87240) : (term123 _87240 x _34996 s) = (term128 _87240 s _34996 x).
Proof. exact (@lem3355313 (term124 _87240 _34996 s) (@I (_87240 -> Prop) _34996 x)). Qed.
Lemma lem3355316 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3355317 {_87240 : Type'} (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : (term129 _87240 _34996 s) = (_34996 = s).
Proof. exact (@lem3355316 (_34996 = s)). Qed.
Lemma lem3355318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3355319 {_87240 : Type'} (_34996 : _87240 -> Prop) (s : _87240 -> Prop) : (term130 _87240 _34996 s) = (term13 _87240 _34996 s).
Proof. exact (MK_COMB (@lem3355318) (@lem3355317 _87240 _34996 s)). Qed.
Lemma lem3355320 {_87240 : Type'} (_34996 : _87240 -> Prop) (x : _87240) : (@I (_87240 -> Prop) _34996 x) = (@I (_87240 -> Prop) _34996 x).
Proof. exact (eq_refl (@I (_87240 -> Prop) _34996 x)). Qed.
Lemma lem3355321 {_87240 : Type'} (s : _87240 -> Prop) (_34996 : _87240 -> Prop) (x : _87240) : (term128 _87240 s _34996 x) = (term131 _87240 s _34996 x).
Proof. exact (MK_COMB (@lem3355319 _87240 _34996 s) (@lem3355320 _87240 _34996 x)). Qed.
Lemma lem3355322 {_87240 : Type'} (s : _87240 -> Prop) (_34996 : _87240 -> Prop) (x : _87240) : (term123 _87240 x _34996 s) = (term131 _87240 s _34996 x).
Proof. exact (TRANS (@lem3355314 _87240 s _34996 x) (@lem3355321 _87240 s _34996 x)). Qed.
Lemma lem3355325 {_87240 : Type'} (_34996 : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term131 _87240 s _34996 x.
Proof. exact (EQ_MP (@lem3355322 _87240 s _34996 x) (@lem3355311 _87240 _34996 s x h1)). Qed.
Lemma lem3355326 {_87240 : Type'} (_34996 : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term131 _87240 s _34996 x.
Proof. exact (@lem3355325 _87240 _34996 s x h1). Qed.
Lemma lem3355327 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term132 _87240 s x.
Proof. exact (@lem3355326 _87240 s s x h1). Qed.
Lemma lem3355330 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : @I (_87240 -> Prop) s x.
Proof. exact (@lem3355327 _87240 s x h1 (@lem3355278 _87240 s)). Qed.
Lemma lem3355331 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term133 _87240 s x.
Proof. exact (fun h0 : term102 _87240 s x => @lem3355330 _87240 s x h1). Qed.
Lemma lem3355333 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3355334 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term133 _87240 s x) = (@I (_87240 -> Prop) s x).
Proof. exact (@lem3355333 (@I (_87240 -> Prop) s x)). Qed.
Lemma lem3355335 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : @I (_87240 -> Prop) s x.
Proof. exact (EQ_MP (@lem3355334 _87240 s x) (@lem3355331 _87240 s x h1)). Qed.
Lemma lem3355338 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3355340 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term102 _87240 s x) = (term134 _87240 s x).
Proof. exact (@lem3355338 (@I (_87240 -> Prop) s x)). Qed.
Lemma lem3355343 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term134 _87240 s x.
Proof. exact (EQ_MP (@lem3355340 _87240 s x) (@lem3355199 _87240 s x h1)). Qed.
Lemma lem3355346 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : False.
Proof. exact (@lem3355343 _87240 s x h1 (@lem3355335 _87240 s x h1)). Qed.
Lemma lem3355347 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : term135.
Proof. exact (fun h0 : ~ False => @lem3355346 _87240 s x h1). Qed.
Lemma lem3355349 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3355350 : term135 = False.
Proof. exact (@lem3355349 False). Qed.
Lemma lem3355351 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term112 _87240 s x) : False.
Proof. exact (EQ_MP (@lem3355350) (@lem3355347 _87240 s x h1)). Qed.
Lemma lem3355353 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : @I (_87240 -> Prop) s x.
Proof. exact (proj2 (@lem3355153 _87240 t s x h1)). Qed.
Lemma lem3355354 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : term133 _87240 s x.
Proof. exact (fun h0 : term102 _87240 s x => @lem3355353 _87240 t s x h1). Qed.
Lemma lem3355356 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3355357 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term133 _87240 s x) = (@I (_87240 -> Prop) s x).
Proof. exact (@lem3355356 (@I (_87240 -> Prop) s x)). Qed.
Lemma lem3355358 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : @I (_87240 -> Prop) s x.
Proof. exact (EQ_MP (@lem3355357 _87240 s x) (@lem3355354 _87240 t s x h1)). Qed.
Lemma lem3355361 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3355363 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term102 _87240 s x) = (term134 _87240 s x).
Proof. exact (@lem3355361 (@I (_87240 -> Prop) s x)). Qed.
Lemma lem3355366 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : term134 _87240 s x.
Proof. exact (EQ_MP (@lem3355363 _87240 s x) (@lem3355246 _87240 t s x h1)). Qed.
Lemma lem3355369 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : False.
Proof. exact (@lem3355366 _87240 t s x h1 (@lem3355358 _87240 t s x h1)). Qed.
Lemma lem3355370 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : term135.
Proof. exact (fun h0 : ~ False => @lem3355369 _87240 t s x h1). Qed.
Lemma lem3355372 (p : Prop) : (term122 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3355373 : term135 = False.
Proof. exact (@lem3355372 False). Qed.
Lemma lem3355375 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term106 _87240 t s x) : False.
Proof. exact (EQ_MP (@lem3355373) (@lem3355370 _87240 t s x h1)). Qed.
Lemma lem3355376 {_87240 : Type'} (t : _87240 -> Prop) (s : _87240 -> Prop) (x : _87240) (h1 : term98 _87240 t s x) : False.
Proof. exact (or_elim (@lem3355151 _87240 t s x h1) (fun h0 : term112 _87240 s x => @lem3355351 _87240 s x h0) (fun h0 : term106 _87240 t s x => @lem3355375 _87240 t s x h0)). Qed.
Lemma lem3355377 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term38 _87240 s x) : False.
Proof. exact (ex_elim (@lem3355083 _87240 s x h1) (fun t : _87240 -> Prop => fun h0 : term100 _87240 s x t => @lem3355376 _87240 t s x h0)). Qed.
Lemma lem3355378 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term38 _87240 s x) : (term38 _87240 s x) = False.
Proof. exact (prop_ext (fun h2 : term38 _87240 s x => @lem3355377 _87240 s x h1) (fun h2 : False => @lem3354896 _87240 s x h1)). Qed.
Lemma lem3355379 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) (h1 : term38 _87240 s x) : False.
Proof. exact (EQ_MP (@lem3355378 _87240 s x h1) (@lem3354896 _87240 s x h1)). Qed.
Lemma lem3355380 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : term37 _87240 s x.
Proof. exact (fun h0 : term38 _87240 s x => @lem3355379 _87240 s x h0). Qed.
Lemma lem3355381 {_87240 : Type'} (s : _87240 -> Prop) (x : _87240) : (term18 _87240 s x) = (s x).
Proof. exact (EQ_MP (@lem3354895 _87240 s x) (@lem3355380 _87240 s x)). Qed.
Lemma lem3355386 {_87240 : Type'} (s : _87240 -> Prop) : term24 _87240 s.
Proof. exact (fun x : _87240 => @lem3355381 _87240 s x). Qed.
Lemma lem3355391 {_87240 : Type'} : term36 _87240.
Proof. exact (fun s : _87240 -> Prop => @lem3355386 _87240 s). Qed.
Lemma lem3355392 {_87240 : Type'} : term35 _87240.
Proof. exact (EQ_MP (@lem3354891 _87240) (@lem3355391 _87240)). Qed.
Lemma lem3355393 {_87240 : Type'} (s : _87240 -> Prop) : term136 _87240 s.
Proof. exact (@lem3355392 _87240 s). Qed.
Lemma lem3355394 {_87240 : Type'} (s : _87240 -> Prop) : (term136 _87240 s) = (term26 _87240 s).
Proof. exact (eq_refl (term136 _87240 s)). Qed.
Lemma lem3355395 {_87240 : Type'} (s : _87240 -> Prop) : term26 _87240 s.
Proof. exact (EQ_MP (@lem3355394 _87240 s) (@lem3355393 _87240 s)). Qed.
Lemma lem3355397 {_87240 : Type'} (s : _87240 -> Prop) : term26 _87240 s.
Proof. exact (@lem3354817 _87240 s (@lem3355395 _87240 s)). Qed.
Lemma lem3355398 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term27 _87240 s) : False.
Proof. exact (@lem3355397 _87240 s (@lem3354801 _87240 s h1)). Qed.
Lemma lem3355399 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term27 _87240 s) : (term27 _87240 s) = False.
Proof. exact (prop_ext (fun h2 : term27 _87240 s => @lem3355398 _87240 s h1) (fun h2 : False => @lem3354801 _87240 s h1)). Qed.
Lemma lem3355400 {_87240 : Type'} (s : _87240 -> Prop) (h1 : term27 _87240 s) : False.
Proof. exact (EQ_MP (@lem3355399 _87240 s h1) (@lem3354801 _87240 s h1)). Qed.
Lemma lem3355401 {_87240 : Type'} (s : _87240 -> Prop) : term26 _87240 s.
Proof. exact (fun h0 : term27 _87240 s => @lem3355400 _87240 s h0). Qed.
Lemma lem3355402 {_87240 : Type'} (s : _87240 -> Prop) : term24 _87240 s.
Proof. exact (EQ_MP (@lem3354800 _87240 s) (@lem3355401 _87240 s)). Qed.
Lemma lem3355403 {_87240 : Type'} (s : _87240 -> Prop) : term23 _87240 s.
Proof. exact (EQ_MP (@lem3354796 _87240 s) (@lem3355402 _87240 s)). Qed.
