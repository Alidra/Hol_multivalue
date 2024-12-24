Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4848608_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm4845633_spec.
Lemma lem4845734 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4845735 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term1 _111301 P Q R) = (term2 _111301 P Q R)) = (term3 _111301 P Q R).
Proof. exact (@lem4845734 ((term1 _111301 P Q R) = (term2 _111301 P Q R))). Qed.
Lemma lem4845736 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term3 _111301 P Q R) = ((term1 _111301 P Q R) = (term2 _111301 P Q R)).
Proof. exact (SYM (@lem4845735 _111301 P Q R)). Qed.
Lemma lem4845737 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : term4 _111301 P Q R.
Proof. exact (h1). Qed.
Lemma lem4845740 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term3 _111301 P Q R) : term3 _111301 P Q R.
Proof. exact (h1). Qed.
Lemma lem4845741 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term5 _111301 P Q R.
Proof. exact (fun h0 : term3 _111301 P Q R => @lem4845740 _111301 P Q R h0). Qed.
Lemma lem4845742 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term5 _111301 P Q R) : term5 _111301 P Q R.
Proof. exact (h1). Qed.
Lemma lem4845743 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term3 _111301 P Q R) : term3 _111301 P Q R.
Proof. exact (h1). Qed.
Lemma lem4845744 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term3 _111301 P Q R) (h2 : term5 _111301 P Q R) : term3 _111301 P Q R.
Proof. exact (@lem4845742 _111301 P Q R h2 (@lem4845743 _111301 P Q R h1)). Qed.
Lemma lem4845745 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term3 _111301 P Q R) : term6 _111301 P Q R.
Proof. exact (fun h0 : term5 _111301 P Q R => @lem4845744 _111301 P Q R h1 h0). Qed.
Lemma lem4845746 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term5 _111301 P Q R) : term5 _111301 P Q R.
Proof. exact (h1). Qed.
Lemma lem4845747 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term3 _111301 P Q R) (h2 : term5 _111301 P Q R) : term3 _111301 P Q R.
Proof. exact (@lem4845745 _111301 P Q R h1 (@lem4845746 _111301 P Q R h2)). Qed.
Lemma lem4845748 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term5 _111301 P Q R) : term5 _111301 P Q R.
Proof. exact (fun h0 : term3 _111301 P Q R => @lem4845747 _111301 P Q R h0 h1). Qed.
Lemma lem4845749 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term7 _111301 P Q R.
Proof. exact (fun h0 : term5 _111301 P Q R => @lem4845748 _111301 P Q R h0). Qed.
Lemma lem4845752 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term5 _111301 P Q R.
Proof. exact (@lem4845749 _111301 P Q R (@lem4845741 _111301 P Q R)). Qed.
Lemma lem4845753 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term5 _111301 P Q R.
Proof. exact (@lem4845752 _111301 P Q R). Qed.
Lemma lem4845767 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4845768 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term3 _111301 P Q R) = (term8 _111301 P Q R).
Proof. exact (@lem4845767 (term4 _111301 P Q R)). Qed.
Lemma lem4845770 (t : Prop) : (term9 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4845771 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term8 _111301 P Q R) = ((term1 _111301 P Q R) = (term2 _111301 P Q R)).
Proof. exact (@lem4845770 ((term1 _111301 P Q R) = (term2 _111301 P Q R))). Qed.
Lemma lem4845772 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term3 _111301 P Q R) = ((term1 _111301 P Q R) = (term2 _111301 P Q R)).
Proof. exact (TRANS (@lem4845768 _111301 P Q R) (@lem4845771 _111301 P Q R)). Qed.
Lemma lem4845831 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) : (term10 _111301 Q R) = (term11 _111301 Q R).
Proof. exact (fun_ext (fun P : type180 _111301 => @lem4845772 _111301 P Q R)). Qed.
Lemma lem4845832 {_111301 : Type'} : (@all (((_111301 -> Prop) -> Prop) -> Prop)) = (@all (((_111301 -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((_111301 -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4845833 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) : (term12 _111301 Q R) = (term13 _111301 Q R).
Proof. exact (MK_COMB (@lem4845832 _111301) (@lem4845831 _111301 Q R)). Qed.
Lemma lem4845838 {_111301 : Type'} (R : type686 _111301) : (term14 _111301 R) = (term15 _111301 R).
Proof. exact (fun_ext (fun Q : type686 _111301 => @lem4845833 _111301 Q R)). Qed.
Lemma lem4845839 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4845840 {_111301 : Type'} (R : type686 _111301) : (term16 _111301 R) = (term17 _111301 R).
Proof. exact (MK_COMB (@lem4845839 _111301) (@lem4845838 _111301 R)). Qed.
Lemma lem4845845 {_111301 : Type'} : (term18 _111301) = (term19 _111301).
Proof. exact (fun_ext (fun R : type686 _111301 => @lem4845840 _111301 R)). Qed.
Lemma lem4845846 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4845855 {_111301 : Type'} : (term20 _111301) = (term21 _111301).
Proof. exact (MK_COMB (@lem4845846 _111301) (@lem4845845 _111301)). Qed.
Lemma lem4845856 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term22 _111301 R t) = (term22 _111301 R t).
Proof. exact (eq_refl (term22 _111301 R t)). Qed.
Lemma lem4845861 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term23 _111301 t Q c) = (term23 _111301 t Q c).
Proof. exact (eq_refl (term23 _111301 t Q c)). Qed.
Lemma lem4845862 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term24 _111301 t Q) = (term24 _111301 t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4845861 _111301 t Q c)). Qed.
Lemma lem4845863 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4845864 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term25 _111301 t Q) = (term25 _111301 t Q).
Proof. exact (MK_COMB (@lem4845863 _111301) (@lem4845862 _111301 t Q)). Qed.
Lemma lem4845867 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term26 _111301 P t) = (term26 _111301 P t).
Proof. exact (eq_refl (term26 _111301 P t)). Qed.
Lemma lem4845868 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term27 _111301 P t Q) = (term27 _111301 P t Q).
Proof. exact (MK_COMB (@lem4845867 _111301 P t) (@lem4845864 _111301 t Q)). Qed.
Lemma lem4845869 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4845870 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term28 _111301 P t Q) = (term28 _111301 P t Q).
Proof. exact (MK_COMB (@lem4845869) (@lem4845868 _111301 P t Q)). Qed.
Lemma lem4845871 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term29 _111301 P Q R t) = (term29 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4845870 _111301 P t Q) (@lem4845856 _111301 R t)). Qed.
Lemma lem4845872 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term30 _111301 P Q R) = (term30 _111301 P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4845871 _111301 P Q R t)). Qed.
Lemma lem4845873 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4845874 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term2 _111301 P Q R) = (term2 _111301 P Q R).
Proof. exact (MK_COMB (@lem4845873 _111301) (@lem4845872 _111301 P Q R)). Qed.
Lemma lem4845875 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4845876 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) : ((@UNIONS _111301 u) = s) = ((@UNIONS _111301 u) = s).
Proof. exact (eq_refl ((@UNIONS _111301 u) = s)). Qed.
Lemma lem4845881 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term23 _111301 u Q c) = (term23 _111301 u Q c).
Proof. exact (eq_refl (term23 _111301 u Q c)). Qed.
Lemma lem4845882 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term24 _111301 u Q) = (term24 _111301 u Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4845881 _111301 u Q c)). Qed.
Lemma lem4845883 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4845884 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term25 _111301 u Q) = (term25 _111301 u Q).
Proof. exact (MK_COMB (@lem4845883 _111301) (@lem4845882 _111301 u Q)). Qed.
Lemma lem4845885 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4845886 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term31 _111301 u Q) = (term31 _111301 u Q).
Proof. exact (MK_COMB (@lem4845885) (@lem4845884 _111301 u Q)). Qed.
Lemma lem4845887 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term32 _111301 Q u s) = (term32 _111301 Q u s).
Proof. exact (MK_COMB (@lem4845886 _111301 u Q) (@lem4845876 _111301 u s)). Qed.
Lemma lem4845890 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term26 _111301 P u) = (term26 _111301 P u).
Proof. exact (eq_refl (term26 _111301 P u)). Qed.
Lemma lem4845891 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term33 _111301 P Q u s) = (term33 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4845890 _111301 P u) (@lem4845887 _111301 Q u s)). Qed.
Lemma lem4845892 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term34 _111301 P Q s) = (term34 _111301 P Q s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4845891 _111301 P Q u s)). Qed.
Lemma lem4845893 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4845894 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term35 _111301 P Q s) = (term35 _111301 P Q s).
Proof. exact (MK_COMB (@lem4845893 _111301) (@lem4845892 _111301 P Q s)). Qed.
Lemma lem4845895 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4845896 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term36 _111301 P Q s) = (term36 _111301 P Q s).
Proof. exact (MK_COMB (@lem4845895) (@lem4845894 _111301 P Q s)). Qed.
Lemma lem4845897 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term37 _111301 P Q R s) = (term37 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4845896 _111301 P Q s) (@lem4845875 _111301 R s)). Qed.
Lemma lem4845898 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term38 _111301 P Q R) = (term38 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4845897 _111301 P Q R s)). Qed.
Lemma lem4845899 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4845900 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term1 _111301 P Q R) = (term1 _111301 P Q R).
Proof. exact (MK_COMB (@lem4845899 _111301) (@lem4845898 _111301 P Q R)). Qed.
Lemma lem4845901 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4845902 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term39 _111301 P Q R) = (term39 _111301 P Q R).
Proof. exact (MK_COMB (@lem4845901) (@lem4845900 _111301 P Q R)). Qed.
Lemma lem4845903 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term1 _111301 P Q R) = (term2 _111301 P Q R)) = ((term1 _111301 P Q R) = (term2 _111301 P Q R)).
Proof. exact (MK_COMB (@lem4845902 _111301 P Q R) (@lem4845874 _111301 P Q R)). Qed.
Lemma lem4845904 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) : (term11 _111301 Q R) = (term11 _111301 Q R).
Proof. exact (fun_ext (fun P : type180 _111301 => @lem4845903 _111301 P Q R)). Qed.
Lemma lem4845905 {_111301 : Type'} : (@all (((_111301 -> Prop) -> Prop) -> Prop)) = (@all (((_111301 -> Prop) -> Prop) -> Prop)).
Proof. exact (eq_refl (@all (((_111301 -> Prop) -> Prop) -> Prop))). Qed.
Lemma lem4845906 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) : (term13 _111301 Q R) = (term13 _111301 Q R).
Proof. exact (MK_COMB (@lem4845905 _111301) (@lem4845904 _111301 Q R)). Qed.
Lemma lem4845907 {_111301 : Type'} (R : type686 _111301) : (term15 _111301 R) = (term15 _111301 R).
Proof. exact (fun_ext (fun Q : type686 _111301 => @lem4845906 _111301 Q R)). Qed.
Lemma lem4845908 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4845909 {_111301 : Type'} (R : type686 _111301) : (term17 _111301 R) = (term17 _111301 R).
Proof. exact (MK_COMB (@lem4845908 _111301) (@lem4845907 _111301 R)). Qed.
Lemma lem4845910 {_111301 : Type'} : (term19 _111301) = (term19 _111301).
Proof. exact (fun_ext (fun R : type686 _111301 => @lem4845909 _111301 R)). Qed.
Lemma lem4845911 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4845912 {_111301 : Type'} : (term21 _111301) = (term21 _111301).
Proof. exact (MK_COMB (@lem4845911 _111301) (@lem4845910 _111301)). Qed.
Lemma lem4845977 {_111301 : Type'} : (term20 _111301) = (term21 _111301).
Proof. exact (TRANS (@lem4845855 _111301) (@lem4845912 _111301)). Qed.
Lemma lem4845978 {_111301 : Type'} : (term21 _111301) = (term20 _111301).
Proof. exact (SYM (@lem4845977 _111301)). Qed.
Lemma lem4845980 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4845981 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term1 _111301 P Q R) = (term2 _111301 P Q R)) = (term3 _111301 P Q R).
Proof. exact (@lem4845980 ((term1 _111301 P Q R) = (term2 _111301 P Q R))). Qed.
Lemma lem4845982 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term3 _111301 P Q R) = ((term1 _111301 P Q R) = (term2 _111301 P Q R)).
Proof. exact (SYM (@lem4845981 _111301 P Q R)). Qed.
Lemma lem4845983 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : term4 _111301 P Q R.
Proof. exact (h1). Qed.
Lemma lem4845994 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term40 _111301 u Q c) = (term41 _111301 u Q c).
Proof. exact (@lem17362 (@IN (_111301 -> Prop) c u) (Q c)). Qed.
Lemma lem4845999 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term23 _111301 u Q c) = (term42 _111301 u Q c).
Proof. exact (@lem17265 (@IN (_111301 -> Prop) c u) (Q c)). Qed.
Lemma lem4846000 {_111301 : Type'} (P : type686 _111301) : (term43 _111301 P) = (term44 _111301 P).
Proof. exact (@lem18392 (_111301 -> Prop) P). Qed.
Lemma lem4846001 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term45 _111301 u Q) = (term46 _111301 u Q).
Proof. exact (@lem4846000 _111301 (term24 _111301 u Q)). Qed.
Lemma lem4846002 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term47 _111301 u Q c) = (term23 _111301 u Q c).
Proof. exact (eq_refl (term47 _111301 u Q c)). Qed.
Lemma lem4846003 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4846004 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term48 _111301 u Q c) = (term40 _111301 u Q c).
Proof. exact (MK_COMB (@lem4846003) (@lem4846002 _111301 u Q c)). Qed.
Lemma lem4846005 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term48 _111301 u Q c) = (term41 _111301 u Q c).
Proof. exact (TRANS (@lem4846004 _111301 u Q c) (@lem4845994 _111301 u Q c)). Qed.
Lemma lem4846006 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term49 _111301 u Q) = (term50 _111301 u Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846005 _111301 u Q c)). Qed.
Lemma lem4846007 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846008 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term46 _111301 u Q) = (term51 _111301 u Q).
Proof. exact (MK_COMB (@lem4846007 _111301) (@lem4846006 _111301 u Q)). Qed.
Lemma lem4846009 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term45 _111301 u Q) = (term51 _111301 u Q).
Proof. exact (TRANS (@lem4846001 _111301 u Q) (@lem4846008 _111301 u Q)). Qed.
Lemma lem4846010 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term24 _111301 u Q) = (term52 _111301 u Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4845999 _111301 u Q c)). Qed.
Lemma lem4846011 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4846012 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term25 _111301 u Q) = (term53 _111301 u Q).
Proof. exact (MK_COMB (@lem4846011 _111301) (@lem4846010 _111301 u Q)). Qed.
Lemma lem4846013 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) : (term54 _111301 u s) = (term54 _111301 u s).
Proof. exact (eq_refl (term54 _111301 u s)). Qed.
Lemma lem4846014 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) : ((@UNIONS _111301 u) = s) = ((@UNIONS _111301 u) = s).
Proof. exact (eq_refl ((@UNIONS _111301 u) = s)). Qed.
Lemma lem4846015 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846016 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term55 _111301 u Q) = (term56 _111301 u Q).
Proof. exact (MK_COMB (@lem4846015) (@lem4846009 _111301 u Q)). Qed.
Lemma lem4846017 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term57 _111301 Q u s) = (term58 _111301 Q u s).
Proof. exact (MK_COMB (@lem4846016 _111301 u Q) (@lem4846013 _111301 u s)). Qed.
Lemma lem4846018 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term59 _111301 Q u s) = (term57 _111301 Q u s).
Proof. exact (@lem17045 (term25 _111301 u Q) ((@UNIONS _111301 u) = s)). Qed.
Lemma lem4846019 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term59 _111301 Q u s) = (term58 _111301 Q u s).
Proof. exact (TRANS (@lem4846018 _111301 Q u s) (@lem4846017 _111301 Q u s)). Qed.
Lemma lem4846020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846021 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term31 _111301 u Q) = (term60 _111301 u Q).
Proof. exact (MK_COMB (@lem4846020) (@lem4846012 _111301 u Q)). Qed.
Lemma lem4846022 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term32 _111301 Q u s) = (term61 _111301 Q u s).
Proof. exact (MK_COMB (@lem4846021 _111301 u Q) (@lem4846014 _111301 u s)). Qed.
Lemma lem4846024 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term62 _111301 P u) = (term62 _111301 P u).
Proof. exact (eq_refl (term62 _111301 P u)). Qed.
Lemma lem4846025 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term63 _111301 P Q u s) = (term64 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846024 _111301 P u) (@lem4846019 _111301 Q u s)). Qed.
Lemma lem4846026 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term65 _111301 P Q u s) = (term63 _111301 P Q u s).
Proof. exact (@lem17045 (P u) (term32 _111301 Q u s)). Qed.
Lemma lem4846027 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term65 _111301 P Q u s) = (term64 _111301 P Q u s).
Proof. exact (TRANS (@lem4846026 _111301 P Q u s) (@lem4846025 _111301 P Q u s)). Qed.
Lemma lem4846029 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term26 _111301 P u) = (term26 _111301 P u).
Proof. exact (eq_refl (term26 _111301 P u)). Qed.
Lemma lem4846030 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term33 _111301 P Q u s) = (term66 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846029 _111301 P u) (@lem4846022 _111301 Q u s)). Qed.
Lemma lem4846031 {_111301 : Type'} (P : type180 _111301) : (term67 _111301 P) = (term68 _111301 P).
Proof. exact (@lem18394 (type686 _111301) P). Qed.
Lemma lem4846032 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term69 _111301 P Q s) = (term70 _111301 P Q s).
Proof. exact (@lem4846031 _111301 (term34 _111301 P Q s)). Qed.
Lemma lem4846033 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term71 _111301 P Q s u) = (term33 _111301 P Q u s).
Proof. exact (eq_refl (term71 _111301 P Q s u)). Qed.
Lemma lem4846034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4846035 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term72 _111301 P Q s u) = (term65 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846034) (@lem4846033 _111301 P Q u s)). Qed.
Lemma lem4846036 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term72 _111301 P Q s u) = (term64 _111301 P Q u s).
Proof. exact (TRANS (@lem4846035 _111301 P Q u s) (@lem4846027 _111301 P Q u s)). Qed.
Lemma lem4846037 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term73 _111301 P Q s) = (term74 _111301 P Q s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846036 _111301 P Q u s)). Qed.
Lemma lem4846038 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846039 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term70 _111301 P Q s) = (term75 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846038 _111301) (@lem4846037 _111301 P Q s)). Qed.
Lemma lem4846040 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term69 _111301 P Q s) = (term75 _111301 P Q s).
Proof. exact (TRANS (@lem4846032 _111301 P Q s) (@lem4846039 _111301 P Q s)). Qed.
Lemma lem4846041 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term34 _111301 P Q s) = (term76 _111301 P Q s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846030 _111301 P Q u s)). Qed.
Lemma lem4846042 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846043 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term35 _111301 P Q s) = (term77 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846042 _111301) (@lem4846041 _111301 P Q s)). Qed.
Lemma lem4846044 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (term78 _111301 R s) = (term78 _111301 R s).
Proof. exact (eq_refl (term78 _111301 R s)). Qed.
Lemma lem4846045 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4846046 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846047 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term79 _111301 P Q s) = (term80 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846046) (@lem4846043 _111301 P Q s)). Qed.
Lemma lem4846048 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term81 _111301 P Q R s) = (term82 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846047 _111301 P Q s) (@lem4846044 _111301 R s)). Qed.
Lemma lem4846049 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term83 _111301 P Q R s) = (term81 _111301 P Q R s).
Proof. exact (@lem17362 (term35 _111301 P Q s) (R s)). Qed.
Lemma lem4846050 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term83 _111301 P Q R s) = (term82 _111301 P Q R s).
Proof. exact (TRANS (@lem4846049 _111301 P Q R s) (@lem4846048 _111301 P Q R s)). Qed.
Lemma lem4846051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846052 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term84 _111301 P Q s) = (term85 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846051) (@lem4846040 _111301 P Q s)). Qed.
Lemma lem4846053 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term86 _111301 P Q R s) = (term87 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846052 _111301 P Q s) (@lem4846045 _111301 R s)). Qed.
Lemma lem4846054 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term37 _111301 P Q R s) = (term86 _111301 P Q R s).
Proof. exact (@lem17265 (term35 _111301 P Q s) (R s)). Qed.
Lemma lem4846055 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term37 _111301 P Q R s) = (term87 _111301 P Q R s).
Proof. exact (TRANS (@lem4846054 _111301 P Q R s) (@lem4846053 _111301 P Q R s)). Qed.
Lemma lem4846056 {_111301 : Type'} (P : type686 _111301) : (term43 _111301 P) = (term44 _111301 P).
Proof. exact (@lem18392 (_111301 -> Prop) P). Qed.
Lemma lem4846057 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term88 _111301 P Q R) = (term89 _111301 P Q R).
Proof. exact (@lem4846056 _111301 (term38 _111301 P Q R)). Qed.
Lemma lem4846058 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term90 _111301 P Q R s) = (term37 _111301 P Q R s).
Proof. exact (eq_refl (term90 _111301 P Q R s)). Qed.
Lemma lem4846059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4846060 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term91 _111301 P Q R s) = (term83 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846059) (@lem4846058 _111301 P Q R s)). Qed.
Lemma lem4846061 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term91 _111301 P Q R s) = (term82 _111301 P Q R s).
Proof. exact (TRANS (@lem4846060 _111301 P Q R s) (@lem4846050 _111301 P Q R s)). Qed.
Lemma lem4846062 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term92 _111301 P Q R) = (term93 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846061 _111301 P Q R s)). Qed.
Lemma lem4846063 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846064 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term89 _111301 P Q R) = (term94 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846063 _111301) (@lem4846062 _111301 P Q R)). Qed.
Lemma lem4846065 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term88 _111301 P Q R) = (term94 _111301 P Q R).
Proof. exact (TRANS (@lem4846057 _111301 P Q R) (@lem4846064 _111301 P Q R)). Qed.
Lemma lem4846066 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term38 _111301 P Q R) = (term95 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846055 _111301 P Q R s)). Qed.
Lemma lem4846067 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4846068 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term1 _111301 P Q R) = (term96 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846067 _111301) (@lem4846066 _111301 P Q R)). Qed.
Lemma lem4846079 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term40 _111301 t Q c) = (term41 _111301 t Q c).
Proof. exact (@lem17362 (@IN (_111301 -> Prop) c t) (Q c)). Qed.
Lemma lem4846084 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term23 _111301 t Q c) = (term42 _111301 t Q c).
Proof. exact (@lem17265 (@IN (_111301 -> Prop) c t) (Q c)). Qed.
Lemma lem4846085 {_111301 : Type'} (P : type686 _111301) : (term43 _111301 P) = (term44 _111301 P).
Proof. exact (@lem18392 (_111301 -> Prop) P). Qed.
Lemma lem4846086 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term45 _111301 t Q) = (term46 _111301 t Q).
Proof. exact (@lem4846085 _111301 (term24 _111301 t Q)). Qed.
Lemma lem4846087 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term47 _111301 t Q c) = (term23 _111301 t Q c).
Proof. exact (eq_refl (term47 _111301 t Q c)). Qed.
Lemma lem4846088 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4846089 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term48 _111301 t Q c) = (term40 _111301 t Q c).
Proof. exact (MK_COMB (@lem4846088) (@lem4846087 _111301 t Q c)). Qed.
Lemma lem4846090 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term48 _111301 t Q c) = (term41 _111301 t Q c).
Proof. exact (TRANS (@lem4846089 _111301 t Q c) (@lem4846079 _111301 t Q c)). Qed.
Lemma lem4846091 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term49 _111301 t Q) = (term50 _111301 t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846090 _111301 t Q c)). Qed.
Lemma lem4846092 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846093 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term46 _111301 t Q) = (term51 _111301 t Q).
Proof. exact (MK_COMB (@lem4846092 _111301) (@lem4846091 _111301 t Q)). Qed.
Lemma lem4846094 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term45 _111301 t Q) = (term51 _111301 t Q).
Proof. exact (TRANS (@lem4846086 _111301 t Q) (@lem4846093 _111301 t Q)). Qed.
Lemma lem4846095 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term24 _111301 t Q) = (term52 _111301 t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846084 _111301 t Q c)). Qed.
Lemma lem4846096 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4846097 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term25 _111301 t Q) = (term53 _111301 t Q).
Proof. exact (MK_COMB (@lem4846096 _111301) (@lem4846095 _111301 t Q)). Qed.
Lemma lem4846099 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term62 _111301 P t) = (term62 _111301 P t).
Proof. exact (eq_refl (term62 _111301 P t)). Qed.
Lemma lem4846100 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term97 _111301 P t Q) = (term98 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846099 _111301 P t) (@lem4846094 _111301 t Q)). Qed.
Lemma lem4846101 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term99 _111301 P t Q) = (term97 _111301 P t Q).
Proof. exact (@lem17045 (P t) (term25 _111301 t Q)). Qed.
Lemma lem4846102 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term99 _111301 P t Q) = (term98 _111301 P t Q).
Proof. exact (TRANS (@lem4846101 _111301 P t Q) (@lem4846100 _111301 P t Q)). Qed.
Lemma lem4846104 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term26 _111301 P t) = (term26 _111301 P t).
Proof. exact (eq_refl (term26 _111301 P t)). Qed.
Lemma lem4846105 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term27 _111301 P t Q) = (term100 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846104 _111301 P t) (@lem4846097 _111301 t Q)). Qed.
Lemma lem4846106 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term101 _111301 R t) = (term101 _111301 R t).
Proof. exact (eq_refl (term101 _111301 R t)). Qed.
Lemma lem4846107 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term22 _111301 R t) = (term22 _111301 R t).
Proof. exact (eq_refl (term22 _111301 R t)). Qed.
Lemma lem4846108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846109 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term102 _111301 P t Q) = (term103 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846108) (@lem4846105 _111301 P t Q)). Qed.
Lemma lem4846110 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term104 _111301 P Q R t) = (term105 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846109 _111301 P t Q) (@lem4846106 _111301 R t)). Qed.
Lemma lem4846111 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term106 _111301 P Q R t) = (term104 _111301 P Q R t).
Proof. exact (@lem17362 (term27 _111301 P t Q) (term22 _111301 R t)). Qed.
Lemma lem4846112 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term106 _111301 P Q R t) = (term105 _111301 P Q R t).
Proof. exact (TRANS (@lem4846111 _111301 P Q R t) (@lem4846110 _111301 P Q R t)). Qed.
Lemma lem4846113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846114 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term107 _111301 P t Q) = (term108 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846113) (@lem4846102 _111301 P t Q)). Qed.
Lemma lem4846115 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term109 _111301 P Q R t) = (term110 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846114 _111301 P t Q) (@lem4846107 _111301 R t)). Qed.
Lemma lem4846116 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term29 _111301 P Q R t) = (term109 _111301 P Q R t).
Proof. exact (@lem17265 (term27 _111301 P t Q) (term22 _111301 R t)). Qed.
Lemma lem4846117 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term29 _111301 P Q R t) = (term110 _111301 P Q R t).
Proof. exact (TRANS (@lem4846116 _111301 P Q R t) (@lem4846115 _111301 P Q R t)). Qed.
Lemma lem4846118 {_111301 : Type'} (P : type180 _111301) : (term111 _111301 P) = (term112 _111301 P).
Proof. exact (@lem18392 (type686 _111301) P). Qed.
Lemma lem4846119 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term113 _111301 P Q R) = (term114 _111301 P Q R).
Proof. exact (@lem4846118 _111301 (term30 _111301 P Q R)). Qed.
Lemma lem4846120 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term115 _111301 P Q R t) = (term29 _111301 P Q R t).
Proof. exact (eq_refl (term115 _111301 P Q R t)). Qed.
Lemma lem4846121 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4846122 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term116 _111301 P Q R t) = (term106 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846121) (@lem4846120 _111301 P Q R t)). Qed.
Lemma lem4846123 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term116 _111301 P Q R t) = (term105 _111301 P Q R t).
Proof. exact (TRANS (@lem4846122 _111301 P Q R t) (@lem4846112 _111301 P Q R t)). Qed.
Lemma lem4846124 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term117 _111301 P Q R) = (term118 _111301 P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846123 _111301 P Q R t)). Qed.
Lemma lem4846125 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846126 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term114 _111301 P Q R) = (term119 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846125 _111301) (@lem4846124 _111301 P Q R)). Qed.
Lemma lem4846127 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term113 _111301 P Q R) = (term119 _111301 P Q R).
Proof. exact (TRANS (@lem4846119 _111301 P Q R) (@lem4846126 _111301 P Q R)). Qed.
Lemma lem4846128 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term30 _111301 P Q R) = (term120 _111301 P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846117 _111301 P Q R t)). Qed.
Lemma lem4846129 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846130 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term2 _111301 P Q R) = (term121 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846129 _111301) (@lem4846128 _111301 P Q R)). Qed.
Lemma lem4846131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846132 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term122 _111301 P Q R) = (term123 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846131) (@lem4846065 _111301 P Q R)). Qed.
Lemma lem4846133 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term124 _111301 P Q R) = (term125 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846132 _111301 P Q R) (@lem4846130 _111301 P Q R)). Qed.
Lemma lem4846134 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846135 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term126 _111301 P Q R) = (term127 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846134) (@lem4846068 _111301 P Q R)). Qed.
Lemma lem4846136 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term128 _111301 P Q R) = (term129 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846135 _111301 P Q R) (@lem4846127 _111301 P Q R)). Qed.
Lemma lem4846137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846138 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term130 _111301 P Q R) = (term131 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846137) (@lem4846136 _111301 P Q R)). Qed.
Lemma lem4846139 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term132 _111301 P Q R) = (term133 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846138 _111301 P Q R) (@lem4846133 _111301 P Q R)). Qed.
Lemma lem4846140 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term4 _111301 P Q R) = (term132 _111301 P Q R).
Proof. exact (@lem17646 (term1 _111301 P Q R) (term2 _111301 P Q R)). Qed.
Lemma lem4846141 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term4 _111301 P Q R) = (term133 _111301 P Q R).
Proof. exact (TRANS (@lem4846140 _111301 P Q R) (@lem4846139 _111301 P Q R)). Qed.
Lemma lem4846556 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4846557 {_111301 : Type'} (P : type686 _111301) (Q : Prop) : (term136 _111301 P Q) = (term137 _111301 P Q).
Proof. exact (@lem4846556 (_111301 -> Prop) P Q). Qed.
Lemma lem4846558 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term138 _111301 Q u s) = (term139 _111301 Q u s).
Proof. exact (@lem4846557 _111301 (term50 _111301 u Q) (term54 _111301 u s)). Qed.
Lemma lem4846559 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term140 _111301 u Q c) = (term41 _111301 u Q c).
Proof. exact (eq_refl (term140 _111301 u Q c)). Qed.
Lemma lem4846560 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term141 _111301 u Q) = (term50 _111301 u Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846559 _111301 u Q c)). Qed.
Lemma lem4846561 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846562 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term142 _111301 u Q) = (term51 _111301 u Q).
Proof. exact (MK_COMB (@lem4846561 _111301) (@lem4846560 _111301 u Q)). Qed.
Lemma lem4846563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846564 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term143 _111301 u Q) = (term56 _111301 u Q).
Proof. exact (MK_COMB (@lem4846563) (@lem4846562 _111301 u Q)). Qed.
Lemma lem4846565 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) : (term54 _111301 u s) = (term54 _111301 u s).
Proof. exact (eq_refl (term54 _111301 u s)). Qed.
Lemma lem4846566 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term138 _111301 Q u s) = (term58 _111301 Q u s).
Proof. exact (MK_COMB (@lem4846564 _111301 u Q) (@lem4846565 _111301 u s)). Qed.
Lemma lem4846567 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846568 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term144 _111301 Q u s) = (term145 _111301 Q u s).
Proof. exact (MK_COMB (@lem4846567) (@lem4846566 _111301 Q u s)). Qed.
Lemma lem4846569 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term140 _111301 u Q c) = (term41 _111301 u Q c).
Proof. exact (eq_refl (term140 _111301 u Q c)). Qed.
Lemma lem4846570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846571 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term146 _111301 u Q c) = (term147 _111301 u Q c).
Proof. exact (MK_COMB (@lem4846570) (@lem4846569 _111301 u Q c)). Qed.
Lemma lem4846572 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) : (term54 _111301 u s) = (term54 _111301 u s).
Proof. exact (eq_refl (term54 _111301 u s)). Qed.
Lemma lem4846573 {_111301 : Type'} (Q : type686 _111301) (c : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) : (term148 _111301 Q c u s) = (term149 _111301 Q c u s).
Proof. exact (MK_COMB (@lem4846571 _111301 u Q c) (@lem4846572 _111301 u s)). Qed.
Lemma lem4846574 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term150 _111301 Q u s) = (term151 _111301 Q u s).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846573 _111301 Q c u s)). Qed.
Lemma lem4846575 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846576 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term139 _111301 Q u s) = (term152 _111301 Q u s).
Proof. exact (MK_COMB (@lem4846575 _111301) (@lem4846574 _111301 Q u s)). Qed.
Lemma lem4846577 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : ((term138 _111301 Q u s) = (term139 _111301 Q u s)) = ((term58 _111301 Q u s) = (term152 _111301 Q u s)).
Proof. exact (MK_COMB (@lem4846568 _111301 Q u s) (@lem4846576 _111301 Q u s)). Qed.
Lemma lem4846578 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term58 _111301 Q u s) = (term152 _111301 Q u s).
Proof. exact (EQ_MP (@lem4846577 _111301 Q u s) (@lem4846558 _111301 Q u s)). Qed.
Lemma lem4846579 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term62 _111301 P u) = (term62 _111301 P u).
Proof. exact (eq_refl (term62 _111301 P u)). Qed.
Lemma lem4846580 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term64 _111301 P Q u s) = (term153 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846579 _111301 P u) (@lem4846578 _111301 Q u s)). Qed.
Lemma lem4846582 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4846583 {_111301 : Type'} (P : Prop) (Q : type686 _111301) : (term156 _111301 P Q) = (term157 _111301 P Q).
Proof. exact (@lem4846582 (_111301 -> Prop) P Q). Qed.
Lemma lem4846584 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term158 _111301 P Q u s) = (term159 _111301 P Q u s).
Proof. exact (@lem4846583 _111301 (term160 _111301 P u) (term151 _111301 Q u s)). Qed.
Lemma lem4846585 {_111301 : Type'} (Q : type686 _111301) (c : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) : (term161 _111301 Q u s c) = (term149 _111301 Q c u s).
Proof. exact (eq_refl (term161 _111301 Q u s c)). Qed.
Lemma lem4846586 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term162 _111301 Q u s) = (term151 _111301 Q u s).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846585 _111301 Q c u s)). Qed.
Lemma lem4846587 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846588 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term163 _111301 Q u s) = (term152 _111301 Q u s).
Proof. exact (MK_COMB (@lem4846587 _111301) (@lem4846586 _111301 Q u s)). Qed.
Lemma lem4846589 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term62 _111301 P u) = (term62 _111301 P u).
Proof. exact (eq_refl (term62 _111301 P u)). Qed.
Lemma lem4846590 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term158 _111301 P Q u s) = (term153 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846589 _111301 P u) (@lem4846588 _111301 Q u s)). Qed.
Lemma lem4846591 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846592 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term164 _111301 P Q u s) = (term165 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846591) (@lem4846590 _111301 P Q u s)). Qed.
Lemma lem4846593 {_111301 : Type'} (Q : type686 _111301) (c : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) : (term161 _111301 Q u s c) = (term149 _111301 Q c u s).
Proof. exact (eq_refl (term161 _111301 Q u s c)). Qed.
Lemma lem4846594 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term62 _111301 P u) = (term62 _111301 P u).
Proof. exact (eq_refl (term62 _111301 P u)). Qed.
Lemma lem4846595 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) : (term166 _111301 P Q u s c) = (term167 _111301 P Q c u s).
Proof. exact (MK_COMB (@lem4846594 _111301 P u) (@lem4846593 _111301 Q c u s)). Qed.
Lemma lem4846596 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term168 _111301 P Q u s) = (term169 _111301 P Q u s).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846595 _111301 P Q c u s)). Qed.
Lemma lem4846597 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846598 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term159 _111301 P Q u s) = (term170 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846597 _111301) (@lem4846596 _111301 P Q u s)). Qed.
Lemma lem4846599 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : ((term158 _111301 P Q u s) = (term159 _111301 P Q u s)) = ((term153 _111301 P Q u s) = (term170 _111301 P Q u s)).
Proof. exact (MK_COMB (@lem4846592 _111301 P Q u s) (@lem4846598 _111301 P Q u s)). Qed.
Lemma lem4846600 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term153 _111301 P Q u s) = (term170 _111301 P Q u s).
Proof. exact (EQ_MP (@lem4846599 _111301 P Q u s) (@lem4846584 _111301 P Q u s)). Qed.
Lemma lem4846601 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term64 _111301 P Q u s) = (term170 _111301 P Q u s).
Proof. exact (TRANS (@lem4846580 _111301 P Q u s) (@lem4846600 _111301 P Q u s)). Qed.
Lemma lem4846602 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term74 _111301 P Q s) = (term171 _111301 P Q s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846601 _111301 P Q u s)). Qed.
Lemma lem4846603 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846604 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term75 _111301 P Q s) = (term172 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846603 _111301) (@lem4846602 _111301 P Q s)). Qed.
Lemma lem4846606 {A B : Type'} (P : type1413 A B) : (term173 A B P) = (term174 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4846607 {_111301 : Type'} (P : type174 _111301) : (term175 _111301 P) = (term176 _111301 P).
Proof. exact (@lem4846606 (type686 _111301) (_111301 -> Prop) P). Qed.
Lemma lem4846608 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term177 _111301 P Q s) = (term178 _111301 P Q s).
Proof. exact (@lem4846607 _111301 (term179 _111301 P Q s)). Qed.
Lemma lem4846609 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term180 _111301 P Q s u) = (term169 _111301 P Q u s).
Proof. exact (eq_refl (term180 _111301 P Q s u)). Qed.
Lemma lem4846610 {_111301 : Type'} (c : _111301 -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4846611 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (c : _111301 -> Prop) : (term181 _111301 P Q s u c) = (term182 _111301 P Q u s c).
Proof. exact (MK_COMB (@lem4846609 _111301 P Q u s) (@lem4846610 _111301 c)). Qed.
Lemma lem4846612 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) : (term182 _111301 P Q u s c) = (term167 _111301 P Q c u s).
Proof. exact (eq_refl (term182 _111301 P Q u s c)). Qed.
Lemma lem4846613 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) : (term181 _111301 P Q s u c) = (term167 _111301 P Q c u s).
Proof. exact (TRANS (@lem4846611 _111301 P Q u s c) (@lem4846612 _111301 P Q c u s)). Qed.
Lemma lem4846614 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term183 _111301 P Q s u) = (term169 _111301 P Q u s).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846613 _111301 P Q c u s)). Qed.
Lemma lem4846615 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846616 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term184 _111301 P Q s u) = (term170 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846615 _111301) (@lem4846614 _111301 P Q u s)). Qed.
Lemma lem4846617 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term185 _111301 P Q s) = (term171 _111301 P Q s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846616 _111301 P Q u s)). Qed.
Lemma lem4846618 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846619 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term177 _111301 P Q s) = (term172 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846618 _111301) (@lem4846617 _111301 P Q s)). Qed.
Lemma lem4846620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846621 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term186 _111301 P Q s) = (term187 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846620) (@lem4846619 _111301 P Q s)). Qed.
Lemma lem4846622 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term180 _111301 P Q s u) = (term169 _111301 P Q u s).
Proof. exact (eq_refl (term180 _111301 P Q s u)). Qed.
Lemma lem4846623 {_111301 : Type'} (c : type178 _111301) (u : type686 _111301) : (c u) = (c u).
Proof. exact (eq_refl (c u)). Qed.
Lemma lem4846624 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) (c : type178 _111301) (u : type686 _111301) : (term188 _111301 P Q s c u) = (term189 _111301 P Q s c u).
Proof. exact (MK_COMB (@lem4846622 _111301 P Q u s) (@lem4846623 _111301 c u)). Qed.
Lemma lem4846625 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term189 _111301 P Q s c u) = (term190 _111301 P Q c u s).
Proof. exact (eq_refl (term189 _111301 P Q s c u)). Qed.
Lemma lem4846626 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term188 _111301 P Q s c u) = (term190 _111301 P Q c u s).
Proof. exact (TRANS (@lem4846624 _111301 P Q s c u) (@lem4846625 _111301 P Q c u s)). Qed.
Lemma lem4846627 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (s : _111301 -> Prop) : (term191 _111301 P Q s c) = (term192 _111301 P Q c s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846626 _111301 P Q c u s)). Qed.
Lemma lem4846628 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846629 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (s : _111301 -> Prop) : (term193 _111301 P Q s c) = (term194 _111301 P Q c s).
Proof. exact (MK_COMB (@lem4846628 _111301) (@lem4846627 _111301 P Q c s)). Qed.
Lemma lem4846630 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term195 _111301 P Q s) = (term196 _111301 P Q s).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4846629 _111301 P Q c s)). Qed.
Lemma lem4846631 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846632 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term178 _111301 P Q s) = (term197 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846631 _111301) (@lem4846630 _111301 P Q s)). Qed.
Lemma lem4846633 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : ((term177 _111301 P Q s) = (term178 _111301 P Q s)) = ((term172 _111301 P Q s) = (term197 _111301 P Q s)).
Proof. exact (MK_COMB (@lem4846621 _111301 P Q s) (@lem4846632 _111301 P Q s)). Qed.
Lemma lem4846634 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term172 _111301 P Q s) = (term197 _111301 P Q s).
Proof. exact (EQ_MP (@lem4846633 _111301 P Q s) (@lem4846608 _111301 P Q s)). Qed.
Lemma lem4846635 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term75 _111301 P Q s) = (term197 _111301 P Q s).
Proof. exact (TRANS (@lem4846604 _111301 P Q s) (@lem4846634 _111301 P Q s)). Qed.
Lemma lem4846636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846637 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term85 _111301 P Q s) = (term198 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846636) (@lem4846635 _111301 P Q s)). Qed.
Lemma lem4846638 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4846639 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term87 _111301 P Q R s) = (term199 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846637 _111301 P Q s) (@lem4846638 _111301 R s)). Qed.
Lemma lem4846641 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4846642 {_111301 : Type'} (P : type72 _111301) (Q : Prop) : (term200 _111301 P Q) = (term201 _111301 P Q).
Proof. exact (@lem4846641 (type178 _111301) P Q). Qed.
Lemma lem4846643 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term202 _111301 P Q R s) = (term203 _111301 P Q R s).
Proof. exact (@lem4846642 _111301 (term196 _111301 P Q s) (R s)). Qed.
Lemma lem4846644 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (s : _111301 -> Prop) : (term204 _111301 P Q s c) = (term194 _111301 P Q c s).
Proof. exact (eq_refl (term204 _111301 P Q s c)). Qed.
Lemma lem4846645 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term205 _111301 P Q s) = (term196 _111301 P Q s).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4846644 _111301 P Q c s)). Qed.
Lemma lem4846646 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846647 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term206 _111301 P Q s) = (term197 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846646 _111301) (@lem4846645 _111301 P Q s)). Qed.
Lemma lem4846648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846649 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term207 _111301 P Q s) = (term198 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846648) (@lem4846647 _111301 P Q s)). Qed.
Lemma lem4846650 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4846651 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term202 _111301 P Q R s) = (term199 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846649 _111301 P Q s) (@lem4846650 _111301 R s)). Qed.
Lemma lem4846652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846653 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term208 _111301 P Q R s) = (term209 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846652) (@lem4846651 _111301 P Q R s)). Qed.
Lemma lem4846654 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (s : _111301 -> Prop) : (term204 _111301 P Q s c) = (term194 _111301 P Q c s).
Proof. exact (eq_refl (term204 _111301 P Q s c)). Qed.
Lemma lem4846655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846656 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (s : _111301 -> Prop) : (term210 _111301 P Q s c) = (term211 _111301 P Q c s).
Proof. exact (MK_COMB (@lem4846655) (@lem4846654 _111301 P Q c s)). Qed.
Lemma lem4846657 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4846658 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term212 _111301 P Q c R s) = (term213 _111301 P Q c R s).
Proof. exact (MK_COMB (@lem4846656 _111301 P Q c s) (@lem4846657 _111301 R s)). Qed.
Lemma lem4846659 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term214 _111301 P Q R s) = (term215 _111301 P Q R s).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4846658 _111301 P Q c R s)). Qed.
Lemma lem4846660 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846661 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term203 _111301 P Q R s) = (term216 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846660 _111301) (@lem4846659 _111301 P Q R s)). Qed.
Lemma lem4846662 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : ((term202 _111301 P Q R s) = (term203 _111301 P Q R s)) = ((term199 _111301 P Q R s) = (term216 _111301 P Q R s)).
Proof. exact (MK_COMB (@lem4846653 _111301 P Q R s) (@lem4846661 _111301 P Q R s)). Qed.
Lemma lem4846663 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term199 _111301 P Q R s) = (term216 _111301 P Q R s).
Proof. exact (EQ_MP (@lem4846662 _111301 P Q R s) (@lem4846643 _111301 P Q R s)). Qed.
Lemma lem4846664 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term87 _111301 P Q R s) = (term216 _111301 P Q R s).
Proof. exact (TRANS (@lem4846639 _111301 P Q R s) (@lem4846663 _111301 P Q R s)). Qed.
Lemma lem4846665 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term95 _111301 P Q R) = (term217 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846664 _111301 P Q R s)). Qed.
Lemma lem4846666 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4846667 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term96 _111301 P Q R) = (term218 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846666 _111301) (@lem4846665 _111301 P Q R)). Qed.
Lemma lem4846669 {A B : Type'} (P : type1413 A B) : (term173 A B P) = (term174 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4846670 {_111301 : Type'} (P : type578 _111301) : (term219 _111301 P) = (term220 _111301 P).
Proof. exact (@lem4846669 (_111301 -> Prop) (type178 _111301) P). Qed.
Lemma lem4846671 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term221 _111301 P Q R) = (term222 _111301 P Q R).
Proof. exact (@lem4846670 _111301 (term223 _111301 P Q R)). Qed.
Lemma lem4846672 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term224 _111301 P Q R s) = (term215 _111301 P Q R s).
Proof. exact (eq_refl (term224 _111301 P Q R s)). Qed.
Lemma lem4846673 {_111301 : Type'} (c : type178 _111301) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4846674 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) (c : type178 _111301) : (term225 _111301 P Q R s c) = (term226 _111301 P Q R s c).
Proof. exact (MK_COMB (@lem4846672 _111301 P Q R s) (@lem4846673 _111301 c)). Qed.
Lemma lem4846675 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term226 _111301 P Q R s c) = (term213 _111301 P Q c R s).
Proof. exact (eq_refl (term226 _111301 P Q R s c)). Qed.
Lemma lem4846676 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term225 _111301 P Q R s c) = (term213 _111301 P Q c R s).
Proof. exact (TRANS (@lem4846674 _111301 P Q R s c) (@lem4846675 _111301 P Q c R s)). Qed.
Lemma lem4846677 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term227 _111301 P Q R s) = (term215 _111301 P Q R s).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4846676 _111301 P Q c R s)). Qed.
Lemma lem4846678 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846679 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term228 _111301 P Q R s) = (term216 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846678 _111301) (@lem4846677 _111301 P Q R s)). Qed.
Lemma lem4846680 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term229 _111301 P Q R) = (term217 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846679 _111301 P Q R s)). Qed.
Lemma lem4846681 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4846682 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term221 _111301 P Q R) = (term218 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846681 _111301) (@lem4846680 _111301 P Q R)). Qed.
Lemma lem4846683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846684 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term230 _111301 P Q R) = (term231 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846683) (@lem4846682 _111301 P Q R)). Qed.
Lemma lem4846685 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term224 _111301 P Q R s) = (term215 _111301 P Q R s).
Proof. exact (eq_refl (term224 _111301 P Q R s)). Qed.
Lemma lem4846686 {_111301 : Type'} (c : type598 _111301) (s : _111301 -> Prop) : (c s) = (c s).
Proof. exact (eq_refl (c s)). Qed.
Lemma lem4846687 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (c : type598 _111301) (s : _111301 -> Prop) : (term232 _111301 P Q R c s) = (term233 _111301 P Q R c s).
Proof. exact (MK_COMB (@lem4846685 _111301 P Q R s) (@lem4846686 _111301 c s)). Qed.
Lemma lem4846688 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term233 _111301 P Q R c s) = (term234 _111301 P Q c R s).
Proof. exact (eq_refl (term233 _111301 P Q R c s)). Qed.
Lemma lem4846689 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term232 _111301 P Q R c s) = (term234 _111301 P Q c R s).
Proof. exact (TRANS (@lem4846687 _111301 P Q R c s) (@lem4846688 _111301 P Q c R s)). Qed.
Lemma lem4846690 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term235 _111301 P Q R c) = (term236 _111301 P Q c R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846689 _111301 P Q c R s)). Qed.
Lemma lem4846691 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4846692 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term237 _111301 P Q R c) = (term238 _111301 P Q c R).
Proof. exact (MK_COMB (@lem4846691 _111301) (@lem4846690 _111301 P Q c R)). Qed.
Lemma lem4846693 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term239 _111301 P Q R) = (term240 _111301 P Q R).
Proof. exact (fun_ext (fun c : type598 _111301 => @lem4846692 _111301 P Q c R)). Qed.
Lemma lem4846694 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846695 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term222 _111301 P Q R) = (term241 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846694 _111301) (@lem4846693 _111301 P Q R)). Qed.
Lemma lem4846696 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term221 _111301 P Q R) = (term222 _111301 P Q R)) = ((term218 _111301 P Q R) = (term241 _111301 P Q R)).
Proof. exact (MK_COMB (@lem4846684 _111301 P Q R) (@lem4846695 _111301 P Q R)). Qed.
Lemma lem4846697 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term218 _111301 P Q R) = (term241 _111301 P Q R).
Proof. exact (EQ_MP (@lem4846696 _111301 P Q R) (@lem4846671 _111301 P Q R)). Qed.
Lemma lem4846698 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term96 _111301 P Q R) = (term241 _111301 P Q R).
Proof. exact (TRANS (@lem4846667 _111301 P Q R) (@lem4846697 _111301 P Q R)). Qed.
Lemma lem4846699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846700 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term127 _111301 P Q R) = (term242 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846699) (@lem4846698 _111301 P Q R)). Qed.
Lemma lem4846701 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term119 _111301 P Q R) = (term119 _111301 P Q R).
Proof. exact (eq_refl (term119 _111301 P Q R)). Qed.
Lemma lem4846702 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term129 _111301 P Q R) = (term243 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846700 _111301 P Q R) (@lem4846701 _111301 P Q R)). Qed.
Lemma lem4846704 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4846705 {_111301 : Type'} (P : type123 _111301) (Q : Prop) : (term246 _111301 P Q) = (term247 _111301 P Q).
Proof. exact (@lem4846704 (type598 _111301) P Q). Qed.
Lemma lem4846706 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term248 _111301 P Q R) = (term249 _111301 P Q R).
Proof. exact (@lem4846705 _111301 (term240 _111301 P Q R) (term119 _111301 P Q R)). Qed.
Lemma lem4846707 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term250 _111301 P Q R c) = (term238 _111301 P Q c R).
Proof. exact (eq_refl (term250 _111301 P Q R c)). Qed.
Lemma lem4846708 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term251 _111301 P Q R) = (term240 _111301 P Q R).
Proof. exact (fun_ext (fun c : type598 _111301 => @lem4846707 _111301 P Q c R)). Qed.
Lemma lem4846709 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846710 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term252 _111301 P Q R) = (term241 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846709 _111301) (@lem4846708 _111301 P Q R)). Qed.
Lemma lem4846711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846712 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term253 _111301 P Q R) = (term242 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846711) (@lem4846710 _111301 P Q R)). Qed.
Lemma lem4846713 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term119 _111301 P Q R) = (term119 _111301 P Q R).
Proof. exact (eq_refl (term119 _111301 P Q R)). Qed.
Lemma lem4846714 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term248 _111301 P Q R) = (term243 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846712 _111301 P Q R) (@lem4846713 _111301 P Q R)). Qed.
Lemma lem4846715 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846716 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term254 _111301 P Q R) = (term255 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846715) (@lem4846714 _111301 P Q R)). Qed.
Lemma lem4846717 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term250 _111301 P Q R c) = (term238 _111301 P Q c R).
Proof. exact (eq_refl (term250 _111301 P Q R c)). Qed.
Lemma lem4846718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846719 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term256 _111301 P Q R c) = (term257 _111301 P Q c R).
Proof. exact (MK_COMB (@lem4846718) (@lem4846717 _111301 P Q c R)). Qed.
Lemma lem4846720 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term119 _111301 P Q R) = (term119 _111301 P Q R).
Proof. exact (eq_refl (term119 _111301 P Q R)). Qed.
Lemma lem4846721 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term258 _111301 c P Q R) = (term259 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846719 _111301 P Q c R) (@lem4846720 _111301 P Q R)). Qed.
Lemma lem4846722 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term260 _111301 P Q R) = (term261 _111301 P Q R).
Proof. exact (fun_ext (fun c : type598 _111301 => @lem4846721 _111301 c P Q R)). Qed.
Lemma lem4846723 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846724 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term249 _111301 P Q R) = (term262 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846723 _111301) (@lem4846722 _111301 P Q R)). Qed.
Lemma lem4846725 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term248 _111301 P Q R) = (term249 _111301 P Q R)) = ((term243 _111301 P Q R) = (term262 _111301 P Q R)).
Proof. exact (MK_COMB (@lem4846716 _111301 P Q R) (@lem4846724 _111301 P Q R)). Qed.
Lemma lem4846726 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term243 _111301 P Q R) = (term262 _111301 P Q R).
Proof. exact (EQ_MP (@lem4846725 _111301 P Q R) (@lem4846706 _111301 P Q R)). Qed.
Lemma lem4846728 {A : Type'} (P : Prop) (Q : A -> Prop) : (term263 A P Q) = (term264 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4846729 {_111301 : Type'} (P : Prop) (Q : type180 _111301) : (term265 _111301 P Q) = (term266 _111301 P Q).
Proof. exact (@lem4846728 (type686 _111301) P Q). Qed.
Lemma lem4846730 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term267 _111301 c P Q R) = (term268 _111301 c P Q R).
Proof. exact (@lem4846729 _111301 (term238 _111301 P Q c R) (term118 _111301 P Q R)). Qed.
Lemma lem4846731 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term269 _111301 P Q R t) = (term105 _111301 P Q R t).
Proof. exact (eq_refl (term269 _111301 P Q R t)). Qed.
Lemma lem4846732 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term270 _111301 P Q R) = (term118 _111301 P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846731 _111301 P Q R t)). Qed.
Lemma lem4846733 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846734 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term271 _111301 P Q R) = (term119 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846733 _111301) (@lem4846732 _111301 P Q R)). Qed.
Lemma lem4846735 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term257 _111301 P Q c R) = (term257 _111301 P Q c R).
Proof. exact (eq_refl (term257 _111301 P Q c R)). Qed.
Lemma lem4846736 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term267 _111301 c P Q R) = (term259 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846735 _111301 P Q c R) (@lem4846734 _111301 P Q R)). Qed.
Lemma lem4846737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846738 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term272 _111301 c P Q R) = (term273 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846737) (@lem4846736 _111301 c P Q R)). Qed.
Lemma lem4846739 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term269 _111301 P Q R t) = (term105 _111301 P Q R t).
Proof. exact (eq_refl (term269 _111301 P Q R t)). Qed.
Lemma lem4846740 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term257 _111301 P Q c R) = (term257 _111301 P Q c R).
Proof. exact (eq_refl (term257 _111301 P Q c R)). Qed.
Lemma lem4846741 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term274 _111301 c P Q R t) = (term275 _111301 c P Q R t).
Proof. exact (MK_COMB (@lem4846740 _111301 P Q c R) (@lem4846739 _111301 P Q R t)). Qed.
Lemma lem4846742 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term276 _111301 c P Q R) = (term277 _111301 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846741 _111301 c P Q R t)). Qed.
Lemma lem4846743 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846744 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term268 _111301 c P Q R) = (term278 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846743 _111301) (@lem4846742 _111301 c P Q R)). Qed.
Lemma lem4846745 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term267 _111301 c P Q R) = (term268 _111301 c P Q R)) = ((term259 _111301 c P Q R) = (term278 _111301 c P Q R)).
Proof. exact (MK_COMB (@lem4846738 _111301 c P Q R) (@lem4846744 _111301 c P Q R)). Qed.
Lemma lem4846746 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term259 _111301 c P Q R) = (term278 _111301 c P Q R).
Proof. exact (EQ_MP (@lem4846745 _111301 c P Q R) (@lem4846730 _111301 c P Q R)). Qed.
Lemma lem4846747 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term261 _111301 P Q R) = (term279 _111301 P Q R).
Proof. exact (fun_ext (fun c : type598 _111301 => @lem4846746 _111301 c P Q R)). Qed.
Lemma lem4846748 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846749 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term262 _111301 P Q R) = (term280 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846748 _111301) (@lem4846747 _111301 P Q R)). Qed.
Lemma lem4846750 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term243 _111301 P Q R) = (term280 _111301 P Q R).
Proof. exact (TRANS (@lem4846726 _111301 P Q R) (@lem4846749 _111301 P Q R)). Qed.
Lemma lem4846751 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term129 _111301 P Q R) = (term280 _111301 P Q R).
Proof. exact (TRANS (@lem4846702 _111301 P Q R) (@lem4846750 _111301 P Q R)). Qed.
Lemma lem4846752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846753 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term131 _111301 P Q R) = (term281 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846752) (@lem4846751 _111301 P Q R)). Qed.
Lemma lem4846755 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4846756 {_111301 : Type'} (P : type180 _111301) (Q : Prop) : (term282 _111301 P Q) = (term283 _111301 P Q).
Proof. exact (@lem4846755 (type686 _111301) P Q). Qed.
Lemma lem4846757 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term284 _111301 P Q R s) = (term285 _111301 P Q R s).
Proof. exact (@lem4846756 _111301 (term76 _111301 P Q s) (term78 _111301 R s)). Qed.
Lemma lem4846758 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term286 _111301 P Q s u) = (term66 _111301 P Q u s).
Proof. exact (eq_refl (term286 _111301 P Q s u)). Qed.
Lemma lem4846759 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term287 _111301 P Q s) = (term76 _111301 P Q s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846758 _111301 P Q u s)). Qed.
Lemma lem4846760 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846761 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term288 _111301 P Q s) = (term77 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846760 _111301) (@lem4846759 _111301 P Q s)). Qed.
Lemma lem4846762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846763 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (s : _111301 -> Prop) : (term289 _111301 P Q s) = (term80 _111301 P Q s).
Proof. exact (MK_COMB (@lem4846762) (@lem4846761 _111301 P Q s)). Qed.
Lemma lem4846764 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (term78 _111301 R s) = (term78 _111301 R s).
Proof. exact (eq_refl (term78 _111301 R s)). Qed.
Lemma lem4846765 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term284 _111301 P Q R s) = (term82 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846763 _111301 P Q s) (@lem4846764 _111301 R s)). Qed.
Lemma lem4846766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846767 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term290 _111301 P Q R s) = (term291 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846766) (@lem4846765 _111301 P Q R s)). Qed.
Lemma lem4846768 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term286 _111301 P Q s u) = (term66 _111301 P Q u s).
Proof. exact (eq_refl (term286 _111301 P Q s u)). Qed.
Lemma lem4846769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846770 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term292 _111301 P Q s u) = (term293 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4846769) (@lem4846768 _111301 P Q u s)). Qed.
Lemma lem4846771 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (term78 _111301 R s) = (term78 _111301 R s).
Proof. exact (eq_refl (term78 _111301 R s)). Qed.
Lemma lem4846772 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term294 _111301 P Q u R s) = (term295 _111301 P Q u R s).
Proof. exact (MK_COMB (@lem4846770 _111301 P Q u s) (@lem4846771 _111301 R s)). Qed.
Lemma lem4846773 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term296 _111301 P Q R s) = (term297 _111301 P Q R s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846772 _111301 P Q u R s)). Qed.
Lemma lem4846774 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846775 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term285 _111301 P Q R s) = (term298 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846774 _111301) (@lem4846773 _111301 P Q R s)). Qed.
Lemma lem4846776 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : ((term284 _111301 P Q R s) = (term285 _111301 P Q R s)) = ((term82 _111301 P Q R s) = (term298 _111301 P Q R s)).
Proof. exact (MK_COMB (@lem4846767 _111301 P Q R s) (@lem4846775 _111301 P Q R s)). Qed.
Lemma lem4846777 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term82 _111301 P Q R s) = (term298 _111301 P Q R s).
Proof. exact (EQ_MP (@lem4846776 _111301 P Q R s) (@lem4846757 _111301 P Q R s)). Qed.
Lemma lem4846778 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term93 _111301 P Q R) = (term299 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846777 _111301 P Q R s)). Qed.
Lemma lem4846779 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846780 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term94 _111301 P Q R) = (term300 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846779 _111301) (@lem4846778 _111301 P Q R)). Qed.
Lemma lem4846781 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846782 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term123 _111301 P Q R) = (term301 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846781) (@lem4846780 _111301 P Q R)). Qed.
Lemma lem4846784 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4846785 {_111301 : Type'} (P : Prop) (Q : type686 _111301) : (term156 _111301 P Q) = (term157 _111301 P Q).
Proof. exact (@lem4846784 (_111301 -> Prop) P Q). Qed.
Lemma lem4846786 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term302 _111301 P t Q) = (term303 _111301 P t Q).
Proof. exact (@lem4846785 _111301 (term160 _111301 P t) (term50 _111301 t Q)). Qed.
Lemma lem4846787 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term140 _111301 t Q c) = (term41 _111301 t Q c).
Proof. exact (eq_refl (term140 _111301 t Q c)). Qed.
Lemma lem4846788 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term141 _111301 t Q) = (term50 _111301 t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846787 _111301 t Q c)). Qed.
Lemma lem4846789 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846790 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term142 _111301 t Q) = (term51 _111301 t Q).
Proof. exact (MK_COMB (@lem4846789 _111301) (@lem4846788 _111301 t Q)). Qed.
Lemma lem4846791 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term62 _111301 P t) = (term62 _111301 P t).
Proof. exact (eq_refl (term62 _111301 P t)). Qed.
Lemma lem4846792 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term302 _111301 P t Q) = (term98 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846791 _111301 P t) (@lem4846790 _111301 t Q)). Qed.
Lemma lem4846793 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846794 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term304 _111301 P t Q) = (term305 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846793) (@lem4846792 _111301 P t Q)). Qed.
Lemma lem4846795 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term140 _111301 t Q c) = (term41 _111301 t Q c).
Proof. exact (eq_refl (term140 _111301 t Q c)). Qed.
Lemma lem4846796 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term62 _111301 P t) = (term62 _111301 P t).
Proof. exact (eq_refl (term62 _111301 P t)). Qed.
Lemma lem4846797 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term306 _111301 P t Q c) = (term307 _111301 P t Q c).
Proof. exact (MK_COMB (@lem4846796 _111301 P t) (@lem4846795 _111301 t Q c)). Qed.
Lemma lem4846798 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term308 _111301 P t Q) = (term309 _111301 P t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846797 _111301 P t Q c)). Qed.
Lemma lem4846799 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846800 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term303 _111301 P t Q) = (term310 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846799 _111301) (@lem4846798 _111301 P t Q)). Qed.
Lemma lem4846801 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : ((term302 _111301 P t Q) = (term303 _111301 P t Q)) = ((term98 _111301 P t Q) = (term310 _111301 P t Q)).
Proof. exact (MK_COMB (@lem4846794 _111301 P t Q) (@lem4846800 _111301 P t Q)). Qed.
Lemma lem4846802 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term98 _111301 P t Q) = (term310 _111301 P t Q).
Proof. exact (EQ_MP (@lem4846801 _111301 P t Q) (@lem4846786 _111301 P t Q)). Qed.
Lemma lem4846803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846804 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term108 _111301 P t Q) = (term311 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846803) (@lem4846802 _111301 P t Q)). Qed.
Lemma lem4846805 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term22 _111301 R t) = (term22 _111301 R t).
Proof. exact (eq_refl (term22 _111301 R t)). Qed.
Lemma lem4846806 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term110 _111301 P Q R t) = (term312 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846804 _111301 P t Q) (@lem4846805 _111301 R t)). Qed.
Lemma lem4846808 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4846809 {_111301 : Type'} (P : type686 _111301) (Q : Prop) : (term136 _111301 P Q) = (term137 _111301 P Q).
Proof. exact (@lem4846808 (_111301 -> Prop) P Q). Qed.
Lemma lem4846810 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term313 _111301 P Q R t) = (term314 _111301 P Q R t).
Proof. exact (@lem4846809 _111301 (term309 _111301 P t Q) (term22 _111301 R t)). Qed.
Lemma lem4846811 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term315 _111301 P t Q c) = (term307 _111301 P t Q c).
Proof. exact (eq_refl (term315 _111301 P t Q c)). Qed.
Lemma lem4846812 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term316 _111301 P t Q) = (term309 _111301 P t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846811 _111301 P t Q c)). Qed.
Lemma lem4846813 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846814 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term317 _111301 P t Q) = (term310 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846813 _111301) (@lem4846812 _111301 P t Q)). Qed.
Lemma lem4846815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846816 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term318 _111301 P t Q) = (term311 _111301 P t Q).
Proof. exact (MK_COMB (@lem4846815) (@lem4846814 _111301 P t Q)). Qed.
Lemma lem4846817 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term22 _111301 R t) = (term22 _111301 R t).
Proof. exact (eq_refl (term22 _111301 R t)). Qed.
Lemma lem4846818 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term313 _111301 P Q R t) = (term312 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846816 _111301 P t Q) (@lem4846817 _111301 R t)). Qed.
Lemma lem4846819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846820 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term319 _111301 P Q R t) = (term320 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846819) (@lem4846818 _111301 P Q R t)). Qed.
Lemma lem4846821 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term315 _111301 P t Q c) = (term307 _111301 P t Q c).
Proof. exact (eq_refl (term315 _111301 P t Q c)). Qed.
Lemma lem4846822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846823 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term321 _111301 P t Q c) = (term322 _111301 P t Q c).
Proof. exact (MK_COMB (@lem4846822) (@lem4846821 _111301 P t Q c)). Qed.
Lemma lem4846824 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term22 _111301 R t) = (term22 _111301 R t).
Proof. exact (eq_refl (term22 _111301 R t)). Qed.
Lemma lem4846825 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : _111301 -> Prop) (R : type686 _111301) (t : type686 _111301) : (term323 _111301 P Q c R t) = (term324 _111301 P Q c R t).
Proof. exact (MK_COMB (@lem4846823 _111301 P t Q c) (@lem4846824 _111301 R t)). Qed.
Lemma lem4846826 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term325 _111301 P Q R t) = (term326 _111301 P Q R t).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846825 _111301 P Q c R t)). Qed.
Lemma lem4846827 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846828 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term314 _111301 P Q R t) = (term327 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846827 _111301) (@lem4846826 _111301 P Q R t)). Qed.
Lemma lem4846829 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : ((term313 _111301 P Q R t) = (term314 _111301 P Q R t)) = ((term312 _111301 P Q R t) = (term327 _111301 P Q R t)).
Proof. exact (MK_COMB (@lem4846820 _111301 P Q R t) (@lem4846828 _111301 P Q R t)). Qed.
Lemma lem4846830 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term312 _111301 P Q R t) = (term327 _111301 P Q R t).
Proof. exact (EQ_MP (@lem4846829 _111301 P Q R t) (@lem4846810 _111301 P Q R t)). Qed.
Lemma lem4846831 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term110 _111301 P Q R t) = (term327 _111301 P Q R t).
Proof. exact (TRANS (@lem4846806 _111301 P Q R t) (@lem4846830 _111301 P Q R t)). Qed.
Lemma lem4846832 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term120 _111301 P Q R) = (term328 _111301 P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846831 _111301 P Q R t)). Qed.
Lemma lem4846833 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846834 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term121 _111301 P Q R) = (term329 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846833 _111301) (@lem4846832 _111301 P Q R)). Qed.
Lemma lem4846836 {A B : Type'} (P : type1413 A B) : (term173 A B P) = (term174 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4846837 {_111301 : Type'} (P : type174 _111301) : (term175 _111301 P) = (term176 _111301 P).
Proof. exact (@lem4846836 (type686 _111301) (_111301 -> Prop) P). Qed.
Lemma lem4846838 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term330 _111301 P Q R) = (term331 _111301 P Q R).
Proof. exact (@lem4846837 _111301 (term332 _111301 P Q R)). Qed.
Lemma lem4846839 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term333 _111301 P Q R t) = (term326 _111301 P Q R t).
Proof. exact (eq_refl (term333 _111301 P Q R t)). Qed.
Lemma lem4846840 {_111301 : Type'} (c : _111301 -> Prop) : c = c.
Proof. exact (eq_refl c). Qed.
Lemma lem4846841 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (c : _111301 -> Prop) : (term334 _111301 P Q R t c) = (term335 _111301 P Q R t c).
Proof. exact (MK_COMB (@lem4846839 _111301 P Q R t) (@lem4846840 _111301 c)). Qed.
Lemma lem4846842 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : _111301 -> Prop) (R : type686 _111301) (t : type686 _111301) : (term335 _111301 P Q R t c) = (term324 _111301 P Q c R t).
Proof. exact (eq_refl (term335 _111301 P Q R t c)). Qed.
Lemma lem4846843 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : _111301 -> Prop) (R : type686 _111301) (t : type686 _111301) : (term334 _111301 P Q R t c) = (term324 _111301 P Q c R t).
Proof. exact (TRANS (@lem4846841 _111301 P Q R t c) (@lem4846842 _111301 P Q c R t)). Qed.
Lemma lem4846844 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term336 _111301 P Q R t) = (term326 _111301 P Q R t).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4846843 _111301 P Q c R t)). Qed.
Lemma lem4846845 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846846 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term337 _111301 P Q R t) = (term327 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4846845 _111301) (@lem4846844 _111301 P Q R t)). Qed.
Lemma lem4846847 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term338 _111301 P Q R) = (term328 _111301 P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846846 _111301 P Q R t)). Qed.
Lemma lem4846848 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846849 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term330 _111301 P Q R) = (term329 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846848 _111301) (@lem4846847 _111301 P Q R)). Qed.
Lemma lem4846850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846851 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term339 _111301 P Q R) = (term340 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846850) (@lem4846849 _111301 P Q R)). Qed.
Lemma lem4846852 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term333 _111301 P Q R t) = (term326 _111301 P Q R t).
Proof. exact (eq_refl (term333 _111301 P Q R t)). Qed.
Lemma lem4846853 {_111301 : Type'} (c : type178 _111301) (t : type686 _111301) : (c t) = (c t).
Proof. exact (eq_refl (c t)). Qed.
Lemma lem4846854 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (c : type178 _111301) (t : type686 _111301) : (term341 _111301 P Q R c t) = (term342 _111301 P Q R c t).
Proof. exact (MK_COMB (@lem4846852 _111301 P Q R t) (@lem4846853 _111301 c t)). Qed.
Lemma lem4846855 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) (t : type686 _111301) : (term342 _111301 P Q R c t) = (term343 _111301 P Q c R t).
Proof. exact (eq_refl (term342 _111301 P Q R c t)). Qed.
Lemma lem4846856 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) (t : type686 _111301) : (term341 _111301 P Q R c t) = (term343 _111301 P Q c R t).
Proof. exact (TRANS (@lem4846854 _111301 P Q R c t) (@lem4846855 _111301 P Q c R t)). Qed.
Lemma lem4846857 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) : (term344 _111301 P Q R c) = (term345 _111301 P Q c R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846856 _111301 P Q c R t)). Qed.
Lemma lem4846858 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846859 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) : (term346 _111301 P Q R c) = (term347 _111301 P Q c R).
Proof. exact (MK_COMB (@lem4846858 _111301) (@lem4846857 _111301 P Q c R)). Qed.
Lemma lem4846860 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term348 _111301 P Q R) = (term349 _111301 P Q R).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4846859 _111301 P Q c R)). Qed.
Lemma lem4846861 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846862 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term331 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846861 _111301) (@lem4846860 _111301 P Q R)). Qed.
Lemma lem4846863 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term330 _111301 P Q R) = (term331 _111301 P Q R)) = ((term329 _111301 P Q R) = (term350 _111301 P Q R)).
Proof. exact (MK_COMB (@lem4846851 _111301 P Q R) (@lem4846862 _111301 P Q R)). Qed.
Lemma lem4846864 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term329 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (EQ_MP (@lem4846863 _111301 P Q R) (@lem4846838 _111301 P Q R)). Qed.
Lemma lem4846865 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term121 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (TRANS (@lem4846834 _111301 P Q R) (@lem4846864 _111301 P Q R)). Qed.
Lemma lem4846866 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term125 _111301 P Q R) = (term351 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846782 _111301 P Q R) (@lem4846865 _111301 P Q R)). Qed.
Lemma lem4846868 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4846869 {_111301 : Type'} (P : type686 _111301) (Q : Prop) : (term352 _111301 P Q) = (term353 _111301 P Q).
Proof. exact (@lem4846868 (_111301 -> Prop) P Q). Qed.
Lemma lem4846870 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term354 _111301 P Q R) = (term355 _111301 P Q R).
Proof. exact (@lem4846869 _111301 (term299 _111301 P Q R) (term350 _111301 P Q R)). Qed.
Lemma lem4846871 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term356 _111301 P Q R s) = (term298 _111301 P Q R s).
Proof. exact (eq_refl (term356 _111301 P Q R s)). Qed.
Lemma lem4846872 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term357 _111301 P Q R) = (term299 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846871 _111301 P Q R s)). Qed.
Lemma lem4846873 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846874 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term358 _111301 P Q R) = (term300 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846873 _111301) (@lem4846872 _111301 P Q R)). Qed.
Lemma lem4846875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846876 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term359 _111301 P Q R) = (term301 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846875) (@lem4846874 _111301 P Q R)). Qed.
Lemma lem4846877 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term350 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (eq_refl (term350 _111301 P Q R)). Qed.
Lemma lem4846878 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term354 _111301 P Q R) = (term351 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846876 _111301 P Q R) (@lem4846877 _111301 P Q R)). Qed.
Lemma lem4846879 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846880 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term360 _111301 P Q R) = (term361 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846879) (@lem4846878 _111301 P Q R)). Qed.
Lemma lem4846881 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term356 _111301 P Q R s) = (term298 _111301 P Q R s).
Proof. exact (eq_refl (term356 _111301 P Q R s)). Qed.
Lemma lem4846882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846883 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term362 _111301 P Q R s) = (term363 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846882) (@lem4846881 _111301 P Q R s)). Qed.
Lemma lem4846884 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term350 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (eq_refl (term350 _111301 P Q R)). Qed.
Lemma lem4846885 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term364 _111301 s P Q R) = (term365 _111301 s P Q R).
Proof. exact (MK_COMB (@lem4846883 _111301 P Q R s) (@lem4846884 _111301 P Q R)). Qed.
Lemma lem4846886 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term366 _111301 P Q R) = (term367 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846885 _111301 s P Q R)). Qed.
Lemma lem4846887 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846888 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term355 _111301 P Q R) = (term368 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846887 _111301) (@lem4846886 _111301 P Q R)). Qed.
Lemma lem4846889 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term354 _111301 P Q R) = (term355 _111301 P Q R)) = ((term351 _111301 P Q R) = (term368 _111301 P Q R)).
Proof. exact (MK_COMB (@lem4846880 _111301 P Q R) (@lem4846888 _111301 P Q R)). Qed.
Lemma lem4846890 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term351 _111301 P Q R) = (term368 _111301 P Q R).
Proof. exact (EQ_MP (@lem4846889 _111301 P Q R) (@lem4846870 _111301 P Q R)). Qed.
Lemma lem4846892 {A : Type'} (P : A -> Prop) (Q : Prop) : (term244 A P Q) = (term245 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4846893 {_111301 : Type'} (P : type180 _111301) (Q : Prop) : (term282 _111301 P Q) = (term283 _111301 P Q).
Proof. exact (@lem4846892 (type686 _111301) P Q). Qed.
Lemma lem4846894 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term369 _111301 s P Q R) = (term370 _111301 s P Q R).
Proof. exact (@lem4846893 _111301 (term297 _111301 P Q R s) (term350 _111301 P Q R)). Qed.
Lemma lem4846895 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term371 _111301 P Q R s u) = (term295 _111301 P Q u R s).
Proof. exact (eq_refl (term371 _111301 P Q R s u)). Qed.
Lemma lem4846896 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term372 _111301 P Q R s) = (term297 _111301 P Q R s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846895 _111301 P Q u R s)). Qed.
Lemma lem4846897 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846898 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term373 _111301 P Q R s) = (term298 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846897 _111301) (@lem4846896 _111301 P Q R s)). Qed.
Lemma lem4846899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846900 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term374 _111301 P Q R s) = (term363 _111301 P Q R s).
Proof. exact (MK_COMB (@lem4846899) (@lem4846898 _111301 P Q R s)). Qed.
Lemma lem4846901 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term350 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (eq_refl (term350 _111301 P Q R)). Qed.
Lemma lem4846902 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term369 _111301 s P Q R) = (term365 _111301 s P Q R).
Proof. exact (MK_COMB (@lem4846900 _111301 P Q R s) (@lem4846901 _111301 P Q R)). Qed.
Lemma lem4846903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846904 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term375 _111301 s P Q R) = (term376 _111301 s P Q R).
Proof. exact (MK_COMB (@lem4846903) (@lem4846902 _111301 s P Q R)). Qed.
Lemma lem4846905 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term371 _111301 P Q R s u) = (term295 _111301 P Q u R s).
Proof. exact (eq_refl (term371 _111301 P Q R s u)). Qed.
Lemma lem4846906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4846907 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term377 _111301 P Q R s u) = (term378 _111301 P Q u R s).
Proof. exact (MK_COMB (@lem4846906) (@lem4846905 _111301 P Q u R s)). Qed.
Lemma lem4846908 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term350 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (eq_refl (term350 _111301 P Q R)). Qed.
Lemma lem4846909 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term379 _111301 s u P Q R) = (term380 _111301 u s P Q R).
Proof. exact (MK_COMB (@lem4846907 _111301 P Q u R s) (@lem4846908 _111301 P Q R)). Qed.
Lemma lem4846910 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term381 _111301 s P Q R) = (term382 _111301 s P Q R).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846909 _111301 u s P Q R)). Qed.
Lemma lem4846911 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846912 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term370 _111301 s P Q R) = (term383 _111301 s P Q R).
Proof. exact (MK_COMB (@lem4846911 _111301) (@lem4846910 _111301 s P Q R)). Qed.
Lemma lem4846913 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term369 _111301 s P Q R) = (term370 _111301 s P Q R)) = ((term365 _111301 s P Q R) = (term383 _111301 s P Q R)).
Proof. exact (MK_COMB (@lem4846904 _111301 s P Q R) (@lem4846912 _111301 s P Q R)). Qed.
Lemma lem4846914 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term365 _111301 s P Q R) = (term383 _111301 s P Q R).
Proof. exact (EQ_MP (@lem4846913 _111301 s P Q R) (@lem4846894 _111301 s P Q R)). Qed.
Lemma lem4846916 {A : Type'} (P : Prop) (Q : A -> Prop) : (term263 A P Q) = (term264 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4846917 {_111301 : Type'} (P : Prop) (Q : type72 _111301) : (term384 _111301 P Q) = (term385 _111301 P Q).
Proof. exact (@lem4846916 (type178 _111301) P Q). Qed.
Lemma lem4846918 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term386 _111301 u s P Q R) = (term387 _111301 u s P Q R).
Proof. exact (@lem4846917 _111301 (term295 _111301 P Q u R s) (term349 _111301 P Q R)). Qed.
Lemma lem4846919 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) : (term388 _111301 P Q R c) = (term347 _111301 P Q c R).
Proof. exact (eq_refl (term388 _111301 P Q R c)). Qed.
Lemma lem4846920 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term389 _111301 P Q R) = (term349 _111301 P Q R).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4846919 _111301 P Q c R)). Qed.
Lemma lem4846921 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846922 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term390 _111301 P Q R) = (term350 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846921 _111301) (@lem4846920 _111301 P Q R)). Qed.
Lemma lem4846923 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term378 _111301 P Q u R s) = (term378 _111301 P Q u R s).
Proof. exact (eq_refl (term378 _111301 P Q u R s)). Qed.
Lemma lem4846924 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term386 _111301 u s P Q R) = (term380 _111301 u s P Q R).
Proof. exact (MK_COMB (@lem4846923 _111301 P Q u R s) (@lem4846922 _111301 P Q R)). Qed.
Lemma lem4846925 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846926 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term391 _111301 u s P Q R) = (term392 _111301 u s P Q R).
Proof. exact (MK_COMB (@lem4846925) (@lem4846924 _111301 u s P Q R)). Qed.
Lemma lem4846927 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) : (term388 _111301 P Q R c) = (term347 _111301 P Q c R).
Proof. exact (eq_refl (term388 _111301 P Q R c)). Qed.
Lemma lem4846928 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term378 _111301 P Q u R s) = (term378 _111301 P Q u R s).
Proof. exact (eq_refl (term378 _111301 P Q u R s)). Qed.
Lemma lem4846929 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) : (term393 _111301 u s P Q R c) = (term394 _111301 u s P Q c R).
Proof. exact (MK_COMB (@lem4846928 _111301 P Q u R s) (@lem4846927 _111301 P Q c R)). Qed.
Lemma lem4846930 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term395 _111301 u s P Q R) = (term396 _111301 u s P Q R).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4846929 _111301 u s P Q c R)). Qed.
Lemma lem4846931 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846932 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term387 _111301 u s P Q R) = (term397 _111301 u s P Q R).
Proof. exact (MK_COMB (@lem4846931 _111301) (@lem4846930 _111301 u s P Q R)). Qed.
Lemma lem4846933 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term386 _111301 u s P Q R) = (term387 _111301 u s P Q R)) = ((term380 _111301 u s P Q R) = (term397 _111301 u s P Q R)).
Proof. exact (MK_COMB (@lem4846926 _111301 u s P Q R) (@lem4846932 _111301 u s P Q R)). Qed.
Lemma lem4846934 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term380 _111301 u s P Q R) = (term397 _111301 u s P Q R).
Proof. exact (EQ_MP (@lem4846933 _111301 u s P Q R) (@lem4846918 _111301 u s P Q R)). Qed.
Lemma lem4846935 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term382 _111301 s P Q R) = (term398 _111301 s P Q R).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4846934 _111301 u s P Q R)). Qed.
Lemma lem4846936 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846937 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term383 _111301 s P Q R) = (term399 _111301 s P Q R).
Proof. exact (MK_COMB (@lem4846936 _111301) (@lem4846935 _111301 s P Q R)). Qed.
Lemma lem4846938 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term365 _111301 s P Q R) = (term399 _111301 s P Q R).
Proof. exact (TRANS (@lem4846914 _111301 s P Q R) (@lem4846937 _111301 s P Q R)). Qed.
Lemma lem4846939 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term367 _111301 P Q R) = (term400 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4846938 _111301 s P Q R)). Qed.
Lemma lem4846940 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4846941 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term368 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846940 _111301) (@lem4846939 _111301 P Q R)). Qed.
Lemma lem4846942 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term351 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (TRANS (@lem4846890 _111301 P Q R) (@lem4846941 _111301 P Q R)). Qed.
Lemma lem4846943 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term125 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (TRANS (@lem4846866 _111301 P Q R) (@lem4846942 _111301 P Q R)). Qed.
Lemma lem4846944 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term133 _111301 P Q R) = (term402 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846753 _111301 P Q R) (@lem4846943 _111301 P Q R)). Qed.
Lemma lem4846948 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4846949 {_111301 : Type'} (P : type123 _111301) (Q : Prop) : (term403 _111301 P Q) = (term404 _111301 P Q).
Proof. exact (@lem4846948 (type598 _111301) P Q). Qed.
Lemma lem4846950 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term405 _111301 P Q R) = (term406 _111301 P Q R).
Proof. exact (@lem4846949 _111301 (term279 _111301 P Q R) (term401 _111301 P Q R)). Qed.
Lemma lem4846951 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term407 _111301 P Q R c) = (term278 _111301 c P Q R).
Proof. exact (eq_refl (term407 _111301 P Q R c)). Qed.
Lemma lem4846952 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term408 _111301 P Q R) = (term279 _111301 P Q R).
Proof. exact (fun_ext (fun c : type598 _111301 => @lem4846951 _111301 c P Q R)). Qed.
Lemma lem4846953 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846954 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term409 _111301 P Q R) = (term280 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846953 _111301) (@lem4846952 _111301 P Q R)). Qed.
Lemma lem4846955 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846956 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term410 _111301 P Q R) = (term281 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846955) (@lem4846954 _111301 P Q R)). Qed.
Lemma lem4846957 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term401 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (eq_refl (term401 _111301 P Q R)). Qed.
Lemma lem4846958 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term405 _111301 P Q R) = (term402 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846956 _111301 P Q R) (@lem4846957 _111301 P Q R)). Qed.
Lemma lem4846959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846960 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term411 _111301 P Q R) = (term412 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846959) (@lem4846958 _111301 P Q R)). Qed.
Lemma lem4846961 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term407 _111301 P Q R c) = (term278 _111301 c P Q R).
Proof. exact (eq_refl (term407 _111301 P Q R c)). Qed.
Lemma lem4846962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846963 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term413 _111301 P Q R c) = (term414 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846962) (@lem4846961 _111301 c P Q R)). Qed.
Lemma lem4846964 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term401 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (eq_refl (term401 _111301 P Q R)). Qed.
Lemma lem4846965 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term415 _111301 c P Q R) = (term416 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846963 _111301 c P Q R) (@lem4846964 _111301 P Q R)). Qed.
Lemma lem4846966 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term417 _111301 P Q R) = (term418 _111301 P Q R).
Proof. exact (fun_ext (fun c : type598 _111301 => @lem4846965 _111301 c P Q R)). Qed.
Lemma lem4846967 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4846968 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term406 _111301 P Q R) = (term419 _111301 P Q R).
Proof. exact (MK_COMB (@lem4846967 _111301) (@lem4846966 _111301 P Q R)). Qed.
Lemma lem4846969 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term405 _111301 P Q R) = (term406 _111301 P Q R)) = ((term402 _111301 P Q R) = (term419 _111301 P Q R)).
Proof. exact (MK_COMB (@lem4846960 _111301 P Q R) (@lem4846968 _111301 P Q R)). Qed.
Lemma lem4846970 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term402 _111301 P Q R) = (term419 _111301 P Q R).
Proof. exact (EQ_MP (@lem4846969 _111301 P Q R) (@lem4846950 _111301 P Q R)). Qed.
Lemma lem4846974 {A : Type'} (P : A -> Prop) (Q : Prop) : (term134 A P Q) = (term135 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4846975 {_111301 : Type'} (P : type180 _111301) (Q : Prop) : (term420 _111301 P Q) = (term421 _111301 P Q).
Proof. exact (@lem4846974 (type686 _111301) P Q). Qed.
Lemma lem4846976 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term422 _111301 c P Q R) = (term423 _111301 c P Q R).
Proof. exact (@lem4846975 _111301 (term277 _111301 c P Q R) (term401 _111301 P Q R)). Qed.
Lemma lem4846977 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term424 _111301 c P Q R t) = (term275 _111301 c P Q R t).
Proof. exact (eq_refl (term424 _111301 c P Q R t)). Qed.
Lemma lem4846978 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term425 _111301 c P Q R) = (term277 _111301 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846977 _111301 c P Q R t)). Qed.
Lemma lem4846979 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846980 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term426 _111301 c P Q R) = (term278 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846979 _111301) (@lem4846978 _111301 c P Q R)). Qed.
Lemma lem4846981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846982 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term427 _111301 c P Q R) = (term414 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846981) (@lem4846980 _111301 c P Q R)). Qed.
Lemma lem4846983 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term401 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (eq_refl (term401 _111301 P Q R)). Qed.
Lemma lem4846984 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term422 _111301 c P Q R) = (term416 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846982 _111301 c P Q R) (@lem4846983 _111301 P Q R)). Qed.
Lemma lem4846985 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4846986 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term428 _111301 c P Q R) = (term429 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846985) (@lem4846984 _111301 c P Q R)). Qed.
Lemma lem4846987 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term424 _111301 c P Q R t) = (term275 _111301 c P Q R t).
Proof. exact (eq_refl (term424 _111301 c P Q R t)). Qed.
Lemma lem4846988 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4846989 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term430 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (MK_COMB (@lem4846988) (@lem4846987 _111301 c P Q R t)). Qed.
Lemma lem4846990 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term401 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (eq_refl (term401 _111301 P Q R)). Qed.
Lemma lem4846991 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term432 _111301 c t P Q R) = (term433 _111301 c t P Q R).
Proof. exact (MK_COMB (@lem4846989 _111301 c P Q R t) (@lem4846990 _111301 P Q R)). Qed.
Lemma lem4846992 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term434 _111301 c P Q R) = (term435 _111301 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4846991 _111301 c t P Q R)). Qed.
Lemma lem4846993 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4846994 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term423 _111301 c P Q R) = (term436 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4846993 _111301) (@lem4846992 _111301 c P Q R)). Qed.
Lemma lem4846995 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term422 _111301 c P Q R) = (term423 _111301 c P Q R)) = ((term416 _111301 c P Q R) = (term436 _111301 c P Q R)).
Proof. exact (MK_COMB (@lem4846986 _111301 c P Q R) (@lem4846994 _111301 c P Q R)). Qed.
Lemma lem4846996 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term416 _111301 c P Q R) = (term436 _111301 c P Q R).
Proof. exact (EQ_MP (@lem4846995 _111301 c P Q R) (@lem4846976 _111301 c P Q R)). Qed.
Lemma lem4846998 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4846999 {_111301 : Type'} (P : Prop) (Q : type686 _111301) : (term156 _111301 P Q) = (term157 _111301 P Q).
Proof. exact (@lem4846998 (_111301 -> Prop) P Q). Qed.
Lemma lem4847000 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term437 _111301 c t P Q R) = (term438 _111301 c t P Q R).
Proof. exact (@lem4846999 _111301 (term275 _111301 c P Q R t) (term400 _111301 P Q R)). Qed.
Lemma lem4847001 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term439 _111301 P Q R s) = (term399 _111301 s P Q R).
Proof. exact (eq_refl (term439 _111301 P Q R s)). Qed.
Lemma lem4847002 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term440 _111301 P Q R) = (term400 _111301 P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4847001 _111301 s P Q R)). Qed.
Lemma lem4847003 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4847004 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term441 _111301 P Q R) = (term401 _111301 P Q R).
Proof. exact (MK_COMB (@lem4847003 _111301) (@lem4847002 _111301 P Q R)). Qed.
Lemma lem4847005 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term431 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (eq_refl (term431 _111301 c P Q R t)). Qed.
Lemma lem4847006 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term437 _111301 c t P Q R) = (term433 _111301 c t P Q R).
Proof. exact (MK_COMB (@lem4847005 _111301 c P Q R t) (@lem4847004 _111301 P Q R)). Qed.
Lemma lem4847007 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4847008 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term442 _111301 c t P Q R) = (term443 _111301 c t P Q R).
Proof. exact (MK_COMB (@lem4847007) (@lem4847006 _111301 c t P Q R)). Qed.
Lemma lem4847009 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term439 _111301 P Q R s) = (term399 _111301 s P Q R).
Proof. exact (eq_refl (term439 _111301 P Q R s)). Qed.
Lemma lem4847010 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term431 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (eq_refl (term431 _111301 c P Q R t)). Qed.
Lemma lem4847011 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term444 _111301 c t P Q R s) = (term445 _111301 c t s P Q R).
Proof. exact (MK_COMB (@lem4847010 _111301 c P Q R t) (@lem4847009 _111301 s P Q R)). Qed.
Lemma lem4847012 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term446 _111301 c t P Q R) = (term447 _111301 c t P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4847011 _111301 c t s P Q R)). Qed.
Lemma lem4847013 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4847014 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term438 _111301 c t P Q R) = (term448 _111301 c t P Q R).
Proof. exact (MK_COMB (@lem4847013 _111301) (@lem4847012 _111301 c t P Q R)). Qed.
Lemma lem4847015 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term437 _111301 c t P Q R) = (term438 _111301 c t P Q R)) = ((term433 _111301 c t P Q R) = (term448 _111301 c t P Q R)).
Proof. exact (MK_COMB (@lem4847008 _111301 c t P Q R) (@lem4847014 _111301 c t P Q R)). Qed.
Lemma lem4847016 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term433 _111301 c t P Q R) = (term448 _111301 c t P Q R).
Proof. exact (EQ_MP (@lem4847015 _111301 c t P Q R) (@lem4847000 _111301 c t P Q R)). Qed.
Lemma lem4847018 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4847019 {_111301 : Type'} (P : Prop) (Q : type180 _111301) : (term449 _111301 P Q) = (term450 _111301 P Q).
Proof. exact (@lem4847018 (type686 _111301) P Q). Qed.
Lemma lem4847020 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term451 _111301 c t s P Q R) = (term452 _111301 c t s P Q R).
Proof. exact (@lem4847019 _111301 (term275 _111301 c P Q R t) (term398 _111301 s P Q R)). Qed.
Lemma lem4847021 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term453 _111301 s P Q R u) = (term397 _111301 u s P Q R).
Proof. exact (eq_refl (term453 _111301 s P Q R u)). Qed.
Lemma lem4847022 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term454 _111301 s P Q R) = (term398 _111301 s P Q R).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4847021 _111301 u s P Q R)). Qed.
Lemma lem4847023 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847024 {_111301 : Type'} (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term455 _111301 s P Q R) = (term399 _111301 s P Q R).
Proof. exact (MK_COMB (@lem4847023 _111301) (@lem4847022 _111301 s P Q R)). Qed.
Lemma lem4847025 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term431 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (eq_refl (term431 _111301 c P Q R t)). Qed.
Lemma lem4847026 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term451 _111301 c t s P Q R) = (term445 _111301 c t s P Q R).
Proof. exact (MK_COMB (@lem4847025 _111301 c P Q R t) (@lem4847024 _111301 s P Q R)). Qed.
Lemma lem4847027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4847028 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term456 _111301 c t s P Q R) = (term457 _111301 c t s P Q R).
Proof. exact (MK_COMB (@lem4847027) (@lem4847026 _111301 c t s P Q R)). Qed.
Lemma lem4847029 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term453 _111301 s P Q R u) = (term397 _111301 u s P Q R).
Proof. exact (eq_refl (term453 _111301 s P Q R u)). Qed.
Lemma lem4847030 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term431 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (eq_refl (term431 _111301 c P Q R t)). Qed.
Lemma lem4847031 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term458 _111301 c t s P Q R u) = (term459 _111301 c t u s P Q R).
Proof. exact (MK_COMB (@lem4847030 _111301 c P Q R t) (@lem4847029 _111301 u s P Q R)). Qed.
Lemma lem4847032 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term460 _111301 c t s P Q R) = (term461 _111301 c t s P Q R).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4847031 _111301 c t u s P Q R)). Qed.
Lemma lem4847033 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847034 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term452 _111301 c t s P Q R) = (term462 _111301 c t s P Q R).
Proof. exact (MK_COMB (@lem4847033 _111301) (@lem4847032 _111301 c t s P Q R)). Qed.
Lemma lem4847035 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term451 _111301 c t s P Q R) = (term452 _111301 c t s P Q R)) = ((term445 _111301 c t s P Q R) = (term462 _111301 c t s P Q R)).
Proof. exact (MK_COMB (@lem4847028 _111301 c t s P Q R) (@lem4847034 _111301 c t s P Q R)). Qed.
Lemma lem4847036 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term445 _111301 c t s P Q R) = (term462 _111301 c t s P Q R).
Proof. exact (EQ_MP (@lem4847035 _111301 c t s P Q R) (@lem4847020 _111301 c t s P Q R)). Qed.
Lemma lem4847038 {A : Type'} (P : Prop) (Q : A -> Prop) : (term154 A P Q) = (term155 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4847039 {_111301 : Type'} (P : Prop) (Q : type72 _111301) : (term463 _111301 P Q) = (term464 _111301 P Q).
Proof. exact (@lem4847038 (type178 _111301) P Q). Qed.
Lemma lem4847040 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term465 _111301 c t u s P Q R) = (term466 _111301 c t u s P Q R).
Proof. exact (@lem4847039 _111301 (term275 _111301 c P Q R t) (term396 _111301 u s P Q R)). Qed.
Lemma lem4847041 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) : (term467 _111301 u s P Q R c) = (term394 _111301 u s P Q c R).
Proof. exact (eq_refl (term467 _111301 u s P Q R c)). Qed.
Lemma lem4847042 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term468 _111301 u s P Q R) = (term396 _111301 u s P Q R).
Proof. exact (fun_ext (fun c : type178 _111301 => @lem4847041 _111301 u s P Q c R)). Qed.
Lemma lem4847043 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4847044 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term469 _111301 u s P Q R) = (term397 _111301 u s P Q R).
Proof. exact (MK_COMB (@lem4847043 _111301) (@lem4847042 _111301 u s P Q R)). Qed.
Lemma lem4847045 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term431 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (eq_refl (term431 _111301 c P Q R t)). Qed.
Lemma lem4847046 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term465 _111301 c t u s P Q R) = (term459 _111301 c t u s P Q R).
Proof. exact (MK_COMB (@lem4847045 _111301 c P Q R t) (@lem4847044 _111301 u s P Q R)). Qed.
Lemma lem4847047 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4847048 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term470 _111301 c t u s P Q R) = (term471 _111301 c t u s P Q R).
Proof. exact (MK_COMB (@lem4847047) (@lem4847046 _111301 c t u s P Q R)). Qed.
Lemma lem4847049 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c : type178 _111301) (R : type686 _111301) : (term467 _111301 u s P Q R c) = (term394 _111301 u s P Q c R).
Proof. exact (eq_refl (term467 _111301 u s P Q R c)). Qed.
Lemma lem4847050 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term431 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (eq_refl (term431 _111301 c P Q R t)). Qed.
Lemma lem4847051 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) : (term472 _111301 c t u s P Q R c') = (term473 _111301 c t u s P Q c' R).
Proof. exact (MK_COMB (@lem4847050 _111301 c P Q R t) (@lem4847049 _111301 u s P Q c' R)). Qed.
Lemma lem4847052 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term474 _111301 c t u s P Q R) = (term475 _111301 c t u s P Q R).
Proof. exact (fun_ext (fun c' : type178 _111301 => @lem4847051 _111301 c t u s P Q c' R)). Qed.
Lemma lem4847053 {_111301 : Type'} : (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex (((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4847054 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term466 _111301 c t u s P Q R) = (term476 _111301 c t u s P Q R).
Proof. exact (MK_COMB (@lem4847053 _111301) (@lem4847052 _111301 c t u s P Q R)). Qed.
Lemma lem4847055 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : ((term465 _111301 c t u s P Q R) = (term466 _111301 c t u s P Q R)) = ((term459 _111301 c t u s P Q R) = (term476 _111301 c t u s P Q R)).
Proof. exact (MK_COMB (@lem4847048 _111301 c t u s P Q R) (@lem4847054 _111301 c t u s P Q R)). Qed.
Lemma lem4847056 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term459 _111301 c t u s P Q R) = (term476 _111301 c t u s P Q R).
Proof. exact (EQ_MP (@lem4847055 _111301 c t u s P Q R) (@lem4847040 _111301 c t u s P Q R)). Qed.
Lemma lem4847057 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term461 _111301 c t s P Q R) = (term477 _111301 c t s P Q R).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4847056 _111301 c t u s P Q R)). Qed.
Lemma lem4847058 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847059 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term462 _111301 c t s P Q R) = (term478 _111301 c t s P Q R).
Proof. exact (MK_COMB (@lem4847058 _111301) (@lem4847057 _111301 c t s P Q R)). Qed.
Lemma lem4847060 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term445 _111301 c t s P Q R) = (term478 _111301 c t s P Q R).
Proof. exact (TRANS (@lem4847036 _111301 c t s P Q R) (@lem4847059 _111301 c t s P Q R)). Qed.
Lemma lem4847061 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term447 _111301 c t P Q R) = (term479 _111301 c t P Q R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4847060 _111301 c t s P Q R)). Qed.
Lemma lem4847062 {_111301 : Type'} : (@ex (_111301 -> Prop)) = (@ex (_111301 -> Prop)).
Proof. exact (eq_refl (@ex (_111301 -> Prop))). Qed.
Lemma lem4847063 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term448 _111301 c t P Q R) = (term480 _111301 c t P Q R).
Proof. exact (MK_COMB (@lem4847062 _111301) (@lem4847061 _111301 c t P Q R)). Qed.
Lemma lem4847064 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term433 _111301 c t P Q R) = (term480 _111301 c t P Q R).
Proof. exact (TRANS (@lem4847016 _111301 c t P Q R) (@lem4847063 _111301 c t P Q R)). Qed.
Lemma lem4847065 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term435 _111301 c P Q R) = (term481 _111301 c P Q R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4847064 _111301 c t P Q R)). Qed.
Lemma lem4847066 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> Prop)) = (@ex ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847067 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term436 _111301 c P Q R) = (term482 _111301 c P Q R).
Proof. exact (MK_COMB (@lem4847066 _111301) (@lem4847065 _111301 c P Q R)). Qed.
Lemma lem4847068 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term416 _111301 c P Q R) = (term482 _111301 c P Q R).
Proof. exact (TRANS (@lem4846996 _111301 c P Q R) (@lem4847067 _111301 c P Q R)). Qed.
Lemma lem4847069 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term418 _111301 P Q R) = (term483 _111301 P Q R).
Proof. exact (fun_ext (fun c : type598 _111301 => @lem4847068 _111301 c P Q R)). Qed.
Lemma lem4847070 {_111301 : Type'} : (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)) = (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop)).
Proof. exact (eq_refl (@ex ((_111301 -> Prop) -> ((_111301 -> Prop) -> Prop) -> _111301 -> Prop))). Qed.
Lemma lem4847071 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term419 _111301 P Q R) = (term484 _111301 P Q R).
Proof. exact (MK_COMB (@lem4847070 _111301) (@lem4847069 _111301 P Q R)). Qed.
Lemma lem4847072 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term402 _111301 P Q R) = (term484 _111301 P Q R).
Proof. exact (TRANS (@lem4846970 _111301 P Q R) (@lem4847071 _111301 P Q R)). Qed.
Lemma lem4847074 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term133 _111301 P Q R) = (term484 _111301 P Q R).
Proof. exact (TRANS (@lem4846944 _111301 P Q R) (@lem4847072 _111301 P Q R)). Qed.
Lemma lem4847075 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term4 _111301 P Q R) = (term484 _111301 P Q R).
Proof. exact (TRANS (@lem4846141 _111301 P Q R) (@lem4847074 _111301 P Q R)). Qed.
Lemma lem4847076 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : term484 _111301 P Q R.
Proof. exact (EQ_MP (@lem4847075 _111301 P Q R) (@lem4845983 _111301 P Q R h1)). Qed.
Lemma lem4847077 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term482 _111301 c P Q R) : term482 _111301 c P Q R.
Proof. exact (h1). Qed.
Lemma lem4847078 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term480 _111301 c t P Q R) : term480 _111301 c t P Q R.
Proof. exact (h1). Qed.
Lemma lem4847079 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term478 _111301 c t s P Q R) : term478 _111301 c t s P Q R.
Proof. exact (h1). Qed.
Lemma lem4847080 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term476 _111301 c t u s P Q R) : term476 _111301 c t u s P Q R.
Proof. exact (h1). Qed.
Lemma lem4847081 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term473 _111301 c t u s P Q c' R) : term473 _111301 c t u s P Q c' R.
Proof. exact (h1). Qed.
Lemma lem4847114 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (t : type686 _111301) : (term343 _111301 P Q c' R t) = (term343 _111301 P Q c' R t).
Proof. exact (eq_refl (term343 _111301 P Q c' R t)). Qed.
Lemma lem4847115 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) : (term345 _111301 P Q c' R) = (term345 _111301 P Q c' R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4847114 _111301 P Q c' R t)). Qed.
Lemma lem4847116 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847117 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) : (term347 _111301 P Q c' R) = (term347 _111301 P Q c' R).
Proof. exact (MK_COMB (@lem4847116 _111301) (@lem4847115 _111301 P Q c' R)). Qed.
Lemma lem4847122 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (term78 _111301 R s) = (term78 _111301 R s).
Proof. exact (eq_refl (term78 _111301 R s)). Qed.
Lemma lem4847129 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) : ((@UNIONS _111301 u) = s) = ((@UNIONS _111301 u) = s).
Proof. exact (eq_refl ((@UNIONS _111301 u) = s)). Qed.
Lemma lem4847142 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term42 _111301 u Q c) = (term42 _111301 u Q c).
Proof. exact (eq_refl (term42 _111301 u Q c)). Qed.
Lemma lem4847143 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term52 _111301 u Q) = (term52 _111301 u Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4847142 _111301 u Q c)). Qed.
Lemma lem4847144 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4847145 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term53 _111301 u Q) = (term53 _111301 u Q).
Proof. exact (MK_COMB (@lem4847144 _111301) (@lem4847143 _111301 u Q)). Qed.
Lemma lem4847146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4847147 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term60 _111301 u Q) = (term60 _111301 u Q).
Proof. exact (MK_COMB (@lem4847146) (@lem4847145 _111301 u Q)). Qed.
Lemma lem4847148 {_111301 : Type'} (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term61 _111301 Q u s) = (term61 _111301 Q u s).
Proof. exact (MK_COMB (@lem4847147 _111301 u Q) (@lem4847129 _111301 u s)). Qed.
Lemma lem4847153 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term26 _111301 P u) = (term26 _111301 P u).
Proof. exact (eq_refl (term26 _111301 P u)). Qed.
Lemma lem4847154 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term66 _111301 P Q u s) = (term66 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4847153 _111301 P u) (@lem4847148 _111301 Q u s)). Qed.
Lemma lem4847155 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4847156 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term293 _111301 P Q u s) = (term293 _111301 P Q u s).
Proof. exact (MK_COMB (@lem4847155) (@lem4847154 _111301 P Q u s)). Qed.
Lemma lem4847157 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term295 _111301 P Q u R s) = (term295 _111301 P Q u R s).
Proof. exact (MK_COMB (@lem4847156 _111301 P Q u s) (@lem4847122 _111301 R s)). Qed.
Lemma lem4847158 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4847159 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term378 _111301 P Q u R s) = (term378 _111301 P Q u R s).
Proof. exact (MK_COMB (@lem4847158) (@lem4847157 _111301 P Q u R s)). Qed.
Lemma lem4847160 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) : (term394 _111301 u s P Q c' R) = (term394 _111301 u s P Q c' R).
Proof. exact (MK_COMB (@lem4847159 _111301 P Q u R s) (@lem4847117 _111301 P Q c' R)). Qed.
Lemma lem4847167 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term101 _111301 R t) = (term101 _111301 R t).
Proof. exact (eq_refl (term101 _111301 R t)). Qed.
Lemma lem4847180 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term42 _111301 t Q c) = (term42 _111301 t Q c).
Proof. exact (eq_refl (term42 _111301 t Q c)). Qed.
Lemma lem4847181 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term52 _111301 t Q) = (term52 _111301 t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4847180 _111301 t Q c)). Qed.
Lemma lem4847182 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4847183 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term53 _111301 t Q) = (term53 _111301 t Q).
Proof. exact (MK_COMB (@lem4847182 _111301) (@lem4847181 _111301 t Q)). Qed.
Lemma lem4847188 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term26 _111301 P t) = (term26 _111301 P t).
Proof. exact (eq_refl (term26 _111301 P t)). Qed.
Lemma lem4847189 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term100 _111301 P t Q) = (term100 _111301 P t Q).
Proof. exact (MK_COMB (@lem4847188 _111301 P t) (@lem4847183 _111301 t Q)). Qed.
Lemma lem4847190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4847191 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) (Q : type686 _111301) : (term103 _111301 P t Q) = (term103 _111301 P t Q).
Proof. exact (MK_COMB (@lem4847190) (@lem4847189 _111301 P t Q)). Qed.
Lemma lem4847192 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term105 _111301 P Q R t) = (term105 _111301 P Q R t).
Proof. exact (MK_COMB (@lem4847191 _111301 P t Q) (@lem4847167 _111301 R t)). Qed.
Lemma lem4847195 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4847236 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term485 _111301 P Q c u s) = (term485 _111301 P Q c u s).
Proof. exact (eq_refl (term485 _111301 P Q c u s)). Qed.
Lemma lem4847237 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (s : _111301 -> Prop) : (term486 _111301 P Q c s) = (term486 _111301 P Q c s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4847236 _111301 P Q c u s)). Qed.
Lemma lem4847238 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847239 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (s : _111301 -> Prop) : (term487 _111301 P Q c s) = (term487 _111301 P Q c s).
Proof. exact (MK_COMB (@lem4847238 _111301) (@lem4847237 _111301 P Q c s)). Qed.
Lemma lem4847240 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4847241 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (s : _111301 -> Prop) : (term488 _111301 P Q c s) = (term488 _111301 P Q c s).
Proof. exact (MK_COMB (@lem4847240) (@lem4847239 _111301 P Q c s)). Qed.
Lemma lem4847242 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term234 _111301 P Q c R s) = (term234 _111301 P Q c R s).
Proof. exact (MK_COMB (@lem4847241 _111301 P Q c s) (@lem4847195 _111301 R s)). Qed.
Lemma lem4847243 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term236 _111301 P Q c R) = (term236 _111301 P Q c R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4847242 _111301 P Q c R s)). Qed.
Lemma lem4847244 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4847245 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term238 _111301 P Q c R) = (term238 _111301 P Q c R).
Proof. exact (MK_COMB (@lem4847244 _111301) (@lem4847243 _111301 P Q c R)). Qed.
Lemma lem4847246 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4847247 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term257 _111301 P Q c R) = (term257 _111301 P Q c R).
Proof. exact (MK_COMB (@lem4847246) (@lem4847245 _111301 P Q c R)). Qed.
Lemma lem4847248 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term275 _111301 c P Q R t) = (term275 _111301 c P Q R t).
Proof. exact (MK_COMB (@lem4847247 _111301 P Q c R) (@lem4847192 _111301 P Q R t)). Qed.
Lemma lem4847249 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4847250 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) : (term431 _111301 c P Q R t) = (term431 _111301 c P Q R t).
Proof. exact (MK_COMB (@lem4847249) (@lem4847248 _111301 c P Q R t)). Qed.
Lemma lem4847251 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) : (term473 _111301 c t u s P Q c' R) = (term473 _111301 c t u s P Q c' R).
Proof. exact (MK_COMB (@lem4847250 _111301 c P Q R t) (@lem4847160 _111301 u s P Q c' R)). Qed.
Lemma lem4847252 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term473 _111301 c t u s P Q c' R) : term473 _111301 c t u s P Q c' R.
Proof. exact (EQ_MP (@lem4847251 _111301 c t u s P Q c' R) (@lem4847081 _111301 c t u s P Q c' R h1)). Qed.
Lemma lem4847253 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term275 _111301 c P Q R t.
Proof. exact (h1). Qed.
Lemma lem4847254 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term394 _111301 u s P Q c' R.
Proof. exact (h1). Qed.
Lemma lem4847255 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term105 _111301 P Q R t.
Proof. exact (proj2 (@lem4847253 _111301 c P Q R t h1)). Qed.
Lemma lem4847256 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term238 _111301 P Q c R.
Proof. exact (proj1 (@lem4847253 _111301 c P Q R t h1)). Qed.
Lemma lem4847258 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term100 _111301 P t Q.
Proof. exact (proj1 (@lem4847255 _111301 c P Q R t h1)). Qed.
Lemma lem4847259 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term53 _111301 t Q.
Proof. exact (proj2 (@lem4847258 _111301 c P Q R t h1)). Qed.
Lemma lem4847261 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term347 _111301 P Q c' R.
Proof. exact (proj2 (@lem4847254 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847262 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term295 _111301 P Q u R s.
Proof. exact (proj1 (@lem4847254 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847264 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term66 _111301 P Q u s.
Proof. exact (proj1 (@lem4847262 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847265 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term61 _111301 Q u s.
Proof. exact (proj2 (@lem4847264 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847268 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term53 _111301 u Q.
Proof. exact (proj1 (@lem4847265 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847270 {A : Type'} (P : A -> Prop) (Q : Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem4847271 {_111301 : Type'} (P : type180 _111301) (Q : Prop) : (term491 _111301 P Q) = (term492 _111301 P Q).
Proof. exact (@lem4847270 (type686 _111301) P Q). Qed.
Lemma lem4847272 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term493 _111301 P Q c R s) = (term494 _111301 P Q c R s).
Proof. exact (@lem4847271 _111301 (term486 _111301 P Q c s) (R s)). Qed.
Lemma lem4847273 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term495 _111301 P Q c s u) = (term485 _111301 P Q c u s).
Proof. exact (eq_refl (term495 _111301 P Q c s u)). Qed.
Lemma lem4847274 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (s : _111301 -> Prop) : (term496 _111301 P Q c s) = (term486 _111301 P Q c s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4847273 _111301 P Q c u s)). Qed.
Lemma lem4847275 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847276 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (s : _111301 -> Prop) : (term497 _111301 P Q c s) = (term487 _111301 P Q c s).
Proof. exact (MK_COMB (@lem4847275 _111301) (@lem4847274 _111301 P Q c s)). Qed.
Lemma lem4847277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4847278 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (s : _111301 -> Prop) : (term498 _111301 P Q c s) = (term488 _111301 P Q c s).
Proof. exact (MK_COMB (@lem4847277) (@lem4847276 _111301 P Q c s)). Qed.
Lemma lem4847279 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4847280 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term493 _111301 P Q c R s) = (term234 _111301 P Q c R s).
Proof. exact (MK_COMB (@lem4847278 _111301 P Q c s) (@lem4847279 _111301 R s)). Qed.
Lemma lem4847281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4847282 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term499 _111301 P Q c R s) = (term500 _111301 P Q c R s).
Proof. exact (MK_COMB (@lem4847281) (@lem4847280 _111301 P Q c R s)). Qed.
Lemma lem4847283 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term495 _111301 P Q c s u) = (term485 _111301 P Q c u s).
Proof. exact (eq_refl (term495 _111301 P Q c s u)). Qed.
Lemma lem4847284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4847285 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term501 _111301 P Q c s u) = (term502 _111301 P Q c u s).
Proof. exact (MK_COMB (@lem4847284) (@lem4847283 _111301 P Q c u s)). Qed.
Lemma lem4847286 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4847287 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term503 _111301 P Q c u R s) = (term504 _111301 P Q c u R s).
Proof. exact (MK_COMB (@lem4847285 _111301 P Q c u s) (@lem4847286 _111301 R s)). Qed.
Lemma lem4847288 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term505 _111301 P Q c R s) = (term506 _111301 P Q c R s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4847287 _111301 P Q c u R s)). Qed.
Lemma lem4847289 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847290 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term494 _111301 P Q c R s) = (term507 _111301 P Q c R s).
Proof. exact (MK_COMB (@lem4847289 _111301) (@lem4847288 _111301 P Q c R s)). Qed.
Lemma lem4847291 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : ((term493 _111301 P Q c R s) = (term494 _111301 P Q c R s)) = ((term234 _111301 P Q c R s) = (term507 _111301 P Q c R s)).
Proof. exact (MK_COMB (@lem4847282 _111301 P Q c R s) (@lem4847290 _111301 P Q c R s)). Qed.
Lemma lem4847292 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term234 _111301 P Q c R s) = (term507 _111301 P Q c R s).
Proof. exact (EQ_MP (@lem4847291 _111301 P Q c R s) (@lem4847272 _111301 P Q c R s)). Qed.
Lemma lem4847293 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term236 _111301 P Q c R) = (term508 _111301 P Q c R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4847292 _111301 P Q c R s)). Qed.
Lemma lem4847294 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4847295 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term238 _111301 P Q c R) = (term509 _111301 P Q c R).
Proof. exact (MK_COMB (@lem4847294 _111301) (@lem4847293 _111301 P Q c R)). Qed.
Lemma lem4847296 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (R s) = (R s).
Proof. exact (eq_refl (R s)). Qed.
Lemma lem4847313 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term510 _111301 Q c u s) = (term511 _111301 Q c u s).
Proof. exact (@lem19699 (term512 _111301 c s u) (term513 _111301 Q c s u) (term54 _111301 u s)). Qed.
Lemma lem4847316 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term62 _111301 P u) = (term62 _111301 P u).
Proof. exact (eq_refl (term62 _111301 P u)). Qed.
Lemma lem4847317 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term485 _111301 P Q c u s) = (term514 _111301 P Q c u s).
Proof. exact (MK_COMB (@lem4847316 _111301 P u) (@lem4847313 _111301 Q c u s)). Qed.
Lemma lem4847324 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term514 _111301 P Q c u s) = (term515 _111301 P Q c u s).
Proof. exact (@lem19490 (term516 _111301 c u s) (term160 _111301 P u) (term517 _111301 Q c u s)). Qed.
Lemma lem4847325 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term485 _111301 P Q c u s) = (term515 _111301 P Q c u s).
Proof. exact (TRANS (@lem4847317 _111301 P Q c u s) (@lem4847324 _111301 P Q c u s)). Qed.
Lemma lem4847326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4847327 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (s : _111301 -> Prop) : (term502 _111301 P Q c u s) = (term518 _111301 P Q c u s).
Proof. exact (MK_COMB (@lem4847326) (@lem4847325 _111301 P Q c u s)). Qed.
Lemma lem4847328 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term504 _111301 P Q c u R s) = (term519 _111301 P Q c u R s).
Proof. exact (MK_COMB (@lem4847327 _111301 P Q c u s) (@lem4847296 _111301 R s)). Qed.
Lemma lem4847335 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term519 _111301 P Q c u R s) = (term520 _111301 P Q c u R s).
Proof. exact (@lem19699 (term521 _111301 P c u s) (term522 _111301 P Q c u s) (R s)). Qed.
Lemma lem4847336 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (u : type686 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term504 _111301 P Q c u R s) = (term520 _111301 P Q c u R s).
Proof. exact (TRANS (@lem4847328 _111301 P Q c u R s) (@lem4847335 _111301 P Q c u R s)). Qed.
Lemma lem4847337 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term506 _111301 P Q c R s) = (term523 _111301 P Q c R s).
Proof. exact (fun_ext (fun u : type686 _111301 => @lem4847336 _111301 P Q c u R s)). Qed.
Lemma lem4847338 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847339 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (s : _111301 -> Prop) : (term507 _111301 P Q c R s) = (term524 _111301 P Q c R s).
Proof. exact (MK_COMB (@lem4847338 _111301) (@lem4847337 _111301 P Q c R s)). Qed.
Lemma lem4847340 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term508 _111301 P Q c R) = (term525 _111301 P Q c R).
Proof. exact (fun_ext (fun s : _111301 -> Prop => @lem4847339 _111301 P Q c R s)). Qed.
Lemma lem4847341 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4847342 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term509 _111301 P Q c R) = (term526 _111301 P Q c R).
Proof. exact (MK_COMB (@lem4847341 _111301) (@lem4847340 _111301 P Q c R)). Qed.
Lemma lem4847343 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) : (term238 _111301 P Q c R) = (term526 _111301 P Q c R).
Proof. exact (TRANS (@lem4847295 _111301 P Q c R) (@lem4847342 _111301 P Q c R)). Qed.
Lemma lem4847344 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term526 _111301 P Q c R.
Proof. exact (EQ_MP (@lem4847343 _111301 P Q c R) (@lem4847256 _111301 c P Q R t h1)). Qed.
Lemma lem4847360 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term42 _111301 t Q c) = (term42 _111301 t Q c).
Proof. exact (eq_refl (term42 _111301 t Q c)). Qed.
Lemma lem4847361 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term52 _111301 t Q) = (term52 _111301 t Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4847360 _111301 t Q c)). Qed.
Lemma lem4847362 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4847364 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) : (term53 _111301 t Q) = (term53 _111301 t Q).
Proof. exact (MK_COMB (@lem4847362 _111301) (@lem4847361 _111301 t Q)). Qed.
Lemma lem4847365 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term53 _111301 t Q.
Proof. exact (EQ_MP (@lem4847364 _111301 t Q) (@lem4847259 _111301 c P Q R t h1)). Qed.
Lemma lem4847367 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term22 _111301 R t) = (term22 _111301 R t).
Proof. exact (eq_refl (term22 _111301 R t)). Qed.
Lemma lem4847384 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (t : type686 _111301) : (term527 _111301 P Q c' t) = (term528 _111301 P Q c' t).
Proof. exact (@lem19490 (term529 _111301 c' t) (term160 _111301 P t) (term530 _111301 Q c' t)). Qed.
Lemma lem4847385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4847386 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (t : type686 _111301) : (term531 _111301 P Q c' t) = (term532 _111301 P Q c' t).
Proof. exact (MK_COMB (@lem4847385) (@lem4847384 _111301 P Q c' t)). Qed.
Lemma lem4847387 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (t : type686 _111301) : (term343 _111301 P Q c' R t) = (term533 _111301 P Q c' R t).
Proof. exact (MK_COMB (@lem4847386 _111301 P Q c' t) (@lem4847367 _111301 R t)). Qed.
Lemma lem4847394 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (t : type686 _111301) : (term533 _111301 P Q c' R t) = (term534 _111301 P Q c' R t).
Proof. exact (@lem19699 (term535 _111301 P c' t) (term536 _111301 P Q c' t) (term22 _111301 R t)). Qed.
Lemma lem4847395 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (t : type686 _111301) : (term343 _111301 P Q c' R t) = (term534 _111301 P Q c' R t).
Proof. exact (TRANS (@lem4847387 _111301 P Q c' R t) (@lem4847394 _111301 P Q c' R t)). Qed.
Lemma lem4847396 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) : (term345 _111301 P Q c' R) = (term537 _111301 P Q c' R).
Proof. exact (fun_ext (fun t : type686 _111301 => @lem4847395 _111301 P Q c' R t)). Qed.
Lemma lem4847397 {_111301 : Type'} : (@all ((_111301 -> Prop) -> Prop)) = (@all ((_111301 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_111301 -> Prop) -> Prop))). Qed.
Lemma lem4847399 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) : (term347 _111301 P Q c' R) = (term538 _111301 P Q c' R).
Proof. exact (MK_COMB (@lem4847397 _111301) (@lem4847396 _111301 P Q c' R)). Qed.
Lemma lem4847400 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term538 _111301 P Q c' R.
Proof. exact (EQ_MP (@lem4847399 _111301 P Q c' R) (@lem4847261 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847416 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (c : _111301 -> Prop) : (term42 _111301 u Q c) = (term42 _111301 u Q c).
Proof. exact (eq_refl (term42 _111301 u Q c)). Qed.
Lemma lem4847417 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term52 _111301 u Q) = (term52 _111301 u Q).
Proof. exact (fun_ext (fun c : _111301 -> Prop => @lem4847416 _111301 u Q c)). Qed.
Lemma lem4847418 {_111301 : Type'} : (@all (_111301 -> Prop)) = (@all (_111301 -> Prop)).
Proof. exact (eq_refl (@all (_111301 -> Prop))). Qed.
Lemma lem4847420 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) : (term53 _111301 u Q) = (term53 _111301 u Q).
Proof. exact (MK_COMB (@lem4847418 _111301) (@lem4847417 _111301 u Q)). Qed.
Lemma lem4847421 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term53 _111301 u Q.
Proof. exact (EQ_MP (@lem4847420 _111301 u Q) (@lem4847268 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847426 {_111301 : Type'} (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term539 _111301 P Q c R _60114.
Proof. exact (@lem4847344 _111301 c P Q R t h1 _60114). Qed.
Lemma lem4847427 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term539 _111301 P Q c R _60114) = (term524 _111301 P Q c R _60114).
Proof. exact (eq_refl (term539 _111301 P Q c R _60114)). Qed.
Lemma lem4847428 {_111301 : Type'} (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term524 _111301 P Q c R _60114.
Proof. exact (EQ_MP (@lem4847427 _111301 P Q c R _60114) (@lem4847426 _111301 _60114 c P Q R t h1)). Qed.
Lemma lem4847429 {_111301 : Type'} (_60114 : _111301 -> Prop) (_60115 : type686 _111301) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term540 _111301 P Q c R _60114 _60115.
Proof. exact (@lem4847428 _111301 _60114 c P Q R t h1 _60115). Qed.
Lemma lem4847430 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term540 _111301 P Q c R _60114 _60115) = (term520 _111301 P Q c _60115 R _60114).
Proof. exact (eq_refl (term540 _111301 P Q c R _60114 _60115)). Qed.
Lemma lem4847431 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term520 _111301 P Q c _60115 R _60114.
Proof. exact (EQ_MP (@lem4847430 _111301 P Q c _60115 R _60114) (@lem4847429 _111301 _60114 _60115 c P Q R t h1)). Qed.
Lemma lem4847432 {_111301 : Type'} (_60116 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term541 _111301 t Q _60116.
Proof. exact (@lem4847365 _111301 c P Q R t h1 _60116). Qed.
Lemma lem4847433 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (_60116 : _111301 -> Prop) : (term541 _111301 t Q _60116) = (term42 _111301 t Q _60116).
Proof. exact (eq_refl (term541 _111301 t Q _60116)). Qed.
Lemma lem4847435 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term542 _111301 P Q c' R _60117.
Proof. exact (@lem4847400 _111301 u s P Q c' R h1 _60117). Qed.
Lemma lem4847436 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term542 _111301 P Q c' R _60117) = (term534 _111301 P Q c' R _60117).
Proof. exact (eq_refl (term542 _111301 P Q c' R _60117)). Qed.
Lemma lem4847437 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term534 _111301 P Q c' R _60117.
Proof. exact (EQ_MP (@lem4847436 _111301 P Q c' R _60117) (@lem4847435 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4847438 {_111301 : Type'} (_60118 : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term541 _111301 u Q _60118.
Proof. exact (@lem4847421 _111301 u s P Q c' R h1 _60118). Qed.
Lemma lem4847439 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (_60118 : _111301 -> Prop) : (term541 _111301 u Q _60118) = (term42 _111301 u Q _60118).
Proof. exact (eq_refl (term541 _111301 u Q _60118)). Qed.
Lemma lem4847441 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term543 _111301 P Q c _60115 R _60114.
Proof. exact (proj2 (@lem4847431 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4847442 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term544 _111301 P c _60115 R _60114.
Proof. exact (proj1 (@lem4847431 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4847443 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term545 _111301 P Q c' R _60117.
Proof. exact (proj2 (@lem4847437 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4847444 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term546 _111301 P c' R _60117.
Proof. exact (proj1 (@lem4847437 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4847446 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term101 _111301 R t.
Proof. exact (proj2 (@lem4847255 _111301 c P Q R t h1)). Qed.
Lemma lem4847454 {_111301 : Type'} (_60116 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term42 _111301 t Q _60116.
Proof. exact (EQ_MP (@lem4847433 _111301 t Q _60116) (@lem4847432 _111301 _60116 c P Q R t h1)). Qed.
Lemma lem4847458 {_111301 : Type'} (P : type180 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term544 _111301 P c _60115 R _60114) = (term547 _111301 P c _60115 R _60114).
Proof. exact (@lem4845633 (term160 _111301 P _60115) (term516 _111301 c _60115 _60114) (R _60114)). Qed.
Lemma lem4847465 {_111301 : Type'} (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term548 _111301 c _60115 R _60114) = (term549 _111301 c _60115 R _60114).
Proof. exact (@lem4845633 (term512 _111301 c _60114 _60115) (term54 _111301 _60115 _60114) (R _60114)). Qed.
Lemma lem4847466 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term62 _111301 P _60115) = (term62 _111301 P _60115).
Proof. exact (eq_refl (term62 _111301 P _60115)). Qed.
Lemma lem4847469 {_111301 : Type'} (P : type180 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term547 _111301 P c _60115 R _60114) = (term550 _111301 P c _60115 R _60114).
Proof. exact (MK_COMB (@lem4847466 _111301 P _60115) (@lem4847465 _111301 c _60115 R _60114)). Qed.
Lemma lem4847471 {_111301 : Type'} (P : type180 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term544 _111301 P c _60115 R _60114) = (term550 _111301 P c _60115 R _60114).
Proof. exact (TRANS (@lem4847458 _111301 P c _60115 R _60114) (@lem4847469 _111301 P c _60115 R _60114)). Qed.
Lemma lem4847472 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term550 _111301 P c _60115 R _60114.
Proof. exact (EQ_MP (@lem4847471 _111301 P c _60115 R _60114) (@lem4847442 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4847476 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term543 _111301 P Q c _60115 R _60114) = (term551 _111301 P Q c _60115 R _60114).
Proof. exact (@lem4845633 (term160 _111301 P _60115) (term517 _111301 Q c _60115 _60114) (R _60114)). Qed.
Lemma lem4847483 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term552 _111301 Q c _60115 R _60114) = (term553 _111301 Q c _60115 R _60114).
Proof. exact (@lem4845633 (term513 _111301 Q c _60114 _60115) (term54 _111301 _60115 _60114) (R _60114)). Qed.
Lemma lem4847484 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term62 _111301 P _60115) = (term62 _111301 P _60115).
Proof. exact (eq_refl (term62 _111301 P _60115)). Qed.
Lemma lem4847487 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term551 _111301 P Q c _60115 R _60114) = (term554 _111301 P Q c _60115 R _60114).
Proof. exact (MK_COMB (@lem4847484 _111301 P _60115) (@lem4847483 _111301 Q c _60115 R _60114)). Qed.
Lemma lem4847489 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term543 _111301 P Q c _60115 R _60114) = (term554 _111301 P Q c _60115 R _60114).
Proof. exact (TRANS (@lem4847476 _111301 P Q c _60115 R _60114) (@lem4847487 _111301 P Q c _60115 R _60114)). Qed.
Lemma lem4847490 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term554 _111301 P Q c _60115 R _60114.
Proof. exact (EQ_MP (@lem4847489 _111301 P Q c _60115 R _60114) (@lem4847441 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4847492 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term78 _111301 R s.
Proof. exact (proj2 (@lem4847262 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847502 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : (@UNIONS _111301 u) = s.
Proof. exact (proj2 (@lem4847265 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847513 {_111301 : Type'} (P : type180 _111301) (c' : type178 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term546 _111301 P c' R _60117) = (term555 _111301 P c' R _60117).
Proof. exact (@lem4845633 (term160 _111301 P _60117) (term529 _111301 c' _60117) (term22 _111301 R _60117)). Qed.
Lemma lem4847525 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term545 _111301 P Q c' R _60117) = (term556 _111301 P Q c' R _60117).
Proof. exact (@lem4845633 (term160 _111301 P _60117) (term530 _111301 Q c' _60117) (term22 _111301 R _60117)). Qed.
Lemma lem4847527 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : s = (@UNIONS _111301 u).
Proof. exact (SYM (@lem4847502 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847542 {_111301 : Type'} (R : type686 _111301) : (term557 _111301 R) = (term557 _111301 R).
Proof. exact (eq_refl (term557 _111301 R)). Qed.
Lemma lem4847543 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : (term558 _111301 R s) = (term559 _111301 R u).
Proof. exact (MK_COMB (@lem4847542 _111301 R) (@lem4847527 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847544 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) : (term559 _111301 R u) = (term101 _111301 R u).
Proof. exact (eq_refl (term559 _111301 R u)). Qed.
Lemma lem4847545 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (term560 _111301 R s) = (term560 _111301 R s).
Proof. exact (eq_refl (term560 _111301 R s)). Qed.
Lemma lem4847546 {_111301 : Type'} (s : _111301 -> Prop) (R : type686 _111301) (u : type686 _111301) : ((term558 _111301 R s) = (term559 _111301 R u)) = ((term558 _111301 R s) = (term101 _111301 R u)).
Proof. exact (MK_COMB (@lem4847545 _111301 R s) (@lem4847544 _111301 R u)). Qed.
Lemma lem4847547 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (term558 _111301 R s) = (term78 _111301 R s).
Proof. exact (eq_refl (term558 _111301 R s)). Qed.
Lemma lem4847548 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4847549 {_111301 : Type'} (R : type686 _111301) (s : _111301 -> Prop) : (term560 _111301 R s) = (term561 _111301 R s).
Proof. exact (MK_COMB (@lem4847548) (@lem4847547 _111301 R s)). Qed.
Lemma lem4847550 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) : (term101 _111301 R u) = (term101 _111301 R u).
Proof. exact (eq_refl (term101 _111301 R u)). Qed.
Lemma lem4847551 {_111301 : Type'} (s : _111301 -> Prop) (R : type686 _111301) (u : type686 _111301) : ((term558 _111301 R s) = (term101 _111301 R u)) = ((term78 _111301 R s) = (term101 _111301 R u)).
Proof. exact (MK_COMB (@lem4847549 _111301 R s) (@lem4847550 _111301 R u)). Qed.
Lemma lem4847552 {_111301 : Type'} (s : _111301 -> Prop) (R : type686 _111301) (u : type686 _111301) : ((term558 _111301 R s) = (term559 _111301 R u)) = ((term78 _111301 R s) = (term101 _111301 R u)).
Proof. exact (TRANS (@lem4847546 _111301 s R u) (@lem4847551 _111301 s R u)). Qed.
Lemma lem4847553 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : (term78 _111301 R s) = (term101 _111301 R u).
Proof. exact (EQ_MP (@lem4847552 _111301 s R u) (@lem4847543 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847554 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term101 _111301 R u.
Proof. exact (EQ_MP (@lem4847553 _111301 u s P Q c' R h1) (@lem4847492 _111301 u s P Q c' R h1)). Qed.
Lemma lem4847582 {_111301 : Type'} (_60118 : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term42 _111301 u Q _60118.
Proof. exact (EQ_MP (@lem4847439 _111301 u Q _60118) (@lem4847438 _111301 _60118 u s P Q c' R h1)). Qed.
Lemma lem4847596 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term555 _111301 P c' R _60117.
Proof. exact (EQ_MP (@lem4847513 _111301 P c' R _60117) (@lem4847444 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4847610 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term556 _111301 P Q c' R _60117.
Proof. exact (EQ_MP (@lem4847525 _111301 P Q c' R _60117) (@lem4847443 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4847694 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : P t.
Proof. exact (proj1 (@lem4847258 _111301 c P Q R t h1)). Qed.
Lemma lem4847695 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term562 _111301 P t.
Proof. exact (fun h0 : term160 _111301 P t => @lem4847694 _111301 c P Q R t h1). Qed.
Lemma lem4847697 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4847698 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term562 _111301 P t) = (P t).
Proof. exact (@lem4847697 (P t)). Qed.
Lemma lem4847699 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : P t.
Proof. exact (EQ_MP (@lem4847698 _111301 P t) (@lem4847695 _111301 c P Q R t h1)). Qed.
Lemma lem4847701 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : P t.
Proof. exact (proj1 (@lem4847258 _111301 c P Q R t h1)). Qed.
Lemma lem4847702 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term562 _111301 P t.
Proof. exact (fun h0 : term160 _111301 P t => @lem4847701 _111301 c P Q R t h1). Qed.
Lemma lem4847704 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4847705 {_111301 : Type'} (P : type180 _111301) (t : type686 _111301) : (term562 _111301 P t) = (P t).
Proof. exact (@lem4847704 (P t)). Qed.
Lemma lem4847706 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : P t.
Proof. exact (EQ_MP (@lem4847705 _111301 P t) (@lem4847702 _111301 c P Q R t h1)). Qed.
Lemma lem4847708 {_111301 : Type'} (x : _111301 -> Prop) : x = x.
Proof. exact (@lem21386 (_111301 -> Prop) x). Qed.
Lemma lem4847709 {_111301 : Type'} (x : _111301 -> Prop) : x = x.
Proof. exact (@lem4847708 _111301 x). Qed.
Lemma lem4847710 {_111301 : Type'} (t : type686 _111301) : (@UNIONS _111301 t) = (@UNIONS _111301 t).
Proof. exact (@lem4847709 _111301 (@UNIONS _111301 t)). Qed.
Lemma lem4847711 {_111301 : Type'} (t : type686 _111301) : term564 _111301 t.
Proof. exact (fun h0 : term565 _111301 t => @lem4847710 _111301 t). Qed.
Lemma lem4847713 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4847714 {_111301 : Type'} (t : type686 _111301) : (term564 _111301 t) = ((@UNIONS _111301 t) = (@UNIONS _111301 t)).
Proof. exact (@lem4847713 ((@UNIONS _111301 t) = (@UNIONS _111301 t))). Qed.
Lemma lem4847715 {_111301 : Type'} (t : type686 _111301) : (@UNIONS _111301 t) = (@UNIONS _111301 t).
Proof. exact (EQ_MP (@lem4847714 _111301 t) (@lem4847711 _111301 t)). Qed.
Lemma lem4847718 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) : term101 _111301 R t.
Proof. exact (h1). Qed.
Lemma lem4847719 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) : term566 _111301 R t.
Proof. exact (fun h0 : term22 _111301 R t => @lem4847718 _111301 R t h1). Qed.
Lemma lem4847721 (p : Prop) : (term567 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4847722 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term566 _111301 R t) = (term101 _111301 R t).
Proof. exact (@lem4847721 (term22 _111301 R t)). Qed.
Lemma lem4847723 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) : term101 _111301 R t.
Proof. exact (EQ_MP (@lem4847722 _111301 R t) (@lem4847719 _111301 R t h1)). Qed.
Lemma lem4847729 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4847730 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term550 _111301 P c _60115 R _60114) = (term569 _111301 c P _60115 R _60114).
Proof. exact (@lem4847729 (term512 _111301 c _60114 _60115) (term160 _111301 P _60115) (term570 _111301 _60115 R _60114)). Qed.
Lemma lem4847754 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4847755 {_111301 : Type'} (R : type686 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term570 _111301 _60115 R _60114) = (term571 _111301 R _60115 _60114).
Proof. exact (@lem4847754 (R _60114) (term54 _111301 _60115 _60114)). Qed.
Lemma lem4847763 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term62 _111301 P _60115) = (term62 _111301 P _60115).
Proof. exact (eq_refl (term62 _111301 P _60115)). Qed.
Lemma lem4847764 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term572 _111301 P _60115 R _60114) = (term573 _111301 P R _60115 _60114).
Proof. exact (MK_COMB (@lem4847763 _111301 P _60115) (@lem4847755 _111301 R _60115 _60114)). Qed.
Lemma lem4847768 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4847769 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term573 _111301 P R _60115 _60114) = (term574 _111301 R P _60115 _60114).
Proof. exact (@lem4847768 (R _60114) (term160 _111301 P _60115) (term54 _111301 _60115 _60114)). Qed.
Lemma lem4847787 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term572 _111301 P _60115 R _60114) = (term574 _111301 R P _60115 _60114).
Proof. exact (TRANS (@lem4847764 _111301 P R _60115 _60114) (@lem4847769 _111301 R P _60115 _60114)). Qed.
Lemma lem4847788 {_111301 : Type'} (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term575 _111301 c _60114 _60115) = (term575 _111301 c _60114 _60115).
Proof. exact (eq_refl (term575 _111301 c _60114 _60115)). Qed.
Lemma lem4847789 {_111301 : Type'} (c : type598 _111301) (R : type686 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term569 _111301 c P _60115 R _60114) = (term576 _111301 c R P _60115 _60114).
Proof. exact (MK_COMB (@lem4847788 _111301 c _60114 _60115) (@lem4847787 _111301 R P _60115 _60114)). Qed.
Lemma lem4847793 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4847794 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term576 _111301 c R P _60115 _60114) = (term577 _111301 R c P _60115 _60114).
Proof. exact (@lem4847793 (R _60114) (term512 _111301 c _60114 _60115) (term578 _111301 P _60115 _60114)). Qed.
Lemma lem4847822 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term569 _111301 c P _60115 R _60114) = (term577 _111301 R c P _60115 _60114).
Proof. exact (TRANS (@lem4847789 _111301 c R P _60115 _60114) (@lem4847794 _111301 R c P _60115 _60114)). Qed.
Lemma lem4847823 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term550 _111301 P c _60115 R _60114) = (term577 _111301 R c P _60115 _60114).
Proof. exact (TRANS (@lem4847730 _111301 c P _60115 R _60114) (@lem4847822 _111301 R c P _60115 _60114)). Qed.
Lemma lem4847824 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4847825 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term579 _111301 P c _60115 R _60114) = (term580 _111301 R c P _60115 _60114).
Proof. exact (MK_COMB (@lem4847824) (@lem4847823 _111301 R c P _60115 _60114)). Qed.
Lemma lem4847849 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4847850 {_111301 : Type'} (R : type686 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term570 _111301 _60115 R _60114) = (term571 _111301 R _60115 _60114).
Proof. exact (@lem4847849 (R _60114) (term54 _111301 _60115 _60114)). Qed.
Lemma lem4847858 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term62 _111301 P _60115) = (term62 _111301 P _60115).
Proof. exact (eq_refl (term62 _111301 P _60115)). Qed.
Lemma lem4847859 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term572 _111301 P _60115 R _60114) = (term573 _111301 P R _60115 _60114).
Proof. exact (MK_COMB (@lem4847858 _111301 P _60115) (@lem4847850 _111301 R _60115 _60114)). Qed.
Lemma lem4847863 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4847864 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term573 _111301 P R _60115 _60114) = (term574 _111301 R P _60115 _60114).
Proof. exact (@lem4847863 (R _60114) (term160 _111301 P _60115) (term54 _111301 _60115 _60114)). Qed.
Lemma lem4847882 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term572 _111301 P _60115 R _60114) = (term574 _111301 R P _60115 _60114).
Proof. exact (TRANS (@lem4847859 _111301 P R _60115 _60114) (@lem4847864 _111301 R P _60115 _60114)). Qed.
Lemma lem4847883 {_111301 : Type'} (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term575 _111301 c _60114 _60115) = (term575 _111301 c _60114 _60115).
Proof. exact (eq_refl (term575 _111301 c _60114 _60115)). Qed.
Lemma lem4847884 {_111301 : Type'} (c : type598 _111301) (R : type686 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term569 _111301 c P _60115 R _60114) = (term576 _111301 c R P _60115 _60114).
Proof. exact (MK_COMB (@lem4847883 _111301 c _60114 _60115) (@lem4847882 _111301 R P _60115 _60114)). Qed.
Lemma lem4847888 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4847889 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term576 _111301 c R P _60115 _60114) = (term577 _111301 R c P _60115 _60114).
Proof. exact (@lem4847888 (R _60114) (term512 _111301 c _60114 _60115) (term578 _111301 P _60115 _60114)). Qed.
Lemma lem4847917 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term569 _111301 c P _60115 R _60114) = (term577 _111301 R c P _60115 _60114).
Proof. exact (TRANS (@lem4847884 _111301 c R P _60115 _60114) (@lem4847889 _111301 R c P _60115 _60114)). Qed.
Lemma lem4847918 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : ((term550 _111301 P c _60115 R _60114) = (term569 _111301 c P _60115 R _60114)) = ((term577 _111301 R c P _60115 _60114) = (term577 _111301 R c P _60115 _60114)).
Proof. exact (MK_COMB (@lem4847825 _111301 R c P _60115 _60114) (@lem4847917 _111301 R c P _60115 _60114)). Qed.
Lemma lem4847920 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4847921 (x : Prop) : (x = x) = True.
Proof. exact (@lem4847920 Prop x). Qed.
Lemma lem4847922 {_111301 : Type'} (R : type686 _111301) (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : ((term577 _111301 R c P _60115 _60114) = (term577 _111301 R c P _60115 _60114)) = True.
Proof. exact (@lem4847921 (term577 _111301 R c P _60115 _60114)). Qed.
Lemma lem4847923 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : ((term550 _111301 P c _60115 R _60114) = (term569 _111301 c P _60115 R _60114)) = True.
Proof. exact (TRANS (@lem4847918 _111301 R c P _60115 _60114) (@lem4847922 _111301 R c P _60115 _60114)). Qed.
Lemma lem4847924 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : True = ((term550 _111301 P c _60115 R _60114) = (term569 _111301 c P _60115 R _60114)).
Proof. exact (SYM (@lem4847923 _111301 c P _60115 R _60114)). Qed.
Lemma lem4847925 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term550 _111301 P c _60115 R _60114) = (term569 _111301 c P _60115 R _60114).
Proof. exact (EQ_MP (@lem4847924 _111301 c P _60115 R _60114) (@lem0)). Qed.
Lemma lem4847926 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term569 _111301 c P _60115 R _60114.
Proof. exact (EQ_MP (@lem4847925 _111301 c P _60115 R _60114) (@lem4847472 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4847928 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4847929 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term569 _111301 c P _60115 R _60114) = (term582 _111301 P R c _60114 _60115).
Proof. exact (@lem4847928 (term572 _111301 P _60115 R _60114) (term512 _111301 c _60114 _60115)). Qed.
Lemma lem4847931 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4847932 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term585 _111301 P _60115 R _60114) = (term586 _111301 P _60115 R _60114).
Proof. exact (@lem4847931 (term160 _111301 P _60115) (term570 _111301 _60115 R _60114)). Qed.
Lemma lem4847934 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4847935 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term587 _111301 P _60115) = (P _60115).
Proof. exact (@lem4847934 (P _60115)). Qed.
Lemma lem4847936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4847937 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term588 _111301 P _60115) = (term26 _111301 P _60115).
Proof. exact (MK_COMB (@lem4847936) (@lem4847935 _111301 P _60115)). Qed.
Lemma lem4847939 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4847940 {_111301 : Type'} (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term589 _111301 _60115 R _60114) = (term590 _111301 _60115 R _60114).
Proof. exact (@lem4847939 (term54 _111301 _60115 _60114) (R _60114)). Qed.
Lemma lem4847942 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4847943 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term591 _111301 _60115 _60114) = ((@UNIONS _111301 _60115) = _60114).
Proof. exact (@lem4847942 ((@UNIONS _111301 _60115) = _60114)). Qed.
Lemma lem4847944 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4847945 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term592 _111301 _60115 _60114) = (term593 _111301 _60115 _60114).
Proof. exact (MK_COMB (@lem4847944) (@lem4847943 _111301 _60115 _60114)). Qed.
Lemma lem4847946 {_111301 : Type'} (R : type686 _111301) (_60114 : _111301 -> Prop) : (term78 _111301 R _60114) = (term78 _111301 R _60114).
Proof. exact (eq_refl (term78 _111301 R _60114)). Qed.
Lemma lem4847947 {_111301 : Type'} (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term590 _111301 _60115 R _60114) = (term594 _111301 _60115 R _60114).
Proof. exact (MK_COMB (@lem4847945 _111301 _60115 _60114) (@lem4847946 _111301 R _60114)). Qed.
Lemma lem4847948 {_111301 : Type'} (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term589 _111301 _60115 R _60114) = (term594 _111301 _60115 R _60114).
Proof. exact (TRANS (@lem4847940 _111301 _60115 R _60114) (@lem4847947 _111301 _60115 R _60114)). Qed.
Lemma lem4847949 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term586 _111301 P _60115 R _60114) = (term595 _111301 P _60115 R _60114).
Proof. exact (MK_COMB (@lem4847937 _111301 P _60115) (@lem4847948 _111301 _60115 R _60114)). Qed.
Lemma lem4847950 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term585 _111301 P _60115 R _60114) = (term595 _111301 P _60115 R _60114).
Proof. exact (TRANS (@lem4847932 _111301 P _60115 R _60114) (@lem4847949 _111301 P _60115 R _60114)). Qed.
Lemma lem4847951 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4847952 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term596 _111301 P _60115 R _60114) = (term597 _111301 P _60115 R _60114).
Proof. exact (MK_COMB (@lem4847951) (@lem4847950 _111301 P _60115 R _60114)). Qed.
Lemma lem4847953 {_111301 : Type'} (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term512 _111301 c _60114 _60115) = (term512 _111301 c _60114 _60115).
Proof. exact (eq_refl (term512 _111301 c _60114 _60115)). Qed.
Lemma lem4847954 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term582 _111301 P R c _60114 _60115) = (term598 _111301 P R c _60114 _60115).
Proof. exact (MK_COMB (@lem4847952 _111301 P _60115 R _60114) (@lem4847953 _111301 c _60114 _60115)). Qed.
Lemma lem4847955 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term569 _111301 c P _60115 R _60114) = (term598 _111301 P R c _60114 _60115).
Proof. exact (TRANS (@lem4847929 _111301 P R c _60114 _60115) (@lem4847954 _111301 P R c _60114 _60115)). Qed.
Lemma lem4847957 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) : term599 _111301 R t.
Proof. exact (conj (@lem4847715 _111301 t) (@lem4847723 _111301 R t h1)). Qed.
Lemma lem4847958 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term600 _111301 P R t.
Proof. exact (conj (@lem4847706 _111301 c P Q R t h2) (@lem4847957 _111301 R t h1)). Qed.
Lemma lem4847960 {_111301 : Type'} (_60114 : _111301 -> Prop) (_60115 : type686 _111301) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term598 _111301 P R c _60114 _60115.
Proof. exact (EQ_MP (@lem4847955 _111301 P R c _60114 _60115) (@lem4847926 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4847961 {_111301 : Type'} (_60114 : _111301 -> Prop) (_60115 : type686 _111301) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term598 _111301 P R c _60114 _60115.
Proof. exact (@lem4847960 _111301 _60114 _60115 c P Q R t h1). Qed.
Lemma lem4847962 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term601 _111301 P R c t.
Proof. exact (@lem4847961 _111301 (@UNIONS _111301 t) t c P Q R t h1). Qed.
Lemma lem4847965 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term602 _111301 c t.
Proof. exact (@lem4847962 _111301 c P Q R t h2 (@lem4847958 _111301 c P Q R t h1 h2)). Qed.
Lemma lem4847966 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term603 _111301 c t.
Proof. exact (fun h0 : term604 _111301 c t => @lem4847965 _111301 c P Q R t h1 h2). Qed.
Lemma lem4847968 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4847969 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) : (term603 _111301 c t) = (term602 _111301 c t).
Proof. exact (@lem4847968 (term602 _111301 c t)). Qed.
Lemma lem4847970 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term602 _111301 c t.
Proof. exact (EQ_MP (@lem4847969 _111301 c t) (@lem4847966 _111301 c P Q R t h1 h2)). Qed.
Lemma lem4847976 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4847977 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : (term42 _111301 t Q _60116) = (term605 _111301 Q _60116 t).
Proof. exact (@lem4847976 (Q _60116) (term606 _111301 _60116 t)). Qed.
Lemma lem4847983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4847984 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : (term607 _111301 t Q _60116) = (term608 _111301 Q _60116 t).
Proof. exact (MK_COMB (@lem4847983) (@lem4847977 _111301 Q _60116 t)). Qed.
Lemma lem4847990 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : (term605 _111301 Q _60116 t) = (term605 _111301 Q _60116 t).
Proof. exact (eq_refl (term605 _111301 Q _60116 t)). Qed.
Lemma lem4847991 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : ((term42 _111301 t Q _60116) = (term605 _111301 Q _60116 t)) = ((term605 _111301 Q _60116 t) = (term605 _111301 Q _60116 t)).
Proof. exact (MK_COMB (@lem4847984 _111301 Q _60116 t) (@lem4847990 _111301 Q _60116 t)). Qed.
Lemma lem4847993 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4847994 (x : Prop) : (x = x) = True.
Proof. exact (@lem4847993 Prop x). Qed.
Lemma lem4847995 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : ((term605 _111301 Q _60116 t) = (term605 _111301 Q _60116 t)) = True.
Proof. exact (@lem4847994 (term605 _111301 Q _60116 t)). Qed.
Lemma lem4847996 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : ((term42 _111301 t Q _60116) = (term605 _111301 Q _60116 t)) = True.
Proof. exact (TRANS (@lem4847991 _111301 Q _60116 t) (@lem4847995 _111301 Q _60116 t)). Qed.
Lemma lem4847997 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : True = ((term42 _111301 t Q _60116) = (term605 _111301 Q _60116 t)).
Proof. exact (SYM (@lem4847996 _111301 Q _60116 t)). Qed.
Lemma lem4847998 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) (t : type686 _111301) : (term42 _111301 t Q _60116) = (term605 _111301 Q _60116 t).
Proof. exact (EQ_MP (@lem4847997 _111301 Q _60116 t) (@lem0)). Qed.
Lemma lem4847999 {_111301 : Type'} (_60116 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term605 _111301 Q _60116 t.
Proof. exact (EQ_MP (@lem4847998 _111301 Q _60116 t) (@lem4847454 _111301 _60116 c P Q R t h1)). Qed.
Lemma lem4848001 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4848002 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (_60116 : _111301 -> Prop) : (term605 _111301 Q _60116 t) = (term609 _111301 t Q _60116).
Proof. exact (@lem4848001 (term606 _111301 _60116 t) (Q _60116)). Qed.
Lemma lem4848004 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848005 {_111301 : Type'} (_60116 : _111301 -> Prop) (t : type686 _111301) : (term610 _111301 _60116 t) = (@IN (_111301 -> Prop) _60116 t).
Proof. exact (@lem4848004 (@IN (_111301 -> Prop) _60116 t)). Qed.
Lemma lem4848006 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848007 {_111301 : Type'} (_60116 : _111301 -> Prop) (t : type686 _111301) : (term611 _111301 _60116 t) = (term612 _111301 _60116 t).
Proof. exact (MK_COMB (@lem4848006) (@lem4848005 _111301 _60116 t)). Qed.
Lemma lem4848008 {_111301 : Type'} (Q : type686 _111301) (_60116 : _111301 -> Prop) : (Q _60116) = (Q _60116).
Proof. exact (eq_refl (Q _60116)). Qed.
Lemma lem4848009 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (_60116 : _111301 -> Prop) : (term609 _111301 t Q _60116) = (term23 _111301 t Q _60116).
Proof. exact (MK_COMB (@lem4848007 _111301 _60116 t) (@lem4848008 _111301 Q _60116)). Qed.
Lemma lem4848010 {_111301 : Type'} (t : type686 _111301) (Q : type686 _111301) (_60116 : _111301 -> Prop) : (term605 _111301 Q _60116 t) = (term23 _111301 t Q _60116).
Proof. exact (TRANS (@lem4848002 _111301 t Q _60116) (@lem4848009 _111301 t Q _60116)). Qed.
Lemma lem4848013 {_111301 : Type'} (_60116 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term23 _111301 t Q _60116.
Proof. exact (EQ_MP (@lem4848010 _111301 t Q _60116) (@lem4847999 _111301 _60116 c P Q R t h1)). Qed.
Lemma lem4848014 {_111301 : Type'} (_60116 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term23 _111301 t Q _60116.
Proof. exact (@lem4848013 _111301 _60116 c P Q R t h1). Qed.
Lemma lem4848015 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term613 _111301 Q c t.
Proof. exact (@lem4848014 _111301 (term614 _111301 c t) c P Q R t h1). Qed.
Lemma lem4848018 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term615 _111301 Q c t.
Proof. exact (@lem4848015 _111301 c P Q R t h2 (@lem4847970 _111301 c P Q R t h1 h2)). Qed.
Lemma lem4848019 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term616 _111301 Q c t.
Proof. exact (fun h0 : term617 _111301 Q c t => @lem4848018 _111301 c P Q R t h1 h2). Qed.
Lemma lem4848021 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848022 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (t : type686 _111301) : (term616 _111301 Q c t) = (term615 _111301 Q c t).
Proof. exact (@lem4848021 (term615 _111301 Q c t)). Qed.
Lemma lem4848023 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term615 _111301 Q c t.
Proof. exact (EQ_MP (@lem4848022 _111301 Q c t) (@lem4848019 _111301 c P Q R t h1 h2)). Qed.
Lemma lem4848025 {_111301 : Type'} (x : _111301 -> Prop) : x = x.
Proof. exact (@lem21386 (_111301 -> Prop) x). Qed.
Lemma lem4848026 {_111301 : Type'} (x : _111301 -> Prop) : x = x.
Proof. exact (@lem4848025 _111301 x). Qed.
Lemma lem4848027 {_111301 : Type'} (t : type686 _111301) : (@UNIONS _111301 t) = (@UNIONS _111301 t).
Proof. exact (@lem4848026 _111301 (@UNIONS _111301 t)). Qed.
Lemma lem4848028 {_111301 : Type'} (t : type686 _111301) : term564 _111301 t.
Proof. exact (fun h0 : term565 _111301 t => @lem4848027 _111301 t). Qed.
Lemma lem4848030 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848031 {_111301 : Type'} (t : type686 _111301) : (term564 _111301 t) = ((@UNIONS _111301 t) = (@UNIONS _111301 t)).
Proof. exact (@lem4848030 ((@UNIONS _111301 t) = (@UNIONS _111301 t))). Qed.
Lemma lem4848032 {_111301 : Type'} (t : type686 _111301) : (@UNIONS _111301 t) = (@UNIONS _111301 t).
Proof. exact (EQ_MP (@lem4848031 _111301 t) (@lem4848028 _111301 t)). Qed.
Lemma lem4848058 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4848059 {_111301 : Type'} (R : type686 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term570 _111301 _60115 R _60114) = (term571 _111301 R _60115 _60114).
Proof. exact (@lem4848058 (R _60114) (term54 _111301 _60115 _60114)). Qed.
Lemma lem4848067 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term618 _111301 Q c _60114 _60115) = (term618 _111301 Q c _60114 _60115).
Proof. exact (eq_refl (term618 _111301 Q c _60114 _60115)). Qed.
Lemma lem4848068 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (R : type686 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term553 _111301 Q c _60115 R _60114) = (term619 _111301 Q c R _60115 _60114).
Proof. exact (MK_COMB (@lem4848067 _111301 Q c _60114 _60115) (@lem4848059 _111301 R _60115 _60114)). Qed.
Lemma lem4848072 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4848073 {_111301 : Type'} (R : type686 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term619 _111301 Q c R _60115 _60114) = (term620 _111301 R Q c _60115 _60114).
Proof. exact (@lem4848072 (R _60114) (term513 _111301 Q c _60114 _60115) (term54 _111301 _60115 _60114)). Qed.
Lemma lem4848091 {_111301 : Type'} (R : type686 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term553 _111301 Q c _60115 R _60114) = (term620 _111301 R Q c _60115 _60114).
Proof. exact (TRANS (@lem4848068 _111301 Q c R _60115 _60114) (@lem4848073 _111301 R Q c _60115 _60114)). Qed.
Lemma lem4848092 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term62 _111301 P _60115) = (term62 _111301 P _60115).
Proof. exact (eq_refl (term62 _111301 P _60115)). Qed.
Lemma lem4848093 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term554 _111301 P Q c _60115 R _60114) = (term621 _111301 P R Q c _60115 _60114).
Proof. exact (MK_COMB (@lem4848092 _111301 P _60115) (@lem4848091 _111301 R Q c _60115 _60114)). Qed.
Lemma lem4848097 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4848098 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term621 _111301 P R Q c _60115 _60114) = (term622 _111301 R P Q c _60115 _60114).
Proof. exact (@lem4848097 (R _60114) (term160 _111301 P _60115) (term517 _111301 Q c _60115 _60114)). Qed.
Lemma lem4848126 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term554 _111301 P Q c _60115 R _60114) = (term622 _111301 R P Q c _60115 _60114).
Proof. exact (TRANS (@lem4848093 _111301 P R Q c _60115 _60114) (@lem4848098 _111301 R P Q c _60115 _60114)). Qed.
Lemma lem4848127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4848128 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term623 _111301 P Q c _60115 R _60114) = (term624 _111301 R P Q c _60115 _60114).
Proof. exact (MK_COMB (@lem4848127) (@lem4848126 _111301 R P Q c _60115 _60114)). Qed.
Lemma lem4848156 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term622 _111301 R P Q c _60115 _60114) = (term622 _111301 R P Q c _60115 _60114).
Proof. exact (eq_refl (term622 _111301 R P Q c _60115 _60114)). Qed.
Lemma lem4848157 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : ((term554 _111301 P Q c _60115 R _60114) = (term622 _111301 R P Q c _60115 _60114)) = ((term622 _111301 R P Q c _60115 _60114) = (term622 _111301 R P Q c _60115 _60114)).
Proof. exact (MK_COMB (@lem4848128 _111301 R P Q c _60115 _60114) (@lem4848156 _111301 R P Q c _60115 _60114)). Qed.
Lemma lem4848159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4848160 (x : Prop) : (x = x) = True.
Proof. exact (@lem4848159 Prop x). Qed.
Lemma lem4848161 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : ((term622 _111301 R P Q c _60115 _60114) = (term622 _111301 R P Q c _60115 _60114)) = True.
Proof. exact (@lem4848160 (term622 _111301 R P Q c _60115 _60114)). Qed.
Lemma lem4848162 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : ((term554 _111301 P Q c _60115 R _60114) = (term622 _111301 R P Q c _60115 _60114)) = True.
Proof. exact (TRANS (@lem4848157 _111301 R P Q c _60115 _60114) (@lem4848161 _111301 R P Q c _60115 _60114)). Qed.
Lemma lem4848163 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : True = ((term554 _111301 P Q c _60115 R _60114) = (term622 _111301 R P Q c _60115 _60114)).
Proof. exact (SYM (@lem4848162 _111301 R P Q c _60115 _60114)). Qed.
Lemma lem4848164 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term554 _111301 P Q c _60115 R _60114) = (term622 _111301 R P Q c _60115 _60114).
Proof. exact (EQ_MP (@lem4848163 _111301 R P Q c _60115 _60114) (@lem0)). Qed.
Lemma lem4848165 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term622 _111301 R P Q c _60115 _60114.
Proof. exact (EQ_MP (@lem4848164 _111301 R P Q c _60115 _60114) (@lem4847490 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4848167 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4848168 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term622 _111301 R P Q c _60115 _60114) = (term625 _111301 P Q c _60115 R _60114).
Proof. exact (@lem4848167 (term522 _111301 P Q c _60115 _60114) (R _60114)). Qed.
Lemma lem4848170 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4848171 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term626 _111301 P Q c _60115 _60114) = (term627 _111301 P Q c _60115 _60114).
Proof. exact (@lem4848170 (term160 _111301 P _60115) (term517 _111301 Q c _60115 _60114)). Qed.
Lemma lem4848173 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848174 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term587 _111301 P _60115) = (P _60115).
Proof. exact (@lem4848173 (P _60115)). Qed.
Lemma lem4848175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4848176 {_111301 : Type'} (P : type180 _111301) (_60115 : type686 _111301) : (term588 _111301 P _60115) = (term26 _111301 P _60115).
Proof. exact (MK_COMB (@lem4848175) (@lem4848174 _111301 P _60115)). Qed.
Lemma lem4848178 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4848179 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term628 _111301 Q c _60115 _60114) = (term629 _111301 Q c _60115 _60114).
Proof. exact (@lem4848178 (term513 _111301 Q c _60114 _60115) (term54 _111301 _60115 _60114)). Qed.
Lemma lem4848181 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848182 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term630 _111301 Q c _60114 _60115) = (term631 _111301 Q c _60114 _60115).
Proof. exact (@lem4848181 (term631 _111301 Q c _60114 _60115)). Qed.
Lemma lem4848183 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4848184 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (_60114 : _111301 -> Prop) (_60115 : type686 _111301) : (term632 _111301 Q c _60114 _60115) = (term633 _111301 Q c _60114 _60115).
Proof. exact (MK_COMB (@lem4848183) (@lem4848182 _111301 Q c _60114 _60115)). Qed.
Lemma lem4848186 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848187 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term591 _111301 _60115 _60114) = ((@UNIONS _111301 _60115) = _60114).
Proof. exact (@lem4848186 ((@UNIONS _111301 _60115) = _60114)). Qed.
Lemma lem4848188 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term629 _111301 Q c _60115 _60114) = (term634 _111301 Q c _60115 _60114).
Proof. exact (MK_COMB (@lem4848184 _111301 Q c _60114 _60115) (@lem4848187 _111301 _60115 _60114)). Qed.
Lemma lem4848189 {_111301 : Type'} (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term628 _111301 Q c _60115 _60114) = (term634 _111301 Q c _60115 _60114).
Proof. exact (TRANS (@lem4848179 _111301 Q c _60115 _60114) (@lem4848188 _111301 Q c _60115 _60114)). Qed.
Lemma lem4848190 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term627 _111301 P Q c _60115 _60114) = (term635 _111301 P Q c _60115 _60114).
Proof. exact (MK_COMB (@lem4848176 _111301 P _60115) (@lem4848189 _111301 Q c _60115 _60114)). Qed.
Lemma lem4848191 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term626 _111301 P Q c _60115 _60114) = (term635 _111301 P Q c _60115 _60114).
Proof. exact (TRANS (@lem4848171 _111301 P Q c _60115 _60114) (@lem4848190 _111301 P Q c _60115 _60114)). Qed.
Lemma lem4848192 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848193 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (_60114 : _111301 -> Prop) : (term636 _111301 P Q c _60115 _60114) = (term637 _111301 P Q c _60115 _60114).
Proof. exact (MK_COMB (@lem4848192) (@lem4848191 _111301 P Q c _60115 _60114)). Qed.
Lemma lem4848194 {_111301 : Type'} (R : type686 _111301) (_60114 : _111301 -> Prop) : (R _60114) = (R _60114).
Proof. exact (eq_refl (R _60114)). Qed.
Lemma lem4848195 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term625 _111301 P Q c _60115 R _60114) = (term638 _111301 P Q c _60115 R _60114).
Proof. exact (MK_COMB (@lem4848193 _111301 P Q c _60115 _60114) (@lem4848194 _111301 R _60114)). Qed.
Lemma lem4848196 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c : type598 _111301) (_60115 : type686 _111301) (R : type686 _111301) (_60114 : _111301 -> Prop) : (term622 _111301 R P Q c _60115 _60114) = (term638 _111301 P Q c _60115 R _60114).
Proof. exact (TRANS (@lem4848168 _111301 P Q c _60115 R _60114) (@lem4848195 _111301 P Q c _60115 R _60114)). Qed.
Lemma lem4848198 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term639 _111301 Q c t.
Proof. exact (conj (@lem4848023 _111301 c P Q R t h1 h2) (@lem4848032 _111301 t)). Qed.
Lemma lem4848199 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term640 _111301 P Q c t.
Proof. exact (conj (@lem4847699 _111301 c P Q R t h2) (@lem4848198 _111301 c P Q R t h1 h2)). Qed.
Lemma lem4848201 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term638 _111301 P Q c _60115 R _60114.
Proof. exact (EQ_MP (@lem4848196 _111301 P Q c _60115 R _60114) (@lem4848165 _111301 _60115 _60114 c P Q R t h1)). Qed.
Lemma lem4848202 {_111301 : Type'} (_60115 : type686 _111301) (_60114 : _111301 -> Prop) (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term638 _111301 P Q c _60115 R _60114.
Proof. exact (@lem4848201 _111301 _60115 _60114 c P Q R t h1). Qed.
Lemma lem4848203 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term641 _111301 P Q c R t.
Proof. exact (@lem4848202 _111301 t (@UNIONS _111301 t) c P Q R t h1). Qed.
Lemma lem4848206 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term101 _111301 R t) (h2 : term275 _111301 c P Q R t) : term22 _111301 R t.
Proof. exact (@lem4848203 _111301 c P Q R t h2 (@lem4848199 _111301 c P Q R t h1 h2)). Qed.
Lemma lem4848207 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term642 _111301 R t.
Proof. exact (fun h0 : term101 _111301 R t => @lem4848206 _111301 c P Q R t h0 h1). Qed.
Lemma lem4848209 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848210 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term642 _111301 R t) = (term22 _111301 R t).
Proof. exact (@lem4848209 (term22 _111301 R t)). Qed.
Lemma lem4848211 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term22 _111301 R t.
Proof. exact (EQ_MP (@lem4848210 _111301 R t) (@lem4848207 _111301 c P Q R t h1)). Qed.
Lemma lem4848214 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4848216 {_111301 : Type'} (R : type686 _111301) (t : type686 _111301) : (term101 _111301 R t) = (term643 _111301 R t).
Proof. exact (@lem4848214 (term22 _111301 R t)). Qed.
Lemma lem4848219 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term643 _111301 R t.
Proof. exact (EQ_MP (@lem4848216 _111301 R t) (@lem4847446 _111301 c P Q R t h1)). Qed.
Lemma lem4848222 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : False.
Proof. exact (@lem4848219 _111301 c P Q R t h1 (@lem4848211 _111301 c P Q R t h1)). Qed.
Lemma lem4848223 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : term644.
Proof. exact (fun h0 : ~ False => @lem4848222 _111301 c P Q R t h1). Qed.
Lemma lem4848225 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848226 : term644 = False.
Proof. exact (@lem4848225 False). Qed.
Lemma lem4848227 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (t : type686 _111301) (h1 : term275 _111301 c P Q R t) : False.
Proof. exact (EQ_MP (@lem4848226) (@lem4848223 _111301 c P Q R t h1)). Qed.
Lemma lem4848229 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : P u.
Proof. exact (proj1 (@lem4847264 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848230 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term562 _111301 P u.
Proof. exact (fun h0 : term160 _111301 P u => @lem4848229 _111301 u s P Q c' R h1). Qed.
Lemma lem4848232 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848233 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term562 _111301 P u) = (P u).
Proof. exact (@lem4848232 (P u)). Qed.
Lemma lem4848234 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : P u.
Proof. exact (EQ_MP (@lem4848233 _111301 P u) (@lem4848230 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848236 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : P u.
Proof. exact (proj1 (@lem4847264 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848237 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term562 _111301 P u.
Proof. exact (fun h0 : term160 _111301 P u => @lem4848236 _111301 u s P Q c' R h1). Qed.
Lemma lem4848239 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848240 {_111301 : Type'} (P : type180 _111301) (u : type686 _111301) : (term562 _111301 P u) = (P u).
Proof. exact (@lem4848239 (P u)). Qed.
Lemma lem4848241 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : P u.
Proof. exact (EQ_MP (@lem4848240 _111301 P u) (@lem4848237 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848244 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) (h1 : term101 _111301 R u) : term101 _111301 R u.
Proof. exact (h1). Qed.
Lemma lem4848245 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) (h1 : term101 _111301 R u) : term566 _111301 R u.
Proof. exact (fun h0 : term22 _111301 R u => @lem4848244 _111301 R u h1). Qed.
Lemma lem4848247 (p : Prop) : (term567 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4848248 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) : (term566 _111301 R u) = (term101 _111301 R u).
Proof. exact (@lem4848247 (term22 _111301 R u)). Qed.
Lemma lem4848249 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) (h1 : term101 _111301 R u) : term101 _111301 R u.
Proof. exact (EQ_MP (@lem4848248 _111301 R u) (@lem4848245 _111301 R u h1)). Qed.
Lemma lem4848255 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4848256 {_111301 : Type'} (c' : type178 _111301) (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term555 _111301 P c' R _60117) = (term645 _111301 c' P R _60117).
Proof. exact (@lem4848255 (term529 _111301 c' _60117) (term160 _111301 P _60117) (term22 _111301 R _60117)). Qed.
Lemma lem4848270 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4848271 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term646 _111301 P R _60117) = (term647 _111301 R P _60117).
Proof. exact (@lem4848270 (term22 _111301 R _60117) (term160 _111301 P _60117)). Qed.
Lemma lem4848277 {_111301 : Type'} (c' : type178 _111301) (_60117 : type686 _111301) : (term648 _111301 c' _60117) = (term648 _111301 c' _60117).
Proof. exact (eq_refl (term648 _111301 c' _60117)). Qed.
Lemma lem4848278 {_111301 : Type'} (c' : type178 _111301) (R : type686 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term645 _111301 c' P R _60117) = (term649 _111301 c' R P _60117).
Proof. exact (MK_COMB (@lem4848277 _111301 c' _60117) (@lem4848271 _111301 R P _60117)). Qed.
Lemma lem4848282 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4848283 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term649 _111301 c' R P _60117) = (term650 _111301 R c' P _60117).
Proof. exact (@lem4848282 (term22 _111301 R _60117) (term529 _111301 c' _60117) (term160 _111301 P _60117)). Qed.
Lemma lem4848299 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term645 _111301 c' P R _60117) = (term650 _111301 R c' P _60117).
Proof. exact (TRANS (@lem4848278 _111301 c' R P _60117) (@lem4848283 _111301 R c' P _60117)). Qed.
Lemma lem4848300 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term555 _111301 P c' R _60117) = (term650 _111301 R c' P _60117).
Proof. exact (TRANS (@lem4848256 _111301 c' P R _60117) (@lem4848299 _111301 R c' P _60117)). Qed.
Lemma lem4848301 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4848302 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term651 _111301 P c' R _60117) = (term652 _111301 R c' P _60117).
Proof. exact (MK_COMB (@lem4848301) (@lem4848300 _111301 R c' P _60117)). Qed.
Lemma lem4848316 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4848317 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term646 _111301 P R _60117) = (term647 _111301 R P _60117).
Proof. exact (@lem4848316 (term22 _111301 R _60117) (term160 _111301 P _60117)). Qed.
Lemma lem4848323 {_111301 : Type'} (c' : type178 _111301) (_60117 : type686 _111301) : (term648 _111301 c' _60117) = (term648 _111301 c' _60117).
Proof. exact (eq_refl (term648 _111301 c' _60117)). Qed.
Lemma lem4848324 {_111301 : Type'} (c' : type178 _111301) (R : type686 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term645 _111301 c' P R _60117) = (term649 _111301 c' R P _60117).
Proof. exact (MK_COMB (@lem4848323 _111301 c' _60117) (@lem4848317 _111301 R P _60117)). Qed.
Lemma lem4848328 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4848329 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term649 _111301 c' R P _60117) = (term650 _111301 R c' P _60117).
Proof. exact (@lem4848328 (term22 _111301 R _60117) (term529 _111301 c' _60117) (term160 _111301 P _60117)). Qed.
Lemma lem4848345 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : (term645 _111301 c' P R _60117) = (term650 _111301 R c' P _60117).
Proof. exact (TRANS (@lem4848324 _111301 c' R P _60117) (@lem4848329 _111301 R c' P _60117)). Qed.
Lemma lem4848346 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : ((term555 _111301 P c' R _60117) = (term645 _111301 c' P R _60117)) = ((term650 _111301 R c' P _60117) = (term650 _111301 R c' P _60117)).
Proof. exact (MK_COMB (@lem4848302 _111301 R c' P _60117) (@lem4848345 _111301 R c' P _60117)). Qed.
Lemma lem4848348 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4848349 (x : Prop) : (x = x) = True.
Proof. exact (@lem4848348 Prop x). Qed.
Lemma lem4848350 {_111301 : Type'} (R : type686 _111301) (c' : type178 _111301) (P : type180 _111301) (_60117 : type686 _111301) : ((term650 _111301 R c' P _60117) = (term650 _111301 R c' P _60117)) = True.
Proof. exact (@lem4848349 (term650 _111301 R c' P _60117)). Qed.
Lemma lem4848351 {_111301 : Type'} (c' : type178 _111301) (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : ((term555 _111301 P c' R _60117) = (term645 _111301 c' P R _60117)) = True.
Proof. exact (TRANS (@lem4848346 _111301 R c' P _60117) (@lem4848350 _111301 R c' P _60117)). Qed.
Lemma lem4848352 {_111301 : Type'} (c' : type178 _111301) (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : True = ((term555 _111301 P c' R _60117) = (term645 _111301 c' P R _60117)).
Proof. exact (SYM (@lem4848351 _111301 c' P R _60117)). Qed.
Lemma lem4848353 {_111301 : Type'} (c' : type178 _111301) (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term555 _111301 P c' R _60117) = (term645 _111301 c' P R _60117).
Proof. exact (EQ_MP (@lem4848352 _111301 c' P R _60117) (@lem0)). Qed.
Lemma lem4848354 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term645 _111301 c' P R _60117.
Proof. exact (EQ_MP (@lem4848353 _111301 c' P R _60117) (@lem4847596 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4848356 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4848357 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term645 _111301 c' P R _60117) = (term653 _111301 P R c' _60117).
Proof. exact (@lem4848356 (term646 _111301 P R _60117) (term529 _111301 c' _60117)). Qed.
Lemma lem4848359 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4848360 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term654 _111301 P R _60117) = (term655 _111301 P R _60117).
Proof. exact (@lem4848359 (term160 _111301 P _60117) (term22 _111301 R _60117)). Qed.
Lemma lem4848362 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848363 {_111301 : Type'} (P : type180 _111301) (_60117 : type686 _111301) : (term587 _111301 P _60117) = (P _60117).
Proof. exact (@lem4848362 (P _60117)). Qed.
Lemma lem4848364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4848365 {_111301 : Type'} (P : type180 _111301) (_60117 : type686 _111301) : (term588 _111301 P _60117) = (term26 _111301 P _60117).
Proof. exact (MK_COMB (@lem4848364) (@lem4848363 _111301 P _60117)). Qed.
Lemma lem4848366 {_111301 : Type'} (R : type686 _111301) (_60117 : type686 _111301) : (term101 _111301 R _60117) = (term101 _111301 R _60117).
Proof. exact (eq_refl (term101 _111301 R _60117)). Qed.
Lemma lem4848367 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term655 _111301 P R _60117) = (term656 _111301 P R _60117).
Proof. exact (MK_COMB (@lem4848365 _111301 P _60117) (@lem4848366 _111301 R _60117)). Qed.
Lemma lem4848368 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term654 _111301 P R _60117) = (term656 _111301 P R _60117).
Proof. exact (TRANS (@lem4848360 _111301 P R _60117) (@lem4848367 _111301 P R _60117)). Qed.
Lemma lem4848369 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848370 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term657 _111301 P R _60117) = (term658 _111301 P R _60117).
Proof. exact (MK_COMB (@lem4848369) (@lem4848368 _111301 P R _60117)). Qed.
Lemma lem4848371 {_111301 : Type'} (c' : type178 _111301) (_60117 : type686 _111301) : (term529 _111301 c' _60117) = (term529 _111301 c' _60117).
Proof. exact (eq_refl (term529 _111301 c' _60117)). Qed.
Lemma lem4848372 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term653 _111301 P R c' _60117) = (term659 _111301 P R c' _60117).
Proof. exact (MK_COMB (@lem4848370 _111301 P R _60117) (@lem4848371 _111301 c' _60117)). Qed.
Lemma lem4848373 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term645 _111301 c' P R _60117) = (term659 _111301 P R c' _60117).
Proof. exact (TRANS (@lem4848357 _111301 P R c' _60117) (@lem4848372 _111301 P R c' _60117)). Qed.
Lemma lem4848375 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term656 _111301 P R u.
Proof. exact (conj (@lem4848241 _111301 u s P Q c' R h2) (@lem4848249 _111301 R u h1)). Qed.
Lemma lem4848377 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term659 _111301 P R c' _60117.
Proof. exact (EQ_MP (@lem4848373 _111301 P R c' _60117) (@lem4848354 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4848378 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term659 _111301 P R c' _60117.
Proof. exact (@lem4848377 _111301 _60117 u s P Q c' R h1). Qed.
Lemma lem4848379 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term659 _111301 P R c' u.
Proof. exact (@lem4848378 _111301 u u s P Q c' R h1). Qed.
Lemma lem4848382 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term529 _111301 c' u.
Proof. exact (@lem4848379 _111301 u s P Q c' R h2 (@lem4848375 _111301 u s P Q c' R h1 h2)). Qed.
Lemma lem4848383 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term660 _111301 c' u.
Proof. exact (fun h0 : term661 _111301 c' u => @lem4848382 _111301 u s P Q c' R h1 h2). Qed.
Lemma lem4848385 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848386 {_111301 : Type'} (c' : type178 _111301) (u : type686 _111301) : (term660 _111301 c' u) = (term529 _111301 c' u).
Proof. exact (@lem4848385 (term529 _111301 c' u)). Qed.
Lemma lem4848387 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term529 _111301 c' u.
Proof. exact (EQ_MP (@lem4848386 _111301 c' u) (@lem4848383 _111301 u s P Q c' R h1 h2)). Qed.
Lemma lem4848393 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4848394 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : (term42 _111301 u Q _60118) = (term605 _111301 Q _60118 u).
Proof. exact (@lem4848393 (Q _60118) (term606 _111301 _60118 u)). Qed.
Lemma lem4848400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4848401 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : (term607 _111301 u Q _60118) = (term608 _111301 Q _60118 u).
Proof. exact (MK_COMB (@lem4848400) (@lem4848394 _111301 Q _60118 u)). Qed.
Lemma lem4848407 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : (term605 _111301 Q _60118 u) = (term605 _111301 Q _60118 u).
Proof. exact (eq_refl (term605 _111301 Q _60118 u)). Qed.
Lemma lem4848408 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : ((term42 _111301 u Q _60118) = (term605 _111301 Q _60118 u)) = ((term605 _111301 Q _60118 u) = (term605 _111301 Q _60118 u)).
Proof. exact (MK_COMB (@lem4848401 _111301 Q _60118 u) (@lem4848407 _111301 Q _60118 u)). Qed.
Lemma lem4848410 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4848411 (x : Prop) : (x = x) = True.
Proof. exact (@lem4848410 Prop x). Qed.
Lemma lem4848412 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : ((term605 _111301 Q _60118 u) = (term605 _111301 Q _60118 u)) = True.
Proof. exact (@lem4848411 (term605 _111301 Q _60118 u)). Qed.
Lemma lem4848413 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : ((term42 _111301 u Q _60118) = (term605 _111301 Q _60118 u)) = True.
Proof. exact (TRANS (@lem4848408 _111301 Q _60118 u) (@lem4848412 _111301 Q _60118 u)). Qed.
Lemma lem4848414 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : True = ((term42 _111301 u Q _60118) = (term605 _111301 Q _60118 u)).
Proof. exact (SYM (@lem4848413 _111301 Q _60118 u)). Qed.
Lemma lem4848415 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) (u : type686 _111301) : (term42 _111301 u Q _60118) = (term605 _111301 Q _60118 u).
Proof. exact (EQ_MP (@lem4848414 _111301 Q _60118 u) (@lem0)). Qed.
Lemma lem4848416 {_111301 : Type'} (_60118 : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term605 _111301 Q _60118 u.
Proof. exact (EQ_MP (@lem4848415 _111301 Q _60118 u) (@lem4847582 _111301 _60118 u s P Q c' R h1)). Qed.
Lemma lem4848418 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4848419 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (_60118 : _111301 -> Prop) : (term605 _111301 Q _60118 u) = (term609 _111301 u Q _60118).
Proof. exact (@lem4848418 (term606 _111301 _60118 u) (Q _60118)). Qed.
Lemma lem4848421 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848422 {_111301 : Type'} (_60118 : _111301 -> Prop) (u : type686 _111301) : (term610 _111301 _60118 u) = (@IN (_111301 -> Prop) _60118 u).
Proof. exact (@lem4848421 (@IN (_111301 -> Prop) _60118 u)). Qed.
Lemma lem4848423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848424 {_111301 : Type'} (_60118 : _111301 -> Prop) (u : type686 _111301) : (term611 _111301 _60118 u) = (term612 _111301 _60118 u).
Proof. exact (MK_COMB (@lem4848423) (@lem4848422 _111301 _60118 u)). Qed.
Lemma lem4848425 {_111301 : Type'} (Q : type686 _111301) (_60118 : _111301 -> Prop) : (Q _60118) = (Q _60118).
Proof. exact (eq_refl (Q _60118)). Qed.
Lemma lem4848426 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (_60118 : _111301 -> Prop) : (term609 _111301 u Q _60118) = (term23 _111301 u Q _60118).
Proof. exact (MK_COMB (@lem4848424 _111301 _60118 u) (@lem4848425 _111301 Q _60118)). Qed.
Lemma lem4848427 {_111301 : Type'} (u : type686 _111301) (Q : type686 _111301) (_60118 : _111301 -> Prop) : (term605 _111301 Q _60118 u) = (term23 _111301 u Q _60118).
Proof. exact (TRANS (@lem4848419 _111301 u Q _60118) (@lem4848426 _111301 u Q _60118)). Qed.
Lemma lem4848430 {_111301 : Type'} (_60118 : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term23 _111301 u Q _60118.
Proof. exact (EQ_MP (@lem4848427 _111301 u Q _60118) (@lem4848416 _111301 _60118 u s P Q c' R h1)). Qed.
Lemma lem4848431 {_111301 : Type'} (_60118 : _111301 -> Prop) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term23 _111301 u Q _60118.
Proof. exact (@lem4848430 _111301 _60118 u s P Q c' R h1). Qed.
Lemma lem4848432 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term662 _111301 Q c' u.
Proof. exact (@lem4848431 _111301 (c' u) u s P Q c' R h1). Qed.
Lemma lem4848435 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term663 _111301 Q c' u.
Proof. exact (@lem4848432 _111301 u s P Q c' R h2 (@lem4848387 _111301 u s P Q c' R h1 h2)). Qed.
Lemma lem4848436 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term664 _111301 Q c' u.
Proof. exact (fun h0 : term530 _111301 Q c' u => @lem4848435 _111301 u s P Q c' R h1 h2). Qed.
Lemma lem4848438 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848439 {_111301 : Type'} (Q : type686 _111301) (c' : type178 _111301) (u : type686 _111301) : (term664 _111301 Q c' u) = (term663 _111301 Q c' u).
Proof. exact (@lem4848438 (term663 _111301 Q c' u)). Qed.
Lemma lem4848440 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term663 _111301 Q c' u.
Proof. exact (EQ_MP (@lem4848439 _111301 Q c' u) (@lem4848436 _111301 u s P Q c' R h1 h2)). Qed.
Lemma lem4848456 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4848457 {_111301 : Type'} (R : type686 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term665 _111301 Q c' R _60117) = (term666 _111301 R Q c' _60117).
Proof. exact (@lem4848456 (term22 _111301 R _60117) (term530 _111301 Q c' _60117)). Qed.
Lemma lem4848463 {_111301 : Type'} (P : type180 _111301) (_60117 : type686 _111301) : (term62 _111301 P _60117) = (term62 _111301 P _60117).
Proof. exact (eq_refl (term62 _111301 P _60117)). Qed.
Lemma lem4848464 {_111301 : Type'} (P : type180 _111301) (R : type686 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term556 _111301 P Q c' R _60117) = (term667 _111301 P R Q c' _60117).
Proof. exact (MK_COMB (@lem4848463 _111301 P _60117) (@lem4848457 _111301 R Q c' _60117)). Qed.
Lemma lem4848468 (q : Prop) (p : Prop) (r : Prop) : (term568 p q r) = (term568 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4848469 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term667 _111301 P R Q c' _60117) = (term668 _111301 R P Q c' _60117).
Proof. exact (@lem4848468 (term22 _111301 R _60117) (term160 _111301 P _60117) (term530 _111301 Q c' _60117)). Qed.
Lemma lem4848485 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term556 _111301 P Q c' R _60117) = (term668 _111301 R P Q c' _60117).
Proof. exact (TRANS (@lem4848464 _111301 P R Q c' _60117) (@lem4848469 _111301 R P Q c' _60117)). Qed.
Lemma lem4848486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4848487 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term669 _111301 P Q c' R _60117) = (term670 _111301 R P Q c' _60117).
Proof. exact (MK_COMB (@lem4848486) (@lem4848485 _111301 R P Q c' _60117)). Qed.
Lemma lem4848503 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term668 _111301 R P Q c' _60117) = (term668 _111301 R P Q c' _60117).
Proof. exact (eq_refl (term668 _111301 R P Q c' _60117)). Qed.
Lemma lem4848504 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : ((term556 _111301 P Q c' R _60117) = (term668 _111301 R P Q c' _60117)) = ((term668 _111301 R P Q c' _60117) = (term668 _111301 R P Q c' _60117)).
Proof. exact (MK_COMB (@lem4848487 _111301 R P Q c' _60117) (@lem4848503 _111301 R P Q c' _60117)). Qed.
Lemma lem4848506 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4848507 (x : Prop) : (x = x) = True.
Proof. exact (@lem4848506 Prop x). Qed.
Lemma lem4848508 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : ((term668 _111301 R P Q c' _60117) = (term668 _111301 R P Q c' _60117)) = True.
Proof. exact (@lem4848507 (term668 _111301 R P Q c' _60117)). Qed.
Lemma lem4848509 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : ((term556 _111301 P Q c' R _60117) = (term668 _111301 R P Q c' _60117)) = True.
Proof. exact (TRANS (@lem4848504 _111301 R P Q c' _60117) (@lem4848508 _111301 R P Q c' _60117)). Qed.
Lemma lem4848510 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : True = ((term556 _111301 P Q c' R _60117) = (term668 _111301 R P Q c' _60117)).
Proof. exact (SYM (@lem4848509 _111301 R P Q c' _60117)). Qed.
Lemma lem4848511 {_111301 : Type'} (R : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term556 _111301 P Q c' R _60117) = (term668 _111301 R P Q c' _60117).
Proof. exact (EQ_MP (@lem4848510 _111301 R P Q c' _60117) (@lem0)). Qed.
Lemma lem4848512 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term668 _111301 R P Q c' _60117.
Proof. exact (EQ_MP (@lem4848511 _111301 R P Q c' _60117) (@lem4847610 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4848514 (b : Prop) (a : Prop) : (a \/ b) = (term581 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4848515 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term668 _111301 R P Q c' _60117) = (term671 _111301 P Q c' R _60117).
Proof. exact (@lem4848514 (term536 _111301 P Q c' _60117) (term22 _111301 R _60117)). Qed.
Lemma lem4848517 (a : Prop) (b : Prop) : (term583 a b) = (term584 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4848518 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term672 _111301 P Q c' _60117) = (term673 _111301 P Q c' _60117).
Proof. exact (@lem4848517 (term160 _111301 P _60117) (term530 _111301 Q c' _60117)). Qed.
Lemma lem4848520 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848521 {_111301 : Type'} (P : type180 _111301) (_60117 : type686 _111301) : (term587 _111301 P _60117) = (P _60117).
Proof. exact (@lem4848520 (P _60117)). Qed.
Lemma lem4848522 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4848523 {_111301 : Type'} (P : type180 _111301) (_60117 : type686 _111301) : (term588 _111301 P _60117) = (term26 _111301 P _60117).
Proof. exact (MK_COMB (@lem4848522) (@lem4848521 _111301 P _60117)). Qed.
Lemma lem4848525 (a : Prop) : (term9 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4848526 {_111301 : Type'} (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term674 _111301 Q c' _60117) = (term663 _111301 Q c' _60117).
Proof. exact (@lem4848525 (term663 _111301 Q c' _60117)). Qed.
Lemma lem4848527 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term673 _111301 P Q c' _60117) = (term675 _111301 P Q c' _60117).
Proof. exact (MK_COMB (@lem4848523 _111301 P _60117) (@lem4848526 _111301 Q c' _60117)). Qed.
Lemma lem4848528 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term672 _111301 P Q c' _60117) = (term675 _111301 P Q c' _60117).
Proof. exact (TRANS (@lem4848518 _111301 P Q c' _60117) (@lem4848527 _111301 P Q c' _60117)). Qed.
Lemma lem4848529 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4848530 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (_60117 : type686 _111301) : (term676 _111301 P Q c' _60117) = (term677 _111301 P Q c' _60117).
Proof. exact (MK_COMB (@lem4848529) (@lem4848528 _111301 P Q c' _60117)). Qed.
Lemma lem4848531 {_111301 : Type'} (R : type686 _111301) (_60117 : type686 _111301) : (term22 _111301 R _60117) = (term22 _111301 R _60117).
Proof. exact (eq_refl (term22 _111301 R _60117)). Qed.
Lemma lem4848532 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term671 _111301 P Q c' R _60117) = (term678 _111301 P Q c' R _60117).
Proof. exact (MK_COMB (@lem4848530 _111301 P Q c' _60117) (@lem4848531 _111301 R _60117)). Qed.
Lemma lem4848533 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (_60117 : type686 _111301) : (term668 _111301 R P Q c' _60117) = (term678 _111301 P Q c' R _60117).
Proof. exact (TRANS (@lem4848515 _111301 P Q c' R _60117) (@lem4848532 _111301 P Q c' R _60117)). Qed.
Lemma lem4848535 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term675 _111301 P Q c' u.
Proof. exact (conj (@lem4848234 _111301 u s P Q c' R h2) (@lem4848440 _111301 u s P Q c' R h1 h2)). Qed.
Lemma lem4848537 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term678 _111301 P Q c' R _60117.
Proof. exact (EQ_MP (@lem4848533 _111301 P Q c' R _60117) (@lem4848512 _111301 _60117 u s P Q c' R h1)). Qed.
Lemma lem4848538 {_111301 : Type'} (_60117 : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term678 _111301 P Q c' R _60117.
Proof. exact (@lem4848537 _111301 _60117 u s P Q c' R h1). Qed.
Lemma lem4848539 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term678 _111301 P Q c' R u.
Proof. exact (@lem4848538 _111301 u u s P Q c' R h1). Qed.
Lemma lem4848542 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term101 _111301 R u) (h2 : term394 _111301 u s P Q c' R) : term22 _111301 R u.
Proof. exact (@lem4848539 _111301 u s P Q c' R h2 (@lem4848535 _111301 u s P Q c' R h1 h2)). Qed.
Lemma lem4848543 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term642 _111301 R u.
Proof. exact (fun h0 : term101 _111301 R u => @lem4848542 _111301 u s P Q c' R h0 h1). Qed.
Lemma lem4848545 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848546 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) : (term642 _111301 R u) = (term22 _111301 R u).
Proof. exact (@lem4848545 (term22 _111301 R u)). Qed.
Lemma lem4848547 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term22 _111301 R u.
Proof. exact (EQ_MP (@lem4848546 _111301 R u) (@lem4848543 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848550 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4848552 {_111301 : Type'} (R : type686 _111301) (u : type686 _111301) : (term101 _111301 R u) = (term643 _111301 R u).
Proof. exact (@lem4848550 (term22 _111301 R u)). Qed.
Lemma lem4848555 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term643 _111301 R u.
Proof. exact (EQ_MP (@lem4848552 _111301 R u) (@lem4847554 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848558 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : False.
Proof. exact (@lem4848555 _111301 u s P Q c' R h1 (@lem4848547 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848559 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : term644.
Proof. exact (fun h0 : ~ False => @lem4848558 _111301 u s P Q c' R h1). Qed.
Lemma lem4848561 (p : Prop) : (term563 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4848562 : term644 = False.
Proof. exact (@lem4848561 False). Qed.
Lemma lem4848564 {_111301 : Type'} (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term394 _111301 u s P Q c' R) : False.
Proof. exact (EQ_MP (@lem4848562) (@lem4848559 _111301 u s P Q c' R h1)). Qed.
Lemma lem4848565 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term473 _111301 c t u s P Q c' R) : False.
Proof. exact (or_elim (@lem4847252 _111301 c t u s P Q c' R h1) (fun h0 : term275 _111301 c P Q R t => @lem4848227 _111301 c P Q R t h0) (fun h0 : term394 _111301 u s P Q c' R => @lem4848564 _111301 u s P Q c' R h0)). Qed.
Lemma lem4848566 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term473 _111301 c t u s P Q c' R) : (term473 _111301 c t u s P Q c' R) = False.
Proof. exact (prop_ext (fun h2 : term473 _111301 c t u s P Q c' R => @lem4848565 _111301 c t u s P Q c' R h1) (fun h2 : False => @lem4847252 _111301 c t u s P Q c' R h1)). Qed.
Lemma lem4848567 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (c' : type178 _111301) (R : type686 _111301) (h1 : term473 _111301 c t u s P Q c' R) : False.
Proof. exact (EQ_MP (@lem4848566 _111301 c t u s P Q c' R h1) (@lem4847252 _111301 c t u s P Q c' R h1)). Qed.
Lemma lem4848568 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (u : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term476 _111301 c t u s P Q R) : False.
Proof. exact (ex_elim (@lem4847080 _111301 c t u s P Q R h1) (fun c' : type178 _111301 => fun h0 : term475 _111301 c t u s P Q R c' => @lem4848567 _111301 c t u s P Q c' R h0)). Qed.
Lemma lem4848569 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (s : _111301 -> Prop) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term478 _111301 c t s P Q R) : False.
Proof. exact (ex_elim (@lem4847079 _111301 c t s P Q R h1) (fun u : type686 _111301 => fun h0 : term477 _111301 c t s P Q R u => @lem4848568 _111301 c t u s P Q R h0)). Qed.
Lemma lem4848570 {_111301 : Type'} (c : type598 _111301) (t : type686 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term480 _111301 c t P Q R) : False.
Proof. exact (ex_elim (@lem4847078 _111301 c t P Q R h1) (fun s : _111301 -> Prop => fun h0 : term479 _111301 c t P Q R s => @lem4848569 _111301 c t s P Q R h0)). Qed.
Lemma lem4848571 {_111301 : Type'} (c : type598 _111301) (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term482 _111301 c P Q R) : False.
Proof. exact (ex_elim (@lem4847077 _111301 c P Q R h1) (fun t : type686 _111301 => fun h0 : term481 _111301 c P Q R t => @lem4848570 _111301 c t P Q R h0)). Qed.
Lemma lem4848572 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : False.
Proof. exact (ex_elim (@lem4847076 _111301 P Q R h1) (fun c : type598 _111301 => fun h0 : term483 _111301 P Q R c => @lem4848571 _111301 c P Q R h0)). Qed.
Lemma lem4848573 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : (term4 _111301 P Q R) = False.
Proof. exact (prop_ext (fun h2 : term4 _111301 P Q R => @lem4848572 _111301 P Q R h1) (fun h2 : False => @lem4845983 _111301 P Q R h1)). Qed.
Lemma lem4848574 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : False.
Proof. exact (EQ_MP (@lem4848573 _111301 P Q R h1) (@lem4845983 _111301 P Q R h1)). Qed.
Lemma lem4848575 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term3 _111301 P Q R.
Proof. exact (fun h0 : term4 _111301 P Q R => @lem4848574 _111301 P Q R h0). Qed.
Lemma lem4848576 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term1 _111301 P Q R) = (term2 _111301 P Q R).
Proof. exact (EQ_MP (@lem4845982 _111301 P Q R) (@lem4848575 _111301 P Q R)). Qed.
Lemma lem4848581 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) : term13 _111301 Q R.
Proof. exact (fun P : type180 _111301 => @lem4848576 _111301 P Q R). Qed.
Lemma lem4848586 {_111301 : Type'} (R : type686 _111301) : term17 _111301 R.
Proof. exact (fun Q : type686 _111301 => @lem4848581 _111301 Q R). Qed.
Lemma lem4848591 {_111301 : Type'} : term21 _111301.
Proof. exact (fun R : type686 _111301 => @lem4848586 _111301 R). Qed.
Lemma lem4848592 {_111301 : Type'} : term20 _111301.
Proof. exact (EQ_MP (@lem4845978 _111301) (@lem4848591 _111301)). Qed.
Lemma lem4848593 {_111301 : Type'} (R : type686 _111301) : term679 _111301 R.
Proof. exact (@lem4848592 _111301 R). Qed.
Lemma lem4848594 {_111301 : Type'} (R : type686 _111301) : (term679 _111301 R) = (term16 _111301 R).
Proof. exact (eq_refl (term679 _111301 R)). Qed.
Lemma lem4848595 {_111301 : Type'} (R : type686 _111301) : term16 _111301 R.
Proof. exact (EQ_MP (@lem4848594 _111301 R) (@lem4848593 _111301 R)). Qed.
Lemma lem4848596 {_111301 : Type'} (R : type686 _111301) (Q : type686 _111301) : term680 _111301 R Q.
Proof. exact (@lem4848595 _111301 R Q). Qed.
Lemma lem4848597 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) : (term680 _111301 R Q) = (term12 _111301 Q R).
Proof. exact (eq_refl (term680 _111301 R Q)). Qed.
Lemma lem4848598 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) : term12 _111301 Q R.
Proof. exact (EQ_MP (@lem4848597 _111301 Q R) (@lem4848596 _111301 R Q)). Qed.
Lemma lem4848599 {_111301 : Type'} (Q : type686 _111301) (R : type686 _111301) (P : type180 _111301) : term681 _111301 Q R P.
Proof. exact (@lem4848598 _111301 Q R P). Qed.
Lemma lem4848600 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term681 _111301 Q R P) = (term3 _111301 P Q R).
Proof. exact (eq_refl (term681 _111301 Q R P)). Qed.
Lemma lem4848601 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term3 _111301 P Q R.
Proof. exact (EQ_MP (@lem4848600 _111301 P Q R) (@lem4848599 _111301 Q R P)). Qed.
Lemma lem4848603 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term3 _111301 P Q R.
Proof. exact (@lem4845753 _111301 P Q R (@lem4848601 _111301 P Q R)). Qed.
Lemma lem4848604 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : False.
Proof. exact (@lem4848603 _111301 P Q R (@lem4845737 _111301 P Q R h1)). Qed.
Lemma lem4848605 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : (term4 _111301 P Q R) = False.
Proof. exact (prop_ext (fun h2 : term4 _111301 P Q R => @lem4848604 _111301 P Q R h1) (fun h2 : False => @lem4845737 _111301 P Q R h1)). Qed.
Lemma lem4848606 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) (h1 : term4 _111301 P Q R) : False.
Proof. exact (EQ_MP (@lem4848605 _111301 P Q R h1) (@lem4845737 _111301 P Q R h1)). Qed.
Lemma lem4848607 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : term3 _111301 P Q R.
Proof. exact (fun h0 : term4 _111301 P Q R => @lem4848606 _111301 P Q R h0). Qed.
Lemma lem4848608 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term1 _111301 P Q R) = (term2 _111301 P Q R).
Proof. exact (EQ_MP (@lem4845736 _111301 P Q R) (@lem4848607 _111301 P Q R)). Qed.
