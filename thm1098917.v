Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098917_term_abbrevs.
Require Import thm1098510_spec.
Require Import thm1098870_spec.
Lemma lem1098871 {_25251 : Type'} : (term0 _25251) = (term1 _25251).
Proof. exact (eq_refl (term0 _25251)). Qed.
Lemma lem1098872 {_25251 : Type'} : term1 _25251.
Proof. exact (EQ_MP (@lem1098871 _25251) (@lem1098510 _25251)). Qed.
Lemma lem1098873 {_25251 : Type'} : term2 _25251.
Proof. exact (@lem1098872 _25251 term3). Qed.
Lemma lem1098874 {_25251 : Type'} : (term2 _25251) = (term4 _25251).
Proof. exact (eq_refl (term2 _25251)). Qed.
Lemma lem1098875 {_25251 : Type'} : term4 _25251.
Proof. exact (EQ_MP (@lem1098874 _25251) (@lem1098873 _25251)). Qed.
Lemma lem1098876 {_25251 : Type'} (h1 : (@List.removelast _25251) = (term5 _25251)) : (@List.removelast _25251) = (term5 _25251).
Proof. exact (h1). Qed.
Lemma lem1098877 {_25251 : Type'} (h1 : (@List.removelast _25251) = (term5 _25251)) : (term5 _25251) = (@List.removelast _25251).
Proof. exact (SYM (@lem1098876 _25251 h1)). Qed.
Lemma lem1098878 {_25251 : Type'} (h1 : (term5 _25251) = (@List.removelast _25251)) : (term5 _25251) = (@List.removelast _25251).
Proof. exact (h1). Qed.
Lemma lem1098879 {_25251 : Type'} (h1 : (term5 _25251) = (@List.removelast _25251)) : (@List.removelast _25251) = (term5 _25251).
Proof. exact (SYM (@lem1098878 _25251 h1)). Qed.
Lemma lem1098880 {_25251 : Type'} : ((@List.removelast _25251) = (term5 _25251)) = ((term5 _25251) = (@List.removelast _25251)).
Proof. exact (prop_ext (fun h1 : (@List.removelast _25251) = (term5 _25251) => @lem1098877 _25251 h1) (fun h1 : (term5 _25251) = (@List.removelast _25251) => @lem1098879 _25251 h1)). Qed.
Lemma lem1098883 {_25251 : Type'} : (term5 _25251) = (@List.removelast _25251).
Proof. exact (EQ_MP (@lem1098880 _25251) (@lem1098870 _25251)). Qed.
Lemma lem1098884 {_25251 : Type'} : (term5 _25251) = (@List.removelast _25251).
Proof. exact (@lem1098883 _25251). Qed.
Lemma lem1098885 {_25251 : Type'} : (@nil _25251) = (@nil _25251).
Proof. exact (eq_refl (@nil _25251)). Qed.
Lemma lem1098886 {_25251 : Type'} : (term6 _25251) = (@List.removelast _25251 (@nil _25251)).
Proof. exact (MK_COMB (@lem1098884 _25251) (@lem1098885 _25251)). Qed.
Lemma lem1098887 {_25251 : Type'} : (@eq (list _25251)) = (@eq (list _25251)).
Proof. exact (eq_refl (@eq (list _25251))). Qed.
Lemma lem1098888 {_25251 : Type'} : (term7 _25251) = (term8 _25251).
Proof. exact (MK_COMB (@lem1098887 _25251) (@lem1098886 _25251)). Qed.
Lemma lem1098889 {_25251 : Type'} : (@nil _25251) = (@nil _25251).
Proof. exact (eq_refl (@nil _25251)). Qed.
Lemma lem1098890 {_25251 : Type'} : ((term6 _25251) = (@nil _25251)) = ((@List.removelast _25251 (@nil _25251)) = (@nil _25251)).
Proof. exact (MK_COMB (@lem1098888 _25251) (@lem1098889 _25251)). Qed.
Lemma lem1098891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1098892 {_25251 : Type'} : (term9 _25251) = (term10 _25251).
Proof. exact (MK_COMB (@lem1098891) (@lem1098890 _25251)). Qed.
Lemma lem1098894 {_25251 : Type'} : (term5 _25251) = (@List.removelast _25251).
Proof. exact (EQ_MP (@lem1098880 _25251) (@lem1098870 _25251)). Qed.
Lemma lem1098895 {_25251 : Type'} : (term5 _25251) = (@List.removelast _25251).
Proof. exact (@lem1098894 _25251). Qed.
Lemma lem1098896 {_25251 : Type'} (h : _25251) (t : list _25251) : (@cons _25251 h t) = (@cons _25251 h t).
Proof. exact (eq_refl (@cons _25251 h t)). Qed.
Lemma lem1098897 {_25251 : Type'} (h : _25251) (t : list _25251) : (term11 _25251 h t) = (term12 _25251 h t).
Proof. exact (MK_COMB (@lem1098895 _25251) (@lem1098896 _25251 h t)). Qed.
Lemma lem1098898 {_25251 : Type'} : (@eq (list _25251)) = (@eq (list _25251)).
Proof. exact (eq_refl (@eq (list _25251))). Qed.
Lemma lem1098899 {_25251 : Type'} (h : _25251) (t : list _25251) : (term13 _25251 h t) = (term14 _25251 h t).
Proof. exact (MK_COMB (@lem1098898 _25251) (@lem1098897 _25251 h t)). Qed.
Lemma lem1098901 {_25251 : Type'} : (term5 _25251) = (@List.removelast _25251).
Proof. exact (EQ_MP (@lem1098880 _25251) (@lem1098870 _25251)). Qed.
Lemma lem1098902 {_25251 : Type'} : (term5 _25251) = (@List.removelast _25251).
Proof. exact (@lem1098901 _25251). Qed.
Lemma lem1098903 {_25251 : Type'} (t : list _25251) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem1098904 {_25251 : Type'} (t : list _25251) : (term15 _25251 t) = (@List.removelast _25251 t).
Proof. exact (MK_COMB (@lem1098902 _25251) (@lem1098903 _25251 t)). Qed.
Lemma lem1098905 {_25251 : Type'} (h : _25251) : (@cons _25251 h) = (@cons _25251 h).
Proof. exact (eq_refl (@cons _25251 h)). Qed.
Lemma lem1098906 {_25251 : Type'} (h : _25251) (t : list _25251) : (term16 _25251 h t) = (term17 _25251 h t).
Proof. exact (MK_COMB (@lem1098905 _25251 h) (@lem1098904 _25251 t)). Qed.
Lemma lem1098907 {_25251 : Type'} (t : list _25251) : (term18 _25251 t) = (term18 _25251 t).
Proof. exact (eq_refl (term18 _25251 t)). Qed.
Lemma lem1098908 {_25251 : Type'} (h : _25251) (t : list _25251) : (term19 _25251 h t) = (term20 _25251 h t).
Proof. exact (MK_COMB (@lem1098907 _25251 t) (@lem1098906 _25251 h t)). Qed.
Lemma lem1098909 {_25251 : Type'} (h : _25251) (t : list _25251) : ((term11 _25251 h t) = (term19 _25251 h t)) = ((term12 _25251 h t) = (term20 _25251 h t)).
Proof. exact (MK_COMB (@lem1098899 _25251 h t) (@lem1098908 _25251 h t)). Qed.
Lemma lem1098910 {_25251 : Type'} (h : _25251) : (term21 _25251 h) = (term22 _25251 h).
Proof. exact (fun_ext (fun t : list _25251 => @lem1098909 _25251 h t)). Qed.
Lemma lem1098911 {_25251 : Type'} : (@all (list _25251)) = (@all (list _25251)).
Proof. exact (eq_refl (@all (list _25251))). Qed.
Lemma lem1098912 {_25251 : Type'} (h : _25251) : (term23 _25251 h) = (term24 _25251 h).
Proof. exact (MK_COMB (@lem1098911 _25251) (@lem1098910 _25251 h)). Qed.
Lemma lem1098913 {_25251 : Type'} : (term25 _25251) = (term26 _25251).
Proof. exact (fun_ext (fun h : _25251 => @lem1098912 _25251 h)). Qed.
Lemma lem1098914 {_25251 : Type'} : (@all _25251) = (@all _25251).
Proof. exact (eq_refl (@all _25251)). Qed.
Lemma lem1098915 {_25251 : Type'} : (term27 _25251) = (term28 _25251).
Proof. exact (MK_COMB (@lem1098914 _25251) (@lem1098913 _25251)). Qed.
Lemma lem1098916 {_25251 : Type'} : (term4 _25251) = (term29 _25251).
Proof. exact (MK_COMB (@lem1098892 _25251) (@lem1098915 _25251)). Qed.
Lemma lem1098917 {_25251 : Type'} : term29 _25251.
Proof. exact (EQ_MP (@lem1098916 _25251) (@lem1098875 _25251)). Qed.
