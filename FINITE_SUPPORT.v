Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUPPORT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import SUPPORT_SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm69_spec.
Lemma lem5719799 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5719800 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5719801 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5719800 t1) (@lem5719799 t1)). Qed.
Lemma lem5719802 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5719801 t1 t2). Qed.
Lemma lem5719803 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5719804 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5719803 t1 t2) (@lem5719802 t1 t2)). Qed.
Lemma lem5719805 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5719804 t1 t2 t3). Qed.
Lemma lem5719806 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5719807 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5719806 t1 t2 t3) (@lem5719805 t1 t2 t3)). Qed.
Lemma lem5719808 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5719807 t1 t2 t3)). Qed.
Lemma lem5719810 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5719811 {_119939 _119945 : Type'} : (term8 _119939 _119945) = (term9 _119939 _119945).
Proof. exact (@lem5719810 (term8 _119939 _119945)). Qed.
Lemma lem5719812 {_119939 _119945 : Type'} : (term9 _119939 _119945) = (term8 _119939 _119945).
Proof. exact (SYM (@lem5719811 _119939 _119945)). Qed.
Lemma lem5719813 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : term10 _119939 _119945.
Proof. exact (h1). Qed.
Lemma lem5719814 {_119939 _119945 : Type'} : term11 _119939 _119945.
Proof. exact (@lem5719798 _119945 _119939). Qed.
Lemma lem5719815 {_119939 : Type'} : term12 _119939.
Proof. exact (@lem3599924 _119939). Qed.
Lemma lem5719819 {_119939 _119945 : Type'} (h1 : term13 _119939 _119945) : term13 _119939 _119945.
Proof. exact (h1). Qed.
Lemma lem5719820 {_119939 _119945 : Type'} : term14 _119939 _119945.
Proof. exact (fun h0 : term13 _119939 _119945 => @lem5719819 _119939 _119945 h0). Qed.
Lemma lem5719821 {_119939 _119945 : Type'} (h1 : term14 _119939 _119945) : term14 _119939 _119945.
Proof. exact (h1). Qed.
Lemma lem5719822 {_119939 _119945 : Type'} (h1 : term13 _119939 _119945) : term13 _119939 _119945.
Proof. exact (h1). Qed.
Lemma lem5719823 {_119939 _119945 : Type'} (h1 : term13 _119939 _119945) (h2 : term14 _119939 _119945) : term13 _119939 _119945.
Proof. exact (@lem5719821 _119939 _119945 h2 (@lem5719822 _119939 _119945 h1)). Qed.
Lemma lem5719824 {_119939 _119945 : Type'} (h1 : term13 _119939 _119945) : term15 _119939 _119945.
Proof. exact (fun h0 : term14 _119939 _119945 => @lem5719823 _119939 _119945 h1 h0). Qed.
Lemma lem5719825 {_119939 _119945 : Type'} (h1 : term14 _119939 _119945) : term14 _119939 _119945.
Proof. exact (h1). Qed.
Lemma lem5719826 {_119939 _119945 : Type'} (h1 : term13 _119939 _119945) (h2 : term14 _119939 _119945) : term13 _119939 _119945.
Proof. exact (@lem5719824 _119939 _119945 h1 (@lem5719825 _119939 _119945 h2)). Qed.
Lemma lem5719827 {_119939 _119945 : Type'} (h1 : term14 _119939 _119945) : term14 _119939 _119945.
Proof. exact (fun h0 : term13 _119939 _119945 => @lem5719826 _119939 _119945 h0 h1). Qed.
Lemma lem5719828 {_119939 _119945 : Type'} : term16 _119939 _119945.
Proof. exact (fun h0 : term14 _119939 _119945 => @lem5719827 _119939 _119945 h0). Qed.
Lemma lem5719831 {_119939 _119945 : Type'} : term14 _119939 _119945.
Proof. exact (@lem5719828 _119939 _119945 (@lem5719820 _119939 _119945)). Qed.
Lemma lem5719832 {_119939 _119945 : Type'} : term14 _119939 _119945.
Proof. exact (@lem5719831 _119939 _119945). Qed.
Lemma lem5719864 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5719865 {_119939 _119945 : Type'} : (term17 _119939 _119945) = (term18 _119939 _119945).
Proof. exact (@lem5719864 (term11 _119939 _119945)). Qed.
Lemma lem5719878 {_119939 : Type'} : (term19 _119939) = (term19 _119939).
Proof. exact (eq_refl (term19 _119939)). Qed.
Lemma lem5719879 {_119939 _119945 : Type'} : (term20 _119939 _119945) = (term21 _119939 _119945).
Proof. exact (MK_COMB (@lem5719878 _119939) (@lem5719865 _119939 _119945)). Qed.
Lemma lem5719882 {_119939 _119945 : Type'} : (term22 _119939 _119945) = (term22 _119939 _119945).
Proof. exact (eq_refl (term22 _119939 _119945)). Qed.
Lemma lem5719889 {_119939 _119945 : Type'} : (term13 _119939 _119945) = (term23 _119939 _119945).
Proof. exact (MK_COMB (@lem5719882 _119939 _119945) (@lem5719879 _119939 _119945)). Qed.
Lemma lem5719890 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term24 _119939 _119945 op f s) = (term24 _119939 _119945 op f s).
Proof. exact (eq_refl (term24 _119939 _119945 op f s)). Qed.
Lemma lem5719891 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term25 _119939 _119945 op f) = (term25 _119939 _119945 op f).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5719890 _119939 _119945 op f s)). Qed.
Lemma lem5719892 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5719893 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term26 _119939 _119945 op f) = (term26 _119939 _119945 op f).
Proof. exact (MK_COMB (@lem5719892 _119939) (@lem5719891 _119939 _119945 op f)). Qed.
Lemma lem5719894 {_119939 _119945 : Type'} (op : type1400 _119945) : (term27 _119939 _119945 op) = (term27 _119939 _119945 op).
Proof. exact (fun_ext (fun f : _119939 -> _119945 => @lem5719893 _119939 _119945 op f)). Qed.
Lemma lem5719895 {_119939 _119945 : Type'} : (@all (_119939 -> _119945)) = (@all (_119939 -> _119945)).
Proof. exact (eq_refl (@all (_119939 -> _119945))). Qed.
Lemma lem5719896 {_119939 _119945 : Type'} (op : type1400 _119945) : (term28 _119939 _119945 op) = (term28 _119939 _119945 op).
Proof. exact (MK_COMB (@lem5719895 _119939 _119945) (@lem5719894 _119939 _119945 op)). Qed.
Lemma lem5719897 {_119939 _119945 : Type'} : (term29 _119939 _119945) = (term29 _119939 _119945).
Proof. exact (fun_ext (fun op : type1400 _119945 => @lem5719896 _119939 _119945 op)). Qed.
Lemma lem5719898 {_119945 : Type'} : (@all (_119945 -> _119945 -> _119945)) = (@all (_119945 -> _119945 -> _119945)).
Proof. exact (eq_refl (@all (_119945 -> _119945 -> _119945))). Qed.
Lemma lem5719899 {_119939 _119945 : Type'} : (term11 _119939 _119945) = (term11 _119939 _119945).
Proof. exact (MK_COMB (@lem5719898 _119945) (@lem5719897 _119939 _119945)). Qed.
Lemma lem5719900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5719901 {_119939 _119945 : Type'} : (term18 _119939 _119945) = (term18 _119939 _119945).
Proof. exact (MK_COMB (@lem5719900) (@lem5719899 _119939 _119945)). Qed.
Lemma lem5719910 {_119939 : Type'} (t : _119939 -> Prop) (s : _119939 -> Prop) : (term30 _119939 t s) = (term30 _119939 t s).
Proof. exact (eq_refl (term30 _119939 t s)). Qed.
Lemma lem5719911 {_119939 : Type'} (s : _119939 -> Prop) : (term31 _119939 s) = (term31 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5719910 _119939 t s)). Qed.
Lemma lem5719912 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5719913 {_119939 : Type'} (s : _119939 -> Prop) : (term32 _119939 s) = (term32 _119939 s).
Proof. exact (MK_COMB (@lem5719912 _119939) (@lem5719911 _119939 s)). Qed.
Lemma lem5719914 {_119939 : Type'} : (term33 _119939) = (term33 _119939).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5719913 _119939 s)). Qed.
Lemma lem5719915 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5719916 {_119939 : Type'} : (term12 _119939) = (term12 _119939).
Proof. exact (MK_COMB (@lem5719915 _119939) (@lem5719914 _119939)). Qed.
Lemma lem5719917 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5719918 {_119939 : Type'} : (term19 _119939) = (term19 _119939).
Proof. exact (MK_COMB (@lem5719917) (@lem5719916 _119939)). Qed.
Lemma lem5719919 {_119939 _119945 : Type'} : (term21 _119939 _119945) = (term21 _119939 _119945).
Proof. exact (MK_COMB (@lem5719918 _119939) (@lem5719901 _119939 _119945)). Qed.
Lemma lem5719924 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term34 _119939 _119945 op f s) = (term34 _119939 _119945 op f s).
Proof. exact (eq_refl (term34 _119939 _119945 op f s)). Qed.
Lemma lem5719925 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term35 _119939 _119945 op f) = (term35 _119939 _119945 op f).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5719924 _119939 _119945 op f s)). Qed.
Lemma lem5719926 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5719927 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term36 _119939 _119945 op f) = (term36 _119939 _119945 op f).
Proof. exact (MK_COMB (@lem5719926 _119939) (@lem5719925 _119939 _119945 op f)). Qed.
Lemma lem5719928 {_119939 _119945 : Type'} (op : type1400 _119945) : (term37 _119939 _119945 op) = (term37 _119939 _119945 op).
Proof. exact (fun_ext (fun f : _119939 -> _119945 => @lem5719927 _119939 _119945 op f)). Qed.
Lemma lem5719929 {_119939 _119945 : Type'} : (@all (_119939 -> _119945)) = (@all (_119939 -> _119945)).
Proof. exact (eq_refl (@all (_119939 -> _119945))). Qed.
Lemma lem5719930 {_119939 _119945 : Type'} (op : type1400 _119945) : (term38 _119939 _119945 op) = (term38 _119939 _119945 op).
Proof. exact (MK_COMB (@lem5719929 _119939 _119945) (@lem5719928 _119939 _119945 op)). Qed.
Lemma lem5719931 {_119939 _119945 : Type'} : (term39 _119939 _119945) = (term39 _119939 _119945).
Proof. exact (fun_ext (fun op : type1400 _119945 => @lem5719930 _119939 _119945 op)). Qed.
Lemma lem5719932 {_119945 : Type'} : (@all (_119945 -> _119945 -> _119945)) = (@all (_119945 -> _119945 -> _119945)).
Proof. exact (eq_refl (@all (_119945 -> _119945 -> _119945))). Qed.
Lemma lem5719933 {_119939 _119945 : Type'} : (term8 _119939 _119945) = (term8 _119939 _119945).
Proof. exact (MK_COMB (@lem5719932 _119945) (@lem5719931 _119939 _119945)). Qed.
Lemma lem5719934 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5719935 {_119939 _119945 : Type'} : (term10 _119939 _119945) = (term10 _119939 _119945).
Proof. exact (MK_COMB (@lem5719934) (@lem5719933 _119939 _119945)). Qed.
Lemma lem5719936 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5719937 {_119939 _119945 : Type'} : (term22 _119939 _119945) = (term22 _119939 _119945).
Proof. exact (MK_COMB (@lem5719936) (@lem5719935 _119939 _119945)). Qed.
Lemma lem5719938 {_119939 _119945 : Type'} : (term23 _119939 _119945) = (term23 _119939 _119945).
Proof. exact (MK_COMB (@lem5719937 _119939 _119945) (@lem5719919 _119939 _119945)). Qed.
Lemma lem5719999 {_119939 _119945 : Type'} : (term13 _119939 _119945) = (term23 _119939 _119945).
Proof. exact (TRANS (@lem5719889 _119939 _119945) (@lem5719938 _119939 _119945)). Qed.
Lemma lem5720000 {_119939 _119945 : Type'} : (term23 _119939 _119945) = (term13 _119939 _119945).
Proof. exact (SYM (@lem5719999 _119939 _119945)). Qed.
Lemma lem5720001 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : term10 _119939 _119945.
Proof. exact (h1). Qed.
Lemma lem5720002 {_119939 : Type'} (h1 : term12 _119939) : term12 _119939.
Proof. exact (h1). Qed.
Lemma lem5720003 {_119939 _119945 : Type'} (h1 : term11 _119939 _119945) : term11 _119939 _119945.
Proof. exact (h1). Qed.
Lemma lem5720010 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term40 _119939 _119945 op f s) = (term41 _119939 _119945 op f s).
Proof. exact (@lem17362 (@FINITE _119939 s) (term42 _119939 _119945 op f s)). Qed.
Lemma lem5720011 {_119939 : Type'} (P : type686 _119939) : (term43 _119939 P) = (term44 _119939 P).
Proof. exact (@lem18392 (_119939 -> Prop) P). Qed.
Lemma lem5720012 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term45 _119939 _119945 op f) = (term46 _119939 _119945 op f).
Proof. exact (@lem5720011 _119939 (term35 _119939 _119945 op f)). Qed.
Lemma lem5720013 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term47 _119939 _119945 op f s) = (term34 _119939 _119945 op f s).
Proof. exact (eq_refl (term47 _119939 _119945 op f s)). Qed.
Lemma lem5720014 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5720015 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term48 _119939 _119945 op f s) = (term40 _119939 _119945 op f s).
Proof. exact (MK_COMB (@lem5720014) (@lem5720013 _119939 _119945 op f s)). Qed.
Lemma lem5720016 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term48 _119939 _119945 op f s) = (term41 _119939 _119945 op f s).
Proof. exact (TRANS (@lem5720015 _119939 _119945 op f s) (@lem5720010 _119939 _119945 op f s)). Qed.
Lemma lem5720017 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term49 _119939 _119945 op f) = (term50 _119939 _119945 op f).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720016 _119939 _119945 op f s)). Qed.
Lemma lem5720018 {_119939 : Type'} : (@ex (_119939 -> Prop)) = (@ex (_119939 -> Prop)).
Proof. exact (eq_refl (@ex (_119939 -> Prop))). Qed.
Lemma lem5720019 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term46 _119939 _119945 op f) = (term51 _119939 _119945 op f).
Proof. exact (MK_COMB (@lem5720018 _119939) (@lem5720017 _119939 _119945 op f)). Qed.
Lemma lem5720020 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term45 _119939 _119945 op f) = (term51 _119939 _119945 op f).
Proof. exact (TRANS (@lem5720012 _119939 _119945 op f) (@lem5720019 _119939 _119945 op f)). Qed.
Lemma lem5720021 {_119939 _119945 : Type'} (P : type572 _119939 _119945) : (term52 _119939 _119945 P) = (term53 _119939 _119945 P).
Proof. exact (@lem18392 (_119939 -> _119945) P). Qed.
Lemma lem5720022 {_119939 _119945 : Type'} (op : type1400 _119945) : (term54 _119939 _119945 op) = (term55 _119939 _119945 op).
Proof. exact (@lem5720021 _119939 _119945 (term37 _119939 _119945 op)). Qed.
Lemma lem5720023 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term56 _119939 _119945 op f) = (term36 _119939 _119945 op f).
Proof. exact (eq_refl (term56 _119939 _119945 op f)). Qed.
Lemma lem5720024 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5720025 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term57 _119939 _119945 op f) = (term45 _119939 _119945 op f).
Proof. exact (MK_COMB (@lem5720024) (@lem5720023 _119939 _119945 op f)). Qed.
Lemma lem5720026 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term57 _119939 _119945 op f) = (term51 _119939 _119945 op f).
Proof. exact (TRANS (@lem5720025 _119939 _119945 op f) (@lem5720020 _119939 _119945 op f)). Qed.
Lemma lem5720027 {_119939 _119945 : Type'} (op : type1400 _119945) : (term58 _119939 _119945 op) = (term59 _119939 _119945 op).
Proof. exact (fun_ext (fun f : _119939 -> _119945 => @lem5720026 _119939 _119945 op f)). Qed.
Lemma lem5720028 {_119939 _119945 : Type'} : (@ex (_119939 -> _119945)) = (@ex (_119939 -> _119945)).
Proof. exact (eq_refl (@ex (_119939 -> _119945))). Qed.
Lemma lem5720029 {_119939 _119945 : Type'} (op : type1400 _119945) : (term55 _119939 _119945 op) = (term60 _119939 _119945 op).
Proof. exact (MK_COMB (@lem5720028 _119939 _119945) (@lem5720027 _119939 _119945 op)). Qed.
Lemma lem5720030 {_119939 _119945 : Type'} (op : type1400 _119945) : (term54 _119939 _119945 op) = (term60 _119939 _119945 op).
Proof. exact (TRANS (@lem5720022 _119939 _119945 op) (@lem5720029 _119939 _119945 op)). Qed.
Lemma lem5720031 {_119945 : Type'} (P : type403 _119945) : (term61 _119945 P) = (term62 _119945 P).
Proof. exact (@lem18392 (type1400 _119945) P). Qed.
Lemma lem5720032 {_119939 _119945 : Type'} : (term10 _119939 _119945) = (term63 _119939 _119945).
Proof. exact (@lem5720031 _119945 (term39 _119939 _119945)). Qed.
Lemma lem5720033 {_119939 _119945 : Type'} (op : type1400 _119945) : (term64 _119939 _119945 op) = (term38 _119939 _119945 op).
Proof. exact (eq_refl (term64 _119939 _119945 op)). Qed.
Lemma lem5720034 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5720035 {_119939 _119945 : Type'} (op : type1400 _119945) : (term65 _119939 _119945 op) = (term54 _119939 _119945 op).
Proof. exact (MK_COMB (@lem5720034) (@lem5720033 _119939 _119945 op)). Qed.
Lemma lem5720036 {_119939 _119945 : Type'} (op : type1400 _119945) : (term65 _119939 _119945 op) = (term60 _119939 _119945 op).
Proof. exact (TRANS (@lem5720035 _119939 _119945 op) (@lem5720030 _119939 _119945 op)). Qed.
Lemma lem5720037 {_119939 _119945 : Type'} : (term66 _119939 _119945) = (term67 _119939 _119945).
Proof. exact (fun_ext (fun op : type1400 _119945 => @lem5720036 _119939 _119945 op)). Qed.
Lemma lem5720038 {_119945 : Type'} : (@ex (_119945 -> _119945 -> _119945)) = (@ex (_119945 -> _119945 -> _119945)).
Proof. exact (eq_refl (@ex (_119945 -> _119945 -> _119945))). Qed.
Lemma lem5720039 {_119939 _119945 : Type'} : (term63 _119939 _119945) = (term68 _119939 _119945).
Proof. exact (MK_COMB (@lem5720038 _119945) (@lem5720037 _119939 _119945)). Qed.
Lemma lem5720080 {_119939 _119945 : Type'} : (term10 _119939 _119945) = (term68 _119939 _119945).
Proof. exact (TRANS (@lem5720032 _119939 _119945) (@lem5720039 _119939 _119945)). Qed.
Lemma lem5720081 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : term68 _119939 _119945.
Proof. exact (EQ_MP (@lem5720080 _119939 _119945) (@lem5720001 _119939 _119945 h1)). Qed.
Lemma lem5720088 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term69 _119939 s t) = (term70 _119939 s t).
Proof. exact (@lem17045 (@FINITE _119939 t) (@SUBSET _119939 s t)). Qed.
Lemma lem5720089 {_119939 : Type'} (s : _119939 -> Prop) : (@FINITE _119939 s) = (@FINITE _119939 s).
Proof. exact (eq_refl (@FINITE _119939 s)). Qed.
Lemma lem5720090 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5720091 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term71 _119939 s t) = (term72 _119939 s t).
Proof. exact (MK_COMB (@lem5720090) (@lem5720088 _119939 s t)). Qed.
Lemma lem5720092 {_119939 : Type'} (t : _119939 -> Prop) (s : _119939 -> Prop) : (term73 _119939 t s) = (term74 _119939 t s).
Proof. exact (MK_COMB (@lem5720091 _119939 s t) (@lem5720089 _119939 s)). Qed.
Lemma lem5720093 {_119939 : Type'} (t : _119939 -> Prop) (s : _119939 -> Prop) : (term30 _119939 t s) = (term73 _119939 t s).
Proof. exact (@lem17265 (term75 _119939 s t) (@FINITE _119939 s)). Qed.
Lemma lem5720094 {_119939 : Type'} (t : _119939 -> Prop) (s : _119939 -> Prop) : (term30 _119939 t s) = (term74 _119939 t s).
Proof. exact (TRANS (@lem5720093 _119939 t s) (@lem5720092 _119939 t s)). Qed.
Lemma lem5720095 {_119939 : Type'} (s : _119939 -> Prop) : (term31 _119939 s) = (term76 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5720094 _119939 t s)). Qed.
Lemma lem5720096 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720097 {_119939 : Type'} (s : _119939 -> Prop) : (term32 _119939 s) = (term77 _119939 s).
Proof. exact (MK_COMB (@lem5720096 _119939) (@lem5720095 _119939 s)). Qed.
Lemma lem5720098 {_119939 : Type'} : (term33 _119939) = (term78 _119939).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720097 _119939 s)). Qed.
Lemma lem5720099 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720100 {_119939 : Type'} : (term12 _119939) = (term79 _119939).
Proof. exact (MK_COMB (@lem5720099 _119939) (@lem5720098 _119939)). Qed.
Lemma lem5720126 {A : Type'} (P : A -> Prop) (Q : Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem5720127 {_119939 : Type'} (P : type686 _119939) (Q : Prop) : (term82 _119939 P Q) = (term83 _119939 P Q).
Proof. exact (@lem5720126 (_119939 -> Prop) P Q). Qed.
Lemma lem5720128 {_119939 : Type'} (s : _119939 -> Prop) : (term84 _119939 s) = (term85 _119939 s).
Proof. exact (@lem5720127 _119939 (term86 _119939 s) (@FINITE _119939 s)). Qed.
Lemma lem5720129 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term87 _119939 s t) = (term70 _119939 s t).
Proof. exact (eq_refl (term87 _119939 s t)). Qed.
Lemma lem5720130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5720131 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term88 _119939 s t) = (term72 _119939 s t).
Proof. exact (MK_COMB (@lem5720130) (@lem5720129 _119939 s t)). Qed.
Lemma lem5720132 {_119939 : Type'} (s : _119939 -> Prop) : (@FINITE _119939 s) = (@FINITE _119939 s).
Proof. exact (eq_refl (@FINITE _119939 s)). Qed.
Lemma lem5720133 {_119939 : Type'} (t : _119939 -> Prop) (s : _119939 -> Prop) : (term89 _119939 t s) = (term74 _119939 t s).
Proof. exact (MK_COMB (@lem5720131 _119939 s t) (@lem5720132 _119939 s)). Qed.
Lemma lem5720134 {_119939 : Type'} (s : _119939 -> Prop) : (term90 _119939 s) = (term76 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5720133 _119939 t s)). Qed.
Lemma lem5720135 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720136 {_119939 : Type'} (s : _119939 -> Prop) : (term84 _119939 s) = (term77 _119939 s).
Proof. exact (MK_COMB (@lem5720135 _119939) (@lem5720134 _119939 s)). Qed.
Lemma lem5720137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5720138 {_119939 : Type'} (s : _119939 -> Prop) : (term91 _119939 s) = (term92 _119939 s).
Proof. exact (MK_COMB (@lem5720137) (@lem5720136 _119939 s)). Qed.
Lemma lem5720139 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term87 _119939 s t) = (term70 _119939 s t).
Proof. exact (eq_refl (term87 _119939 s t)). Qed.
Lemma lem5720140 {_119939 : Type'} (s : _119939 -> Prop) : (term93 _119939 s) = (term86 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5720139 _119939 s t)). Qed.
Lemma lem5720141 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720142 {_119939 : Type'} (s : _119939 -> Prop) : (term94 _119939 s) = (term95 _119939 s).
Proof. exact (MK_COMB (@lem5720141 _119939) (@lem5720140 _119939 s)). Qed.
Lemma lem5720143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5720144 {_119939 : Type'} (s : _119939 -> Prop) : (term96 _119939 s) = (term97 _119939 s).
Proof. exact (MK_COMB (@lem5720143) (@lem5720142 _119939 s)). Qed.
Lemma lem5720145 {_119939 : Type'} (s : _119939 -> Prop) : (@FINITE _119939 s) = (@FINITE _119939 s).
Proof. exact (eq_refl (@FINITE _119939 s)). Qed.
Lemma lem5720146 {_119939 : Type'} (s : _119939 -> Prop) : (term85 _119939 s) = (term98 _119939 s).
Proof. exact (MK_COMB (@lem5720144 _119939 s) (@lem5720145 _119939 s)). Qed.
Lemma lem5720147 {_119939 : Type'} (s : _119939 -> Prop) : ((term84 _119939 s) = (term85 _119939 s)) = ((term77 _119939 s) = (term98 _119939 s)).
Proof. exact (MK_COMB (@lem5720138 _119939 s) (@lem5720146 _119939 s)). Qed.
Lemma lem5720148 {_119939 : Type'} (s : _119939 -> Prop) : (term77 _119939 s) = (term98 _119939 s).
Proof. exact (EQ_MP (@lem5720147 _119939 s) (@lem5720128 _119939 s)). Qed.
Lemma lem5720197 {_119939 : Type'} : (term78 _119939) = (term99 _119939).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720148 _119939 s)). Qed.
Lemma lem5720198 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720233 {_119939 : Type'} : (term79 _119939) = (term100 _119939).
Proof. exact (MK_COMB (@lem5720198 _119939) (@lem5720197 _119939)). Qed.
Lemma lem5720234 {_119939 : Type'} : (term12 _119939) = (term100 _119939).
Proof. exact (TRANS (@lem5720100 _119939) (@lem5720233 _119939)). Qed.
Lemma lem5720235 {_119939 : Type'} (h1 : term12 _119939) : term100 _119939.
Proof. exact (EQ_MP (@lem5720234 _119939) (@lem5720002 _119939 h1)). Qed.
Lemma lem5720236 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term24 _119939 _119945 op f s) = (term24 _119939 _119945 op f s).
Proof. exact (eq_refl (term24 _119939 _119945 op f s)). Qed.
Lemma lem5720237 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term25 _119939 _119945 op f) = (term25 _119939 _119945 op f).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720236 _119939 _119945 op f s)). Qed.
Lemma lem5720238 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720239 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term26 _119939 _119945 op f) = (term26 _119939 _119945 op f).
Proof. exact (MK_COMB (@lem5720238 _119939) (@lem5720237 _119939 _119945 op f)). Qed.
Lemma lem5720240 {_119939 _119945 : Type'} (op : type1400 _119945) : (term27 _119939 _119945 op) = (term27 _119939 _119945 op).
Proof. exact (fun_ext (fun f : _119939 -> _119945 => @lem5720239 _119939 _119945 op f)). Qed.
Lemma lem5720241 {_119939 _119945 : Type'} : (@all (_119939 -> _119945)) = (@all (_119939 -> _119945)).
Proof. exact (eq_refl (@all (_119939 -> _119945))). Qed.
Lemma lem5720242 {_119939 _119945 : Type'} (op : type1400 _119945) : (term28 _119939 _119945 op) = (term28 _119939 _119945 op).
Proof. exact (MK_COMB (@lem5720241 _119939 _119945) (@lem5720240 _119939 _119945 op)). Qed.
Lemma lem5720243 {_119939 _119945 : Type'} : (term29 _119939 _119945) = (term29 _119939 _119945).
Proof. exact (fun_ext (fun op : type1400 _119945 => @lem5720242 _119939 _119945 op)). Qed.
Lemma lem5720244 {_119945 : Type'} : (@all (_119945 -> _119945 -> _119945)) = (@all (_119945 -> _119945 -> _119945)).
Proof. exact (eq_refl (@all (_119945 -> _119945 -> _119945))). Qed.
Lemma lem5720261 {_119939 _119945 : Type'} : (term11 _119939 _119945) = (term11 _119939 _119945).
Proof. exact (MK_COMB (@lem5720244 _119945) (@lem5720243 _119939 _119945)). Qed.
Lemma lem5720262 {_119939 _119945 : Type'} (h1 : term11 _119939 _119945) : term11 _119939 _119945.
Proof. exact (EQ_MP (@lem5720261 _119939 _119945) (@lem5720003 _119939 _119945 h1)). Qed.
Lemma lem5720263 {_119939 _119945 : Type'} (op : type1400 _119945) (h1 : term60 _119939 _119945 op) : term60 _119939 _119945 op.
Proof. exact (h1). Qed.
Lemma lem5720264 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (h1 : term51 _119939 _119945 op f) : term51 _119939 _119945 op f.
Proof. exact (h1). Qed.
Lemma lem5720268 {_119939 : Type'} (s : _119939 -> Prop) : (@FINITE _119939 s) = (@FINITE _119939 s).
Proof. exact (eq_refl (@FINITE _119939 s)). Qed.
Lemma lem5720283 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term70 _119939 s t) = (term70 _119939 s t).
Proof. exact (eq_refl (term70 _119939 s t)). Qed.
Lemma lem5720284 {_119939 : Type'} (s : _119939 -> Prop) : (term86 _119939 s) = (term86 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5720283 _119939 s t)). Qed.
Lemma lem5720285 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720286 {_119939 : Type'} (s : _119939 -> Prop) : (term95 _119939 s) = (term95 _119939 s).
Proof. exact (MK_COMB (@lem5720285 _119939) (@lem5720284 _119939 s)). Qed.
Lemma lem5720287 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5720288 {_119939 : Type'} (s : _119939 -> Prop) : (term97 _119939 s) = (term97 _119939 s).
Proof. exact (MK_COMB (@lem5720287) (@lem5720286 _119939 s)). Qed.
Lemma lem5720289 {_119939 : Type'} (s : _119939 -> Prop) : (term98 _119939 s) = (term98 _119939 s).
Proof. exact (MK_COMB (@lem5720288 _119939 s) (@lem5720268 _119939 s)). Qed.
Lemma lem5720290 {_119939 : Type'} : (term99 _119939) = (term99 _119939).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720289 _119939 s)). Qed.
Lemma lem5720291 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720292 {_119939 : Type'} : (term100 _119939) = (term100 _119939).
Proof. exact (MK_COMB (@lem5720291 _119939) (@lem5720290 _119939)). Qed.
Lemma lem5720293 {_119939 : Type'} (h1 : term12 _119939) : term100 _119939.
Proof. exact (EQ_MP (@lem5720292 _119939) (@lem5720235 _119939 h1)). Qed.
Lemma lem5720304 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term24 _119939 _119945 op f s) = (term24 _119939 _119945 op f s).
Proof. exact (eq_refl (term24 _119939 _119945 op f s)). Qed.
Lemma lem5720305 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term25 _119939 _119945 op f) = (term25 _119939 _119945 op f).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720304 _119939 _119945 op f s)). Qed.
Lemma lem5720306 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720307 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term26 _119939 _119945 op f) = (term26 _119939 _119945 op f).
Proof. exact (MK_COMB (@lem5720306 _119939) (@lem5720305 _119939 _119945 op f)). Qed.
Lemma lem5720308 {_119939 _119945 : Type'} (op : type1400 _119945) : (term27 _119939 _119945 op) = (term27 _119939 _119945 op).
Proof. exact (fun_ext (fun f : _119939 -> _119945 => @lem5720307 _119939 _119945 op f)). Qed.
Lemma lem5720309 {_119939 _119945 : Type'} : (@all (_119939 -> _119945)) = (@all (_119939 -> _119945)).
Proof. exact (eq_refl (@all (_119939 -> _119945))). Qed.
Lemma lem5720310 {_119939 _119945 : Type'} (op : type1400 _119945) : (term28 _119939 _119945 op) = (term28 _119939 _119945 op).
Proof. exact (MK_COMB (@lem5720309 _119939 _119945) (@lem5720308 _119939 _119945 op)). Qed.
Lemma lem5720311 {_119939 _119945 : Type'} : (term29 _119939 _119945) = (term29 _119939 _119945).
Proof. exact (fun_ext (fun op : type1400 _119945 => @lem5720310 _119939 _119945 op)). Qed.
Lemma lem5720312 {_119945 : Type'} : (@all (_119945 -> _119945 -> _119945)) = (@all (_119945 -> _119945 -> _119945)).
Proof. exact (eq_refl (@all (_119945 -> _119945 -> _119945))). Qed.
Lemma lem5720313 {_119939 _119945 : Type'} : (term11 _119939 _119945) = (term11 _119939 _119945).
Proof. exact (MK_COMB (@lem5720312 _119945) (@lem5720311 _119939 _119945)). Qed.
Lemma lem5720314 {_119939 _119945 : Type'} (h1 : term11 _119939 _119945) : term11 _119939 _119945.
Proof. exact (EQ_MP (@lem5720313 _119939 _119945) (@lem5720262 _119939 _119945 h1)). Qed.
Lemma lem5720332 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term41 _119939 _119945 op f s) : term41 _119939 _119945 op f s.
Proof. exact (h1). Qed.
Lemma lem5720336 {A : Type'} (P : A -> Prop) (Q : Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5720337 {_119939 : Type'} (P : type686 _119939) (Q : Prop) : (term83 _119939 P Q) = (term82 _119939 P Q).
Proof. exact (@lem5720336 (_119939 -> Prop) P Q). Qed.
Lemma lem5720338 {_119939 : Type'} (s : _119939 -> Prop) : (term85 _119939 s) = (term84 _119939 s).
Proof. exact (@lem5720337 _119939 (term86 _119939 s) (@FINITE _119939 s)). Qed.
Lemma lem5720339 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term87 _119939 s t) = (term70 _119939 s t).
Proof. exact (eq_refl (term87 _119939 s t)). Qed.
Lemma lem5720340 {_119939 : Type'} (s : _119939 -> Prop) : (term93 _119939 s) = (term86 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5720339 _119939 s t)). Qed.
Lemma lem5720341 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720342 {_119939 : Type'} (s : _119939 -> Prop) : (term94 _119939 s) = (term95 _119939 s).
Proof. exact (MK_COMB (@lem5720341 _119939) (@lem5720340 _119939 s)). Qed.
Lemma lem5720343 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5720344 {_119939 : Type'} (s : _119939 -> Prop) : (term96 _119939 s) = (term97 _119939 s).
Proof. exact (MK_COMB (@lem5720343) (@lem5720342 _119939 s)). Qed.
Lemma lem5720345 {_119939 : Type'} (s : _119939 -> Prop) : (@FINITE _119939 s) = (@FINITE _119939 s).
Proof. exact (eq_refl (@FINITE _119939 s)). Qed.
Lemma lem5720346 {_119939 : Type'} (s : _119939 -> Prop) : (term85 _119939 s) = (term98 _119939 s).
Proof. exact (MK_COMB (@lem5720344 _119939 s) (@lem5720345 _119939 s)). Qed.
Lemma lem5720347 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5720348 {_119939 : Type'} (s : _119939 -> Prop) : (term101 _119939 s) = (term102 _119939 s).
Proof. exact (MK_COMB (@lem5720347) (@lem5720346 _119939 s)). Qed.
Lemma lem5720349 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term87 _119939 s t) = (term70 _119939 s t).
Proof. exact (eq_refl (term87 _119939 s t)). Qed.
Lemma lem5720350 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5720351 {_119939 : Type'} (s : _119939 -> Prop) (t : _119939 -> Prop) : (term88 _119939 s t) = (term72 _119939 s t).
Proof. exact (MK_COMB (@lem5720350) (@lem5720349 _119939 s t)). Qed.
Lemma lem5720352 {_119939 : Type'} (s : _119939 -> Prop) : (@FINITE _119939 s) = (@FINITE _119939 s).
Proof. exact (eq_refl (@FINITE _119939 s)). Qed.
Lemma lem5720353 {_119939 : Type'} (t : _119939 -> Prop) (s : _119939 -> Prop) : (term89 _119939 t s) = (term74 _119939 t s).
Proof. exact (MK_COMB (@lem5720351 _119939 s t) (@lem5720352 _119939 s)). Qed.
Lemma lem5720354 {_119939 : Type'} (s : _119939 -> Prop) : (term90 _119939 s) = (term76 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5720353 _119939 t s)). Qed.
Lemma lem5720355 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720356 {_119939 : Type'} (s : _119939 -> Prop) : (term84 _119939 s) = (term77 _119939 s).
Proof. exact (MK_COMB (@lem5720355 _119939) (@lem5720354 _119939 s)). Qed.
Lemma lem5720357 {_119939 : Type'} (s : _119939 -> Prop) : ((term85 _119939 s) = (term84 _119939 s)) = ((term98 _119939 s) = (term77 _119939 s)).
Proof. exact (MK_COMB (@lem5720348 _119939 s) (@lem5720356 _119939 s)). Qed.
Lemma lem5720358 {_119939 : Type'} (s : _119939 -> Prop) : (term98 _119939 s) = (term77 _119939 s).
Proof. exact (EQ_MP (@lem5720357 _119939 s) (@lem5720338 _119939 s)). Qed.
Lemma lem5720359 {_119939 : Type'} : (term99 _119939) = (term78 _119939).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720358 _119939 s)). Qed.
Lemma lem5720360 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720361 {_119939 : Type'} : (term100 _119939) = (term79 _119939).
Proof. exact (MK_COMB (@lem5720360 _119939) (@lem5720359 _119939)). Qed.
Lemma lem5720374 {_119939 : Type'} (t : _119939 -> Prop) (s : _119939 -> Prop) : (term74 _119939 t s) = (term74 _119939 t s).
Proof. exact (eq_refl (term74 _119939 t s)). Qed.
Lemma lem5720375 {_119939 : Type'} (s : _119939 -> Prop) : (term76 _119939 s) = (term76 _119939 s).
Proof. exact (fun_ext (fun t : _119939 -> Prop => @lem5720374 _119939 t s)). Qed.
Lemma lem5720376 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720377 {_119939 : Type'} (s : _119939 -> Prop) : (term77 _119939 s) = (term77 _119939 s).
Proof. exact (MK_COMB (@lem5720376 _119939) (@lem5720375 _119939 s)). Qed.
Lemma lem5720378 {_119939 : Type'} : (term78 _119939) = (term78 _119939).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720377 _119939 s)). Qed.
Lemma lem5720379 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720380 {_119939 : Type'} : (term79 _119939) = (term79 _119939).
Proof. exact (MK_COMB (@lem5720379 _119939) (@lem5720378 _119939)). Qed.
Lemma lem5720381 {_119939 : Type'} : (term100 _119939) = (term79 _119939).
Proof. exact (TRANS (@lem5720361 _119939) (@lem5720380 _119939)). Qed.
Lemma lem5720382 {_119939 : Type'} (h1 : term12 _119939) : term79 _119939.
Proof. exact (EQ_MP (@lem5720381 _119939) (@lem5720293 _119939 h1)). Qed.
Lemma lem5720384 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term24 _119939 _119945 op f s) = (term24 _119939 _119945 op f s).
Proof. exact (eq_refl (term24 _119939 _119945 op f s)). Qed.
Lemma lem5720385 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term25 _119939 _119945 op f) = (term25 _119939 _119945 op f).
Proof. exact (fun_ext (fun s : _119939 -> Prop => @lem5720384 _119939 _119945 op f s)). Qed.
Lemma lem5720386 {_119939 : Type'} : (@all (_119939 -> Prop)) = (@all (_119939 -> Prop)).
Proof. exact (eq_refl (@all (_119939 -> Prop))). Qed.
Lemma lem5720387 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) : (term26 _119939 _119945 op f) = (term26 _119939 _119945 op f).
Proof. exact (MK_COMB (@lem5720386 _119939) (@lem5720385 _119939 _119945 op f)). Qed.
Lemma lem5720388 {_119939 _119945 : Type'} (op : type1400 _119945) : (term27 _119939 _119945 op) = (term27 _119939 _119945 op).
Proof. exact (fun_ext (fun f : _119939 -> _119945 => @lem5720387 _119939 _119945 op f)). Qed.
Lemma lem5720389 {_119939 _119945 : Type'} : (@all (_119939 -> _119945)) = (@all (_119939 -> _119945)).
Proof. exact (eq_refl (@all (_119939 -> _119945))). Qed.
Lemma lem5720390 {_119939 _119945 : Type'} (op : type1400 _119945) : (term28 _119939 _119945 op) = (term28 _119939 _119945 op).
Proof. exact (MK_COMB (@lem5720389 _119939 _119945) (@lem5720388 _119939 _119945 op)). Qed.
Lemma lem5720391 {_119939 _119945 : Type'} : (term29 _119939 _119945) = (term29 _119939 _119945).
Proof. exact (fun_ext (fun op : type1400 _119945 => @lem5720390 _119939 _119945 op)). Qed.
Lemma lem5720392 {_119945 : Type'} : (@all (_119945 -> _119945 -> _119945)) = (@all (_119945 -> _119945 -> _119945)).
Proof. exact (eq_refl (@all (_119945 -> _119945 -> _119945))). Qed.
Lemma lem5720394 {_119939 _119945 : Type'} : (term11 _119939 _119945) = (term11 _119939 _119945).
Proof. exact (MK_COMB (@lem5720392 _119945) (@lem5720391 _119939 _119945)). Qed.
Lemma lem5720395 {_119939 _119945 : Type'} (h1 : term11 _119939 _119945) : term11 _119939 _119945.
Proof. exact (EQ_MP (@lem5720394 _119939 _119945) (@lem5720314 _119939 _119945 h1)). Qed.
Lemma lem5720404 {_119939 : Type'} (_71754 : _119939 -> Prop) (h1 : term12 _119939) : term103 _119939 _71754.
Proof. exact (@lem5720382 _119939 h1 _71754). Qed.
Lemma lem5720405 {_119939 : Type'} (_71754 : _119939 -> Prop) : (term103 _119939 _71754) = (term77 _119939 _71754).
Proof. exact (eq_refl (term103 _119939 _71754)). Qed.
Lemma lem5720406 {_119939 : Type'} (_71754 : _119939 -> Prop) (h1 : term12 _119939) : term77 _119939 _71754.
Proof. exact (EQ_MP (@lem5720405 _119939 _71754) (@lem5720404 _119939 _71754 h1)). Qed.
Lemma lem5720407 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) (h1 : term12 _119939) : term104 _119939 _71754 _71755.
Proof. exact (@lem5720406 _119939 _71754 h1 _71755). Qed.
Lemma lem5720408 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) : (term104 _119939 _71754 _71755) = (term74 _119939 _71755 _71754).
Proof. exact (eq_refl (term104 _119939 _71754 _71755)). Qed.
Lemma lem5720409 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) (h1 : term12 _119939) : term74 _119939 _71755 _71754.
Proof. exact (EQ_MP (@lem5720408 _119939 _71755 _71754) (@lem5720407 _119939 _71754 _71755 h1)). Qed.
Lemma lem5720410 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (h1 : term11 _119939 _119945) : term105 _119939 _119945 _71756.
Proof. exact (@lem5720395 _119939 _119945 h1 _71756). Qed.
Lemma lem5720411 {_119939 _119945 : Type'} (_71756 : type1400 _119945) : (term105 _119939 _119945 _71756) = (term28 _119939 _119945 _71756).
Proof. exact (eq_refl (term105 _119939 _119945 _71756)). Qed.
Lemma lem5720412 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (h1 : term11 _119939 _119945) : term28 _119939 _119945 _71756.
Proof. exact (EQ_MP (@lem5720411 _119939 _119945 _71756) (@lem5720410 _119939 _119945 _71756 h1)). Qed.
Lemma lem5720413 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (_71757 : _119939 -> _119945) (h1 : term11 _119939 _119945) : term106 _119939 _119945 _71756 _71757.
Proof. exact (@lem5720412 _119939 _119945 _71756 h1 _71757). Qed.
Lemma lem5720414 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (_71757 : _119939 -> _119945) : (term106 _119939 _119945 _71756 _71757) = (term26 _119939 _119945 _71756 _71757).
Proof. exact (eq_refl (term106 _119939 _119945 _71756 _71757)). Qed.
Lemma lem5720415 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (_71757 : _119939 -> _119945) (h1 : term11 _119939 _119945) : term26 _119939 _119945 _71756 _71757.
Proof. exact (EQ_MP (@lem5720414 _119939 _119945 _71756 _71757) (@lem5720413 _119939 _119945 _71756 _71757 h1)). Qed.
Lemma lem5720416 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (_71757 : _119939 -> _119945) (_71758 : _119939 -> Prop) (h1 : term11 _119939 _119945) : term107 _119939 _119945 _71756 _71757 _71758.
Proof. exact (@lem5720415 _119939 _119945 _71756 _71757 h1 _71758). Qed.
Lemma lem5720417 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (_71757 : _119939 -> _119945) (_71758 : _119939 -> Prop) : (term107 _119939 _119945 _71756 _71757 _71758) = (term24 _119939 _119945 _71756 _71757 _71758).
Proof. exact (eq_refl (term107 _119939 _119945 _71756 _71757 _71758)). Qed.
Lemma lem5720429 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) : (term74 _119939 _71755 _71754) = (term108 _119939 _71755 _71754).
Proof. exact (@lem5719808 (term109 _119939 _71755) (term110 _119939 _71754 _71755) (@FINITE _119939 _71754)). Qed.
Lemma lem5720430 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) (h1 : term12 _119939) : term108 _119939 _71755 _71754.
Proof. exact (EQ_MP (@lem5720429 _119939 _71755 _71754) (@lem5720409 _119939 _71755 _71754 h1)). Qed.
Lemma lem5720436 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term41 _119939 _119945 op f s) : term111 _119939 _119945 op f s.
Proof. exact (proj2 (@lem5720332 _119939 _119945 op f s h1)). Qed.
Lemma lem5720438 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term41 _119939 _119945 op f s) : @FINITE _119939 s.
Proof. exact (proj1 (@lem5720332 _119939 _119945 op f s h1)). Qed.
Lemma lem5720439 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term41 _119939 _119945 op f s) : term112 _119939 s.
Proof. exact (fun h0 : term109 _119939 s => @lem5720438 _119939 _119945 op f s h1). Qed.
Lemma lem5720441 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5720442 {_119939 : Type'} (s : _119939 -> Prop) : (term112 _119939 s) = (@FINITE _119939 s).
Proof. exact (@lem5720441 (@FINITE _119939 s)). Qed.
Lemma lem5720443 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term41 _119939 _119945 op f s) : @FINITE _119939 s.
Proof. exact (EQ_MP (@lem5720442 _119939 s) (@lem5720439 _119939 _119945 op f s h1)). Qed.
Lemma lem5720445 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (_71757 : _119939 -> _119945) (_71758 : _119939 -> Prop) (h1 : term11 _119939 _119945) : term24 _119939 _119945 _71756 _71757 _71758.
Proof. exact (EQ_MP (@lem5720417 _119939 _119945 _71756 _71757 _71758) (@lem5720416 _119939 _119945 _71756 _71757 _71758 h1)). Qed.
Lemma lem5720446 {_119939 _119945 : Type'} (_71756 : type1400 _119945) (_71757 : _119939 -> _119945) (_71758 : _119939 -> Prop) (h1 : term11 _119939 _119945) : term24 _119939 _119945 _71756 _71757 _71758.
Proof. exact (@lem5720445 _119939 _119945 _71756 _71757 _71758 h1). Qed.
Lemma lem5720447 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term11 _119939 _119945) : term24 _119939 _119945 op f s.
Proof. exact (@lem5720446 _119939 _119945 op f s h1). Qed.
Lemma lem5720448 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term11 _119939 _119945) : term114 _119939 _119945 op f s.
Proof. exact (fun h0 : term115 _119939 _119945 op f s => @lem5720447 _119939 _119945 op f s h1). Qed.
Lemma lem5720450 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5720451 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term114 _119939 _119945 op f s) = (term24 _119939 _119945 op f s).
Proof. exact (@lem5720450 (term24 _119939 _119945 op f s)). Qed.
Lemma lem5720452 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term11 _119939 _119945) : term24 _119939 _119945 op f s.
Proof. exact (EQ_MP (@lem5720451 _119939 _119945 op f s) (@lem5720448 _119939 _119945 op f s h1)). Qed.
Lemma lem5720468 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5720469 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term116 _119939 _71755 _71754) = (term117 _119939 _71754 _71755).
Proof. exact (@lem5720468 (@FINITE _119939 _71754) (term110 _119939 _71754 _71755)). Qed.
Lemma lem5720475 {_119939 : Type'} (_71755 : _119939 -> Prop) : (term118 _119939 _71755) = (term118 _119939 _71755).
Proof. exact (eq_refl (term118 _119939 _71755)). Qed.
Lemma lem5720476 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term108 _119939 _71755 _71754) = (term119 _119939 _71754 _71755).
Proof. exact (MK_COMB (@lem5720475 _119939 _71755) (@lem5720469 _119939 _71754 _71755)). Qed.
Lemma lem5720480 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5720481 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term119 _119939 _71754 _71755) = (term120 _119939 _71754 _71755).
Proof. exact (@lem5720480 (@FINITE _119939 _71754) (term109 _119939 _71755) (term110 _119939 _71754 _71755)). Qed.
Lemma lem5720497 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term108 _119939 _71755 _71754) = (term120 _119939 _71754 _71755).
Proof. exact (TRANS (@lem5720476 _119939 _71754 _71755) (@lem5720481 _119939 _71754 _71755)). Qed.
Lemma lem5720498 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5720499 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term121 _119939 _71755 _71754) = (term122 _119939 _71754 _71755).
Proof. exact (MK_COMB (@lem5720498) (@lem5720497 _119939 _71754 _71755)). Qed.
Lemma lem5720515 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term120 _119939 _71754 _71755) = (term120 _119939 _71754 _71755).
Proof. exact (eq_refl (term120 _119939 _71754 _71755)). Qed.
Lemma lem5720516 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : ((term108 _119939 _71755 _71754) = (term120 _119939 _71754 _71755)) = ((term120 _119939 _71754 _71755) = (term120 _119939 _71754 _71755)).
Proof. exact (MK_COMB (@lem5720499 _119939 _71754 _71755) (@lem5720515 _119939 _71754 _71755)). Qed.
Lemma lem5720518 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5720519 (x : Prop) : (x = x) = True.
Proof. exact (@lem5720518 Prop x). Qed.
Lemma lem5720520 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : ((term120 _119939 _71754 _71755) = (term120 _119939 _71754 _71755)) = True.
Proof. exact (@lem5720519 (term120 _119939 _71754 _71755)). Qed.
Lemma lem5720521 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : ((term108 _119939 _71755 _71754) = (term120 _119939 _71754 _71755)) = True.
Proof. exact (TRANS (@lem5720516 _119939 _71754 _71755) (@lem5720520 _119939 _71754 _71755)). Qed.
Lemma lem5720522 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : True = ((term108 _119939 _71755 _71754) = (term120 _119939 _71754 _71755)).
Proof. exact (SYM (@lem5720521 _119939 _71754 _71755)). Qed.
Lemma lem5720523 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term108 _119939 _71755 _71754) = (term120 _119939 _71754 _71755).
Proof. exact (EQ_MP (@lem5720522 _119939 _71754 _71755) (@lem0)). Qed.
Lemma lem5720524 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) (h1 : term12 _119939) : term120 _119939 _71754 _71755.
Proof. exact (EQ_MP (@lem5720523 _119939 _71754 _71755) (@lem5720430 _119939 _71755 _71754 h1)). Qed.
Lemma lem5720526 (b : Prop) (a : Prop) : (a \/ b) = (term123 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5720527 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) : (term120 _119939 _71754 _71755) = (term124 _119939 _71755 _71754).
Proof. exact (@lem5720526 (term70 _119939 _71754 _71755) (@FINITE _119939 _71754)). Qed.
Lemma lem5720529 (a : Prop) (b : Prop) : (term125 a b) = (term126 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5720530 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term127 _119939 _71754 _71755) = (term128 _119939 _71754 _71755).
Proof. exact (@lem5720529 (term109 _119939 _71755) (term110 _119939 _71754 _71755)). Qed.
Lemma lem5720532 (a : Prop) : (term129 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5720533 {_119939 : Type'} (_71755 : _119939 -> Prop) : (term130 _119939 _71755) = (@FINITE _119939 _71755).
Proof. exact (@lem5720532 (@FINITE _119939 _71755)). Qed.
Lemma lem5720534 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5720535 {_119939 : Type'} (_71755 : _119939 -> Prop) : (term131 _119939 _71755) = (term132 _119939 _71755).
Proof. exact (MK_COMB (@lem5720534) (@lem5720533 _119939 _71755)). Qed.
Lemma lem5720537 (a : Prop) : (term129 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5720538 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term133 _119939 _71754 _71755) = (@SUBSET _119939 _71754 _71755).
Proof. exact (@lem5720537 (@SUBSET _119939 _71754 _71755)). Qed.
Lemma lem5720539 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term128 _119939 _71754 _71755) = (term75 _119939 _71754 _71755).
Proof. exact (MK_COMB (@lem5720535 _119939 _71755) (@lem5720538 _119939 _71754 _71755)). Qed.
Lemma lem5720540 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term127 _119939 _71754 _71755) = (term75 _119939 _71754 _71755).
Proof. exact (TRANS (@lem5720530 _119939 _71754 _71755) (@lem5720539 _119939 _71754 _71755)). Qed.
Lemma lem5720541 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5720542 {_119939 : Type'} (_71754 : _119939 -> Prop) (_71755 : _119939 -> Prop) : (term134 _119939 _71754 _71755) = (term135 _119939 _71754 _71755).
Proof. exact (MK_COMB (@lem5720541) (@lem5720540 _119939 _71754 _71755)). Qed.
Lemma lem5720543 {_119939 : Type'} (_71754 : _119939 -> Prop) : (@FINITE _119939 _71754) = (@FINITE _119939 _71754).
Proof. exact (eq_refl (@FINITE _119939 _71754)). Qed.
Lemma lem5720544 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) : (term124 _119939 _71755 _71754) = (term30 _119939 _71755 _71754).
Proof. exact (MK_COMB (@lem5720542 _119939 _71754 _71755) (@lem5720543 _119939 _71754)). Qed.
Lemma lem5720545 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) : (term120 _119939 _71754 _71755) = (term30 _119939 _71755 _71754).
Proof. exact (TRANS (@lem5720527 _119939 _71755 _71754) (@lem5720544 _119939 _71755 _71754)). Qed.
Lemma lem5720547 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term11 _119939 _119945) (h2 : term41 _119939 _119945 op f s) : term136 _119939 _119945 op f s.
Proof. exact (conj (@lem5720443 _119939 _119945 op f s h2) (@lem5720452 _119939 _119945 op f s h1)). Qed.
Lemma lem5720549 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) (h1 : term12 _119939) : term30 _119939 _71755 _71754.
Proof. exact (EQ_MP (@lem5720545 _119939 _71755 _71754) (@lem5720524 _119939 _71754 _71755 h1)). Qed.
Lemma lem5720550 {_119939 : Type'} (_71755 : _119939 -> Prop) (_71754 : _119939 -> Prop) (h1 : term12 _119939) : term30 _119939 _71755 _71754.
Proof. exact (@lem5720549 _119939 _71755 _71754 h1). Qed.
Lemma lem5720551 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) : term137 _119939 _119945 op f s.
Proof. exact (@lem5720550 _119939 s (@support _119939 _119945 op f s) h1). Qed.
Lemma lem5720554 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : term42 _119939 _119945 op f s.
Proof. exact (@lem5720551 _119939 _119945 op f s h1 (@lem5720547 _119939 _119945 op f s h2 h3)). Qed.
Lemma lem5720555 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : term138 _119939 _119945 op f s.
Proof. exact (fun h0 : term111 _119939 _119945 op f s => @lem5720554 _119939 _119945 op f s h1 h2 h3). Qed.
Lemma lem5720557 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5720558 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term138 _119939 _119945 op f s) = (term42 _119939 _119945 op f s).
Proof. exact (@lem5720557 (term42 _119939 _119945 op f s)). Qed.
Lemma lem5720559 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : term42 _119939 _119945 op f s.
Proof. exact (EQ_MP (@lem5720558 _119939 _119945 op f s) (@lem5720555 _119939 _119945 op f s h1 h2 h3)). Qed.
Lemma lem5720562 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5720564 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) : (term111 _119939 _119945 op f s) = (term139 _119939 _119945 op f s).
Proof. exact (@lem5720562 (term42 _119939 _119945 op f s)). Qed.
Lemma lem5720567 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term41 _119939 _119945 op f s) : term139 _119939 _119945 op f s.
Proof. exact (EQ_MP (@lem5720564 _119939 _119945 op f s) (@lem5720436 _119939 _119945 op f s h1)). Qed.
Lemma lem5720570 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : False.
Proof. exact (@lem5720567 _119939 _119945 op f s h3 (@lem5720559 _119939 _119945 op f s h1 h2 h3)). Qed.
Lemma lem5720571 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : term140.
Proof. exact (fun h0 : ~ False => @lem5720570 _119939 _119945 op f s h1 h2 h3). Qed.
Lemma lem5720573 (p : Prop) : (term113 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5720574 : term140 = False.
Proof. exact (@lem5720573 False). Qed.
Lemma lem5720575 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : False.
Proof. exact (EQ_MP (@lem5720574) (@lem5720571 _119939 _119945 op f s h1 h2 h3)). Qed.
Lemma lem5720576 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : (term11 _119939 _119945) = False.
Proof. exact (prop_ext (fun h4 : term11 _119939 _119945 => @lem5720575 _119939 _119945 op f s h1 h2 h3) (fun h4 : False => @lem5720395 _119939 _119945 h2)). Qed.
Lemma lem5720577 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : False.
Proof. exact (EQ_MP (@lem5720576 _119939 _119945 op f s h1 h2 h3) (@lem5720395 _119939 _119945 h2)). Qed.
Lemma lem5720578 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : (term41 _119939 _119945 op f s) = False.
Proof. exact (prop_ext (fun h4 : term41 _119939 _119945 op f s => @lem5720577 _119939 _119945 op f s h1 h2 h3) (fun h4 : False => @lem5720332 _119939 _119945 op f s h3)). Qed.
Lemma lem5720579 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : False.
Proof. exact (EQ_MP (@lem5720578 _119939 _119945 op f s h1 h2 h3) (@lem5720332 _119939 _119945 op f s h3)). Qed.
Lemma lem5720580 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : (term11 _119939 _119945) = False.
Proof. exact (prop_ext (fun h4 : term11 _119939 _119945 => @lem5720579 _119939 _119945 op f s h1 h2 h3) (fun h4 : False => @lem5720314 _119939 _119945 h2)). Qed.
Lemma lem5720581 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (s : _119939 -> Prop) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term41 _119939 _119945 op f s) : False.
Proof. exact (EQ_MP (@lem5720580 _119939 _119945 op f s h1 h2 h3) (@lem5720314 _119939 _119945 h2)). Qed.
Lemma lem5720582 {_119939 _119945 : Type'} (op : type1400 _119945) (f : _119939 -> _119945) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term51 _119939 _119945 op f) : False.
Proof. exact (ex_elim (@lem5720264 _119939 _119945 op f h3) (fun s : _119939 -> Prop => fun h0 : term50 _119939 _119945 op f s => @lem5720581 _119939 _119945 op f s h1 h2 h0)). Qed.
Lemma lem5720583 {_119939 _119945 : Type'} (op : type1400 _119945) (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term60 _119939 _119945 op) : False.
Proof. exact (ex_elim (@lem5720263 _119939 _119945 op h3) (fun f : _119939 -> _119945 => fun h0 : term59 _119939 _119945 op f => @lem5720582 _119939 _119945 op f h1 h2 h0)). Qed.
Lemma lem5720584 {_119939 _119945 : Type'} (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term10 _119939 _119945) : False.
Proof. exact (ex_elim (@lem5720081 _119939 _119945 h3) (fun op : type1400 _119945 => fun h0 : term67 _119939 _119945 op => @lem5720583 _119939 _119945 op h1 h2 h0)). Qed.
Lemma lem5720585 {_119939 _119945 : Type'} (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term10 _119939 _119945) : (term11 _119939 _119945) = False.
Proof. exact (prop_ext (fun h4 : term11 _119939 _119945 => @lem5720584 _119939 _119945 h1 h2 h3) (fun h4 : False => @lem5720262 _119939 _119945 h2)). Qed.
Lemma lem5720586 {_119939 _119945 : Type'} (h1 : term12 _119939) (h2 : term11 _119939 _119945) (h3 : term10 _119939 _119945) : False.
Proof. exact (EQ_MP (@lem5720585 _119939 _119945 h1 h2 h3) (@lem5720262 _119939 _119945 h2)). Qed.
Lemma lem5720587 {_119939 _119945 : Type'} (h1 : term12 _119939) (h2 : term10 _119939 _119945) : term17 _119939 _119945.
Proof. exact (fun h0 : term11 _119939 _119945 => @lem5720586 _119939 _119945 h1 h0 h2). Qed.
Lemma lem5720588 {_119939 _119945 : Type'} : (term17 _119939 _119945) = (term18 _119939 _119945).
Proof. exact (@lem69 (term11 _119939 _119945)). Qed.
Lemma lem5720589 {_119939 _119945 : Type'} (h1 : term12 _119939) (h2 : term10 _119939 _119945) : term18 _119939 _119945.
Proof. exact (EQ_MP (@lem5720588 _119939 _119945) (@lem5720587 _119939 _119945 h1 h2)). Qed.
Lemma lem5720590 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : term21 _119939 _119945.
Proof. exact (fun h0 : term12 _119939 => @lem5720589 _119939 _119945 h0 h1). Qed.
Lemma lem5720591 {_119939 _119945 : Type'} : term23 _119939 _119945.
Proof. exact (fun h0 : term10 _119939 _119945 => @lem5720590 _119939 _119945 h0). Qed.
Lemma lem5720592 {_119939 _119945 : Type'} : term13 _119939 _119945.
Proof. exact (EQ_MP (@lem5720000 _119939 _119945) (@lem5720591 _119939 _119945)). Qed.
Lemma lem5720594 {_119939 _119945 : Type'} : term13 _119939 _119945.
Proof. exact (@lem5719832 _119939 _119945 (@lem5720592 _119939 _119945)). Qed.
Lemma lem5720595 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : term20 _119939 _119945.
Proof. exact (@lem5720594 _119939 _119945 (@lem5719813 _119939 _119945 h1)). Qed.
Lemma lem5720596 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : term17 _119939 _119945.
Proof. exact (@lem5720595 _119939 _119945 h1 (@lem5719815 _119939)). Qed.
Lemma lem5720597 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : False.
Proof. exact (@lem5720596 _119939 _119945 h1 (@lem5719814 _119939 _119945)). Qed.
Lemma lem5720598 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : (term10 _119939 _119945) = False.
Proof. exact (prop_ext (fun h2 : term10 _119939 _119945 => @lem5720597 _119939 _119945 h1) (fun h2 : False => @lem5719813 _119939 _119945 h1)). Qed.
Lemma lem5720599 {_119939 _119945 : Type'} (h1 : term10 _119939 _119945) : False.
Proof. exact (EQ_MP (@lem5720598 _119939 _119945 h1) (@lem5719813 _119939 _119945 h1)). Qed.
Lemma lem5720600 {_119939 _119945 : Type'} : term9 _119939 _119945.
Proof. exact (fun h0 : term10 _119939 _119945 => @lem5720599 _119939 _119945 h0). Qed.
Lemma lem5720601 {_119939 _119945 : Type'} : term8 _119939 _119945.
Proof. exact (EQ_MP (@lem5719812 _119939 _119945) (@lem5720600 _119939 _119945)). Qed.
