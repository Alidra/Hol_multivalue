Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FUNCTION_FACTORS_LEFT_GEN_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import SKOLEM_THM_spec.
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
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18964_spec.
Require Import thm18965_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem3576801 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3576802 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3576803 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3576802 t1) (@lem3576801 t1)). Qed.
Lemma lem3576804 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3576803 t1 t2). Qed.
Lemma lem3576805 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3576806 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3576805 t1 t2) (@lem3576804 t1 t2)). Qed.
Lemma lem3576807 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3576806 t1 t2 t3). Qed.
Lemma lem3576808 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3576809 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3576808 t1 t2 t3) (@lem3576807 t1 t2 t3)). Qed.
Lemma lem3576810 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3576809 t1 t2 t3)). Qed.
Lemma lem3576812 {A B : Type'} (P : type1413 A B) (h1 : (term7 A B P) = (term8 A B P)) : (term7 A B P) = (term8 A B P).
Proof. exact (h1). Qed.
Lemma lem3576813 {A B : Type'} (P : type1413 A B) (h1 : (term7 A B P) = (term8 A B P)) : (term8 A B P) = (term7 A B P).
Proof. exact (SYM (@lem3576812 A B P h1)). Qed.
Lemma lem3576814 {A B : Type'} (P : type1413 A B) (h1 : (term8 A B P) = (term7 A B P)) : (term8 A B P) = (term7 A B P).
Proof. exact (h1). Qed.
Lemma lem3576815 {A B : Type'} (P : type1413 A B) (h1 : (term8 A B P) = (term7 A B P)) : (term7 A B P) = (term8 A B P).
Proof. exact (SYM (@lem3576814 A B P h1)). Qed.
Lemma lem3576816 {A B : Type'} (P : type1413 A B) : ((term7 A B P) = (term8 A B P)) = ((term8 A B P) = (term7 A B P)).
Proof. exact (prop_ext (fun h1 : (term7 A B P) = (term8 A B P) => @lem3576813 A B P h1) (fun h1 : (term8 A B P) = (term7 A B P) => @lem3576815 A B P h1)). Qed.
Lemma lem3576817 {A B : Type'} : (term9 A B) = (term10 A B).
Proof. exact (fun_ext (fun P : type1413 A B => @lem3576816 A B P)). Qed.
Lemma lem3576818 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem3576819 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem3576818 A B) (@lem3576817 A B)). Qed.
Lemma lem3576820 {A B : Type'} : term12 A B.
Proof. exact (EQ_MP (@lem3576819 A B) (@lem13546 A B)). Qed.
Lemma lem3576821 {A B : Type'} (P : type1413 A B) : term13 A B P.
Proof. exact (@lem3576820 A B P). Qed.
Lemma lem3576822 {A B : Type'} (P : type1413 A B) : (term13 A B P) = ((term8 A B P) = (term7 A B P)).
Proof. exact (eq_refl (term13 A B P)). Qed.
Lemma lem3576824 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3576825 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3576826 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3576825 t1) (@lem3576824 t1)). Qed.
Lemma lem3576827 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3576826 t1 t2). Qed.
Lemma lem3576828 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3576829 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3576828 t1 t2) (@lem3576827 t1 t2)). Qed.
Lemma lem3576830 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3576829 t1 t2 t3). Qed.
Lemma lem3576831 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3576832 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3576831 t1 t2 t3) (@lem3576830 t1 t2 t3)). Qed.
Lemma lem3576833 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3576832 t1 t2 t3)). Qed.
Lemma lem3576835 (p : Prop) : p = (term14 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3576836 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)) = (term17 _91703 _91706 _91707 P k f g).
Proof. exact (@lem3576835 ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g))). Qed.
Lemma lem3576837 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term17 _91703 _91706 _91707 P k f g) = ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)).
Proof. exact (SYM (@lem3576836 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576838 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : term18 _91703 _91706 _91707 P k f g.
Proof. exact (h1). Qed.
Lemma lem3576841 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term17 _91703 _91706 _91707 P k f g) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (h1). Qed.
Lemma lem3576842 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term19 _91703 _91706 _91707 P k f g.
Proof. exact (fun h0 : term17 _91703 _91706 _91707 P k f g => @lem3576841 _91703 _91706 _91707 P k f g h0). Qed.
Lemma lem3576843 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term19 _91703 _91706 _91707 P k f g) : term19 _91703 _91706 _91707 P k f g.
Proof. exact (h1). Qed.
Lemma lem3576844 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term17 _91703 _91706 _91707 P k f g) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (h1). Qed.
Lemma lem3576845 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term17 _91703 _91706 _91707 P k f g) (h2 : term19 _91703 _91706 _91707 P k f g) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (@lem3576843 _91703 _91706 _91707 P k f g h2 (@lem3576844 _91703 _91706 _91707 P k f g h1)). Qed.
Lemma lem3576846 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term17 _91703 _91706 _91707 P k f g) : term20 _91703 _91706 _91707 P k f g.
Proof. exact (fun h0 : term19 _91703 _91706 _91707 P k f g => @lem3576845 _91703 _91706 _91707 P k f g h1 h0). Qed.
Lemma lem3576847 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term19 _91703 _91706 _91707 P k f g) : term19 _91703 _91706 _91707 P k f g.
Proof. exact (h1). Qed.
Lemma lem3576848 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term17 _91703 _91706 _91707 P k f g) (h2 : term19 _91703 _91706 _91707 P k f g) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (@lem3576846 _91703 _91706 _91707 P k f g h1 (@lem3576847 _91703 _91706 _91707 P k f g h2)). Qed.
Lemma lem3576849 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term19 _91703 _91706 _91707 P k f g) : term19 _91703 _91706 _91707 P k f g.
Proof. exact (fun h0 : term17 _91703 _91706 _91707 P k f g => @lem3576848 _91703 _91706 _91707 P k f g h0 h1). Qed.
Lemma lem3576850 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term21 _91703 _91706 _91707 P k f g.
Proof. exact (fun h0 : term19 _91703 _91706 _91707 P k f g => @lem3576849 _91703 _91706 _91707 P k f g h0). Qed.
Lemma lem3576853 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term19 _91703 _91706 _91707 P k f g.
Proof. exact (@lem3576850 _91703 _91706 _91707 P k f g (@lem3576842 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576854 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term19 _91703 _91706 _91707 P k f g.
Proof. exact (@lem3576853 _91703 _91706 _91707 P k f g). Qed.
Lemma lem3576872 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3576873 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term17 _91703 _91706 _91707 P k f g) = (term22 _91703 _91706 _91707 P k f g).
Proof. exact (@lem3576872 (term18 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576875 (t : Prop) : (term23 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3576876 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term22 _91703 _91706 _91707 P k f g) = ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)).
Proof. exact (@lem3576875 ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g))). Qed.
Lemma lem3576877 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term17 _91703 _91706 _91707 P k f g) = ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)).
Proof. exact (TRANS (@lem3576873 _91703 _91706 _91707 P k f g) (@lem3576876 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576896 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term24 _91703 _91706 _91707 k f g) = (term25 _91703 _91706 _91707 k f g).
Proof. exact (fun_ext (fun P : _91706 -> Prop => @lem3576877 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576897 {_91706 : Type'} : (@all (_91706 -> Prop)) = (@all (_91706 -> Prop)).
Proof. exact (eq_refl (@all (_91706 -> Prop))). Qed.
Lemma lem3576898 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term26 _91703 _91706 _91707 k f g) = (term27 _91703 _91706 _91707 k f g).
Proof. exact (MK_COMB (@lem3576897 _91706) (@lem3576896 _91703 _91706 _91707 k f g)). Qed.
Lemma lem3576903 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) : (term28 _91703 _91706 _91707 f g) = (term29 _91703 _91706 _91707 f g).
Proof. exact (fun_ext (fun k : _91706 -> _91707 => @lem3576898 _91703 _91706 _91707 k f g)). Qed.
Lemma lem3576904 {_91706 _91707 : Type'} : (@all (_91706 -> _91707)) = (@all (_91706 -> _91707)).
Proof. exact (eq_refl (@all (_91706 -> _91707))). Qed.
Lemma lem3576905 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) : (term30 _91703 _91706 _91707 f g) = (term31 _91703 _91706 _91707 f g).
Proof. exact (MK_COMB (@lem3576904 _91706 _91707) (@lem3576903 _91703 _91706 _91707 f g)). Qed.
Lemma lem3576910 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : (term32 _91703 _91706 _91707 g) = (term33 _91703 _91706 _91707 g).
Proof. exact (fun_ext (fun f : _91706 -> _91703 => @lem3576905 _91703 _91706 _91707 f g)). Qed.
Lemma lem3576911 {_91703 _91706 : Type'} : (@all (_91706 -> _91703)) = (@all (_91706 -> _91703)).
Proof. exact (eq_refl (@all (_91706 -> _91703))). Qed.
Lemma lem3576912 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : (term34 _91703 _91706 _91707 g) = (term35 _91703 _91706 _91707 g).
Proof. exact (MK_COMB (@lem3576911 _91703 _91706) (@lem3576910 _91703 _91706 _91707 g)). Qed.
Lemma lem3576917 {_91703 _91706 _91707 : Type'} : (term36 _91703 _91706 _91707) = (term37 _91703 _91706 _91707).
Proof. exact (fun_ext (fun g : _91707 -> _91703 => @lem3576912 _91703 _91706 _91707 g)). Qed.
Lemma lem3576918 {_91703 _91707 : Type'} : (@all (_91707 -> _91703)) = (@all (_91707 -> _91703)).
Proof. exact (eq_refl (@all (_91707 -> _91703))). Qed.
Lemma lem3576927 {_91703 _91706 _91707 : Type'} : (term38 _91703 _91706 _91707) = (term39 _91703 _91706 _91707).
Proof. exact (MK_COMB (@lem3576918 _91703 _91707) (@lem3576917 _91703 _91706 _91707)). Qed.
Lemma lem3576936 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term40 _91703 _91706 _91707 P k f x g y) = (term40 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term40 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3576937 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term41 _91703 _91706 _91707 P k f g y) = (term41 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3576936 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3576938 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3576939 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term42 _91703 _91706 _91707 P k f g y) = (term42 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3576938 _91706) (@lem3576937 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3576940 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term43 _91703 _91706 _91707 P k f g) = (term43 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3576939 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3576941 {_91707 : Type'} : (@all _91707) = (@all _91707).
Proof. exact (eq_refl (@all _91707)). Qed.
Lemma lem3576942 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term16 _91703 _91706 _91707 P k f g) = (term16 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3576941 _91707) (@lem3576940 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576947 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term44 _91703 _91706 _91707 P f g k x) = (term44 _91703 _91706 _91707 P f g k x).
Proof. exact (eq_refl (term44 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3576948 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term45 _91703 _91706 _91707 P f g k) = (term45 _91703 _91706 _91707 P f g k).
Proof. exact (fun_ext (fun x : _91706 => @lem3576947 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3576949 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3576950 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term15 _91703 _91706 _91707 P f g k) = (term15 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3576949 _91706) (@lem3576948 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3576951 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3576952 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term46 _91703 _91706 _91707 P f g k) = (term46 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3576951) (@lem3576950 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3576953 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)) = ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)).
Proof. exact (MK_COMB (@lem3576952 _91703 _91706 _91707 P f g k) (@lem3576942 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576954 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term25 _91703 _91706 _91707 k f g) = (term25 _91703 _91706 _91707 k f g).
Proof. exact (fun_ext (fun P : _91706 -> Prop => @lem3576953 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3576955 {_91706 : Type'} : (@all (_91706 -> Prop)) = (@all (_91706 -> Prop)).
Proof. exact (eq_refl (@all (_91706 -> Prop))). Qed.
Lemma lem3576956 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term27 _91703 _91706 _91707 k f g) = (term27 _91703 _91706 _91707 k f g).
Proof. exact (MK_COMB (@lem3576955 _91706) (@lem3576954 _91703 _91706 _91707 k f g)). Qed.
Lemma lem3576957 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) : (term29 _91703 _91706 _91707 f g) = (term29 _91703 _91706 _91707 f g).
Proof. exact (fun_ext (fun k : _91706 -> _91707 => @lem3576956 _91703 _91706 _91707 k f g)). Qed.
Lemma lem3576958 {_91706 _91707 : Type'} : (@all (_91706 -> _91707)) = (@all (_91706 -> _91707)).
Proof. exact (eq_refl (@all (_91706 -> _91707))). Qed.
Lemma lem3576959 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) : (term31 _91703 _91706 _91707 f g) = (term31 _91703 _91706 _91707 f g).
Proof. exact (MK_COMB (@lem3576958 _91706 _91707) (@lem3576957 _91703 _91706 _91707 f g)). Qed.
Lemma lem3576960 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : (term33 _91703 _91706 _91707 g) = (term33 _91703 _91706 _91707 g).
Proof. exact (fun_ext (fun f : _91706 -> _91703 => @lem3576959 _91703 _91706 _91707 f g)). Qed.
Lemma lem3576961 {_91703 _91706 : Type'} : (@all (_91706 -> _91703)) = (@all (_91706 -> _91703)).
Proof. exact (eq_refl (@all (_91706 -> _91703))). Qed.
Lemma lem3576962 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : (term35 _91703 _91706 _91707 g) = (term35 _91703 _91706 _91707 g).
Proof. exact (MK_COMB (@lem3576961 _91703 _91706) (@lem3576960 _91703 _91706 _91707 g)). Qed.
Lemma lem3576963 {_91703 _91706 _91707 : Type'} : (term37 _91703 _91706 _91707) = (term37 _91703 _91706 _91707).
Proof. exact (fun_ext (fun g : _91707 -> _91703 => @lem3576962 _91703 _91706 _91707 g)). Qed.
Lemma lem3576964 {_91703 _91707 : Type'} : (@all (_91707 -> _91703)) = (@all (_91707 -> _91703)).
Proof. exact (eq_refl (@all (_91707 -> _91703))). Qed.
Lemma lem3576965 {_91703 _91706 _91707 : Type'} : (term39 _91703 _91706 _91707) = (term39 _91703 _91706 _91707).
Proof. exact (MK_COMB (@lem3576964 _91703 _91707) (@lem3576963 _91703 _91706 _91707)). Qed.
Lemma lem3577016 {_91703 _91706 _91707 : Type'} : (term38 _91703 _91706 _91707) = (term39 _91703 _91706 _91707).
Proof. exact (TRANS (@lem3576927 _91703 _91706 _91707) (@lem3576965 _91703 _91706 _91707)). Qed.
Lemma lem3577017 {_91703 _91706 _91707 : Type'} : (term39 _91703 _91706 _91707) = (term38 _91703 _91706 _91707).
Proof. exact (SYM (@lem3577016 _91703 _91706 _91707)). Qed.
Lemma lem3577019 (p : Prop) : p = (term14 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3577020 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)) = (term17 _91703 _91706 _91707 P k f g).
Proof. exact (@lem3577019 ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g))). Qed.
Lemma lem3577021 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term17 _91703 _91706 _91707 P k f g) = ((term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g)).
Proof. exact (SYM (@lem3577020 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577022 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : term18 _91703 _91706 _91707 P k f g.
Proof. exact (h1). Qed.
Lemma lem3577031 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term47 _91703 _91706 _91707 P f g k x) = (term48 _91703 _91706 _91707 P f g k x).
Proof. exact (@lem17362 (P x) ((f x) = (term49 _91703 _91706 _91707 g k x))). Qed.
Lemma lem3577036 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term44 _91703 _91706 _91707 P f g k x) = (term50 _91703 _91706 _91707 P f g k x).
Proof. exact (@lem17265 (P x) ((f x) = (term49 _91703 _91706 _91707 g k x))). Qed.
Lemma lem3577037 {_91706 : Type'} (P : _91706 -> Prop) : (term51 _91706 P) = (term52 _91706 P).
Proof. exact (@lem18392 _91706 P). Qed.
Lemma lem3577038 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term53 _91703 _91706 _91707 P f g k) = (term54 _91703 _91706 _91707 P f g k).
Proof. exact (@lem3577037 _91706 (term45 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577039 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term55 _91703 _91706 _91707 P f g k x) = (term44 _91703 _91706 _91707 P f g k x).
Proof. exact (eq_refl (term55 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577040 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3577041 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term56 _91703 _91706 _91707 P f g k x) = (term47 _91703 _91706 _91707 P f g k x).
Proof. exact (MK_COMB (@lem3577040) (@lem3577039 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577042 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term56 _91703 _91706 _91707 P f g k x) = (term48 _91703 _91706 _91707 P f g k x).
Proof. exact (TRANS (@lem3577041 _91703 _91706 _91707 P f g k x) (@lem3577031 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577043 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term57 _91703 _91706 _91707 P f g k) = (term58 _91703 _91706 _91707 P f g k).
Proof. exact (fun_ext (fun x : _91706 => @lem3577042 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577044 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577045 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term54 _91703 _91706 _91707 P f g k) = (term59 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577044 _91706) (@lem3577043 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577046 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term53 _91703 _91706 _91707 P f g k) = (term59 _91703 _91706 _91707 P f g k).
Proof. exact (TRANS (@lem3577038 _91703 _91706 _91707 P f g k) (@lem3577045 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577047 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term45 _91703 _91706 _91707 P f g k) = (term60 _91703 _91706 _91707 P f g k).
Proof. exact (fun_ext (fun x : _91706 => @lem3577036 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577048 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3577049 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term15 _91703 _91706 _91707 P f g k) = (term61 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577048 _91706) (@lem3577047 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577058 {_91706 _91707 : Type'} (P : _91706 -> Prop) (y : _91707) (k : _91706 -> _91707) (x : _91706) : (term62 _91706 _91707 P y k x) = (term63 _91706 _91707 P y k x).
Proof. exact (@lem17045 (P x) (y = (k x))). Qed.
Lemma lem3577063 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : ((f x) = (g y)) = ((f x) = (g y)).
Proof. exact (eq_refl ((f x) = (g y))). Qed.
Lemma lem3577068 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term64 _91703 _91706 _91707 P k f x g y) = (term65 _91703 _91706 _91707 P k f x g y).
Proof. exact (@lem17362 (term66 _91706 _91707 P y k x) ((f x) = (g y))). Qed.
Lemma lem3577069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577070 {_91706 _91707 : Type'} (P : _91706 -> Prop) (y : _91707) (k : _91706 -> _91707) (x : _91706) : (term67 _91706 _91707 P y k x) = (term68 _91706 _91707 P y k x).
Proof. exact (MK_COMB (@lem3577069) (@lem3577058 _91706 _91707 P y k x)). Qed.
Lemma lem3577071 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term69 _91703 _91706 _91707 P k f x g y) = (term70 _91703 _91706 _91707 P k f x g y).
Proof. exact (MK_COMB (@lem3577070 _91706 _91707 P y k x) (@lem3577063 _91703 _91706 _91707 f x g y)). Qed.
Lemma lem3577072 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term40 _91703 _91706 _91707 P k f x g y) = (term69 _91703 _91706 _91707 P k f x g y).
Proof. exact (@lem17265 (term66 _91706 _91707 P y k x) ((f x) = (g y))). Qed.
Lemma lem3577073 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term40 _91703 _91706 _91707 P k f x g y) = (term70 _91703 _91706 _91707 P k f x g y).
Proof. exact (TRANS (@lem3577072 _91703 _91706 _91707 P k f x g y) (@lem3577071 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577074 {_91706 : Type'} (P : _91706 -> Prop) : (term51 _91706 P) = (term52 _91706 P).
Proof. exact (@lem18392 _91706 P). Qed.
Lemma lem3577075 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term71 _91703 _91706 _91707 P k f g y) = (term72 _91703 _91706 _91707 P k f g y).
Proof. exact (@lem3577074 _91706 (term41 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577076 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term73 _91703 _91706 _91707 P k f g y x) = (term40 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term73 _91703 _91706 _91707 P k f g y x)). Qed.
Lemma lem3577077 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3577078 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term74 _91703 _91706 _91707 P k f g y x) = (term64 _91703 _91706 _91707 P k f x g y).
Proof. exact (MK_COMB (@lem3577077) (@lem3577076 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577079 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term74 _91703 _91706 _91707 P k f g y x) = (term65 _91703 _91706 _91707 P k f x g y).
Proof. exact (TRANS (@lem3577078 _91703 _91706 _91707 P k f x g y) (@lem3577068 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577080 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term75 _91703 _91706 _91707 P k f g y) = (term76 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3577079 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577081 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577082 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term72 _91703 _91706 _91707 P k f g y) = (term77 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577081 _91706) (@lem3577080 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577083 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term71 _91703 _91706 _91707 P k f g y) = (term77 _91703 _91706 _91707 P k f g y).
Proof. exact (TRANS (@lem3577075 _91703 _91706 _91707 P k f g y) (@lem3577082 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577084 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term41 _91703 _91706 _91707 P k f g y) = (term78 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3577073 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577085 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3577086 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term42 _91703 _91706 _91707 P k f g y) = (term79 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577085 _91706) (@lem3577084 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577087 {_91707 : Type'} (P : _91707 -> Prop) : (term51 _91707 P) = (term52 _91707 P).
Proof. exact (@lem18392 _91707 P). Qed.
Lemma lem3577088 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term80 _91703 _91706 _91707 P k f g) = (term81 _91703 _91706 _91707 P k f g).
Proof. exact (@lem3577087 _91707 (term43 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577089 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term82 _91703 _91706 _91707 P k f g y) = (term42 _91703 _91706 _91707 P k f g y).
Proof. exact (eq_refl (term82 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3577091 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term83 _91703 _91706 _91707 P k f g y) = (term71 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577090) (@lem3577089 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577092 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term83 _91703 _91706 _91707 P k f g y) = (term77 _91703 _91706 _91707 P k f g y).
Proof. exact (TRANS (@lem3577091 _91703 _91706 _91707 P k f g y) (@lem3577083 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577093 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term84 _91703 _91706 _91707 P k f g) = (term85 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577092 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577094 {_91707 : Type'} : (@ex _91707) = (@ex _91707).
Proof. exact (eq_refl (@ex _91707)). Qed.
Lemma lem3577095 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term81 _91703 _91706 _91707 P k f g) = (term86 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577094 _91707) (@lem3577093 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577096 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term80 _91703 _91706 _91707 P k f g) = (term86 _91703 _91706 _91707 P k f g).
Proof. exact (TRANS (@lem3577088 _91703 _91706 _91707 P k f g) (@lem3577095 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577097 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term43 _91703 _91706 _91707 P k f g) = (term87 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577086 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577098 {_91707 : Type'} : (@all _91707) = (@all _91707).
Proof. exact (eq_refl (@all _91707)). Qed.
Lemma lem3577099 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term16 _91703 _91706 _91707 P k f g) = (term88 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577098 _91707) (@lem3577097 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3577101 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term89 _91703 _91706 _91707 P f g k) = (term90 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577100) (@lem3577046 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577102 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term91 _91703 _91706 _91707 P k f g) = (term92 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577101 _91703 _91706 _91707 P f g k) (@lem3577099 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3577104 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term93 _91703 _91706 _91707 P f g k) = (term94 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577103) (@lem3577049 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577105 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term95 _91703 _91706 _91707 P k f g) = (term96 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577104 _91703 _91706 _91707 P f g k) (@lem3577096 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577107 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term97 _91703 _91706 _91707 P k f g) = (term98 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577106) (@lem3577105 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577108 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term99 _91703 _91706 _91707 P k f g) = (term100 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577107 _91703 _91706 _91707 P k f g) (@lem3577102 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577109 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term18 _91703 _91706 _91707 P k f g) = (term99 _91703 _91706 _91707 P k f g).
Proof. exact (@lem17646 (term15 _91703 _91706 _91707 P f g k) (term16 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577110 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term18 _91703 _91706 _91707 P k f g) = (term100 _91703 _91706 _91707 P k f g).
Proof. exact (TRANS (@lem3577109 _91703 _91706 _91707 P k f g) (@lem3577108 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577293 {A : Type'} (P : Prop) (Q : A -> Prop) : (term101 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3577294 {_91707 : Type'} (P : Prop) (Q : _91707 -> Prop) : (term101 _91707 P Q) = (term102 _91707 P Q).
Proof. exact (@lem3577293 _91707 P Q). Qed.
Lemma lem3577295 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term103 _91703 _91706 _91707 P k f g) = (term104 _91703 _91706 _91707 P k f g).
Proof. exact (@lem3577294 _91707 (term61 _91703 _91706 _91707 P f g k) (term85 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577296 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term105 _91703 _91706 _91707 P k f g y) = (term77 _91703 _91706 _91707 P k f g y).
Proof. exact (eq_refl (term105 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577297 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term106 _91703 _91706 _91707 P k f g) = (term85 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577296 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577298 {_91707 : Type'} : (@ex _91707) = (@ex _91707).
Proof. exact (eq_refl (@ex _91707)). Qed.
Lemma lem3577299 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term107 _91703 _91706 _91707 P k f g) = (term86 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577298 _91707) (@lem3577297 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577300 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term94 _91703 _91706 _91707 P f g k) = (term94 _91703 _91706 _91707 P f g k).
Proof. exact (eq_refl (term94 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577301 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term103 _91703 _91706 _91707 P k f g) = (term96 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577300 _91703 _91706 _91707 P f g k) (@lem3577299 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577302 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577303 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term108 _91703 _91706 _91707 P k f g) = (term109 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577302) (@lem3577301 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577304 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term105 _91703 _91706 _91707 P k f g y) = (term77 _91703 _91706 _91707 P k f g y).
Proof. exact (eq_refl (term105 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577305 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term94 _91703 _91706 _91707 P f g k) = (term94 _91703 _91706 _91707 P f g k).
Proof. exact (eq_refl (term94 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577306 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term110 _91703 _91706 _91707 P k f g y) = (term111 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577305 _91703 _91706 _91707 P f g k) (@lem3577304 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577307 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term112 _91703 _91706 _91707 P k f g) = (term113 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577306 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577308 {_91707 : Type'} : (@ex _91707) = (@ex _91707).
Proof. exact (eq_refl (@ex _91707)). Qed.
Lemma lem3577309 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term104 _91703 _91706 _91707 P k f g) = (term114 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577308 _91707) (@lem3577307 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577310 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : ((term103 _91703 _91706 _91707 P k f g) = (term104 _91703 _91706 _91707 P k f g)) = ((term96 _91703 _91706 _91707 P k f g) = (term114 _91703 _91706 _91707 P k f g)).
Proof. exact (MK_COMB (@lem3577303 _91703 _91706 _91707 P k f g) (@lem3577309 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577311 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term96 _91703 _91706 _91707 P k f g) = (term114 _91703 _91706 _91707 P k f g).
Proof. exact (EQ_MP (@lem3577310 _91703 _91706 _91707 P k f g) (@lem3577295 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577313 {A : Type'} (P : Prop) (Q : A -> Prop) : (term101 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3577314 {_91706 : Type'} (P : Prop) (Q : _91706 -> Prop) : (term101 _91706 P Q) = (term102 _91706 P Q).
Proof. exact (@lem3577313 _91706 P Q). Qed.
Lemma lem3577315 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term115 _91703 _91706 _91707 P k f g y) = (term116 _91703 _91706 _91707 P k f g y).
Proof. exact (@lem3577314 _91706 (term61 _91703 _91706 _91707 P f g k) (term76 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577316 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term117 _91703 _91706 _91707 P k f g y x) = (term65 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term117 _91703 _91706 _91707 P k f g y x)). Qed.
Lemma lem3577317 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term118 _91703 _91706 _91707 P k f g y) = (term76 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3577316 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577318 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577319 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term119 _91703 _91706 _91707 P k f g y) = (term77 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577318 _91706) (@lem3577317 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577320 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term94 _91703 _91706 _91707 P f g k) = (term94 _91703 _91706 _91707 P f g k).
Proof. exact (eq_refl (term94 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577321 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term115 _91703 _91706 _91707 P k f g y) = (term111 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577320 _91703 _91706 _91707 P f g k) (@lem3577319 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577323 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term120 _91703 _91706 _91707 P k f g y) = (term121 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577322) (@lem3577321 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577324 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term117 _91703 _91706 _91707 P k f g y x) = (term65 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term117 _91703 _91706 _91707 P k f g y x)). Qed.
Lemma lem3577325 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term94 _91703 _91706 _91707 P f g k) = (term94 _91703 _91706 _91707 P f g k).
Proof. exact (eq_refl (term94 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577326 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term122 _91703 _91706 _91707 P k f g y x) = (term123 _91703 _91706 _91707 P k f x g y).
Proof. exact (MK_COMB (@lem3577325 _91703 _91706 _91707 P f g k) (@lem3577324 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577327 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term124 _91703 _91706 _91707 P k f g y) = (term125 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3577326 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577328 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577329 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term116 _91703 _91706 _91707 P k f g y) = (term126 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577328 _91706) (@lem3577327 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577330 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : ((term115 _91703 _91706 _91707 P k f g y) = (term116 _91703 _91706 _91707 P k f g y)) = ((term111 _91703 _91706 _91707 P k f g y) = (term126 _91703 _91706 _91707 P k f g y)).
Proof. exact (MK_COMB (@lem3577323 _91703 _91706 _91707 P k f g y) (@lem3577329 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577331 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term111 _91703 _91706 _91707 P k f g y) = (term126 _91703 _91706 _91707 P k f g y).
Proof. exact (EQ_MP (@lem3577330 _91703 _91706 _91707 P k f g y) (@lem3577315 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577332 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term113 _91703 _91706 _91707 P k f g) = (term127 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577331 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577333 {_91707 : Type'} : (@ex _91707) = (@ex _91707).
Proof. exact (eq_refl (@ex _91707)). Qed.
Lemma lem3577334 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term114 _91703 _91706 _91707 P k f g) = (term128 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577333 _91707) (@lem3577332 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577335 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term96 _91703 _91706 _91707 P k f g) = (term128 _91703 _91706 _91707 P k f g).
Proof. exact (TRANS (@lem3577311 _91703 _91706 _91707 P k f g) (@lem3577334 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577336 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577337 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term98 _91703 _91706 _91707 P k f g) = (term129 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577336) (@lem3577335 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577339 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3577340 {_91706 : Type'} (P : _91706 -> Prop) (Q : Prop) : (term130 _91706 P Q) = (term131 _91706 P Q).
Proof. exact (@lem3577339 _91706 P Q). Qed.
Lemma lem3577341 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term132 _91703 _91706 _91707 P k f g) = (term133 _91703 _91706 _91707 P k f g).
Proof. exact (@lem3577340 _91706 (term58 _91703 _91706 _91707 P f g k) (term88 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577342 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term134 _91703 _91706 _91707 P f g k x) = (term48 _91703 _91706 _91707 P f g k x).
Proof. exact (eq_refl (term134 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577343 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term135 _91703 _91706 _91707 P f g k) = (term58 _91703 _91706 _91707 P f g k).
Proof. exact (fun_ext (fun x : _91706 => @lem3577342 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577344 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577345 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term136 _91703 _91706 _91707 P f g k) = (term59 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577344 _91706) (@lem3577343 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577346 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3577347 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term137 _91703 _91706 _91707 P f g k) = (term90 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577346) (@lem3577345 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577348 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term88 _91703 _91706 _91707 P k f g) = (term88 _91703 _91706 _91707 P k f g).
Proof. exact (eq_refl (term88 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577349 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term132 _91703 _91706 _91707 P k f g) = (term92 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577347 _91703 _91706 _91707 P f g k) (@lem3577348 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577351 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term138 _91703 _91706 _91707 P k f g) = (term139 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577350) (@lem3577349 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577352 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term134 _91703 _91706 _91707 P f g k x) = (term48 _91703 _91706 _91707 P f g k x).
Proof. exact (eq_refl (term134 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3577354 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term140 _91703 _91706 _91707 P f g k x) = (term141 _91703 _91706 _91707 P f g k x).
Proof. exact (MK_COMB (@lem3577353) (@lem3577352 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577355 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term88 _91703 _91706 _91707 P k f g) = (term88 _91703 _91706 _91707 P k f g).
Proof. exact (eq_refl (term88 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577356 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term142 _91703 _91706 _91707 x P k f g) = (term143 _91703 _91706 _91707 x P k f g).
Proof. exact (MK_COMB (@lem3577354 _91703 _91706 _91707 P f g k x) (@lem3577355 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577357 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term144 _91703 _91706 _91707 P k f g) = (term145 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun x : _91706 => @lem3577356 _91703 _91706 _91707 x P k f g)). Qed.
Lemma lem3577358 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577359 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term133 _91703 _91706 _91707 P k f g) = (term146 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577358 _91706) (@lem3577357 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577360 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : ((term132 _91703 _91706 _91707 P k f g) = (term133 _91703 _91706 _91707 P k f g)) = ((term92 _91703 _91706 _91707 P k f g) = (term146 _91703 _91706 _91707 P k f g)).
Proof. exact (MK_COMB (@lem3577351 _91703 _91706 _91707 P k f g) (@lem3577359 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577361 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term92 _91703 _91706 _91707 P k f g) = (term146 _91703 _91706 _91707 P k f g).
Proof. exact (EQ_MP (@lem3577360 _91703 _91706 _91707 P k f g) (@lem3577341 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577362 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term100 _91703 _91706 _91707 P k f g) = (term147 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577337 _91703 _91706 _91707 P k f g) (@lem3577361 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577366 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3577367 {_91707 : Type'} (P : _91707 -> Prop) (Q : Prop) : (term148 _91707 P Q) = (term149 _91707 P Q).
Proof. exact (@lem3577366 _91707 P Q). Qed.
Lemma lem3577368 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term150 _91703 _91706 _91707 P k f g) = (term151 _91703 _91706 _91707 P k f g).
Proof. exact (@lem3577367 _91707 (term127 _91703 _91706 _91707 P k f g) (term146 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577369 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term152 _91703 _91706 _91707 P k f g y) = (term126 _91703 _91706 _91707 P k f g y).
Proof. exact (eq_refl (term152 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577370 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term153 _91703 _91706 _91707 P k f g) = (term127 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577369 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577371 {_91707 : Type'} : (@ex _91707) = (@ex _91707).
Proof. exact (eq_refl (@ex _91707)). Qed.
Lemma lem3577372 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term154 _91703 _91706 _91707 P k f g) = (term128 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577371 _91707) (@lem3577370 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577374 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term155 _91703 _91706 _91707 P k f g) = (term129 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577373) (@lem3577372 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577375 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term146 _91703 _91706 _91707 P k f g) = (term146 _91703 _91706 _91707 P k f g).
Proof. exact (eq_refl (term146 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577376 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term150 _91703 _91706 _91707 P k f g) = (term147 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577374 _91703 _91706 _91707 P k f g) (@lem3577375 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577378 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term156 _91703 _91706 _91707 P k f g) = (term157 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577377) (@lem3577376 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577379 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term152 _91703 _91706 _91707 P k f g y) = (term126 _91703 _91706 _91707 P k f g y).
Proof. exact (eq_refl (term152 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577380 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577381 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term158 _91703 _91706 _91707 P k f g y) = (term159 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577380) (@lem3577379 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577382 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term146 _91703 _91706 _91707 P k f g) = (term146 _91703 _91706 _91707 P k f g).
Proof. exact (eq_refl (term146 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577383 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term160 _91703 _91706 _91707 y P k f g) = (term161 _91703 _91706 _91707 y P k f g).
Proof. exact (MK_COMB (@lem3577381 _91703 _91706 _91707 P k f g y) (@lem3577382 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577384 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term162 _91703 _91706 _91707 P k f g) = (term163 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577383 _91703 _91706 _91707 y P k f g)). Qed.
Lemma lem3577385 {_91707 : Type'} : (@ex _91707) = (@ex _91707).
Proof. exact (eq_refl (@ex _91707)). Qed.
Lemma lem3577386 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term151 _91703 _91706 _91707 P k f g) = (term164 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577385 _91707) (@lem3577384 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577387 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : ((term150 _91703 _91706 _91707 P k f g) = (term151 _91703 _91706 _91707 P k f g)) = ((term147 _91703 _91706 _91707 P k f g) = (term164 _91703 _91706 _91707 P k f g)).
Proof. exact (MK_COMB (@lem3577378 _91703 _91706 _91707 P k f g) (@lem3577386 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577388 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term147 _91703 _91706 _91707 P k f g) = (term164 _91703 _91706 _91707 P k f g).
Proof. exact (EQ_MP (@lem3577387 _91703 _91706 _91707 P k f g) (@lem3577368 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577390 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term165 A P Q) = (term166 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3577391 {_91706 : Type'} (P : _91706 -> Prop) (Q : _91706 -> Prop) : (term165 _91706 P Q) = (term166 _91706 P Q).
Proof. exact (@lem3577390 _91706 P Q). Qed.
Lemma lem3577392 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term167 _91703 _91706 _91707 y P k f g) = (term168 _91703 _91706 _91707 y P k f g).
Proof. exact (@lem3577391 _91706 (term125 _91703 _91706 _91707 P k f g y) (term145 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577393 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term169 _91703 _91706 _91707 P k f g y x) = (term123 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term169 _91703 _91706 _91707 P k f g y x)). Qed.
Lemma lem3577394 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term170 _91703 _91706 _91707 P k f g y) = (term125 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3577393 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577395 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577396 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term171 _91703 _91706 _91707 P k f g y) = (term126 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577395 _91706) (@lem3577394 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577398 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term172 _91703 _91706 _91707 P k f g y) = (term159 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577397) (@lem3577396 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577399 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term173 _91703 _91706 _91707 P k f g x) = (term143 _91703 _91706 _91707 x P k f g).
Proof. exact (eq_refl (term173 _91703 _91706 _91707 P k f g x)). Qed.
Lemma lem3577400 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term174 _91703 _91706 _91707 P k f g) = (term145 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun x : _91706 => @lem3577399 _91703 _91706 _91707 x P k f g)). Qed.
Lemma lem3577401 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577402 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term175 _91703 _91706 _91707 P k f g) = (term146 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577401 _91706) (@lem3577400 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577403 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term167 _91703 _91706 _91707 y P k f g) = (term161 _91703 _91706 _91707 y P k f g).
Proof. exact (MK_COMB (@lem3577398 _91703 _91706 _91707 P k f g y) (@lem3577402 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577405 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term176 _91703 _91706 _91707 y P k f g) = (term177 _91703 _91706 _91707 y P k f g).
Proof. exact (MK_COMB (@lem3577404) (@lem3577403 _91703 _91706 _91707 y P k f g)). Qed.
Lemma lem3577406 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term169 _91703 _91706 _91707 P k f g y x) = (term123 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term169 _91703 _91706 _91707 P k f g y x)). Qed.
Lemma lem3577407 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577408 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term178 _91703 _91706 _91707 P k f g y x) = (term179 _91703 _91706 _91707 P k f x g y).
Proof. exact (MK_COMB (@lem3577407) (@lem3577406 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577409 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term173 _91703 _91706 _91707 P k f g x) = (term143 _91703 _91706 _91707 x P k f g).
Proof. exact (eq_refl (term173 _91703 _91706 _91707 P k f g x)). Qed.
Lemma lem3577410 {_91703 _91706 _91707 : Type'} (y : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term180 _91703 _91706 _91707 y P k f g x) = (term181 _91703 _91706 _91707 y x P k f g).
Proof. exact (MK_COMB (@lem3577408 _91703 _91706 _91707 P k f x g y) (@lem3577409 _91703 _91706 _91707 x P k f g)). Qed.
Lemma lem3577411 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term182 _91703 _91706 _91707 y P k f g) = (term183 _91703 _91706 _91707 y P k f g).
Proof. exact (fun_ext (fun x : _91706 => @lem3577410 _91703 _91706 _91707 y x P k f g)). Qed.
Lemma lem3577412 {_91706 : Type'} : (@ex _91706) = (@ex _91706).
Proof. exact (eq_refl (@ex _91706)). Qed.
Lemma lem3577413 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term168 _91703 _91706 _91707 y P k f g) = (term184 _91703 _91706 _91707 y P k f g).
Proof. exact (MK_COMB (@lem3577412 _91706) (@lem3577411 _91703 _91706 _91707 y P k f g)). Qed.
Lemma lem3577414 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : ((term167 _91703 _91706 _91707 y P k f g) = (term168 _91703 _91706 _91707 y P k f g)) = ((term161 _91703 _91706 _91707 y P k f g) = (term184 _91703 _91706 _91707 y P k f g)).
Proof. exact (MK_COMB (@lem3577405 _91703 _91706 _91707 y P k f g) (@lem3577413 _91703 _91706 _91707 y P k f g)). Qed.
Lemma lem3577415 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term161 _91703 _91706 _91707 y P k f g) = (term184 _91703 _91706 _91707 y P k f g).
Proof. exact (EQ_MP (@lem3577414 _91703 _91706 _91707 y P k f g) (@lem3577392 _91703 _91706 _91707 y P k f g)). Qed.
Lemma lem3577416 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term163 _91703 _91706 _91707 P k f g) = (term185 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577415 _91703 _91706 _91707 y P k f g)). Qed.
Lemma lem3577417 {_91707 : Type'} : (@ex _91707) = (@ex _91707).
Proof. exact (eq_refl (@ex _91707)). Qed.
Lemma lem3577418 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term164 _91703 _91706 _91707 P k f g) = (term186 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577417 _91707) (@lem3577416 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577419 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term147 _91703 _91706 _91707 P k f g) = (term186 _91703 _91706 _91707 P k f g).
Proof. exact (TRANS (@lem3577388 _91703 _91706 _91707 P k f g) (@lem3577418 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577421 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term100 _91703 _91706 _91707 P k f g) = (term186 _91703 _91706 _91707 P k f g).
Proof. exact (TRANS (@lem3577362 _91703 _91706 _91707 P k f g) (@lem3577419 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577422 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term18 _91703 _91706 _91707 P k f g) = (term186 _91703 _91706 _91707 P k f g).
Proof. exact (TRANS (@lem3577110 _91703 _91706 _91707 P k f g) (@lem3577421 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577423 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : term186 _91703 _91706 _91707 P k f g.
Proof. exact (EQ_MP (@lem3577422 _91703 _91706 _91707 P k f g) (@lem3577022 _91703 _91706 _91707 P k f g h1)). Qed.
Lemma lem3577424 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term184 _91703 _91706 _91707 y P k f g) : term184 _91703 _91706 _91707 y P k f g.
Proof. exact (h1). Qed.
Lemma lem3577425 {_91703 _91706 _91707 : Type'} (y : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term181 _91703 _91706 _91707 y x P k f g) : term181 _91703 _91706 _91707 y x P k f g.
Proof. exact (h1). Qed.
Lemma lem3577454 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term70 _91703 _91706 _91707 P k f x g y) = (term70 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term70 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577455 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term78 _91703 _91706 _91707 P k f g y) = (term78 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3577454 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577456 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3577457 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term79 _91703 _91706 _91707 P k f g y) = (term79 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577456 _91706) (@lem3577455 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577458 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term87 _91703 _91706 _91707 P k f g) = (term87 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577457 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577459 {_91707 : Type'} : (@all _91707) = (@all _91707).
Proof. exact (eq_refl (@all _91707)). Qed.
Lemma lem3577460 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term88 _91703 _91706 _91707 P k f g) = (term88 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577459 _91707) (@lem3577458 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577481 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term141 _91703 _91706 _91707 P f g k x) = (term141 _91703 _91706 _91707 P f g k x).
Proof. exact (eq_refl (term141 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577482 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term143 _91703 _91706 _91707 x P k f g) = (term143 _91703 _91706 _91707 x P k f g).
Proof. exact (MK_COMB (@lem3577481 _91703 _91706 _91707 P f g k x) (@lem3577460 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577509 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term65 _91703 _91706 _91707 P k f x g y) = (term65 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term65 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577528 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term50 _91703 _91706 _91707 P f g k x) = (term50 _91703 _91706 _91707 P f g k x).
Proof. exact (eq_refl (term50 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577529 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term60 _91703 _91706 _91707 P f g k) = (term60 _91703 _91706 _91707 P f g k).
Proof. exact (fun_ext (fun x : _91706 => @lem3577528 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577530 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3577531 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term61 _91703 _91706 _91707 P f g k) = (term61 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577530 _91706) (@lem3577529 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3577533 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term94 _91703 _91706 _91707 P f g k) = (term94 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577532) (@lem3577531 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577534 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term123 _91703 _91706 _91707 P k f x g y) = (term123 _91703 _91706 _91707 P k f x g y).
Proof. exact (MK_COMB (@lem3577533 _91703 _91706 _91707 P f g k) (@lem3577509 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577535 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3577536 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term179 _91703 _91706 _91707 P k f x g y) = (term179 _91703 _91706 _91707 P k f x g y).
Proof. exact (MK_COMB (@lem3577535) (@lem3577534 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577537 {_91703 _91706 _91707 : Type'} (y : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term181 _91703 _91706 _91707 y x P k f g) = (term181 _91703 _91706 _91707 y x P k f g).
Proof. exact (MK_COMB (@lem3577536 _91703 _91706 _91707 P k f x g y) (@lem3577482 _91703 _91706 _91707 x P k f g)). Qed.
Lemma lem3577538 {_91703 _91706 _91707 : Type'} (y : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term181 _91703 _91706 _91707 y x P k f g) : term181 _91703 _91706 _91707 y x P k f g.
Proof. exact (EQ_MP (@lem3577537 _91703 _91706 _91707 y x P k f g) (@lem3577425 _91703 _91706 _91707 y x P k f g h1)). Qed.
Lemma lem3577539 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term123 _91703 _91706 _91707 P k f x g y.
Proof. exact (h1). Qed.
Lemma lem3577540 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term143 _91703 _91706 _91707 x P k f g.
Proof. exact (h1). Qed.
Lemma lem3577541 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term65 _91703 _91706 _91707 P k f x g y.
Proof. exact (proj2 (@lem3577539 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577542 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term61 _91703 _91706 _91707 P f g k.
Proof. exact (proj1 (@lem3577539 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577544 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term66 _91706 _91707 P y k x.
Proof. exact (proj1 (@lem3577541 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577547 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term88 _91703 _91706 _91707 P k f g.
Proof. exact (proj2 (@lem3577540 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577548 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term48 _91703 _91706 _91707 P f g k x.
Proof. exact (proj1 (@lem3577540 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577558 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term50 _91703 _91706 _91707 P f g k x) = (term50 _91703 _91706 _91707 P f g k x).
Proof. exact (eq_refl (term50 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577559 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term60 _91703 _91706 _91707 P f g k) = (term60 _91703 _91706 _91707 P f g k).
Proof. exact (fun_ext (fun x : _91706 => @lem3577558 _91703 _91706 _91707 P f g k x)). Qed.
Lemma lem3577560 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3577562 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : (term61 _91703 _91706 _91707 P f g k) = (term61 _91703 _91706 _91707 P f g k).
Proof. exact (MK_COMB (@lem3577560 _91706) (@lem3577559 _91703 _91706 _91707 P f g k)). Qed.
Lemma lem3577563 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term61 _91703 _91706 _91707 P f g k.
Proof. exact (EQ_MP (@lem3577562 _91703 _91706 _91707 P f g k) (@lem3577542 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577589 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term70 _91703 _91706 _91707 P k f x g y) = (term70 _91703 _91706 _91707 P k f x g y).
Proof. exact (eq_refl (term70 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577590 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term78 _91703 _91706 _91707 P k f g y) = (term78 _91703 _91706 _91707 P k f g y).
Proof. exact (fun_ext (fun x : _91706 => @lem3577589 _91703 _91706 _91707 P k f x g y)). Qed.
Lemma lem3577591 {_91706 : Type'} : (@all _91706) = (@all _91706).
Proof. exact (eq_refl (@all _91706)). Qed.
Lemma lem3577592 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (y : _91707) : (term79 _91703 _91706 _91707 P k f g y) = (term79 _91703 _91706 _91707 P k f g y).
Proof. exact (MK_COMB (@lem3577591 _91706) (@lem3577590 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577593 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term87 _91703 _91706 _91707 P k f g) = (term87 _91703 _91706 _91707 P k f g).
Proof. exact (fun_ext (fun y : _91707 => @lem3577592 _91703 _91706 _91707 P k f g y)). Qed.
Lemma lem3577594 {_91707 : Type'} : (@all _91707) = (@all _91707).
Proof. exact (eq_refl (@all _91707)). Qed.
Lemma lem3577596 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term88 _91703 _91706 _91707 P k f g) = (term88 _91703 _91706 _91707 P k f g).
Proof. exact (MK_COMB (@lem3577594 _91707) (@lem3577593 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3577597 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term88 _91703 _91706 _91707 P k f g.
Proof. exact (EQ_MP (@lem3577596 _91703 _91706 _91707 P k f g) (@lem3577547 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577606 {_91703 _91706 _91707 : Type'} (_38595 : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term187 _91703 _91706 _91707 P f g k _38595.
Proof. exact (@lem3577563 _91703 _91706 _91707 P k f x g y h1 _38595). Qed.
Lemma lem3577607 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (_38595 : _91706) : (term187 _91703 _91706 _91707 P f g k _38595) = (term50 _91703 _91706 _91707 P f g k _38595).
Proof. exact (eq_refl (term187 _91703 _91706 _91707 P f g k _38595)). Qed.
Lemma lem3577609 {_91703 _91706 _91707 : Type'} (_38596 : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term188 _91703 _91706 _91707 P k f g _38596.
Proof. exact (@lem3577597 _91703 _91706 _91707 x P k f g h1 _38596). Qed.
Lemma lem3577610 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (_38596 : _91707) : (term188 _91703 _91706 _91707 P k f g _38596) = (term79 _91703 _91706 _91707 P k f g _38596).
Proof. exact (eq_refl (term188 _91703 _91706 _91707 P k f g _38596)). Qed.
Lemma lem3577611 {_91703 _91706 _91707 : Type'} (_38596 : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term79 _91703 _91706 _91707 P k f g _38596.
Proof. exact (EQ_MP (@lem3577610 _91703 _91706 _91707 P k f g _38596) (@lem3577609 _91703 _91706 _91707 _38596 x P k f g h1)). Qed.
Lemma lem3577612 {_91703 _91706 _91707 : Type'} (_38596 : _91707) (_38597 : _91706) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term189 _91703 _91706 _91707 P k f g _38596 _38597.
Proof. exact (@lem3577611 _91703 _91706 _91707 _38596 x P k f g h1 _38597). Qed.
Lemma lem3577613 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (_38597 : _91706) (g : _91707 -> _91703) (_38596 : _91707) : (term189 _91703 _91706 _91707 P k f g _38596 _38597) = (term70 _91703 _91706 _91707 P k f _38597 g _38596).
Proof. exact (eq_refl (term189 _91703 _91706 _91707 P k f g _38596 _38597)). Qed.
Lemma lem3577614 {_91703 _91706 _91707 : Type'} (_38597 : _91706) (_38596 : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term70 _91703 _91706 _91707 P k f _38597 g _38596.
Proof. exact (EQ_MP (@lem3577613 _91703 _91706 _91707 P k f _38597 g _38596) (@lem3577612 _91703 _91706 _91707 _38596 _38597 x P k f g h1)). Qed.
Lemma lem3577622 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term190 _91703 _91706 _91707 f x g y.
Proof. exact (proj2 (@lem3577541 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577626 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : y = (k x).
Proof. exact (proj2 (@lem3577544 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577637 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (_38597 : _91706) (g : _91707 -> _91703) (_38596 : _91707) : (term70 _91703 _91706 _91707 P k f _38597 g _38596) = (term191 _91703 _91706 _91707 P k f _38597 g _38596).
Proof. exact (@lem3576833 (term192 _91706 P _38597) (term193 _91706 _91707 _38596 k _38597) ((f _38597) = (g _38596))). Qed.
Lemma lem3577638 {_91703 _91706 _91707 : Type'} (_38597 : _91706) (_38596 : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term191 _91703 _91706 _91707 P k f _38597 g _38596.
Proof. exact (EQ_MP (@lem3577637 _91703 _91706 _91707 P k f _38597 g _38596) (@lem3577614 _91703 _91706 _91707 _38597 _38596 x P k f g h1)). Qed.
Lemma lem3577642 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term194 _91703 _91706 _91707 f g k x.
Proof. exact (proj2 (@lem3577548 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577670 {_91703 _91706 _91707 : Type'} (_38595 : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term50 _91703 _91706 _91707 P f g k _38595.
Proof. exact (EQ_MP (@lem3577607 _91703 _91706 _91707 P f g k _38595) (@lem3577606 _91703 _91706 _91707 _38595 P k f x g y h1)). Qed.
Lemma lem3577671 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) : (term195 _91703 _91706 _91707 f x g) = (term195 _91703 _91706 _91707 f x g).
Proof. exact (eq_refl (term195 _91703 _91706 _91707 f x g)). Qed.
Lemma lem3577672 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : (term196 _91703 _91706 _91707 f x g y) = (term197 _91703 _91706 _91707 f g k x).
Proof. exact (MK_COMB (@lem3577671 _91703 _91706 _91707 f x g) (@lem3577626 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577673 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term197 _91703 _91706 _91707 f g k x) = (term194 _91703 _91706 _91707 f g k x).
Proof. exact (eq_refl (term197 _91703 _91706 _91707 f g k x)). Qed.
Lemma lem3577674 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term198 _91703 _91706 _91707 f x g y) = (term198 _91703 _91706 _91707 f x g y).
Proof. exact (eq_refl (term198 _91703 _91706 _91707 f x g y)). Qed.
Lemma lem3577675 {_91703 _91706 _91707 : Type'} (y : _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : ((term196 _91703 _91706 _91707 f x g y) = (term197 _91703 _91706 _91707 f g k x)) = ((term196 _91703 _91706 _91707 f x g y) = (term194 _91703 _91706 _91707 f g k x)).
Proof. exact (MK_COMB (@lem3577674 _91703 _91706 _91707 f x g y) (@lem3577673 _91703 _91706 _91707 f g k x)). Qed.
Lemma lem3577676 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term196 _91703 _91706 _91707 f x g y) = (term190 _91703 _91706 _91707 f x g y).
Proof. exact (eq_refl (term196 _91703 _91706 _91707 f x g y)). Qed.
Lemma lem3577677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577678 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) : (term198 _91703 _91706 _91707 f x g y) = (term199 _91703 _91706 _91707 f x g y).
Proof. exact (MK_COMB (@lem3577677) (@lem3577676 _91703 _91706 _91707 f x g y)). Qed.
Lemma lem3577679 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term194 _91703 _91706 _91707 f g k x) = (term194 _91703 _91706 _91707 f g k x).
Proof. exact (eq_refl (term194 _91703 _91706 _91707 f g k x)). Qed.
Lemma lem3577680 {_91703 _91706 _91707 : Type'} (y : _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : ((term196 _91703 _91706 _91707 f x g y) = (term194 _91703 _91706 _91707 f g k x)) = ((term190 _91703 _91706 _91707 f x g y) = (term194 _91703 _91706 _91707 f g k x)).
Proof. exact (MK_COMB (@lem3577678 _91703 _91706 _91707 f x g y) (@lem3577679 _91703 _91706 _91707 f g k x)). Qed.
Lemma lem3577681 {_91703 _91706 _91707 : Type'} (y : _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : ((term196 _91703 _91706 _91707 f x g y) = (term197 _91703 _91706 _91707 f g k x)) = ((term190 _91703 _91706 _91707 f x g y) = (term194 _91703 _91706 _91707 f g k x)).
Proof. exact (TRANS (@lem3577675 _91703 _91706 _91707 y f g k x) (@lem3577680 _91703 _91706 _91707 y f g k x)). Qed.
Lemma lem3577682 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : (term190 _91703 _91706 _91707 f x g y) = (term194 _91703 _91706 _91707 f g k x).
Proof. exact (EQ_MP (@lem3577681 _91703 _91706 _91707 y f g k x) (@lem3577672 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577683 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term194 _91703 _91706 _91707 f g k x.
Proof. exact (EQ_MP (@lem3577682 _91703 _91706 _91707 P k f x g y h1) (@lem3577622 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577741 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : P x.
Proof. exact (proj1 (@lem3577544 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577742 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term200 _91706 P x.
Proof. exact (fun h0 : term192 _91706 P x => @lem3577741 _91703 _91706 _91707 P k f x g y h1). Qed.
Lemma lem3577744 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3577745 {_91706 : Type'} (P : _91706 -> Prop) (x : _91706) : (term200 _91706 P x) = (P x).
Proof. exact (@lem3577744 (P x)). Qed.
Lemma lem3577746 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : P x.
Proof. exact (EQ_MP (@lem3577745 _91706 P x) (@lem3577742 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577752 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3577753 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : (term50 _91703 _91706 _91707 P f g k _38595) = (term202 _91703 _91706 _91707 f g k P _38595).
Proof. exact (@lem3577752 ((f _38595) = (term49 _91703 _91706 _91707 g k _38595)) (term192 _91706 P _38595)). Qed.
Lemma lem3577761 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577762 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : (term203 _91703 _91706 _91707 P f g k _38595) = (term204 _91703 _91706 _91707 f g k P _38595).
Proof. exact (MK_COMB (@lem3577761) (@lem3577753 _91703 _91706 _91707 f g k P _38595)). Qed.
Lemma lem3577770 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : (term202 _91703 _91706 _91707 f g k P _38595) = (term202 _91703 _91706 _91707 f g k P _38595).
Proof. exact (eq_refl (term202 _91703 _91706 _91707 f g k P _38595)). Qed.
Lemma lem3577771 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : ((term50 _91703 _91706 _91707 P f g k _38595) = (term202 _91703 _91706 _91707 f g k P _38595)) = ((term202 _91703 _91706 _91707 f g k P _38595) = (term202 _91703 _91706 _91707 f g k P _38595)).
Proof. exact (MK_COMB (@lem3577762 _91703 _91706 _91707 f g k P _38595) (@lem3577770 _91703 _91706 _91707 f g k P _38595)). Qed.
Lemma lem3577773 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3577774 (x : Prop) : (x = x) = True.
Proof. exact (@lem3577773 Prop x). Qed.
Lemma lem3577775 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : ((term202 _91703 _91706 _91707 f g k P _38595) = (term202 _91703 _91706 _91707 f g k P _38595)) = True.
Proof. exact (@lem3577774 (term202 _91703 _91706 _91707 f g k P _38595)). Qed.
Lemma lem3577776 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : ((term50 _91703 _91706 _91707 P f g k _38595) = (term202 _91703 _91706 _91707 f g k P _38595)) = True.
Proof. exact (TRANS (@lem3577771 _91703 _91706 _91707 f g k P _38595) (@lem3577775 _91703 _91706 _91707 f g k P _38595)). Qed.
Lemma lem3577777 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : True = ((term50 _91703 _91706 _91707 P f g k _38595) = (term202 _91703 _91706 _91707 f g k P _38595)).
Proof. exact (SYM (@lem3577776 _91703 _91706 _91707 f g k P _38595)). Qed.
Lemma lem3577778 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (P : _91706 -> Prop) (_38595 : _91706) : (term50 _91703 _91706 _91707 P f g k _38595) = (term202 _91703 _91706 _91707 f g k P _38595).
Proof. exact (EQ_MP (@lem3577777 _91703 _91706 _91707 f g k P _38595) (@lem0)). Qed.
Lemma lem3577779 {_91703 _91706 _91707 : Type'} (_38595 : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term202 _91703 _91706 _91707 f g k P _38595.
Proof. exact (EQ_MP (@lem3577778 _91703 _91706 _91707 f g k P _38595) (@lem3577670 _91703 _91706 _91707 _38595 P k f x g y h1)). Qed.
Lemma lem3577781 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3577782 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (_38595 : _91706) : (term202 _91703 _91706 _91707 f g k P _38595) = (term206 _91703 _91706 _91707 P f g k _38595).
Proof. exact (@lem3577781 (term192 _91706 P _38595) ((f _38595) = (term49 _91703 _91706 _91707 g k _38595))). Qed.
Lemma lem3577784 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3577785 {_91706 : Type'} (P : _91706 -> Prop) (_38595 : _91706) : (term207 _91706 P _38595) = (P _38595).
Proof. exact (@lem3577784 (P _38595)). Qed.
Lemma lem3577786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3577787 {_91706 : Type'} (P : _91706 -> Prop) (_38595 : _91706) : (term208 _91706 P _38595) = (term209 _91706 P _38595).
Proof. exact (MK_COMB (@lem3577786) (@lem3577785 _91706 P _38595)). Qed.
Lemma lem3577788 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (_38595 : _91706) : ((f _38595) = (term49 _91703 _91706 _91707 g k _38595)) = ((f _38595) = (term49 _91703 _91706 _91707 g k _38595)).
Proof. exact (eq_refl ((f _38595) = (term49 _91703 _91706 _91707 g k _38595))). Qed.
Lemma lem3577789 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (_38595 : _91706) : (term206 _91703 _91706 _91707 P f g k _38595) = (term44 _91703 _91706 _91707 P f g k _38595).
Proof. exact (MK_COMB (@lem3577787 _91706 P _38595) (@lem3577788 _91703 _91706 _91707 f g k _38595)). Qed.
Lemma lem3577790 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (_38595 : _91706) : (term202 _91703 _91706 _91707 f g k P _38595) = (term44 _91703 _91706 _91707 P f g k _38595).
Proof. exact (TRANS (@lem3577782 _91703 _91706 _91707 P f g k _38595) (@lem3577789 _91703 _91706 _91707 P f g k _38595)). Qed.
Lemma lem3577793 {_91703 _91706 _91707 : Type'} (_38595 : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term44 _91703 _91706 _91707 P f g k _38595.
Proof. exact (EQ_MP (@lem3577790 _91703 _91706 _91707 P f g k _38595) (@lem3577779 _91703 _91706 _91707 _38595 P k f x g y h1)). Qed.
Lemma lem3577794 {_91703 _91706 _91707 : Type'} (_38595 : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term44 _91703 _91706 _91707 P f g k _38595.
Proof. exact (@lem3577793 _91703 _91706 _91707 _38595 P k f x g y h1). Qed.
Lemma lem3577795 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term44 _91703 _91706 _91707 P f g k x.
Proof. exact (@lem3577794 _91703 _91706 _91707 x P k f x g y h1). Qed.
Lemma lem3577798 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : (f x) = (term49 _91703 _91706 _91707 g k x).
Proof. exact (@lem3577795 _91703 _91706 _91707 P k f x g y h1 (@lem3577746 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577799 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term210 _91703 _91706 _91707 f g k x.
Proof. exact (fun h0 : term194 _91703 _91706 _91707 f g k x => @lem3577798 _91703 _91706 _91707 P k f x g y h1). Qed.
Lemma lem3577801 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3577802 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term210 _91703 _91706 _91707 f g k x) = ((f x) = (term49 _91703 _91706 _91707 g k x)).
Proof. exact (@lem3577801 ((f x) = (term49 _91703 _91706 _91707 g k x))). Qed.
Lemma lem3577803 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : (f x) = (term49 _91703 _91706 _91707 g k x).
Proof. exact (EQ_MP (@lem3577802 _91703 _91706 _91707 f g k x) (@lem3577799 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577806 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3577808 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term194 _91703 _91706 _91707 f g k x) = (term211 _91703 _91706 _91707 f g k x).
Proof. exact (@lem3577806 ((f x) = (term49 _91703 _91706 _91707 g k x))). Qed.
Lemma lem3577811 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term211 _91703 _91706 _91707 f g k x.
Proof. exact (EQ_MP (@lem3577808 _91703 _91706 _91707 f g k x) (@lem3577683 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577814 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : False.
Proof. exact (@lem3577811 _91703 _91706 _91707 P k f x g y h1 (@lem3577803 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3577815 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : term212.
Proof. exact (fun h0 : ~ False => @lem3577814 _91703 _91706 _91707 P k f x g y h1). Qed.
Lemma lem3577817 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3577818 : term212 = False.
Proof. exact (@lem3577817 False). Qed.
Lemma lem3577863 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : P x.
Proof. exact (proj1 (@lem3577548 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577864 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term200 _91706 P x.
Proof. exact (fun h0 : term192 _91706 P x => @lem3577863 _91703 _91706 _91707 x P k f g h1). Qed.
Lemma lem3577866 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3577867 {_91706 : Type'} (P : _91706 -> Prop) (x : _91706) : (term200 _91706 P x) = (P x).
Proof. exact (@lem3577866 (P x)). Qed.
Lemma lem3577868 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : P x.
Proof. exact (EQ_MP (@lem3577867 _91706 P x) (@lem3577864 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577870 {_91707 : Type'} (x : _91707) : x = x.
Proof. exact (@lem21386 _91707 x). Qed.
Lemma lem3577871 {_91707 : Type'} (x : _91707) : x = x.
Proof. exact (@lem3577870 _91707 x). Qed.
Lemma lem3577872 {_91706 _91707 : Type'} (k : _91706 -> _91707) (x : _91706) : (k x) = (k x).
Proof. exact (@lem3577871 _91707 (k x)). Qed.
Lemma lem3577873 {_91706 _91707 : Type'} (k : _91706 -> _91707) (x : _91706) : term213 _91706 _91707 k x.
Proof. exact (fun h0 : term214 _91706 _91707 k x => @lem3577872 _91706 _91707 k x). Qed.
Lemma lem3577875 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3577876 {_91706 _91707 : Type'} (k : _91706 -> _91707) (x : _91706) : (term213 _91706 _91707 k x) = ((k x) = (k x)).
Proof. exact (@lem3577875 ((k x) = (k x))). Qed.
Lemma lem3577877 {_91706 _91707 : Type'} (k : _91706 -> _91707) (x : _91706) : (k x) = (k x).
Proof. exact (EQ_MP (@lem3577876 _91706 _91707 k x) (@lem3577873 _91706 _91707 k x)). Qed.
Lemma lem3577893 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3577894 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term215 _91703 _91706 _91707 k f _38597 g _38596) = (term216 _91703 _91706 _91707 f g _38596 k _38597).
Proof. exact (@lem3577893 ((f _38597) = (g _38596)) (term193 _91706 _91707 _38596 k _38597)). Qed.
Lemma lem3577904 {_91706 : Type'} (P : _91706 -> Prop) (_38597 : _91706) : (term217 _91706 P _38597) = (term217 _91706 P _38597).
Proof. exact (eq_refl (term217 _91706 P _38597)). Qed.
Lemma lem3577905 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (f : _91706 -> _91703) (g : _91707 -> _91703) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term191 _91703 _91706 _91707 P k f _38597 g _38596) = (term218 _91703 _91706 _91707 P f g _38596 k _38597).
Proof. exact (MK_COMB (@lem3577904 _91706 P _38597) (@lem3577894 _91703 _91706 _91707 f g _38596 k _38597)). Qed.
Lemma lem3577909 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3577910 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term218 _91703 _91706 _91707 P f g _38596 k _38597) = (term219 _91703 _91706 _91707 f g P _38596 k _38597).
Proof. exact (@lem3577909 ((f _38597) = (g _38596)) (term192 _91706 P _38597) (term193 _91706 _91707 _38596 k _38597)). Qed.
Lemma lem3577930 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term191 _91703 _91706 _91707 P k f _38597 g _38596) = (term219 _91703 _91706 _91707 f g P _38596 k _38597).
Proof. exact (TRANS (@lem3577905 _91703 _91706 _91707 P f g _38596 k _38597) (@lem3577910 _91703 _91706 _91707 f g P _38596 k _38597)). Qed.
Lemma lem3577931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3577932 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term220 _91703 _91706 _91707 P k f _38597 g _38596) = (term221 _91703 _91706 _91707 f g P _38596 k _38597).
Proof. exact (MK_COMB (@lem3577931) (@lem3577930 _91703 _91706 _91707 f g P _38596 k _38597)). Qed.
Lemma lem3577952 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term219 _91703 _91706 _91707 f g P _38596 k _38597) = (term219 _91703 _91706 _91707 f g P _38596 k _38597).
Proof. exact (eq_refl (term219 _91703 _91706 _91707 f g P _38596 k _38597)). Qed.
Lemma lem3577953 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : ((term191 _91703 _91706 _91707 P k f _38597 g _38596) = (term219 _91703 _91706 _91707 f g P _38596 k _38597)) = ((term219 _91703 _91706 _91707 f g P _38596 k _38597) = (term219 _91703 _91706 _91707 f g P _38596 k _38597)).
Proof. exact (MK_COMB (@lem3577932 _91703 _91706 _91707 f g P _38596 k _38597) (@lem3577952 _91703 _91706 _91707 f g P _38596 k _38597)). Qed.
Lemma lem3577955 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3577956 (x : Prop) : (x = x) = True.
Proof. exact (@lem3577955 Prop x). Qed.
Lemma lem3577957 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : ((term219 _91703 _91706 _91707 f g P _38596 k _38597) = (term219 _91703 _91706 _91707 f g P _38596 k _38597)) = True.
Proof. exact (@lem3577956 (term219 _91703 _91706 _91707 f g P _38596 k _38597)). Qed.
Lemma lem3577958 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : ((term191 _91703 _91706 _91707 P k f _38597 g _38596) = (term219 _91703 _91706 _91707 f g P _38596 k _38597)) = True.
Proof. exact (TRANS (@lem3577953 _91703 _91706 _91707 f g P _38596 k _38597) (@lem3577957 _91703 _91706 _91707 f g P _38596 k _38597)). Qed.
Lemma lem3577959 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : True = ((term191 _91703 _91706 _91707 P k f _38597 g _38596) = (term219 _91703 _91706 _91707 f g P _38596 k _38597)).
Proof. exact (SYM (@lem3577958 _91703 _91706 _91707 f g P _38596 k _38597)). Qed.
Lemma lem3577960 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term191 _91703 _91706 _91707 P k f _38597 g _38596) = (term219 _91703 _91706 _91707 f g P _38596 k _38597).
Proof. exact (EQ_MP (@lem3577959 _91703 _91706 _91707 f g P _38596 k _38597) (@lem0)). Qed.
Lemma lem3577961 {_91703 _91706 _91707 : Type'} (_38596 : _91707) (_38597 : _91706) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term219 _91703 _91706 _91707 f g P _38596 k _38597.
Proof. exact (EQ_MP (@lem3577960 _91703 _91706 _91707 f g P _38596 k _38597) (@lem3577638 _91703 _91706 _91707 _38597 _38596 x P k f g h1)). Qed.
Lemma lem3577963 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3577964 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (_38597 : _91706) (g : _91707 -> _91703) (_38596 : _91707) : (term219 _91703 _91706 _91707 f g P _38596 k _38597) = (term222 _91703 _91706 _91707 P k f _38597 g _38596).
Proof. exact (@lem3577963 (term63 _91706 _91707 P _38596 k _38597) ((f _38597) = (g _38596))). Qed.
Lemma lem3577966 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3577967 {_91706 _91707 : Type'} (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term225 _91706 _91707 P _38596 k _38597) = (term226 _91706 _91707 P _38596 k _38597).
Proof. exact (@lem3577966 (term192 _91706 P _38597) (term193 _91706 _91707 _38596 k _38597)). Qed.
Lemma lem3577969 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3577970 {_91706 : Type'} (P : _91706 -> Prop) (_38597 : _91706) : (term207 _91706 P _38597) = (P _38597).
Proof. exact (@lem3577969 (P _38597)). Qed.
Lemma lem3577971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3577972 {_91706 : Type'} (P : _91706 -> Prop) (_38597 : _91706) : (term227 _91706 P _38597) = (term228 _91706 P _38597).
Proof. exact (MK_COMB (@lem3577971) (@lem3577970 _91706 P _38597)). Qed.
Lemma lem3577974 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3577975 {_91706 _91707 : Type'} (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term229 _91706 _91707 _38596 k _38597) = (_38596 = (k _38597)).
Proof. exact (@lem3577974 (_38596 = (k _38597))). Qed.
Lemma lem3577976 {_91706 _91707 : Type'} (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term226 _91706 _91707 P _38596 k _38597) = (term66 _91706 _91707 P _38596 k _38597).
Proof. exact (MK_COMB (@lem3577972 _91706 P _38597) (@lem3577975 _91706 _91707 _38596 k _38597)). Qed.
Lemma lem3577977 {_91706 _91707 : Type'} (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term225 _91706 _91707 P _38596 k _38597) = (term66 _91706 _91707 P _38596 k _38597).
Proof. exact (TRANS (@lem3577967 _91706 _91707 P _38596 k _38597) (@lem3577976 _91706 _91707 P _38596 k _38597)). Qed.
Lemma lem3577978 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3577979 {_91706 _91707 : Type'} (P : _91706 -> Prop) (_38596 : _91707) (k : _91706 -> _91707) (_38597 : _91706) : (term230 _91706 _91707 P _38596 k _38597) = (term231 _91706 _91707 P _38596 k _38597).
Proof. exact (MK_COMB (@lem3577978) (@lem3577977 _91706 _91707 P _38596 k _38597)). Qed.
Lemma lem3577980 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (_38597 : _91706) (g : _91707 -> _91703) (_38596 : _91707) : ((f _38597) = (g _38596)) = ((f _38597) = (g _38596)).
Proof. exact (eq_refl ((f _38597) = (g _38596))). Qed.
Lemma lem3577981 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (_38597 : _91706) (g : _91707 -> _91703) (_38596 : _91707) : (term222 _91703 _91706 _91707 P k f _38597 g _38596) = (term40 _91703 _91706 _91707 P k f _38597 g _38596).
Proof. exact (MK_COMB (@lem3577979 _91706 _91707 P _38596 k _38597) (@lem3577980 _91703 _91706 _91707 f _38597 g _38596)). Qed.
Lemma lem3577982 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (_38597 : _91706) (g : _91707 -> _91703) (_38596 : _91707) : (term219 _91703 _91706 _91707 f g P _38596 k _38597) = (term40 _91703 _91706 _91707 P k f _38597 g _38596).
Proof. exact (TRANS (@lem3577964 _91703 _91706 _91707 P k f _38597 g _38596) (@lem3577981 _91703 _91706 _91707 P k f _38597 g _38596)). Qed.
Lemma lem3577984 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term232 _91706 _91707 P k x.
Proof. exact (conj (@lem3577868 _91703 _91706 _91707 x P k f g h1) (@lem3577877 _91706 _91707 k x)). Qed.
Lemma lem3577986 {_91703 _91706 _91707 : Type'} (_38597 : _91706) (_38596 : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term40 _91703 _91706 _91707 P k f _38597 g _38596.
Proof. exact (EQ_MP (@lem3577982 _91703 _91706 _91707 P k f _38597 g _38596) (@lem3577961 _91703 _91706 _91707 _38596 _38597 x P k f g h1)). Qed.
Lemma lem3577987 {_91703 _91706 _91707 : Type'} (_38597 : _91706) (_38596 : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term40 _91703 _91706 _91707 P k f _38597 g _38596.
Proof. exact (@lem3577986 _91703 _91706 _91707 _38597 _38596 x P k f g h1). Qed.
Lemma lem3577988 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term233 _91703 _91706 _91707 P f g k x.
Proof. exact (@lem3577987 _91703 _91706 _91707 x (k x) x P k f g h1). Qed.
Lemma lem3577991 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : (f x) = (term49 _91703 _91706 _91707 g k x).
Proof. exact (@lem3577988 _91703 _91706 _91707 x P k f g h1 (@lem3577984 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577992 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term210 _91703 _91706 _91707 f g k x.
Proof. exact (fun h0 : term194 _91703 _91706 _91707 f g k x => @lem3577991 _91703 _91706 _91707 x P k f g h1). Qed.
Lemma lem3577994 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3577995 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term210 _91703 _91706 _91707 f g k x) = ((f x) = (term49 _91703 _91706 _91707 g k x)).
Proof. exact (@lem3577994 ((f x) = (term49 _91703 _91706 _91707 g k x))). Qed.
Lemma lem3577996 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : (f x) = (term49 _91703 _91706 _91707 g k x).
Proof. exact (EQ_MP (@lem3577995 _91703 _91706 _91707 f g k x) (@lem3577992 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3577999 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3578001 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) (x : _91706) : (term194 _91703 _91706 _91707 f g k x) = (term211 _91703 _91706 _91707 f g k x).
Proof. exact (@lem3577999 ((f x) = (term49 _91703 _91706 _91707 g k x))). Qed.
Lemma lem3578004 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term211 _91703 _91706 _91707 f g k x.
Proof. exact (EQ_MP (@lem3578001 _91703 _91706 _91707 f g k x) (@lem3577642 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3578007 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : False.
Proof. exact (@lem3578004 _91703 _91706 _91707 x P k f g h1 (@lem3577996 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3578008 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : term212.
Proof. exact (fun h0 : ~ False => @lem3578007 _91703 _91706 _91707 x P k f g h1). Qed.
Lemma lem3578010 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3578011 : term212 = False.
Proof. exact (@lem3578010 False). Qed.
Lemma lem3578012 {_91703 _91706 _91707 : Type'} (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term143 _91703 _91706 _91707 x P k f g) : False.
Proof. exact (EQ_MP (@lem3578011) (@lem3578008 _91703 _91706 _91707 x P k f g h1)). Qed.
Lemma lem3578013 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (x : _91706) (g : _91707 -> _91703) (y : _91707) (h1 : term123 _91703 _91706 _91707 P k f x g y) : False.
Proof. exact (EQ_MP (@lem3577818) (@lem3577815 _91703 _91706 _91707 P k f x g y h1)). Qed.
Lemma lem3578014 {_91703 _91706 _91707 : Type'} (y : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term181 _91703 _91706 _91707 y x P k f g) : False.
Proof. exact (or_elim (@lem3577538 _91703 _91706 _91707 y x P k f g h1) (fun h0 : term123 _91703 _91706 _91707 P k f x g y => @lem3578013 _91703 _91706 _91707 P k f x g y h0) (fun h0 : term143 _91703 _91706 _91707 x P k f g => @lem3578012 _91703 _91706 _91707 x P k f g h0)). Qed.
Lemma lem3578015 {_91703 _91706 _91707 : Type'} (y : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term181 _91703 _91706 _91707 y x P k f g) : (term181 _91703 _91706 _91707 y x P k f g) = False.
Proof. exact (prop_ext (fun h2 : term181 _91703 _91706 _91707 y x P k f g => @lem3578014 _91703 _91706 _91707 y x P k f g h1) (fun h2 : False => @lem3577538 _91703 _91706 _91707 y x P k f g h1)). Qed.
Lemma lem3578016 {_91703 _91706 _91707 : Type'} (y : _91707) (x : _91706) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term181 _91703 _91706 _91707 y x P k f g) : False.
Proof. exact (EQ_MP (@lem3578015 _91703 _91706 _91707 y x P k f g h1) (@lem3577538 _91703 _91706 _91707 y x P k f g h1)). Qed.
Lemma lem3578017 {_91703 _91706 _91707 : Type'} (y : _91707) (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term184 _91703 _91706 _91707 y P k f g) : False.
Proof. exact (ex_elim (@lem3577424 _91703 _91706 _91707 y P k f g h1) (fun x : _91706 => fun h0 : term183 _91703 _91706 _91707 y P k f g x => @lem3578016 _91703 _91706 _91707 y x P k f g h0)). Qed.
Lemma lem3578018 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : False.
Proof. exact (ex_elim (@lem3577423 _91703 _91706 _91707 P k f g h1) (fun y : _91707 => fun h0 : term185 _91703 _91706 _91707 P k f g y => @lem3578017 _91703 _91706 _91707 y P k f g h0)). Qed.
Lemma lem3578019 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : (term18 _91703 _91706 _91707 P k f g) = False.
Proof. exact (prop_ext (fun h2 : term18 _91703 _91706 _91707 P k f g => @lem3578018 _91703 _91706 _91707 P k f g h1) (fun h2 : False => @lem3577022 _91703 _91706 _91707 P k f g h1)). Qed.
Lemma lem3578020 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : False.
Proof. exact (EQ_MP (@lem3578019 _91703 _91706 _91707 P k f g h1) (@lem3577022 _91703 _91706 _91707 P k f g h1)). Qed.
Lemma lem3578021 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (fun h0 : term18 _91703 _91706 _91707 P k f g => @lem3578020 _91703 _91706 _91707 P k f g h0). Qed.
Lemma lem3578022 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g).
Proof. exact (EQ_MP (@lem3577021 _91703 _91706 _91707 P k f g) (@lem3578021 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3578027 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term27 _91703 _91706 _91707 k f g.
Proof. exact (fun P : _91706 -> Prop => @lem3578022 _91703 _91706 _91707 P k f g). Qed.
Lemma lem3578032 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) : term31 _91703 _91706 _91707 f g.
Proof. exact (fun k : _91706 -> _91707 => @lem3578027 _91703 _91706 _91707 k f g). Qed.
Lemma lem3578037 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : term35 _91703 _91706 _91707 g.
Proof. exact (fun f : _91706 -> _91703 => @lem3578032 _91703 _91706 _91707 f g). Qed.
Lemma lem3578042 {_91703 _91706 _91707 : Type'} : term39 _91703 _91706 _91707.
Proof. exact (fun g : _91707 -> _91703 => @lem3578037 _91703 _91706 _91707 g). Qed.
Lemma lem3578043 {_91703 _91706 _91707 : Type'} : term38 _91703 _91706 _91707.
Proof. exact (EQ_MP (@lem3577017 _91703 _91706 _91707) (@lem3578042 _91703 _91706 _91707)). Qed.
Lemma lem3578044 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : term234 _91703 _91706 _91707 g.
Proof. exact (@lem3578043 _91703 _91706 _91707 g). Qed.
Lemma lem3578045 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : (term234 _91703 _91706 _91707 g) = (term34 _91703 _91706 _91707 g).
Proof. exact (eq_refl (term234 _91703 _91706 _91707 g)). Qed.
Lemma lem3578046 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) : term34 _91703 _91706 _91707 g.
Proof. exact (EQ_MP (@lem3578045 _91703 _91706 _91707 g) (@lem3578044 _91703 _91706 _91707 g)). Qed.
Lemma lem3578047 {_91703 _91706 _91707 : Type'} (g : _91707 -> _91703) (f : _91706 -> _91703) : term235 _91703 _91706 _91707 g f.
Proof. exact (@lem3578046 _91703 _91706 _91707 g f). Qed.
Lemma lem3578048 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) : (term235 _91703 _91706 _91707 g f) = (term30 _91703 _91706 _91707 f g).
Proof. exact (eq_refl (term235 _91703 _91706 _91707 g f)). Qed.
Lemma lem3578049 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) : term30 _91703 _91706 _91707 f g.
Proof. exact (EQ_MP (@lem3578048 _91703 _91706 _91707 f g) (@lem3578047 _91703 _91706 _91707 g f)). Qed.
Lemma lem3578050 {_91703 _91706 _91707 : Type'} (f : _91706 -> _91703) (g : _91707 -> _91703) (k : _91706 -> _91707) : term236 _91703 _91706 _91707 f g k.
Proof. exact (@lem3578049 _91703 _91706 _91707 f g k). Qed.
Lemma lem3578051 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term236 _91703 _91706 _91707 f g k) = (term26 _91703 _91706 _91707 k f g).
Proof. exact (eq_refl (term236 _91703 _91706 _91707 f g k)). Qed.
Lemma lem3578052 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term26 _91703 _91706 _91707 k f g.
Proof. exact (EQ_MP (@lem3578051 _91703 _91706 _91707 k f g) (@lem3578050 _91703 _91706 _91707 f g k)). Qed.
Lemma lem3578053 {_91703 _91706 _91707 : Type'} (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (P : _91706 -> Prop) : term237 _91703 _91706 _91707 k f g P.
Proof. exact (@lem3578052 _91703 _91706 _91707 k f g P). Qed.
Lemma lem3578054 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term237 _91703 _91706 _91707 k f g P) = (term17 _91703 _91706 _91707 P k f g).
Proof. exact (eq_refl (term237 _91703 _91706 _91707 k f g P)). Qed.
Lemma lem3578055 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (EQ_MP (@lem3578054 _91703 _91706 _91707 P k f g) (@lem3578053 _91703 _91706 _91707 k f g P)). Qed.
Lemma lem3578057 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (@lem3576854 _91703 _91706 _91707 P k f g (@lem3578055 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3578058 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : False.
Proof. exact (@lem3578057 _91703 _91706 _91707 P k f g (@lem3576838 _91703 _91706 _91707 P k f g h1)). Qed.
Lemma lem3578059 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : (term18 _91703 _91706 _91707 P k f g) = False.
Proof. exact (prop_ext (fun h2 : term18 _91703 _91706 _91707 P k f g => @lem3578058 _91703 _91706 _91707 P k f g h1) (fun h2 : False => @lem3576838 _91703 _91706 _91707 P k f g h1)). Qed.
Lemma lem3578060 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) (h1 : term18 _91703 _91706 _91707 P k f g) : False.
Proof. exact (EQ_MP (@lem3578059 _91703 _91706 _91707 P k f g h1) (@lem3576838 _91703 _91706 _91707 P k f g h1)). Qed.
Lemma lem3578061 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : term17 _91703 _91706 _91707 P k f g.
Proof. exact (fun h0 : term18 _91703 _91706 _91707 P k f g => @lem3578060 _91703 _91706 _91707 P k f g h0). Qed.
Lemma lem3578082 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g).
Proof. exact (EQ_MP (@lem3576837 _91703 _91706 _91707 P k f g) (@lem3578061 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3578083 {_91760 _91765 : Type'} (P : _91765 -> Prop) (k : _91765 -> _91765) (f : _91765 -> _91760) (g : _91765 -> _91760) : (term238 _91760 _91765 P f g k) = (term239 _91760 _91765 P k f g).
Proof. exact (@lem3578082 _91760 _91765 _91765 P k f g). Qed.
Lemma lem3578084 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term240 _91760 _91764 _91765 P g x f) = (term241 _91760 _91764 _91765 P g x f).
Proof. exact (@lem3578083 _91760 _91765 (term242 _91764 _91765 P x g) (term243 _91765) (term244 _91760 _91765 f x) f). Qed.
Lemma lem3578085 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term245 _91764 _91765 P x g y) = (term246 _91764 _91765 P x g y).
Proof. exact (eq_refl (term245 _91764 _91765 P x g y)). Qed.
Lemma lem3578086 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3578087 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term247 _91764 _91765 P x g y) = (term248 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3578086) (@lem3578085 _91764 _91765 P x g y)). Qed.
Lemma lem3578088 {_91760 _91765 : Type'} (y : _91765) (f : _91765 -> _91760) (x : _91765) : (term249 _91760 _91765 f x y) = (f x).
Proof. exact (eq_refl (term249 _91760 _91765 f x y)). Qed.
Lemma lem3578089 {_91760 : Type'} : (@eq _91760) = (@eq _91760).
Proof. exact (eq_refl (@eq _91760)). Qed.
Lemma lem3578090 {_91760 _91765 : Type'} (y : _91765) (f : _91765 -> _91760) (x : _91765) : (term250 _91760 _91765 f x y) = (term251 _91760 _91765 f x).
Proof. exact (MK_COMB (@lem3578089 _91760) (@lem3578088 _91760 _91765 y f x)). Qed.
Lemma lem3578091 {_91765 : Type'} (y : _91765) : (term252 _91765 y) = y.
Proof. exact (eq_refl (term252 _91765 y)). Qed.
Lemma lem3578092 {_91760 _91765 : Type'} (f : _91765 -> _91760) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem3578093 {_91760 _91765 : Type'} (f : _91765 -> _91760) (y : _91765) : (term253 _91760 _91765 f y) = (f y).
Proof. exact (MK_COMB (@lem3578092 _91760 _91765 f) (@lem3578091 _91765 y)). Qed.
Lemma lem3578094 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((term249 _91760 _91765 f x y) = (term253 _91760 _91765 f y)) = ((f x) = (f y)).
Proof. exact (MK_COMB (@lem3578090 _91760 _91765 y f x) (@lem3578093 _91760 _91765 f y)). Qed.
Lemma lem3578095 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term254 _91760 _91764 _91765 P g x f y) = (term255 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578087 _91764 _91765 P x g y) (@lem3578094 _91760 _91765 x f y)). Qed.
Lemma lem3578096 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term256 _91760 _91764 _91765 P g x f) = (term257 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3578095 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578097 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578098 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term240 _91760 _91764 _91765 P g x f) = (term258 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578097 _91765) (@lem3578096 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3578100 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term259 _91760 _91764 _91765 P g x f) = (term260 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578099) (@lem3578098 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578101 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y' : _91765) : (term245 _91764 _91765 P x g y') = (term246 _91764 _91765 P x g y').
Proof. exact (eq_refl (term245 _91764 _91765 P x g y')). Qed.
Lemma lem3578102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3578103 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y' : _91765) : (term261 _91764 _91765 P x g y') = (term262 _91764 _91765 P x g y').
Proof. exact (MK_COMB (@lem3578102) (@lem3578101 _91764 _91765 P x g y')). Qed.
Lemma lem3578104 {_91765 : Type'} (y' : _91765) : (term252 _91765 y') = y'.
Proof. exact (eq_refl (term252 _91765 y')). Qed.
Lemma lem3578105 {_91765 : Type'} (y : _91765) : (@eq _91765 y) = (@eq _91765 y).
Proof. exact (eq_refl (@eq _91765 y)). Qed.
Lemma lem3578106 {_91765 : Type'} (y : _91765) (y' : _91765) : (y = (term252 _91765 y')) = (y = y').
Proof. exact (MK_COMB (@lem3578105 _91765 y) (@lem3578104 _91765 y')). Qed.
Lemma lem3578107 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term263 _91764 _91765 P x g y y') = (term264 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3578103 _91764 _91765 P x g y') (@lem3578106 _91765 y y')). Qed.
Lemma lem3578108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3578109 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term265 _91764 _91765 P x g y y') = (term266 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3578108) (@lem3578107 _91764 _91765 P x g y y')). Qed.
Lemma lem3578110 {_91760 _91765 : Type'} (y' : _91765) (f : _91765 -> _91760) (x : _91765) : (term249 _91760 _91765 f x y') = (f x).
Proof. exact (eq_refl (term249 _91760 _91765 f x y')). Qed.
Lemma lem3578111 {_91760 : Type'} : (@eq _91760) = (@eq _91760).
Proof. exact (eq_refl (@eq _91760)). Qed.
Lemma lem3578112 {_91760 _91765 : Type'} (y' : _91765) (f : _91765 -> _91760) (x : _91765) : (term250 _91760 _91765 f x y') = (term251 _91760 _91765 f x).
Proof. exact (MK_COMB (@lem3578111 _91760) (@lem3578110 _91760 _91765 y' f x)). Qed.
Lemma lem3578113 {_91760 _91765 : Type'} (f : _91765 -> _91760) (y : _91765) : (f y) = (f y).
Proof. exact (eq_refl (f y)). Qed.
Lemma lem3578114 {_91760 _91765 : Type'} (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((term249 _91760 _91765 f x y') = (f y)) = ((f x) = (f y)).
Proof. exact (MK_COMB (@lem3578112 _91760 _91765 y' f x) (@lem3578113 _91760 _91765 f y)). Qed.
Lemma lem3578115 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term267 _91760 _91764 _91765 P g x y' f y) = (term268 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3578109 _91764 _91765 P x g y y') (@lem3578114 _91760 _91765 y' x f y)). Qed.
Lemma lem3578116 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term269 _91760 _91764 _91765 P g x f y) = (term270 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578115 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578117 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578118 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term271 _91760 _91764 _91765 P g x f y) = (term272 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578117 _91765) (@lem3578116 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578119 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term273 _91760 _91764 _91765 P g x f) = (term274 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3578118 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578120 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578121 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term241 _91760 _91764 _91765 P g x f) = (term275 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578120 _91765) (@lem3578119 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578122 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : ((term240 _91760 _91764 _91765 P g x f) = (term241 _91760 _91764 _91765 P g x f)) = ((term258 _91760 _91764 _91765 P g x f) = (term275 _91760 _91764 _91765 P g x f)).
Proof. exact (MK_COMB (@lem3578100 _91760 _91764 _91765 P g x f) (@lem3578121 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578123 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term258 _91760 _91764 _91765 P g x f) = (term275 _91760 _91764 _91765 P g x f).
Proof. exact (EQ_MP (@lem3578122 _91760 _91764 _91765 P g x f) (@lem3578084 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578124 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term276 _91760 _91764 _91765 P g f) = (term277 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3578123 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578125 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578126 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term278 _91760 _91764 _91765 P g f) = (term279 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578125 _91765) (@lem3578124 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578127 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3578128 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term280 _91760 _91764 _91765 P g f) = (term281 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578127) (@lem3578126 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578134 {_91703 _91706 _91707 : Type'} (P : _91706 -> Prop) (k : _91706 -> _91707) (f : _91706 -> _91703) (g : _91707 -> _91703) : (term15 _91703 _91706 _91707 P f g k) = (term16 _91703 _91706 _91707 P k f g).
Proof. exact (EQ_MP (@lem3576837 _91703 _91706 _91707 P k f g) (@lem3578061 _91703 _91706 _91707 P k f g)). Qed.
Lemma lem3578135 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (k : _91765 -> _91764) (f : _91765 -> _91760) (g : _91764 -> _91760) : (term282 _91760 _91764 _91765 P f g k) = (term283 _91760 _91764 _91765 P k f g).
Proof. exact (@lem3578134 _91760 _91765 _91764 P k f g). Qed.
Lemma lem3578136 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term282 _91760 _91764 _91765 P f h g) = (term283 _91760 _91764 _91765 P g f h).
Proof. exact (@lem3578135 _91760 _91764 _91765 P g f h). Qed.
Lemma lem3578137 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term284 _91760 _91764 _91765 P f g) = (term285 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3578136 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3578138 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3578139 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term286 _91760 _91764 _91765 P f g) = (term287 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578138 _91760 _91764) (@lem3578137 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578140 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term278 _91760 _91764 _91765 P g f) = (term286 _91760 _91764 _91765 P f g)) = ((term279 _91760 _91764 _91765 P g f) = (term287 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3578128 _91760 _91764 _91765 P g f) (@lem3578139 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578141 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : (term288 _91760 _91764 _91765 P f) = (term289 _91760 _91764 _91765 P f).
Proof. exact (fun_ext (fun g : _91765 -> _91764 => @lem3578140 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578142 {_91764 _91765 : Type'} : (@all (_91765 -> _91764)) = (@all (_91765 -> _91764)).
Proof. exact (eq_refl (@all (_91765 -> _91764))). Qed.
Lemma lem3578143 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : (term290 _91760 _91764 _91765 P f) = (term291 _91760 _91764 _91765 P f).
Proof. exact (MK_COMB (@lem3578142 _91764 _91765) (@lem3578141 _91760 _91764 _91765 P f)). Qed.
Lemma lem3578144 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : (term292 _91760 _91764 _91765 P) = (term293 _91760 _91764 _91765 P).
Proof. exact (fun_ext (fun f : _91765 -> _91760 => @lem3578143 _91760 _91764 _91765 P f)). Qed.
Lemma lem3578145 {_91760 _91765 : Type'} : (@all (_91765 -> _91760)) = (@all (_91765 -> _91760)).
Proof. exact (eq_refl (@all (_91765 -> _91760))). Qed.
Lemma lem3578146 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : (term294 _91760 _91764 _91765 P) = (term295 _91760 _91764 _91765 P).
Proof. exact (MK_COMB (@lem3578145 _91760 _91765) (@lem3578144 _91760 _91764 _91765 P)). Qed.
Lemma lem3578147 {_91760 _91764 _91765 : Type'} : (term296 _91760 _91764 _91765) = (term297 _91760 _91764 _91765).
Proof. exact (fun_ext (fun P : _91765 -> Prop => @lem3578146 _91760 _91764 _91765 P)). Qed.
Lemma lem3578148 {_91765 : Type'} : (@all (_91765 -> Prop)) = (@all (_91765 -> Prop)).
Proof. exact (eq_refl (@all (_91765 -> Prop))). Qed.
Lemma lem3578149 {_91760 _91764 _91765 : Type'} : (term298 _91760 _91764 _91765) = (term299 _91760 _91764 _91765).
Proof. exact (MK_COMB (@lem3578148 _91765) (@lem3578147 _91760 _91764 _91765)). Qed.
Lemma lem3578150 {_91760 _91764 _91765 : Type'} : (term299 _91760 _91764 _91765) = (term298 _91760 _91764 _91765).
Proof. exact (SYM (@lem3578149 _91760 _91764 _91765)). Qed.
Lemma lem3578192 {A B : Type'} (P : type1413 A B) : (term8 A B P) = (term7 A B P).
Proof. exact (EQ_MP (@lem3576822 A B P) (@lem3576821 A B P)). Qed.
Lemma lem3578193 {_91760 _91764 : Type'} (P : type1470 _91760 _91764) : (term300 _91760 _91764 P) = (term301 _91760 _91764 P).
Proof. exact (@lem3578192 _91764 _91760 P). Qed.
Lemma lem3578194 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term302 _91760 _91764 _91765 P g f) = (term303 _91760 _91764 _91765 P g f).
Proof. exact (@lem3578193 _91760 _91764 (term304 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578195 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term305 _91760 _91764 _91765 P g f y) = (term306 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term305 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3578196 {_91760 _91764 : Type'} (h : _91764 -> _91760) (y : _91764) : (h y) = (h y).
Proof. exact (eq_refl (h y)). Qed.
Lemma lem3578197 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term307 _91760 _91764 _91765 P g f h y) = (term308 _91760 _91764 _91765 P g f h y).
Proof. exact (MK_COMB (@lem3578195 _91760 _91764 _91765 P y g f) (@lem3578196 _91760 _91764 h y)). Qed.
Lemma lem3578198 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term308 _91760 _91764 _91765 P g f h y) = (term309 _91760 _91764 _91765 P g f h y).
Proof. exact (eq_refl (term308 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3578199 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term307 _91760 _91764 _91765 P g f h y) = (term309 _91760 _91764 _91765 P g f h y).
Proof. exact (TRANS (@lem3578197 _91760 _91764 _91765 P g f h y) (@lem3578198 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3578200 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term310 _91760 _91764 _91765 P g f h) = (term311 _91760 _91764 _91765 P g f h).
Proof. exact (fun_ext (fun y : _91764 => @lem3578199 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3578201 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3578202 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term312 _91760 _91764 _91765 P g f h) = (term283 _91760 _91764 _91765 P g f h).
Proof. exact (MK_COMB (@lem3578201 _91764) (@lem3578200 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3578203 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term313 _91760 _91764 _91765 P g f) = (term285 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3578202 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3578204 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3578205 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term302 _91760 _91764 _91765 P g f) = (term287 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578204 _91760 _91764) (@lem3578203 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3578207 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term314 _91760 _91764 _91765 P g f) = (term315 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578206) (@lem3578205 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578208 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term305 _91760 _91764 _91765 P g f y) = (term306 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term305 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3578209 {_91760 : Type'} (h : _91760) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem3578210 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term316 _91760 _91764 _91765 P g f y h) = (term317 _91760 _91764 _91765 P y g f h).
Proof. exact (MK_COMB (@lem3578208 _91760 _91764 _91765 P y g f) (@lem3578209 _91760 h)). Qed.
Lemma lem3578211 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term317 _91760 _91764 _91765 P y g f h) = (term318 _91760 _91764 _91765 P y g f h).
Proof. exact (eq_refl (term317 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578212 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term316 _91760 _91764 _91765 P g f y h) = (term318 _91760 _91764 _91765 P y g f h).
Proof. exact (TRANS (@lem3578210 _91760 _91764 _91765 P y g f h) (@lem3578211 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578213 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term319 _91760 _91764 _91765 P g f y) = (term306 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun h : _91760 => @lem3578212 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578214 {_91760 : Type'} : (@ex _91760) = (@ex _91760).
Proof. exact (eq_refl (@ex _91760)). Qed.
Lemma lem3578215 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term320 _91760 _91764 _91765 P g f y) = (term321 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3578214 _91760) (@lem3578213 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578216 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term322 _91760 _91764 _91765 P g f) = (term323 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3578215 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578217 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3578218 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term303 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578217 _91764) (@lem3578216 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578219 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term302 _91760 _91764 _91765 P g f) = (term303 _91760 _91764 _91765 P g f)) = ((term287 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3578207 _91760 _91764 _91765 P g f) (@lem3578218 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578220 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term287 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f).
Proof. exact (EQ_MP (@lem3578219 _91760 _91764 _91765 P g f) (@lem3578194 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578243 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term281 _91760 _91764 _91765 P g f) = (term281 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term281 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578244 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term279 _91760 _91764 _91765 P g f) = (term287 _91760 _91764 _91765 P g f)) = ((term279 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3578243 _91760 _91764 _91765 P g f) (@lem3578220 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578247 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : (term289 _91760 _91764 _91765 P f) = (term325 _91760 _91764 _91765 P f).
Proof. exact (fun_ext (fun g : _91765 -> _91764 => @lem3578244 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578248 {_91764 _91765 : Type'} : (@all (_91765 -> _91764)) = (@all (_91765 -> _91764)).
Proof. exact (eq_refl (@all (_91765 -> _91764))). Qed.
Lemma lem3578249 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : (term291 _91760 _91764 _91765 P f) = (term326 _91760 _91764 _91765 P f).
Proof. exact (MK_COMB (@lem3578248 _91764 _91765) (@lem3578247 _91760 _91764 _91765 P f)). Qed.
Lemma lem3578254 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : (term293 _91760 _91764 _91765 P) = (term327 _91760 _91764 _91765 P).
Proof. exact (fun_ext (fun f : _91765 -> _91760 => @lem3578249 _91760 _91764 _91765 P f)). Qed.
Lemma lem3578255 {_91760 _91765 : Type'} : (@all (_91765 -> _91760)) = (@all (_91765 -> _91760)).
Proof. exact (eq_refl (@all (_91765 -> _91760))). Qed.
Lemma lem3578256 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : (term295 _91760 _91764 _91765 P) = (term328 _91760 _91764 _91765 P).
Proof. exact (MK_COMB (@lem3578255 _91760 _91765) (@lem3578254 _91760 _91764 _91765 P)). Qed.
Lemma lem3578261 {_91760 _91764 _91765 : Type'} : (term297 _91760 _91764 _91765) = (term329 _91760 _91764 _91765).
Proof. exact (fun_ext (fun P : _91765 -> Prop => @lem3578256 _91760 _91764 _91765 P)). Qed.
Lemma lem3578262 {_91765 : Type'} : (@all (_91765 -> Prop)) = (@all (_91765 -> Prop)).
Proof. exact (eq_refl (@all (_91765 -> Prop))). Qed.
Lemma lem3578263 {_91760 _91764 _91765 : Type'} : (term299 _91760 _91764 _91765) = (term330 _91760 _91764 _91765).
Proof. exact (MK_COMB (@lem3578262 _91765) (@lem3578261 _91760 _91764 _91765)). Qed.
Lemma lem3578268 {_91760 _91764 _91765 : Type'} : (term330 _91760 _91764 _91765) = (term299 _91760 _91764 _91765).
Proof. exact (SYM (@lem3578263 _91760 _91764 _91765)). Qed.
Lemma lem3578270 (p : Prop) : p = (term14 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3578271 {_91760 _91764 _91765 : Type'} : (term330 _91760 _91764 _91765) = (term331 _91760 _91764 _91765).
Proof. exact (@lem3578270 (term330 _91760 _91764 _91765)). Qed.
Lemma lem3578272 {_91760 _91764 _91765 : Type'} : (term331 _91760 _91764 _91765) = (term330 _91760 _91764 _91765).
Proof. exact (SYM (@lem3578271 _91760 _91764 _91765)). Qed.
Lemma lem3578273 {_91760 _91764 _91765 : Type'} (h1 : term332 _91760 _91764 _91765) : term332 _91760 _91764 _91765.
Proof. exact (h1). Qed.
Lemma lem3578276 {_91760 _91764 _91765 : Type'} (h1 : term331 _91760 _91764 _91765) : term331 _91760 _91764 _91765.
Proof. exact (h1). Qed.
Lemma lem3578277 {_91760 _91764 _91765 : Type'} : term333 _91760 _91764 _91765.
Proof. exact (fun h0 : term331 _91760 _91764 _91765 => @lem3578276 _91760 _91764 _91765 h0). Qed.
Lemma lem3578278 {_91760 _91764 _91765 : Type'} (h1 : term333 _91760 _91764 _91765) : term333 _91760 _91764 _91765.
Proof. exact (h1). Qed.
Lemma lem3578279 {_91760 _91764 _91765 : Type'} (h1 : term331 _91760 _91764 _91765) : term331 _91760 _91764 _91765.
Proof. exact (h1). Qed.
Lemma lem3578280 {_91760 _91764 _91765 : Type'} (h1 : term331 _91760 _91764 _91765) (h2 : term333 _91760 _91764 _91765) : term331 _91760 _91764 _91765.
Proof. exact (@lem3578278 _91760 _91764 _91765 h2 (@lem3578279 _91760 _91764 _91765 h1)). Qed.
Lemma lem3578281 {_91760 _91764 _91765 : Type'} (h1 : term331 _91760 _91764 _91765) : term334 _91760 _91764 _91765.
Proof. exact (fun h0 : term333 _91760 _91764 _91765 => @lem3578280 _91760 _91764 _91765 h1 h0). Qed.
Lemma lem3578282 {_91760 _91764 _91765 : Type'} (h1 : term333 _91760 _91764 _91765) : term333 _91760 _91764 _91765.
Proof. exact (h1). Qed.
Lemma lem3578283 {_91760 _91764 _91765 : Type'} (h1 : term331 _91760 _91764 _91765) (h2 : term333 _91760 _91764 _91765) : term331 _91760 _91764 _91765.
Proof. exact (@lem3578281 _91760 _91764 _91765 h1 (@lem3578282 _91760 _91764 _91765 h2)). Qed.
Lemma lem3578284 {_91760 _91764 _91765 : Type'} (h1 : term333 _91760 _91764 _91765) : term333 _91760 _91764 _91765.
Proof. exact (fun h0 : term331 _91760 _91764 _91765 => @lem3578283 _91760 _91764 _91765 h0 h1). Qed.
Lemma lem3578285 {_91760 _91764 _91765 : Type'} : term335 _91760 _91764 _91765.
Proof. exact (fun h0 : term333 _91760 _91764 _91765 => @lem3578284 _91760 _91764 _91765 h0). Qed.
Lemma lem3578288 {_91760 _91764 _91765 : Type'} : term333 _91760 _91764 _91765.
Proof. exact (@lem3578285 _91760 _91764 _91765 (@lem3578277 _91760 _91764 _91765)). Qed.
Lemma lem3578289 {_91760 _91764 _91765 : Type'} : term333 _91760 _91764 _91765.
Proof. exact (@lem3578288 _91760 _91764 _91765). Qed.
Lemma lem3578291 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3578292 {_91760 _91764 _91765 : Type'} : (term331 _91760 _91764 _91765) = (term336 _91760 _91764 _91765).
Proof. exact (@lem3578291 (term332 _91760 _91764 _91765)). Qed.
Lemma lem3578294 (t : Prop) : (term23 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3578295 {_91760 _91764 _91765 : Type'} : (term336 _91760 _91764 _91765) = (term330 _91760 _91764 _91765).
Proof. exact (@lem3578294 (term330 _91760 _91764 _91765)). Qed.
Lemma lem3578348 {_91760 _91764 _91765 : Type'} : (term331 _91760 _91764 _91765) = (term330 _91760 _91764 _91765).
Proof. exact (TRANS (@lem3578292 _91760 _91764 _91765) (@lem3578295 _91760 _91764 _91765)). Qed.
Lemma lem3578357 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term337 _91760 _91764 _91765 P y g f x h) = (term337 _91760 _91764 _91765 P y g f x h).
Proof. exact (eq_refl (term337 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3578358 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term338 _91760 _91764 _91765 P y g f h) = (term338 _91760 _91764 _91765 P y g f h).
Proof. exact (fun_ext (fun x : _91765 => @lem3578357 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3578359 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578360 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term318 _91760 _91764 _91765 P y g f h) = (term318 _91760 _91764 _91765 P y g f h).
Proof. exact (MK_COMB (@lem3578359 _91765) (@lem3578358 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578361 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term306 _91760 _91764 _91765 P y g f) = (term306 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun h : _91760 => @lem3578360 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578362 {_91760 : Type'} : (@ex _91760) = (@ex _91760).
Proof. exact (eq_refl (@ex _91760)). Qed.
Lemma lem3578363 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term321 _91760 _91764 _91765 P y g f) = (term321 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3578362 _91760) (@lem3578361 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578364 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term323 _91760 _91764 _91765 P g f) = (term323 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3578363 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578365 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3578366 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term324 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578365 _91764) (@lem3578364 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578383 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term268 _91760 _91764 _91765 P g y' x f y) = (term268 _91760 _91764 _91765 P g y' x f y).
Proof. exact (eq_refl (term268 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578384 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term270 _91760 _91764 _91765 P g x f y) = (term270 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578383 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578385 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578386 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term272 _91760 _91764 _91765 P g x f y) = (term272 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578385 _91765) (@lem3578384 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578387 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term274 _91760 _91764 _91765 P g x f) = (term274 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3578386 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578388 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578389 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term275 _91760 _91764 _91765 P g x f) = (term275 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578388 _91765) (@lem3578387 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578390 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term277 _91760 _91764 _91765 P g f) = (term277 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3578389 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578391 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578392 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term279 _91760 _91764 _91765 P g f) = (term279 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578391 _91765) (@lem3578390 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3578394 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term281 _91760 _91764 _91765 P g f) = (term281 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578393) (@lem3578392 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578395 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term279 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f)) = ((term279 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3578394 _91760 _91764 _91765 P g f) (@lem3578366 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578396 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : (term325 _91760 _91764 _91765 P f) = (term325 _91760 _91764 _91765 P f).
Proof. exact (fun_ext (fun g : _91765 -> _91764 => @lem3578395 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578397 {_91764 _91765 : Type'} : (@all (_91765 -> _91764)) = (@all (_91765 -> _91764)).
Proof. exact (eq_refl (@all (_91765 -> _91764))). Qed.
Lemma lem3578398 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : (term326 _91760 _91764 _91765 P f) = (term326 _91760 _91764 _91765 P f).
Proof. exact (MK_COMB (@lem3578397 _91764 _91765) (@lem3578396 _91760 _91764 _91765 P f)). Qed.
Lemma lem3578399 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : (term327 _91760 _91764 _91765 P) = (term327 _91760 _91764 _91765 P).
Proof. exact (fun_ext (fun f : _91765 -> _91760 => @lem3578398 _91760 _91764 _91765 P f)). Qed.
Lemma lem3578400 {_91760 _91765 : Type'} : (@all (_91765 -> _91760)) = (@all (_91765 -> _91760)).
Proof. exact (eq_refl (@all (_91765 -> _91760))). Qed.
Lemma lem3578401 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : (term328 _91760 _91764 _91765 P) = (term328 _91760 _91764 _91765 P).
Proof. exact (MK_COMB (@lem3578400 _91760 _91765) (@lem3578399 _91760 _91764 _91765 P)). Qed.
Lemma lem3578402 {_91760 _91764 _91765 : Type'} : (term329 _91760 _91764 _91765) = (term329 _91760 _91764 _91765).
Proof. exact (fun_ext (fun P : _91765 -> Prop => @lem3578401 _91760 _91764 _91765 P)). Qed.
Lemma lem3578403 {_91765 : Type'} : (@all (_91765 -> Prop)) = (@all (_91765 -> Prop)).
Proof. exact (eq_refl (@all (_91765 -> Prop))). Qed.
Lemma lem3578404 {_91760 _91764 _91765 : Type'} : (term330 _91760 _91764 _91765) = (term330 _91760 _91764 _91765).
Proof. exact (MK_COMB (@lem3578403 _91765) (@lem3578402 _91760 _91764 _91765)). Qed.
Lemma lem3578473 {_91760 _91764 _91765 : Type'} : (term331 _91760 _91764 _91765) = (term330 _91760 _91764 _91765).
Proof. exact (TRANS (@lem3578348 _91760 _91764 _91765) (@lem3578404 _91760 _91764 _91765)). Qed.
Lemma lem3578474 {_91760 _91764 _91765 : Type'} : (term330 _91760 _91764 _91765) = (term331 _91760 _91764 _91765).
Proof. exact (SYM (@lem3578473 _91760 _91764 _91765)). Qed.
Lemma lem3578476 (p : Prop) : p = (term14 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3578477 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term279 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f)) = (term339 _91760 _91764 _91765 P g f).
Proof. exact (@lem3578476 ((term279 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f))). Qed.
Lemma lem3578478 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term339 _91760 _91764 _91765 P g f) = ((term279 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f)).
Proof. exact (SYM (@lem3578477 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578479 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term340 _91760 _91764 _91765 P g f) : term340 _91760 _91764 _91765 P g f.
Proof. exact (h1). Qed.
Lemma lem3578490 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y' : _91765) : (term341 _91764 _91765 P x g y') = (term342 _91764 _91765 P x g y').
Proof. exact (@lem17045 (P y') ((g x) = (g y'))). Qed.
Lemma lem3578495 {_91765 : Type'} (P : _91765 -> Prop) (x : _91765) : (term217 _91765 P x) = (term217 _91765 P x).
Proof. exact (eq_refl (term217 _91765 P x)). Qed.
Lemma lem3578496 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y' : _91765) : (term343 _91764 _91765 P x g y') = (term344 _91764 _91765 P x g y').
Proof. exact (MK_COMB (@lem3578495 _91765 P x) (@lem3578490 _91764 _91765 P x g y')). Qed.
Lemma lem3578497 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y' : _91765) : (term345 _91764 _91765 P x g y') = (term343 _91764 _91765 P x g y').
Proof. exact (@lem17045 (P x) (term346 _91764 _91765 P x g y')). Qed.
Lemma lem3578498 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y' : _91765) : (term345 _91764 _91765 P x g y') = (term344 _91764 _91765 P x g y').
Proof. exact (TRANS (@lem3578497 _91764 _91765 P x g y') (@lem3578496 _91764 _91765 P x g y')). Qed.
Lemma lem3578502 {_91765 : Type'} (y : _91765) (y' : _91765) : (term347 _91765 y y') = (term347 _91765 y y').
Proof. exact (eq_refl (term347 _91765 y y')). Qed.
Lemma lem3578504 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3578505 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y' : _91765) : (term348 _91764 _91765 P x g y') = (term349 _91764 _91765 P x g y').
Proof. exact (MK_COMB (@lem3578504) (@lem3578498 _91764 _91765 P x g y')). Qed.
Lemma lem3578506 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term350 _91764 _91765 P x g y y') = (term351 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3578505 _91764 _91765 P x g y') (@lem3578502 _91765 y y')). Qed.
Lemma lem3578507 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term352 _91764 _91765 P x g y y') = (term350 _91764 _91765 P x g y y').
Proof. exact (@lem17045 (term246 _91764 _91765 P x g y') (y = y')). Qed.
Lemma lem3578508 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term352 _91764 _91765 P x g y y') = (term351 _91764 _91765 P x g y y').
Proof. exact (TRANS (@lem3578507 _91764 _91765 P x g y y') (@lem3578506 _91764 _91765 P x g y y')). Qed.
Lemma lem3578513 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3578518 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term353 _91760 _91764 _91765 P g y' x f y) = (term354 _91760 _91764 _91765 P g y' x f y).
Proof. exact (@lem17362 (term264 _91764 _91765 P x g y y') ((f x) = (f y))). Qed.
Lemma lem3578519 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3578520 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term355 _91764 _91765 P x g y y') = (term356 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3578519) (@lem3578508 _91764 _91765 P x g y y')). Qed.
Lemma lem3578521 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term357 _91760 _91764 _91765 P g y' x f y) = (term358 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3578520 _91764 _91765 P x g y y') (@lem3578513 _91760 _91765 x f y)). Qed.
Lemma lem3578522 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term268 _91760 _91764 _91765 P g y' x f y) = (term357 _91760 _91764 _91765 P g y' x f y).
Proof. exact (@lem17265 (term264 _91764 _91765 P x g y y') ((f x) = (f y))). Qed.
Lemma lem3578523 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term268 _91760 _91764 _91765 P g y' x f y) = (term358 _91760 _91764 _91765 P g y' x f y).
Proof. exact (TRANS (@lem3578522 _91760 _91764 _91765 P g y' x f y) (@lem3578521 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578524 {_91765 : Type'} (P : _91765 -> Prop) : (term51 _91765 P) = (term52 _91765 P).
Proof. exact (@lem18392 _91765 P). Qed.
Lemma lem3578525 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term359 _91760 _91764 _91765 P g x f y) = (term360 _91760 _91764 _91765 P g x f y).
Proof. exact (@lem3578524 _91765 (term270 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578526 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term361 _91760 _91764 _91765 P g x f y y') = (term268 _91760 _91764 _91765 P g y' x f y).
Proof. exact (eq_refl (term361 _91760 _91764 _91765 P g x f y y')). Qed.
Lemma lem3578527 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3578528 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term362 _91760 _91764 _91765 P g x f y y') = (term353 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3578527) (@lem3578526 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578529 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term362 _91760 _91764 _91765 P g x f y y') = (term354 _91760 _91764 _91765 P g y' x f y).
Proof. exact (TRANS (@lem3578528 _91760 _91764 _91765 P g y' x f y) (@lem3578518 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578530 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term363 _91760 _91764 _91765 P g x f y) = (term364 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578529 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578531 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3578532 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term360 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578531 _91765) (@lem3578530 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578533 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term359 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (TRANS (@lem3578525 _91760 _91764 _91765 P g x f y) (@lem3578532 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578534 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term270 _91760 _91764 _91765 P g x f y) = (term366 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578523 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578535 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578536 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term272 _91760 _91764 _91765 P g x f y) = (term367 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578535 _91765) (@lem3578534 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578537 {_91765 : Type'} (P : _91765 -> Prop) : (term51 _91765 P) = (term52 _91765 P).
Proof. exact (@lem18392 _91765 P). Qed.
Lemma lem3578538 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term368 _91760 _91764 _91765 P g x f) = (term369 _91760 _91764 _91765 P g x f).
Proof. exact (@lem3578537 _91765 (term274 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578539 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term370 _91760 _91764 _91765 P g x f y) = (term272 _91760 _91764 _91765 P g x f y).
Proof. exact (eq_refl (term370 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578540 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3578541 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term371 _91760 _91764 _91765 P g x f y) = (term359 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578540) (@lem3578539 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578542 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term371 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (TRANS (@lem3578541 _91760 _91764 _91765 P g x f y) (@lem3578533 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578543 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term372 _91760 _91764 _91765 P g x f) = (term373 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3578542 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578544 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3578545 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term369 _91760 _91764 _91765 P g x f) = (term374 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578544 _91765) (@lem3578543 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578546 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term368 _91760 _91764 _91765 P g x f) = (term374 _91760 _91764 _91765 P g x f).
Proof. exact (TRANS (@lem3578538 _91760 _91764 _91765 P g x f) (@lem3578545 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578547 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term274 _91760 _91764 _91765 P g x f) = (term375 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3578536 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578548 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578549 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term275 _91760 _91764 _91765 P g x f) = (term376 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578548 _91765) (@lem3578547 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578550 {_91765 : Type'} (P : _91765 -> Prop) : (term51 _91765 P) = (term52 _91765 P).
Proof. exact (@lem18392 _91765 P). Qed.
Lemma lem3578551 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term377 _91760 _91764 _91765 P g f) = (term378 _91760 _91764 _91765 P g f).
Proof. exact (@lem3578550 _91765 (term277 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578552 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term379 _91760 _91764 _91765 P g f x) = (term275 _91760 _91764 _91765 P g x f).
Proof. exact (eq_refl (term379 _91760 _91764 _91765 P g f x)). Qed.
Lemma lem3578553 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3578554 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term380 _91760 _91764 _91765 P g f x) = (term368 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578553) (@lem3578552 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578555 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term380 _91760 _91764 _91765 P g f x) = (term374 _91760 _91764 _91765 P g x f).
Proof. exact (TRANS (@lem3578554 _91760 _91764 _91765 P g x f) (@lem3578546 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578556 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term381 _91760 _91764 _91765 P g f) = (term382 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3578555 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578557 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3578558 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term378 _91760 _91764 _91765 P g f) = (term383 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578557 _91765) (@lem3578556 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578559 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term377 _91760 _91764 _91765 P g f) = (term383 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3578551 _91760 _91764 _91765 P g f) (@lem3578558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578560 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term277 _91760 _91764 _91765 P g f) = (term384 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3578549 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578561 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578562 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term279 _91760 _91764 _91765 P g f) = (term385 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578561 _91765) (@lem3578560 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578571 {_91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (x : _91765) : (term386 _91764 _91765 P y g x) = (term387 _91764 _91765 P y g x).
Proof. exact (@lem17045 (P x) (y = (g x))). Qed.
Lemma lem3578576 {_91760 _91765 : Type'} (f : _91765 -> _91760) (x : _91765) (h : _91760) : ((f x) = h) = ((f x) = h).
Proof. exact (eq_refl ((f x) = h)). Qed.
Lemma lem3578581 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term388 _91760 _91764 _91765 P y g f x h) = (term389 _91760 _91764 _91765 P y g f x h).
Proof. exact (@lem17362 (term390 _91764 _91765 P y g x) ((f x) = h)). Qed.
Lemma lem3578582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3578583 {_91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (x : _91765) : (term391 _91764 _91765 P y g x) = (term392 _91764 _91765 P y g x).
Proof. exact (MK_COMB (@lem3578582) (@lem3578571 _91764 _91765 P y g x)). Qed.
Lemma lem3578584 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term393 _91760 _91764 _91765 P y g f x h) = (term394 _91760 _91764 _91765 P y g f x h).
Proof. exact (MK_COMB (@lem3578583 _91764 _91765 P y g x) (@lem3578576 _91760 _91765 f x h)). Qed.
Lemma lem3578585 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term337 _91760 _91764 _91765 P y g f x h) = (term393 _91760 _91764 _91765 P y g f x h).
Proof. exact (@lem17265 (term390 _91764 _91765 P y g x) ((f x) = h)). Qed.
Lemma lem3578586 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term337 _91760 _91764 _91765 P y g f x h) = (term394 _91760 _91764 _91765 P y g f x h).
Proof. exact (TRANS (@lem3578585 _91760 _91764 _91765 P y g f x h) (@lem3578584 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3578587 {_91765 : Type'} (P : _91765 -> Prop) : (term51 _91765 P) = (term52 _91765 P).
Proof. exact (@lem18392 _91765 P). Qed.
Lemma lem3578588 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term395 _91760 _91764 _91765 P y g f h) = (term396 _91760 _91764 _91765 P y g f h).
Proof. exact (@lem3578587 _91765 (term338 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578589 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term397 _91760 _91764 _91765 P y g f h x) = (term337 _91760 _91764 _91765 P y g f x h).
Proof. exact (eq_refl (term397 _91760 _91764 _91765 P y g f h x)). Qed.
Lemma lem3578590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3578591 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term398 _91760 _91764 _91765 P y g f h x) = (term388 _91760 _91764 _91765 P y g f x h).
Proof. exact (MK_COMB (@lem3578590) (@lem3578589 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3578592 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term398 _91760 _91764 _91765 P y g f h x) = (term389 _91760 _91764 _91765 P y g f x h).
Proof. exact (TRANS (@lem3578591 _91760 _91764 _91765 P y g f x h) (@lem3578581 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3578593 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term399 _91760 _91764 _91765 P y g f h) = (term400 _91760 _91764 _91765 P y g f h).
Proof. exact (fun_ext (fun x : _91765 => @lem3578592 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3578594 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3578595 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term396 _91760 _91764 _91765 P y g f h) = (term401 _91760 _91764 _91765 P y g f h).
Proof. exact (MK_COMB (@lem3578594 _91765) (@lem3578593 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578596 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term395 _91760 _91764 _91765 P y g f h) = (term401 _91760 _91764 _91765 P y g f h).
Proof. exact (TRANS (@lem3578588 _91760 _91764 _91765 P y g f h) (@lem3578595 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578597 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term338 _91760 _91764 _91765 P y g f h) = (term402 _91760 _91764 _91765 P y g f h).
Proof. exact (fun_ext (fun x : _91765 => @lem3578586 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3578598 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578599 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term318 _91760 _91764 _91765 P y g f h) = (term403 _91760 _91764 _91765 P y g f h).
Proof. exact (MK_COMB (@lem3578598 _91765) (@lem3578597 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578600 {_91760 : Type'} (P : _91760 -> Prop) : (term404 _91760 P) = (term405 _91760 P).
Proof. exact (@lem18394 _91760 P). Qed.
Lemma lem3578601 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term406 _91760 _91764 _91765 P y g f) = (term407 _91760 _91764 _91765 P y g f).
Proof. exact (@lem3578600 _91760 (term306 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578602 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term317 _91760 _91764 _91765 P y g f h) = (term318 _91760 _91764 _91765 P y g f h).
Proof. exact (eq_refl (term317 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578603 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3578604 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term408 _91760 _91764 _91765 P y g f h) = (term395 _91760 _91764 _91765 P y g f h).
Proof. exact (MK_COMB (@lem3578603) (@lem3578602 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578605 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term408 _91760 _91764 _91765 P y g f h) = (term401 _91760 _91764 _91765 P y g f h).
Proof. exact (TRANS (@lem3578604 _91760 _91764 _91765 P y g f h) (@lem3578596 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578606 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term409 _91760 _91764 _91765 P y g f) = (term410 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun h : _91760 => @lem3578605 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578607 {_91760 : Type'} : (@all _91760) = (@all _91760).
Proof. exact (eq_refl (@all _91760)). Qed.
Lemma lem3578608 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term407 _91760 _91764 _91765 P y g f) = (term411 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3578607 _91760) (@lem3578606 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578609 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term406 _91760 _91764 _91765 P y g f) = (term411 _91760 _91764 _91765 P y g f).
Proof. exact (TRANS (@lem3578601 _91760 _91764 _91765 P y g f) (@lem3578608 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578610 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term306 _91760 _91764 _91765 P y g f) = (term412 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun h : _91760 => @lem3578599 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3578611 {_91760 : Type'} : (@ex _91760) = (@ex _91760).
Proof. exact (eq_refl (@ex _91760)). Qed.
Lemma lem3578612 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term321 _91760 _91764 _91765 P y g f) = (term413 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3578611 _91760) (@lem3578610 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578613 {_91764 : Type'} (P : _91764 -> Prop) : (term51 _91764 P) = (term52 _91764 P).
Proof. exact (@lem18392 _91764 P). Qed.
Lemma lem3578614 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term414 _91760 _91764 _91765 P g f) = (term415 _91760 _91764 _91765 P g f).
Proof. exact (@lem3578613 _91764 (term323 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578615 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term416 _91760 _91764 _91765 P g f y) = (term321 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term416 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3578616 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3578617 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term417 _91760 _91764 _91765 P g f y) = (term406 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3578616) (@lem3578615 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578618 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term417 _91760 _91764 _91765 P g f y) = (term411 _91760 _91764 _91765 P y g f).
Proof. exact (TRANS (@lem3578617 _91760 _91764 _91765 P y g f) (@lem3578609 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578619 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term418 _91760 _91764 _91765 P g f) = (term419 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3578618 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578620 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3578621 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term415 _91760 _91764 _91765 P g f) = (term420 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578620 _91764) (@lem3578619 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578622 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term414 _91760 _91764 _91765 P g f) = (term420 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3578614 _91760 _91764 _91765 P g f) (@lem3578621 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578623 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term323 _91760 _91764 _91765 P g f) = (term421 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3578612 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3578624 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3578625 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term324 _91760 _91764 _91765 P g f) = (term422 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578624 _91764) (@lem3578623 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3578627 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term423 _91760 _91764 _91765 P g f) = (term424 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578626) (@lem3578559 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578628 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term425 _91760 _91764 _91765 P g f) = (term426 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578627 _91760 _91764 _91765 P g f) (@lem3578625 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3578630 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term427 _91760 _91764 _91765 P g f) = (term428 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578629) (@lem3578562 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578631 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term429 _91760 _91764 _91765 P g f) = (term430 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578630 _91760 _91764 _91765 P g f) (@lem3578622 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578632 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3578633 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term431 _91760 _91764 _91765 P g f) = (term432 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578632) (@lem3578631 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578634 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term433 _91760 _91764 _91765 P g f) = (term434 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578633 _91760 _91764 _91765 P g f) (@lem3578628 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578635 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term340 _91760 _91764 _91765 P g f) = (term433 _91760 _91764 _91765 P g f).
Proof. exact (@lem17646 (term279 _91760 _91764 _91765 P g f) (term324 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578636 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term340 _91760 _91764 _91765 P g f) = (term434 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3578635 _91760 _91764 _91765 P g f) (@lem3578634 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578666 {A : Type'} (P : A -> Prop) (Q : Prop) : (term435 A P Q) = (term436 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3578667 {_91765 : Type'} (P : _91765 -> Prop) (Q : Prop) : (term435 _91765 P Q) = (term436 _91765 P Q).
Proof. exact (@lem3578666 _91765 P Q). Qed.
Lemma lem3578668 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term437 _91760 _91764 _91765 P g x f y) = (term438 _91760 _91764 _91765 P g x f y).
Proof. exact (@lem3578667 _91765 (term439 _91764 _91765 P x g y) ((f x) = (f y))). Qed.
Lemma lem3578669 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term440 _91764 _91765 P x g y y') = (term351 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term440 _91764 _91765 P x g y y')). Qed.
Lemma lem3578670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3578671 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term441 _91764 _91765 P x g y y') = (term356 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3578670) (@lem3578669 _91764 _91765 P x g y y')). Qed.
Lemma lem3578672 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3578673 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term442 _91760 _91764 _91765 P g y' x f y) = (term358 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3578671 _91764 _91765 P x g y y') (@lem3578672 _91760 _91765 x f y)). Qed.
Lemma lem3578674 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term443 _91760 _91764 _91765 P g x f y) = (term366 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578673 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578675 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578676 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term437 _91760 _91764 _91765 P g x f y) = (term367 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578675 _91765) (@lem3578674 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578677 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3578678 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term444 _91760 _91764 _91765 P g x f y) = (term445 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578677) (@lem3578676 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578679 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term440 _91764 _91765 P x g y y') = (term351 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term440 _91764 _91765 P x g y y')). Qed.
Lemma lem3578680 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term446 _91764 _91765 P x g y) = (term439 _91764 _91765 P x g y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578679 _91764 _91765 P x g y y')). Qed.
Lemma lem3578681 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578682 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term447 _91764 _91765 P x g y) = (term448 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3578681 _91765) (@lem3578680 _91764 _91765 P x g y)). Qed.
Lemma lem3578683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3578684 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term449 _91764 _91765 P x g y) = (term450 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3578683) (@lem3578682 _91764 _91765 P x g y)). Qed.
Lemma lem3578685 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3578686 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term438 _91760 _91764 _91765 P g x f y) = (term451 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578684 _91764 _91765 P x g y) (@lem3578685 _91760 _91765 x f y)). Qed.
Lemma lem3578687 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((term437 _91760 _91764 _91765 P g x f y) = (term438 _91760 _91764 _91765 P g x f y)) = ((term367 _91760 _91764 _91765 P g x f y) = (term451 _91760 _91764 _91765 P g x f y)).
Proof. exact (MK_COMB (@lem3578678 _91760 _91764 _91765 P g x f y) (@lem3578686 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578688 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term367 _91760 _91764 _91765 P g x f y) = (term451 _91760 _91764 _91765 P g x f y).
Proof. exact (EQ_MP (@lem3578687 _91760 _91764 _91765 P g x f y) (@lem3578668 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578737 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term375 _91760 _91764 _91765 P g x f) = (term452 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3578688 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578738 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578739 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term376 _91760 _91764 _91765 P g x f) = (term453 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578738 _91765) (@lem3578737 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578788 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term384 _91760 _91764 _91765 P g f) = (term454 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3578739 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3578789 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3578790 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term385 _91760 _91764 _91765 P g f) = (term455 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578789 _91765) (@lem3578788 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3578796 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term428 _91760 _91764 _91765 P g f) = (term456 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578795) (@lem3578790 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578853 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term420 _91760 _91764 _91765 P g f) = (term420 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term420 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578854 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term430 _91760 _91764 _91765 P g f) = (term457 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578796 _91760 _91764 _91765 P g f) (@lem3578853 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3578856 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term432 _91760 _91764 _91765 P g f) = (term458 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578855) (@lem3578854 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3578886 {A : Type'} (P : A -> Prop) (Q : Prop) : (term131 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18965 A P Q) (@lem18964 A P Q)). Qed.
Lemma lem3578887 {_91765 : Type'} (P : _91765 -> Prop) (Q : Prop) : (term131 _91765 P Q) = (term130 _91765 P Q).
Proof. exact (@lem3578886 _91765 P Q). Qed.
Lemma lem3578888 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term459 _91760 _91764 _91765 P g x f y) = (term460 _91760 _91764 _91765 P g x f y).
Proof. exact (@lem3578887 _91765 (term461 _91764 _91765 P x g y) (term462 _91760 _91765 x f y)). Qed.
Lemma lem3578889 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term463 _91764 _91765 P x g y y') = (term264 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term463 _91764 _91765 P x g y y')). Qed.
Lemma lem3578890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3578891 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term464 _91764 _91765 P x g y y') = (term465 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3578890) (@lem3578889 _91764 _91765 P x g y y')). Qed.
Lemma lem3578892 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term462 _91760 _91765 x f y) = (term462 _91760 _91765 x f y).
Proof. exact (eq_refl (term462 _91760 _91765 x f y)). Qed.
Lemma lem3578893 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term466 _91760 _91764 _91765 P g y' x f y) = (term354 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3578891 _91764 _91765 P x g y y') (@lem3578892 _91760 _91765 x f y)). Qed.
Lemma lem3578894 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term467 _91760 _91764 _91765 P g x f y) = (term364 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578893 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3578895 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3578896 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term459 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578895 _91765) (@lem3578894 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578897 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3578898 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term468 _91760 _91764 _91765 P g x f y) = (term469 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578897) (@lem3578896 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578899 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term463 _91764 _91765 P x g y y') = (term264 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term463 _91764 _91765 P x g y y')). Qed.
Lemma lem3578900 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term470 _91764 _91765 P x g y) = (term461 _91764 _91765 P x g y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3578899 _91764 _91765 P x g y y')). Qed.
Lemma lem3578901 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3578902 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term471 _91764 _91765 P x g y) = (term472 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3578901 _91765) (@lem3578900 _91764 _91765 P x g y)). Qed.
Lemma lem3578903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3578904 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term473 _91764 _91765 P x g y) = (term474 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3578903) (@lem3578902 _91764 _91765 P x g y)). Qed.
Lemma lem3578905 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term462 _91760 _91765 x f y) = (term462 _91760 _91765 x f y).
Proof. exact (eq_refl (term462 _91760 _91765 x f y)). Qed.
Lemma lem3578906 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term460 _91760 _91764 _91765 P g x f y) = (term475 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3578904 _91764 _91765 P x g y) (@lem3578905 _91760 _91765 x f y)). Qed.
Lemma lem3578907 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((term459 _91760 _91764 _91765 P g x f y) = (term460 _91760 _91764 _91765 P g x f y)) = ((term365 _91760 _91764 _91765 P g x f y) = (term475 _91760 _91764 _91765 P g x f y)).
Proof. exact (MK_COMB (@lem3578898 _91760 _91764 _91765 P g x f y) (@lem3578906 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578908 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term365 _91760 _91764 _91765 P g x f y) = (term475 _91760 _91764 _91765 P g x f y).
Proof. exact (EQ_MP (@lem3578907 _91760 _91764 _91765 P g x f y) (@lem3578888 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578957 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term373 _91760 _91764 _91765 P g x f) = (term476 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3578908 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3578958 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3578959 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term374 _91760 _91764 _91765 P g x f) = (term477 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3578958 _91765) (@lem3578957 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579008 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term382 _91760 _91764 _91765 P g f) = (term478 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3578959 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579009 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579010 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term383 _91760 _91764 _91765 P g f) = (term479 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579009 _91765) (@lem3579008 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579016 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term424 _91760 _91764 _91765 P g f) = (term480 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579015) (@lem3579010 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579073 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term422 _91760 _91764 _91765 P g f) = (term422 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term422 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579074 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term426 _91760 _91764 _91765 P g f) = (term481 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579016 _91760 _91764 _91765 P g f) (@lem3579073 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579075 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term434 _91760 _91764 _91765 P g f) = (term482 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3578856 _91760 _91764 _91765 P g f) (@lem3579074 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579077 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3579078 {_91760 _91765 : Type'} (P : type1413 _91760 _91765) : (term7 _91760 _91765 P) = (term8 _91760 _91765 P).
Proof. exact (@lem3579077 _91760 _91765 P). Qed.
Lemma lem3579079 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term483 _91760 _91764 _91765 P y g f) = (term484 _91760 _91764 _91765 P y g f).
Proof. exact (@lem3579078 _91760 _91765 (term485 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579080 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term486 _91760 _91764 _91765 P y g f h) = (term400 _91760 _91764 _91765 P y g f h).
Proof. exact (eq_refl (term486 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3579081 {_91765 : Type'} (x : _91765) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3579082 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) (x : _91765) : (term487 _91760 _91764 _91765 P y g f h x) = (term488 _91760 _91764 _91765 P y g f h x).
Proof. exact (MK_COMB (@lem3579080 _91760 _91764 _91765 P y g f h) (@lem3579081 _91765 x)). Qed.
Lemma lem3579083 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term488 _91760 _91764 _91765 P y g f h x) = (term389 _91760 _91764 _91765 P y g f x h).
Proof. exact (eq_refl (term488 _91760 _91764 _91765 P y g f h x)). Qed.
Lemma lem3579084 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91760) : (term487 _91760 _91764 _91765 P y g f h x) = (term389 _91760 _91764 _91765 P y g f x h).
Proof. exact (TRANS (@lem3579082 _91760 _91764 _91765 P y g f h x) (@lem3579083 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579085 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term489 _91760 _91764 _91765 P y g f h) = (term400 _91760 _91764 _91765 P y g f h).
Proof. exact (fun_ext (fun x : _91765 => @lem3579084 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579086 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579087 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term490 _91760 _91764 _91765 P y g f h) = (term401 _91760 _91764 _91765 P y g f h).
Proof. exact (MK_COMB (@lem3579086 _91765) (@lem3579085 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3579088 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term491 _91760 _91764 _91765 P y g f) = (term410 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun h : _91760 => @lem3579087 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3579089 {_91760 : Type'} : (@all _91760) = (@all _91760).
Proof. exact (eq_refl (@all _91760)). Qed.
Lemma lem3579090 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term483 _91760 _91764 _91765 P y g f) = (term411 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579089 _91760) (@lem3579088 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579092 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term492 _91760 _91764 _91765 P y g f) = (term493 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579091) (@lem3579090 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579093 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term486 _91760 _91764 _91765 P y g f h) = (term400 _91760 _91764 _91765 P y g f h).
Proof. exact (eq_refl (term486 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3579094 {_91760 _91765 : Type'} (x : _91760 -> _91765) (h : _91760) : (x h) = (x h).
Proof. exact (eq_refl (x h)). Qed.
Lemma lem3579095 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h : _91760) : (term494 _91760 _91764 _91765 P y g f x h) = (term495 _91760 _91764 _91765 P y g f x h).
Proof. exact (MK_COMB (@lem3579093 _91760 _91764 _91765 P y g f h) (@lem3579094 _91760 _91765 x h)). Qed.
Lemma lem3579096 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h : _91760) : (term495 _91760 _91764 _91765 P y g f x h) = (term496 _91760 _91764 _91765 P y g f x h).
Proof. exact (eq_refl (term495 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579097 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h : _91760) : (term494 _91760 _91764 _91765 P y g f x h) = (term496 _91760 _91764 _91765 P y g f x h).
Proof. exact (TRANS (@lem3579095 _91760 _91764 _91765 P y g f x h) (@lem3579096 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579098 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term497 _91760 _91764 _91765 P y g f x) = (term498 _91760 _91764 _91765 P y g f x).
Proof. exact (fun_ext (fun h : _91760 => @lem3579097 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579099 {_91760 : Type'} : (@all _91760) = (@all _91760).
Proof. exact (eq_refl (@all _91760)). Qed.
Lemma lem3579100 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term499 _91760 _91764 _91765 P y g f x) = (term500 _91760 _91764 _91765 P y g f x).
Proof. exact (MK_COMB (@lem3579099 _91760) (@lem3579098 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579101 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term501 _91760 _91764 _91765 P y g f) = (term502 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun x : _91760 -> _91765 => @lem3579100 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579102 {_91760 _91765 : Type'} : (@ex (_91760 -> _91765)) = (@ex (_91760 -> _91765)).
Proof. exact (eq_refl (@ex (_91760 -> _91765))). Qed.
Lemma lem3579103 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term484 _91760 _91764 _91765 P y g f) = (term503 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579102 _91760 _91765) (@lem3579101 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579104 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term483 _91760 _91764 _91765 P y g f) = (term484 _91760 _91764 _91765 P y g f)) = ((term411 _91760 _91764 _91765 P y g f) = (term503 _91760 _91764 _91765 P y g f)).
Proof. exact (MK_COMB (@lem3579092 _91760 _91764 _91765 P y g f) (@lem3579103 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579105 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term411 _91760 _91764 _91765 P y g f) = (term503 _91760 _91764 _91765 P y g f).
Proof. exact (EQ_MP (@lem3579104 _91760 _91764 _91765 P y g f) (@lem3579079 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579106 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term419 _91760 _91764 _91765 P g f) = (term504 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579105 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579107 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3579108 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term420 _91760 _91764 _91765 P g f) = (term505 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579107 _91764) (@lem3579106 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579109 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term456 _91760 _91764 _91765 P g f) = (term456 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term456 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579110 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term457 _91760 _91764 _91765 P g f) = (term506 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579109 _91760 _91764 _91765 P g f) (@lem3579108 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579112 {A : Type'} (P : Prop) (Q : A -> Prop) : (term101 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3579113 {_91764 : Type'} (P : Prop) (Q : _91764 -> Prop) : (term101 _91764 P Q) = (term102 _91764 P Q).
Proof. exact (@lem3579112 _91764 P Q). Qed.
Lemma lem3579114 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term507 _91760 _91764 _91765 P g f) = (term508 _91760 _91764 _91765 P g f).
Proof. exact (@lem3579113 _91764 (term455 _91760 _91764 _91765 P g f) (term504 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579115 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term509 _91760 _91764 _91765 P g f y) = (term503 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term509 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3579116 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term510 _91760 _91764 _91765 P g f) = (term504 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579115 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579117 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3579118 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term511 _91760 _91764 _91765 P g f) = (term505 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579117 _91764) (@lem3579116 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579119 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term456 _91760 _91764 _91765 P g f) = (term456 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term456 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579120 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term507 _91760 _91764 _91765 P g f) = (term506 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579119 _91760 _91764 _91765 P g f) (@lem3579118 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579121 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579122 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term512 _91760 _91764 _91765 P g f) = (term513 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579121) (@lem3579120 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579123 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term509 _91760 _91764 _91765 P g f y) = (term503 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term509 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3579124 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term456 _91760 _91764 _91765 P g f) = (term456 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term456 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579125 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term514 _91760 _91764 _91765 P g f y) = (term515 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579124 _91760 _91764 _91765 P g f) (@lem3579123 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579126 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term516 _91760 _91764 _91765 P g f) = (term517 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579125 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579127 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3579128 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term508 _91760 _91764 _91765 P g f) = (term518 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579127 _91764) (@lem3579126 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579129 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term507 _91760 _91764 _91765 P g f) = (term508 _91760 _91764 _91765 P g f)) = ((term506 _91760 _91764 _91765 P g f) = (term518 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3579122 _91760 _91764 _91765 P g f) (@lem3579128 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579130 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term506 _91760 _91764 _91765 P g f) = (term518 _91760 _91764 _91765 P g f).
Proof. exact (EQ_MP (@lem3579129 _91760 _91764 _91765 P g f) (@lem3579114 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579132 {A : Type'} (P : Prop) (Q : A -> Prop) : (term101 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3579133 {_91760 _91765 : Type'} (P : Prop) (Q : type572 _91760 _91765) : (term519 _91760 _91765 P Q) = (term520 _91760 _91765 P Q).
Proof. exact (@lem3579132 (_91760 -> _91765) P Q). Qed.
Lemma lem3579134 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term521 _91760 _91764 _91765 P y g f) = (term522 _91760 _91764 _91765 P y g f).
Proof. exact (@lem3579133 _91760 _91765 (term455 _91760 _91764 _91765 P g f) (term502 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579135 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term523 _91760 _91764 _91765 P y g f x) = (term500 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term523 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579136 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term524 _91760 _91764 _91765 P y g f) = (term502 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun x : _91760 -> _91765 => @lem3579135 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579137 {_91760 _91765 : Type'} : (@ex (_91760 -> _91765)) = (@ex (_91760 -> _91765)).
Proof. exact (eq_refl (@ex (_91760 -> _91765))). Qed.
Lemma lem3579138 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term525 _91760 _91764 _91765 P y g f) = (term503 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579137 _91760 _91765) (@lem3579136 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579139 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term456 _91760 _91764 _91765 P g f) = (term456 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term456 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579140 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term521 _91760 _91764 _91765 P y g f) = (term515 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579139 _91760 _91764 _91765 P g f) (@lem3579138 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579141 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579142 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term526 _91760 _91764 _91765 P y g f) = (term527 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579141) (@lem3579140 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579143 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term523 _91760 _91764 _91765 P y g f x) = (term500 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term523 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579144 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term456 _91760 _91764 _91765 P g f) = (term456 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term456 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579145 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term528 _91760 _91764 _91765 P y g f x) = (term529 _91760 _91764 _91765 P y g f x).
Proof. exact (MK_COMB (@lem3579144 _91760 _91764 _91765 P g f) (@lem3579143 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579146 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term530 _91760 _91764 _91765 P y g f) = (term531 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun x : _91760 -> _91765 => @lem3579145 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579147 {_91760 _91765 : Type'} : (@ex (_91760 -> _91765)) = (@ex (_91760 -> _91765)).
Proof. exact (eq_refl (@ex (_91760 -> _91765))). Qed.
Lemma lem3579148 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term522 _91760 _91764 _91765 P y g f) = (term532 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579147 _91760 _91765) (@lem3579146 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579149 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term521 _91760 _91764 _91765 P y g f) = (term522 _91760 _91764 _91765 P y g f)) = ((term515 _91760 _91764 _91765 P y g f) = (term532 _91760 _91764 _91765 P y g f)).
Proof. exact (MK_COMB (@lem3579142 _91760 _91764 _91765 P y g f) (@lem3579148 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579150 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term515 _91760 _91764 _91765 P y g f) = (term532 _91760 _91764 _91765 P y g f).
Proof. exact (EQ_MP (@lem3579149 _91760 _91764 _91765 P y g f) (@lem3579134 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579151 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term517 _91760 _91764 _91765 P g f) = (term533 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579150 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579152 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3579153 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term518 _91760 _91764 _91765 P g f) = (term534 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579152 _91764) (@lem3579151 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579154 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term506 _91760 _91764 _91765 P g f) = (term534 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579130 _91760 _91764 _91765 P g f) (@lem3579153 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579155 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term457 _91760 _91764 _91765 P g f) = (term534 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579110 _91760 _91764 _91765 P g f) (@lem3579154 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579157 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term458 _91760 _91764 _91765 P g f) = (term535 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579156) (@lem3579155 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579159 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3579160 {_91765 : Type'} (P : _91765 -> Prop) (Q : Prop) : (term130 _91765 P Q) = (term131 _91765 P Q).
Proof. exact (@lem3579159 _91765 P Q). Qed.
Lemma lem3579161 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term460 _91760 _91764 _91765 P g x f y) = (term459 _91760 _91764 _91765 P g x f y).
Proof. exact (@lem3579160 _91765 (term461 _91764 _91765 P x g y) (term462 _91760 _91765 x f y)). Qed.
Lemma lem3579162 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term463 _91764 _91765 P x g y y') = (term264 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term463 _91764 _91765 P x g y y')). Qed.
Lemma lem3579163 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term470 _91764 _91765 P x g y) = (term461 _91764 _91765 P x g y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579162 _91764 _91765 P x g y y')). Qed.
Lemma lem3579164 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579165 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term471 _91764 _91765 P x g y) = (term472 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3579164 _91765) (@lem3579163 _91764 _91765 P x g y)). Qed.
Lemma lem3579166 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579167 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term473 _91764 _91765 P x g y) = (term474 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3579166) (@lem3579165 _91764 _91765 P x g y)). Qed.
Lemma lem3579168 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term462 _91760 _91765 x f y) = (term462 _91760 _91765 x f y).
Proof. exact (eq_refl (term462 _91760 _91765 x f y)). Qed.
Lemma lem3579169 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term460 _91760 _91764 _91765 P g x f y) = (term475 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579167 _91764 _91765 P x g y) (@lem3579168 _91760 _91765 x f y)). Qed.
Lemma lem3579170 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579171 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term536 _91760 _91764 _91765 P g x f y) = (term537 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579170) (@lem3579169 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579172 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term463 _91764 _91765 P x g y y') = (term264 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term463 _91764 _91765 P x g y y')). Qed.
Lemma lem3579173 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579174 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term464 _91764 _91765 P x g y y') = (term465 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3579173) (@lem3579172 _91764 _91765 P x g y y')). Qed.
Lemma lem3579175 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term462 _91760 _91765 x f y) = (term462 _91760 _91765 x f y).
Proof. exact (eq_refl (term462 _91760 _91765 x f y)). Qed.
Lemma lem3579176 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term466 _91760 _91764 _91765 P g y' x f y) = (term354 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3579174 _91764 _91765 P x g y y') (@lem3579175 _91760 _91765 x f y)). Qed.
Lemma lem3579177 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term467 _91760 _91764 _91765 P g x f y) = (term364 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579176 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579178 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579179 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term459 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579178 _91765) (@lem3579177 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579180 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((term460 _91760 _91764 _91765 P g x f y) = (term459 _91760 _91764 _91765 P g x f y)) = ((term475 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y)).
Proof. exact (MK_COMB (@lem3579171 _91760 _91764 _91765 P g x f y) (@lem3579179 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579181 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term475 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (EQ_MP (@lem3579180 _91760 _91764 _91765 P g x f y) (@lem3579161 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579182 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term476 _91760 _91764 _91765 P g x f) = (term373 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579181 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579183 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579184 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term477 _91760 _91764 _91765 P g x f) = (term374 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3579183 _91765) (@lem3579182 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579185 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term478 _91760 _91764 _91765 P g f) = (term382 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579184 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579186 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579187 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term479 _91760 _91764 _91765 P g f) = (term383 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579186 _91765) (@lem3579185 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579188 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579189 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term480 _91760 _91764 _91765 P g f) = (term424 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579188) (@lem3579187 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579191 {A B : Type'} (P : type1413 A B) : (term7 A B P) = (term8 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3579192 {_91760 _91764 : Type'} (P : type1470 _91760 _91764) : (term301 _91760 _91764 P) = (term300 _91760 _91764 P).
Proof. exact (@lem3579191 _91764 _91760 P). Qed.
Lemma lem3579193 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term538 _91760 _91764 _91765 P g f) = (term539 _91760 _91764 _91765 P g f).
Proof. exact (@lem3579192 _91760 _91764 (term540 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579194 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term541 _91760 _91764 _91765 P g f y) = (term412 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term541 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3579195 {_91760 : Type'} (h : _91760) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem3579196 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term542 _91760 _91764 _91765 P g f y h) = (term543 _91760 _91764 _91765 P y g f h).
Proof. exact (MK_COMB (@lem3579194 _91760 _91764 _91765 P y g f) (@lem3579195 _91760 h)). Qed.
Lemma lem3579197 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term543 _91760 _91764 _91765 P y g f h) = (term403 _91760 _91764 _91765 P y g f h).
Proof. exact (eq_refl (term543 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3579198 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91760) : (term542 _91760 _91764 _91765 P g f y h) = (term403 _91760 _91764 _91765 P y g f h).
Proof. exact (TRANS (@lem3579196 _91760 _91764 _91765 P y g f h) (@lem3579197 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3579199 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term544 _91760 _91764 _91765 P g f y) = (term412 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun h : _91760 => @lem3579198 _91760 _91764 _91765 P y g f h)). Qed.
Lemma lem3579200 {_91760 : Type'} : (@ex _91760) = (@ex _91760).
Proof. exact (eq_refl (@ex _91760)). Qed.
Lemma lem3579201 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term545 _91760 _91764 _91765 P g f y) = (term413 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579200 _91760) (@lem3579199 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579202 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term546 _91760 _91764 _91765 P g f) = (term421 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579201 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579203 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3579204 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term538 _91760 _91764 _91765 P g f) = (term422 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579203 _91764) (@lem3579202 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579205 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579206 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term547 _91760 _91764 _91765 P g f) = (term548 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579205) (@lem3579204 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579207 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term541 _91760 _91764 _91765 P g f y) = (term412 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term541 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3579208 {_91760 _91764 : Type'} (h : _91764 -> _91760) (y : _91764) : (h y) = (h y).
Proof. exact (eq_refl (h y)). Qed.
Lemma lem3579209 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term549 _91760 _91764 _91765 P g f h y) = (term550 _91760 _91764 _91765 P g f h y).
Proof. exact (MK_COMB (@lem3579207 _91760 _91764 _91765 P y g f) (@lem3579208 _91760 _91764 h y)). Qed.
Lemma lem3579210 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term550 _91760 _91764 _91765 P g f h y) = (term551 _91760 _91764 _91765 P g f h y).
Proof. exact (eq_refl (term550 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3579211 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term549 _91760 _91764 _91765 P g f h y) = (term551 _91760 _91764 _91765 P g f h y).
Proof. exact (TRANS (@lem3579209 _91760 _91764 _91765 P g f h y) (@lem3579210 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3579212 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term552 _91760 _91764 _91765 P g f h) = (term553 _91760 _91764 _91765 P g f h).
Proof. exact (fun_ext (fun y : _91764 => @lem3579211 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3579213 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3579214 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term554 _91760 _91764 _91765 P g f h) = (term555 _91760 _91764 _91765 P g f h).
Proof. exact (MK_COMB (@lem3579213 _91764) (@lem3579212 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579215 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term556 _91760 _91764 _91765 P g f) = (term557 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3579214 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579216 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3579217 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term539 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579216 _91760 _91764) (@lem3579215 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579218 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term538 _91760 _91764 _91765 P g f) = (term539 _91760 _91764 _91765 P g f)) = ((term422 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3579206 _91760 _91764 _91765 P g f) (@lem3579217 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579219 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term422 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (EQ_MP (@lem3579218 _91760 _91764 _91765 P g f) (@lem3579193 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579220 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term481 _91760 _91764 _91765 P g f) = (term559 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579189 _91760 _91764 _91765 P g f) (@lem3579219 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579222 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3579223 {_91765 : Type'} (P : _91765 -> Prop) (Q : Prop) : (term130 _91765 P Q) = (term131 _91765 P Q).
Proof. exact (@lem3579222 _91765 P Q). Qed.
Lemma lem3579224 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term560 _91760 _91764 _91765 P g f) = (term561 _91760 _91764 _91765 P g f).
Proof. exact (@lem3579223 _91765 (term382 _91760 _91764 _91765 P g f) (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579225 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term562 _91760 _91764 _91765 P g f x) = (term374 _91760 _91764 _91765 P g x f).
Proof. exact (eq_refl (term562 _91760 _91764 _91765 P g f x)). Qed.
Lemma lem3579226 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term563 _91760 _91764 _91765 P g f) = (term382 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579225 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579227 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579228 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term564 _91760 _91764 _91765 P g f) = (term383 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579227 _91765) (@lem3579226 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579229 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579230 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term565 _91760 _91764 _91765 P g f) = (term424 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579229) (@lem3579228 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579231 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term558 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579232 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term560 _91760 _91764 _91765 P g f) = (term559 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579230 _91760 _91764 _91765 P g f) (@lem3579231 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579233 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579234 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term566 _91760 _91764 _91765 P g f) = (term567 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579233) (@lem3579232 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579235 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term562 _91760 _91764 _91765 P g f x) = (term374 _91760 _91764 _91765 P g x f).
Proof. exact (eq_refl (term562 _91760 _91764 _91765 P g f x)). Qed.
Lemma lem3579236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579237 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term568 _91760 _91764 _91765 P g f x) = (term569 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3579236) (@lem3579235 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579238 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term558 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579239 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term570 _91760 _91764 _91765 x P g f) = (term571 _91760 _91764 _91765 x P g f).
Proof. exact (MK_COMB (@lem3579237 _91760 _91764 _91765 P g x f) (@lem3579238 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579240 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term572 _91760 _91764 _91765 P g f) = (term573 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579239 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579241 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579242 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term561 _91760 _91764 _91765 P g f) = (term574 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579241 _91765) (@lem3579240 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579243 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term560 _91760 _91764 _91765 P g f) = (term561 _91760 _91764 _91765 P g f)) = ((term559 _91760 _91764 _91765 P g f) = (term574 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3579234 _91760 _91764 _91765 P g f) (@lem3579242 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579244 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term559 _91760 _91764 _91765 P g f) = (term574 _91760 _91764 _91765 P g f).
Proof. exact (EQ_MP (@lem3579243 _91760 _91764 _91765 P g f) (@lem3579224 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579246 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3579247 {_91765 : Type'} (P : _91765 -> Prop) (Q : Prop) : (term130 _91765 P Q) = (term131 _91765 P Q).
Proof. exact (@lem3579246 _91765 P Q). Qed.
Lemma lem3579248 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term575 _91760 _91764 _91765 x P g f) = (term576 _91760 _91764 _91765 x P g f).
Proof. exact (@lem3579247 _91765 (term373 _91760 _91764 _91765 P g x f) (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579249 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term577 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (eq_refl (term577 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579250 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term578 _91760 _91764 _91765 P g x f) = (term373 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579249 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579251 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579252 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term579 _91760 _91764 _91765 P g x f) = (term374 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3579251 _91765) (@lem3579250 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579254 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term580 _91760 _91764 _91765 P g x f) = (term569 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3579253) (@lem3579252 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579255 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term558 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579256 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term575 _91760 _91764 _91765 x P g f) = (term571 _91760 _91764 _91765 x P g f).
Proof. exact (MK_COMB (@lem3579254 _91760 _91764 _91765 P g x f) (@lem3579255 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579258 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term581 _91760 _91764 _91765 x P g f) = (term582 _91760 _91764 _91765 x P g f).
Proof. exact (MK_COMB (@lem3579257) (@lem3579256 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579259 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term577 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (eq_refl (term577 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579261 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term583 _91760 _91764 _91765 P g x f y) = (term584 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579260) (@lem3579259 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579262 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term558 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579263 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term585 _91760 _91764 _91765 x y P g f) = (term586 _91760 _91764 _91765 x y P g f).
Proof. exact (MK_COMB (@lem3579261 _91760 _91764 _91765 P g x f y) (@lem3579262 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579264 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term587 _91760 _91764 _91765 x P g f) = (term588 _91760 _91764 _91765 x P g f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579263 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579265 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579266 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term576 _91760 _91764 _91765 x P g f) = (term589 _91760 _91764 _91765 x P g f).
Proof. exact (MK_COMB (@lem3579265 _91765) (@lem3579264 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579267 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term575 _91760 _91764 _91765 x P g f) = (term576 _91760 _91764 _91765 x P g f)) = ((term571 _91760 _91764 _91765 x P g f) = (term589 _91760 _91764 _91765 x P g f)).
Proof. exact (MK_COMB (@lem3579258 _91760 _91764 _91765 x P g f) (@lem3579266 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579268 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term571 _91760 _91764 _91765 x P g f) = (term589 _91760 _91764 _91765 x P g f).
Proof. exact (EQ_MP (@lem3579267 _91760 _91764 _91765 x P g f) (@lem3579248 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579270 {A : Type'} (P : A -> Prop) (Q : Prop) : (term130 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3579271 {_91765 : Type'} (P : _91765 -> Prop) (Q : Prop) : (term130 _91765 P Q) = (term131 _91765 P Q).
Proof. exact (@lem3579270 _91765 P Q). Qed.
Lemma lem3579272 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term590 _91760 _91764 _91765 x y P g f) = (term591 _91760 _91764 _91765 x y P g f).
Proof. exact (@lem3579271 _91765 (term364 _91760 _91764 _91765 P g x f y) (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579273 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term592 _91760 _91764 _91765 P g x f y y') = (term354 _91760 _91764 _91765 P g y' x f y).
Proof. exact (eq_refl (term592 _91760 _91764 _91765 P g x f y y')). Qed.
Lemma lem3579274 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term593 _91760 _91764 _91765 P g x f y) = (term364 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579273 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579275 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579276 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term594 _91760 _91764 _91765 P g x f y) = (term365 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579275 _91765) (@lem3579274 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579278 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term595 _91760 _91764 _91765 P g x f y) = (term584 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579277) (@lem3579276 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579279 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term558 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579280 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term590 _91760 _91764 _91765 x y P g f) = (term586 _91760 _91764 _91765 x y P g f).
Proof. exact (MK_COMB (@lem3579278 _91760 _91764 _91765 P g x f y) (@lem3579279 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579282 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term596 _91760 _91764 _91765 x y P g f) = (term597 _91760 _91764 _91765 x y P g f).
Proof. exact (MK_COMB (@lem3579281) (@lem3579280 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579283 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term592 _91760 _91764 _91765 P g x f y y') = (term354 _91760 _91764 _91765 P g y' x f y).
Proof. exact (eq_refl (term592 _91760 _91764 _91765 P g x f y y')). Qed.
Lemma lem3579284 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579285 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term598 _91760 _91764 _91765 P g x f y y') = (term599 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3579284) (@lem3579283 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579286 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term558 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term558 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579287 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term600 _91760 _91764 _91765 x y y' P g f) = (term601 _91760 _91764 _91765 y' x y P g f).
Proof. exact (MK_COMB (@lem3579285 _91760 _91764 _91765 P g y' x f y) (@lem3579286 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579288 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term602 _91760 _91764 _91765 x y P g f) = (term603 _91760 _91764 _91765 x y P g f).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579287 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579289 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579290 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term591 _91760 _91764 _91765 x y P g f) = (term604 _91760 _91764 _91765 x y P g f).
Proof. exact (MK_COMB (@lem3579289 _91765) (@lem3579288 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579291 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term590 _91760 _91764 _91765 x y P g f) = (term591 _91760 _91764 _91765 x y P g f)) = ((term586 _91760 _91764 _91765 x y P g f) = (term604 _91760 _91764 _91765 x y P g f)).
Proof. exact (MK_COMB (@lem3579282 _91760 _91764 _91765 x y P g f) (@lem3579290 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579292 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term586 _91760 _91764 _91765 x y P g f) = (term604 _91760 _91764 _91765 x y P g f).
Proof. exact (EQ_MP (@lem3579291 _91760 _91764 _91765 x y P g f) (@lem3579272 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579294 {A : Type'} (P : Prop) (Q : A -> Prop) : (term101 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3579295 {_91760 _91764 : Type'} (P : Prop) (Q : type805 _91760 _91764) : (term605 _91760 _91764 P Q) = (term606 _91760 _91764 P Q).
Proof. exact (@lem3579294 (_91764 -> _91760) P Q). Qed.
Lemma lem3579296 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term607 _91760 _91764 _91765 y' x y P g f) = (term608 _91760 _91764 _91765 y' x y P g f).
Proof. exact (@lem3579295 _91760 _91764 (term354 _91760 _91764 _91765 P g y' x f y) (term557 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579297 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term609 _91760 _91764 _91765 P g f h) = (term555 _91760 _91764 _91765 P g f h).
Proof. exact (eq_refl (term609 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579298 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term610 _91760 _91764 _91765 P g f) = (term557 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3579297 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579299 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3579300 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term611 _91760 _91764 _91765 P g f) = (term558 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579299 _91760 _91764) (@lem3579298 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579301 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term599 _91760 _91764 _91765 P g y' x f y) = (term599 _91760 _91764 _91765 P g y' x f y).
Proof. exact (eq_refl (term599 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579302 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term607 _91760 _91764 _91765 y' x y P g f) = (term601 _91760 _91764 _91765 y' x y P g f).
Proof. exact (MK_COMB (@lem3579301 _91760 _91764 _91765 P g y' x f y) (@lem3579300 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579304 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term612 _91760 _91764 _91765 y' x y P g f) = (term613 _91760 _91764 _91765 y' x y P g f).
Proof. exact (MK_COMB (@lem3579303) (@lem3579302 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579305 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term609 _91760 _91764 _91765 P g f h) = (term555 _91760 _91764 _91765 P g f h).
Proof. exact (eq_refl (term609 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579306 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term599 _91760 _91764 _91765 P g y' x f y) = (term599 _91760 _91764 _91765 P g y' x f y).
Proof. exact (eq_refl (term599 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579307 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term614 _91760 _91764 _91765 y' x y P g f h) = (term615 _91760 _91764 _91765 y' x y P g f h).
Proof. exact (MK_COMB (@lem3579306 _91760 _91764 _91765 P g y' x f y) (@lem3579305 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579308 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term616 _91760 _91764 _91765 y' x y P g f) = (term617 _91760 _91764 _91765 y' x y P g f).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3579307 _91760 _91764 _91765 y' x y P g f h)). Qed.
Lemma lem3579309 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3579310 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term608 _91760 _91764 _91765 y' x y P g f) = (term618 _91760 _91764 _91765 y' x y P g f).
Proof. exact (MK_COMB (@lem3579309 _91760 _91764) (@lem3579308 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579311 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term607 _91760 _91764 _91765 y' x y P g f) = (term608 _91760 _91764 _91765 y' x y P g f)) = ((term601 _91760 _91764 _91765 y' x y P g f) = (term618 _91760 _91764 _91765 y' x y P g f)).
Proof. exact (MK_COMB (@lem3579304 _91760 _91764 _91765 y' x y P g f) (@lem3579310 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579312 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term601 _91760 _91764 _91765 y' x y P g f) = (term618 _91760 _91764 _91765 y' x y P g f).
Proof. exact (EQ_MP (@lem3579311 _91760 _91764 _91765 y' x y P g f) (@lem3579296 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579313 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term603 _91760 _91764 _91765 x y P g f) = (term619 _91760 _91764 _91765 x y P g f).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579312 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579314 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579315 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term604 _91760 _91764 _91765 x y P g f) = (term620 _91760 _91764 _91765 x y P g f).
Proof. exact (MK_COMB (@lem3579314 _91765) (@lem3579313 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579316 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term586 _91760 _91764 _91765 x y P g f) = (term620 _91760 _91764 _91765 x y P g f).
Proof. exact (TRANS (@lem3579292 _91760 _91764 _91765 x y P g f) (@lem3579315 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579317 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term588 _91760 _91764 _91765 x P g f) = (term621 _91760 _91764 _91765 x P g f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579316 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579318 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579319 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term589 _91760 _91764 _91765 x P g f) = (term622 _91760 _91764 _91765 x P g f).
Proof. exact (MK_COMB (@lem3579318 _91765) (@lem3579317 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579320 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term571 _91760 _91764 _91765 x P g f) = (term622 _91760 _91764 _91765 x P g f).
Proof. exact (TRANS (@lem3579268 _91760 _91764 _91765 x P g f) (@lem3579319 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579321 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term573 _91760 _91764 _91765 P g f) = (term623 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579320 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579322 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579323 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term574 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579322 _91765) (@lem3579321 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579324 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term559 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579244 _91760 _91764 _91765 P g f) (@lem3579323 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579325 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term481 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579220 _91760 _91764 _91765 P g f) (@lem3579324 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579326 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term482 _91760 _91764 _91765 P g f) = (term625 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579157 _91760 _91764 _91765 P g f) (@lem3579325 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579330 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3579331 {_91764 : Type'} (P : _91764 -> Prop) (Q : Prop) : (term148 _91764 P Q) = (term149 _91764 P Q).
Proof. exact (@lem3579330 _91764 P Q). Qed.
Lemma lem3579332 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term626 _91760 _91764 _91765 P g f) = (term627 _91760 _91764 _91765 P g f).
Proof. exact (@lem3579331 _91764 (term533 _91760 _91764 _91765 P g f) (term624 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579333 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term628 _91760 _91764 _91765 P g f y) = (term532 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term628 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3579334 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term629 _91760 _91764 _91765 P g f) = (term533 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579333 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579335 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3579336 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term630 _91760 _91764 _91765 P g f) = (term534 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579335 _91764) (@lem3579334 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579337 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579338 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term631 _91760 _91764 _91765 P g f) = (term535 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579337) (@lem3579336 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579339 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term624 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term624 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579340 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term626 _91760 _91764 _91765 P g f) = (term625 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579338 _91760 _91764 _91765 P g f) (@lem3579339 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579342 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term632 _91760 _91764 _91765 P g f) = (term633 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579341) (@lem3579340 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579343 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term628 _91760 _91764 _91765 P g f y) = (term532 _91760 _91764 _91765 P y g f).
Proof. exact (eq_refl (term628 _91760 _91764 _91765 P g f y)). Qed.
Lemma lem3579344 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579345 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term634 _91760 _91764 _91765 P g f y) = (term635 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579344) (@lem3579343 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579346 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term624 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term624 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579347 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term636 _91760 _91764 _91765 y P g f) = (term637 _91760 _91764 _91765 y P g f).
Proof. exact (MK_COMB (@lem3579345 _91760 _91764 _91765 P y g f) (@lem3579346 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579348 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term638 _91760 _91764 _91765 P g f) = (term639 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579347 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579349 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3579350 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term627 _91760 _91764 _91765 P g f) = (term640 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579349 _91764) (@lem3579348 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579351 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term626 _91760 _91764 _91765 P g f) = (term627 _91760 _91764 _91765 P g f)) = ((term625 _91760 _91764 _91765 P g f) = (term640 _91760 _91764 _91765 P g f)).
Proof. exact (MK_COMB (@lem3579342 _91760 _91764 _91765 P g f) (@lem3579350 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579352 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term625 _91760 _91764 _91765 P g f) = (term640 _91760 _91764 _91765 P g f).
Proof. exact (EQ_MP (@lem3579351 _91760 _91764 _91765 P g f) (@lem3579332 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579356 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3579357 {_91760 _91765 : Type'} (P : type572 _91760 _91765) (Q : Prop) : (term641 _91760 _91765 P Q) = (term642 _91760 _91765 P Q).
Proof. exact (@lem3579356 (_91760 -> _91765) P Q). Qed.
Lemma lem3579358 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term643 _91760 _91764 _91765 y P g f) = (term644 _91760 _91764 _91765 y P g f).
Proof. exact (@lem3579357 _91760 _91765 (term531 _91760 _91764 _91765 P y g f) (term624 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579359 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term645 _91760 _91764 _91765 P y g f x) = (term529 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term645 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579360 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term646 _91760 _91764 _91765 P y g f) = (term531 _91760 _91764 _91765 P y g f).
Proof. exact (fun_ext (fun x : _91760 -> _91765 => @lem3579359 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579361 {_91760 _91765 : Type'} : (@ex (_91760 -> _91765)) = (@ex (_91760 -> _91765)).
Proof. exact (eq_refl (@ex (_91760 -> _91765))). Qed.
Lemma lem3579362 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term647 _91760 _91764 _91765 P y g f) = (term532 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579361 _91760 _91765) (@lem3579360 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579364 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term648 _91760 _91764 _91765 P y g f) = (term635 _91760 _91764 _91765 P y g f).
Proof. exact (MK_COMB (@lem3579363) (@lem3579362 _91760 _91764 _91765 P y g f)). Qed.
Lemma lem3579365 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term624 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term624 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579366 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term643 _91760 _91764 _91765 y P g f) = (term637 _91760 _91764 _91765 y P g f).
Proof. exact (MK_COMB (@lem3579364 _91760 _91764 _91765 P y g f) (@lem3579365 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579368 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term649 _91760 _91764 _91765 y P g f) = (term650 _91760 _91764 _91765 y P g f).
Proof. exact (MK_COMB (@lem3579367) (@lem3579366 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579369 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term645 _91760 _91764 _91765 P y g f x) = (term529 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term645 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579370 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579371 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term651 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (MK_COMB (@lem3579370) (@lem3579369 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579372 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term624 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (eq_refl (term624 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579373 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term653 _91760 _91764 _91765 y x P g f) = (term654 _91760 _91764 _91765 y x P g f).
Proof. exact (MK_COMB (@lem3579371 _91760 _91764 _91765 P y g f x) (@lem3579372 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579374 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term655 _91760 _91764 _91765 y P g f) = (term656 _91760 _91764 _91765 y P g f).
Proof. exact (fun_ext (fun x : _91760 -> _91765 => @lem3579373 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579375 {_91760 _91765 : Type'} : (@ex (_91760 -> _91765)) = (@ex (_91760 -> _91765)).
Proof. exact (eq_refl (@ex (_91760 -> _91765))). Qed.
Lemma lem3579376 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term644 _91760 _91764 _91765 y P g f) = (term657 _91760 _91764 _91765 y P g f).
Proof. exact (MK_COMB (@lem3579375 _91760 _91765) (@lem3579374 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579377 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term643 _91760 _91764 _91765 y P g f) = (term644 _91760 _91764 _91765 y P g f)) = ((term637 _91760 _91764 _91765 y P g f) = (term657 _91760 _91764 _91765 y P g f)).
Proof. exact (MK_COMB (@lem3579368 _91760 _91764 _91765 y P g f) (@lem3579376 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579378 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term637 _91760 _91764 _91765 y P g f) = (term657 _91760 _91764 _91765 y P g f).
Proof. exact (EQ_MP (@lem3579377 _91760 _91764 _91765 y P g f) (@lem3579358 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579380 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3579381 {_91765 : Type'} (P : Prop) (Q : _91765 -> Prop) : (term658 _91765 P Q) = (term659 _91765 P Q).
Proof. exact (@lem3579380 _91765 P Q). Qed.
Lemma lem3579382 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term660 _91760 _91764 _91765 y x P g f) = (term661 _91760 _91764 _91765 y x P g f).
Proof. exact (@lem3579381 _91765 (term529 _91760 _91764 _91765 P y g f x) (term623 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579383 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term662 _91760 _91764 _91765 P g f x) = (term622 _91760 _91764 _91765 x P g f).
Proof. exact (eq_refl (term662 _91760 _91764 _91765 P g f x)). Qed.
Lemma lem3579384 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term663 _91760 _91764 _91765 P g f) = (term623 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579383 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579385 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579386 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term664 _91760 _91764 _91765 P g f) = (term624 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579385 _91765) (@lem3579384 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579387 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579388 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term660 _91760 _91764 _91765 y x P g f) = (term654 _91760 _91764 _91765 y x P g f).
Proof. exact (MK_COMB (@lem3579387 _91760 _91764 _91765 P y g f x) (@lem3579386 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579390 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term665 _91760 _91764 _91765 y x P g f) = (term666 _91760 _91764 _91765 y x P g f).
Proof. exact (MK_COMB (@lem3579389) (@lem3579388 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579391 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term662 _91760 _91764 _91765 P g f x) = (term622 _91760 _91764 _91765 x P g f).
Proof. exact (eq_refl (term662 _91760 _91764 _91765 P g f x)). Qed.
Lemma lem3579392 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579393 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term667 _91760 _91764 _91765 y x P g f x') = (term668 _91760 _91764 _91765 y x x' P g f).
Proof. exact (MK_COMB (@lem3579392 _91760 _91764 _91765 P y g f x) (@lem3579391 _91760 _91764 _91765 x' P g f)). Qed.
Lemma lem3579394 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term669 _91760 _91764 _91765 y x P g f) = (term670 _91760 _91764 _91765 y x P g f).
Proof. exact (fun_ext (fun x' : _91765 => @lem3579393 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579395 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579396 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term661 _91760 _91764 _91765 y x P g f) = (term671 _91760 _91764 _91765 y x P g f).
Proof. exact (MK_COMB (@lem3579395 _91765) (@lem3579394 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579397 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term660 _91760 _91764 _91765 y x P g f) = (term661 _91760 _91764 _91765 y x P g f)) = ((term654 _91760 _91764 _91765 y x P g f) = (term671 _91760 _91764 _91765 y x P g f)).
Proof. exact (MK_COMB (@lem3579390 _91760 _91764 _91765 y x P g f) (@lem3579396 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579398 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term654 _91760 _91764 _91765 y x P g f) = (term671 _91760 _91764 _91765 y x P g f).
Proof. exact (EQ_MP (@lem3579397 _91760 _91764 _91765 y x P g f) (@lem3579382 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579400 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3579401 {_91765 : Type'} (P : Prop) (Q : _91765 -> Prop) : (term658 _91765 P Q) = (term659 _91765 P Q).
Proof. exact (@lem3579400 _91765 P Q). Qed.
Lemma lem3579402 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term672 _91760 _91764 _91765 y x x' P g f) = (term673 _91760 _91764 _91765 y x x' P g f).
Proof. exact (@lem3579401 _91765 (term529 _91760 _91764 _91765 P y g f x) (term621 _91760 _91764 _91765 x' P g f)). Qed.
Lemma lem3579403 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term674 _91760 _91764 _91765 x P g f y) = (term620 _91760 _91764 _91765 x y P g f).
Proof. exact (eq_refl (term674 _91760 _91764 _91765 x P g f y)). Qed.
Lemma lem3579404 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term675 _91760 _91764 _91765 x P g f) = (term621 _91760 _91764 _91765 x P g f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579403 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579405 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579406 {_91760 _91764 _91765 : Type'} (x : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term676 _91760 _91764 _91765 x P g f) = (term622 _91760 _91764 _91765 x P g f).
Proof. exact (MK_COMB (@lem3579405 _91765) (@lem3579404 _91760 _91764 _91765 x P g f)). Qed.
Lemma lem3579407 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579408 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term672 _91760 _91764 _91765 y x x' P g f) = (term668 _91760 _91764 _91765 y x x' P g f).
Proof. exact (MK_COMB (@lem3579407 _91760 _91764 _91765 P y g f x) (@lem3579406 _91760 _91764 _91765 x' P g f)). Qed.
Lemma lem3579409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579410 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term677 _91760 _91764 _91765 y x x' P g f) = (term678 _91760 _91764 _91765 y x x' P g f).
Proof. exact (MK_COMB (@lem3579409) (@lem3579408 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579411 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term674 _91760 _91764 _91765 x P g f y) = (term620 _91760 _91764 _91765 x y P g f).
Proof. exact (eq_refl (term674 _91760 _91764 _91765 x P g f y)). Qed.
Lemma lem3579412 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579413 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term679 _91760 _91764 _91765 y x x' P g f y') = (term680 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (MK_COMB (@lem3579412 _91760 _91764 _91765 P y g f x) (@lem3579411 _91760 _91764 _91765 x' y' P g f)). Qed.
Lemma lem3579414 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term681 _91760 _91764 _91765 y x x' P g f) = (term682 _91760 _91764 _91765 y x x' P g f).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579413 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579415 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579416 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term673 _91760 _91764 _91765 y x x' P g f) = (term683 _91760 _91764 _91765 y x x' P g f).
Proof. exact (MK_COMB (@lem3579415 _91765) (@lem3579414 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579417 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term672 _91760 _91764 _91765 y x x' P g f) = (term673 _91760 _91764 _91765 y x x' P g f)) = ((term668 _91760 _91764 _91765 y x x' P g f) = (term683 _91760 _91764 _91765 y x x' P g f)).
Proof. exact (MK_COMB (@lem3579410 _91760 _91764 _91765 y x x' P g f) (@lem3579416 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579418 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term668 _91760 _91764 _91765 y x x' P g f) = (term683 _91760 _91764 _91765 y x x' P g f).
Proof. exact (EQ_MP (@lem3579417 _91760 _91764 _91765 y x x' P g f) (@lem3579402 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579420 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3579421 {_91765 : Type'} (P : Prop) (Q : _91765 -> Prop) : (term658 _91765 P Q) = (term659 _91765 P Q).
Proof. exact (@lem3579420 _91765 P Q). Qed.
Lemma lem3579422 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term684 _91760 _91764 _91765 y x x' y' P g f) = (term685 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (@lem3579421 _91765 (term529 _91760 _91764 _91765 P y g f x) (term619 _91760 _91764 _91765 x' y' P g f)). Qed.
Lemma lem3579423 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term686 _91760 _91764 _91765 x y P g f y') = (term618 _91760 _91764 _91765 y' x y P g f).
Proof. exact (eq_refl (term686 _91760 _91764 _91765 x y P g f y')). Qed.
Lemma lem3579424 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term687 _91760 _91764 _91765 x y P g f) = (term619 _91760 _91764 _91765 x y P g f).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579423 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579425 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579426 {_91760 _91764 _91765 : Type'} (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term688 _91760 _91764 _91765 x y P g f) = (term620 _91760 _91764 _91765 x y P g f).
Proof. exact (MK_COMB (@lem3579425 _91765) (@lem3579424 _91760 _91764 _91765 x y P g f)). Qed.
Lemma lem3579427 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579428 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term684 _91760 _91764 _91765 y x x' y' P g f) = (term680 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (MK_COMB (@lem3579427 _91760 _91764 _91765 P y g f x) (@lem3579426 _91760 _91764 _91765 x' y' P g f)). Qed.
Lemma lem3579429 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579430 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term689 _91760 _91764 _91765 y x x' y' P g f) = (term690 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (MK_COMB (@lem3579429) (@lem3579428 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579431 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term686 _91760 _91764 _91765 x y P g f y') = (term618 _91760 _91764 _91765 y' x y P g f).
Proof. exact (eq_refl (term686 _91760 _91764 _91765 x y P g f y')). Qed.
Lemma lem3579432 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579433 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term691 _91760 _91764 _91765 y x x' y'' P g f y') = (term692 _91760 _91764 _91765 y x y' x' y'' P g f).
Proof. exact (MK_COMB (@lem3579432 _91760 _91764 _91765 P y g f x) (@lem3579431 _91760 _91764 _91765 y' x' y'' P g f)). Qed.
Lemma lem3579434 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term693 _91760 _91764 _91765 y x x' y' P g f) = (term694 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (fun_ext (fun y'' : _91765 => @lem3579433 _91760 _91764 _91765 y x y'' x' y' P g f)). Qed.
Lemma lem3579435 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579436 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term685 _91760 _91764 _91765 y x x' y' P g f) = (term695 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (MK_COMB (@lem3579435 _91765) (@lem3579434 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579437 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term684 _91760 _91764 _91765 y x x' y' P g f) = (term685 _91760 _91764 _91765 y x x' y' P g f)) = ((term680 _91760 _91764 _91765 y x x' y' P g f) = (term695 _91760 _91764 _91765 y x x' y' P g f)).
Proof. exact (MK_COMB (@lem3579430 _91760 _91764 _91765 y x x' y' P g f) (@lem3579436 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579438 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term680 _91760 _91764 _91765 y x x' y' P g f) = (term695 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (EQ_MP (@lem3579437 _91760 _91764 _91765 y x x' y' P g f) (@lem3579422 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579440 {A : Type'} (P : Prop) (Q : A -> Prop) : (term658 A P Q) = (term659 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3579441 {_91760 _91764 : Type'} (P : Prop) (Q : type805 _91760 _91764) : (term696 _91760 _91764 P Q) = (term697 _91760 _91764 P Q).
Proof. exact (@lem3579440 (_91764 -> _91760) P Q). Qed.
Lemma lem3579442 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term698 _91760 _91764 _91765 y x y' x' y'' P g f) = (term699 _91760 _91764 _91765 y x y' x' y'' P g f).
Proof. exact (@lem3579441 _91760 _91764 (term529 _91760 _91764 _91765 P y g f x) (term617 _91760 _91764 _91765 y' x' y'' P g f)). Qed.
Lemma lem3579443 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term700 _91760 _91764 _91765 y' x y P g f h) = (term615 _91760 _91764 _91765 y' x y P g f h).
Proof. exact (eq_refl (term700 _91760 _91764 _91765 y' x y P g f h)). Qed.
Lemma lem3579444 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term701 _91760 _91764 _91765 y' x y P g f) = (term617 _91760 _91764 _91765 y' x y P g f).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3579443 _91760 _91764 _91765 y' x y P g f h)). Qed.
Lemma lem3579445 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3579446 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term702 _91760 _91764 _91765 y' x y P g f) = (term618 _91760 _91764 _91765 y' x y P g f).
Proof. exact (MK_COMB (@lem3579445 _91760 _91764) (@lem3579444 _91760 _91764 _91765 y' x y P g f)). Qed.
Lemma lem3579447 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579448 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term698 _91760 _91764 _91765 y x y' x' y'' P g f) = (term692 _91760 _91764 _91765 y x y' x' y'' P g f).
Proof. exact (MK_COMB (@lem3579447 _91760 _91764 _91765 P y g f x) (@lem3579446 _91760 _91764 _91765 y' x' y'' P g f)). Qed.
Lemma lem3579449 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579450 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term703 _91760 _91764 _91765 y x y' x' y'' P g f) = (term704 _91760 _91764 _91765 y x y' x' y'' P g f).
Proof. exact (MK_COMB (@lem3579449) (@lem3579448 _91760 _91764 _91765 y x y' x' y'' P g f)). Qed.
Lemma lem3579451 {_91760 _91764 _91765 : Type'} (y' : _91765) (x : _91765) (y : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term700 _91760 _91764 _91765 y' x y P g f h) = (term615 _91760 _91764 _91765 y' x y P g f h).
Proof. exact (eq_refl (term700 _91760 _91764 _91765 y' x y P g f h)). Qed.
Lemma lem3579452 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (eq_refl (term652 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579453 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term705 _91760 _91764 _91765 y x y' x' y'' P g f h) = (term706 _91760 _91764 _91765 y x y' x' y'' P g f h).
Proof. exact (MK_COMB (@lem3579452 _91760 _91764 _91765 P y g f x) (@lem3579451 _91760 _91764 _91765 y' x' y'' P g f h)). Qed.
Lemma lem3579454 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term707 _91760 _91764 _91765 y x y' x' y'' P g f) = (term708 _91760 _91764 _91765 y x y' x' y'' P g f).
Proof. exact (fun_ext (fun h : _91764 -> _91760 => @lem3579453 _91760 _91764 _91765 y x y' x' y'' P g f h)). Qed.
Lemma lem3579455 {_91760 _91764 : Type'} : (@ex (_91764 -> _91760)) = (@ex (_91764 -> _91760)).
Proof. exact (eq_refl (@ex (_91764 -> _91760))). Qed.
Lemma lem3579456 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term699 _91760 _91764 _91765 y x y' x' y'' P g f) = (term709 _91760 _91764 _91765 y x y' x' y'' P g f).
Proof. exact (MK_COMB (@lem3579455 _91760 _91764) (@lem3579454 _91760 _91764 _91765 y x y' x' y'' P g f)). Qed.
Lemma lem3579457 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : ((term698 _91760 _91764 _91765 y x y' x' y'' P g f) = (term699 _91760 _91764 _91765 y x y' x' y'' P g f)) = ((term692 _91760 _91764 _91765 y x y' x' y'' P g f) = (term709 _91760 _91764 _91765 y x y' x' y'' P g f)).
Proof. exact (MK_COMB (@lem3579450 _91760 _91764 _91765 y x y' x' y'' P g f) (@lem3579456 _91760 _91764 _91765 y x y' x' y'' P g f)). Qed.
Lemma lem3579458 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y' : _91765) (x' : _91765) (y'' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term692 _91760 _91764 _91765 y x y' x' y'' P g f) = (term709 _91760 _91764 _91765 y x y' x' y'' P g f).
Proof. exact (EQ_MP (@lem3579457 _91760 _91764 _91765 y x y' x' y'' P g f) (@lem3579442 _91760 _91764 _91765 y x y' x' y'' P g f)). Qed.
Lemma lem3579459 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term694 _91760 _91764 _91765 y x x' y' P g f) = (term710 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (fun_ext (fun y'' : _91765 => @lem3579458 _91760 _91764 _91765 y x y'' x' y' P g f)). Qed.
Lemma lem3579460 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579461 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term695 _91760 _91764 _91765 y x x' y' P g f) = (term711 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (MK_COMB (@lem3579460 _91765) (@lem3579459 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579462 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term680 _91760 _91764 _91765 y x x' y' P g f) = (term711 _91760 _91764 _91765 y x x' y' P g f).
Proof. exact (TRANS (@lem3579438 _91760 _91764 _91765 y x x' y' P g f) (@lem3579461 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579463 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term682 _91760 _91764 _91765 y x x' P g f) = (term712 _91760 _91764 _91765 y x x' P g f).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579462 _91760 _91764 _91765 y x x' y' P g f)). Qed.
Lemma lem3579464 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579465 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term683 _91760 _91764 _91765 y x x' P g f) = (term713 _91760 _91764 _91765 y x x' P g f).
Proof. exact (MK_COMB (@lem3579464 _91765) (@lem3579463 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579466 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term668 _91760 _91764 _91765 y x x' P g f) = (term713 _91760 _91764 _91765 y x x' P g f).
Proof. exact (TRANS (@lem3579418 _91760 _91764 _91765 y x x' P g f) (@lem3579465 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579467 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term670 _91760 _91764 _91765 y x P g f) = (term714 _91760 _91764 _91765 y x P g f).
Proof. exact (fun_ext (fun x' : _91765 => @lem3579466 _91760 _91764 _91765 y x x' P g f)). Qed.
Lemma lem3579468 {_91765 : Type'} : (@ex _91765) = (@ex _91765).
Proof. exact (eq_refl (@ex _91765)). Qed.
Lemma lem3579469 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term671 _91760 _91764 _91765 y x P g f) = (term715 _91760 _91764 _91765 y x P g f).
Proof. exact (MK_COMB (@lem3579468 _91765) (@lem3579467 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579470 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term654 _91760 _91764 _91765 y x P g f) = (term715 _91760 _91764 _91765 y x P g f).
Proof. exact (TRANS (@lem3579398 _91760 _91764 _91765 y x P g f) (@lem3579469 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579471 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term656 _91760 _91764 _91765 y P g f) = (term716 _91760 _91764 _91765 y P g f).
Proof. exact (fun_ext (fun x : _91760 -> _91765 => @lem3579470 _91760 _91764 _91765 y x P g f)). Qed.
Lemma lem3579472 {_91760 _91765 : Type'} : (@ex (_91760 -> _91765)) = (@ex (_91760 -> _91765)).
Proof. exact (eq_refl (@ex (_91760 -> _91765))). Qed.
Lemma lem3579473 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term657 _91760 _91764 _91765 y P g f) = (term717 _91760 _91764 _91765 y P g f).
Proof. exact (MK_COMB (@lem3579472 _91760 _91765) (@lem3579471 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579474 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term637 _91760 _91764 _91765 y P g f) = (term717 _91760 _91764 _91765 y P g f).
Proof. exact (TRANS (@lem3579378 _91760 _91764 _91765 y P g f) (@lem3579473 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579475 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term639 _91760 _91764 _91765 P g f) = (term718 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun y : _91764 => @lem3579474 _91760 _91764 _91765 y P g f)). Qed.
Lemma lem3579476 {_91764 : Type'} : (@ex _91764) = (@ex _91764).
Proof. exact (eq_refl (@ex _91764)). Qed.
Lemma lem3579477 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term640 _91760 _91764 _91765 P g f) = (term719 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579476 _91764) (@lem3579475 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579478 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term625 _91760 _91764 _91765 P g f) = (term719 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579352 _91760 _91764 _91765 P g f) (@lem3579477 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579479 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term482 _91760 _91764 _91765 P g f) = (term719 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579326 _91760 _91764 _91765 P g f) (@lem3579478 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579480 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term434 _91760 _91764 _91765 P g f) = (term719 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579075 _91760 _91764 _91765 P g f) (@lem3579479 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579481 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term340 _91760 _91764 _91765 P g f) = (term719 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3578636 _91760 _91764 _91765 P g f) (@lem3579480 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579482 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term340 _91760 _91764 _91765 P g f) : term719 _91760 _91764 _91765 P g f.
Proof. exact (EQ_MP (@lem3579481 _91760 _91764 _91765 P g f) (@lem3578479 _91760 _91764 _91765 P g f h1)). Qed.
Lemma lem3579483 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term717 _91760 _91764 _91765 y P g f) : term717 _91760 _91764 _91765 y P g f.
Proof. exact (h1). Qed.
Lemma lem3579484 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term715 _91760 _91764 _91765 y x P g f) : term715 _91760 _91764 _91765 y x P g f.
Proof. exact (h1). Qed.
Lemma lem3579485 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term713 _91760 _91764 _91765 y x x' P g f) : term713 _91760 _91764 _91765 y x x' P g f.
Proof. exact (h1). Qed.
Lemma lem3579486 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term711 _91760 _91764 _91765 y x x' y' P g f) : term711 _91760 _91764 _91765 y x x' y' P g f.
Proof. exact (h1). Qed.
Lemma lem3579487 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term709 _91760 _91764 _91765 y x y'' x' y' P g f) : term709 _91760 _91764 _91765 y x y'' x' y' P g f.
Proof. exact (h1). Qed.
Lemma lem3579488 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term706 _91760 _91764 _91765 y x y'' x' y' P g f h) : term706 _91760 _91764 _91765 y x y'' x' y' P g f h.
Proof. exact (h1). Qed.
Lemma lem3579517 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91764 -> _91760) (y : _91764) : (term720 _91760 _91764 _91765 P g f x h y) = (term720 _91760 _91764 _91765 P g f x h y).
Proof. exact (eq_refl (term720 _91760 _91764 _91765 P g f x h y)). Qed.
Lemma lem3579518 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term721 _91760 _91764 _91765 P g f h y) = (term721 _91760 _91764 _91765 P g f h y).
Proof. exact (fun_ext (fun x : _91765 => @lem3579517 _91760 _91764 _91765 P g f x h y)). Qed.
Lemma lem3579519 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579520 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term551 _91760 _91764 _91765 P g f h y) = (term551 _91760 _91764 _91765 P g f h y).
Proof. exact (MK_COMB (@lem3579519 _91765) (@lem3579518 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3579521 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term553 _91760 _91764 _91765 P g f h) = (term553 _91760 _91764 _91765 P g f h).
Proof. exact (fun_ext (fun y : _91764 => @lem3579520 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3579522 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3579523 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term555 _91760 _91764 _91765 P g f h) = (term555 _91760 _91764 _91765 P g f h).
Proof. exact (MK_COMB (@lem3579522 _91764) (@lem3579521 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579568 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y'' : _91765) (x' : _91765) (f : _91765 -> _91760) (y' : _91765) : (term599 _91760 _91764 _91765 P g y'' x' f y') = (term599 _91760 _91764 _91765 P g y'' x' f y').
Proof. exact (eq_refl (term599 _91760 _91764 _91765 P g y'' x' f y')). Qed.
Lemma lem3579569 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term615 _91760 _91764 _91765 y'' x' y' P g f h) = (term615 _91760 _91764 _91765 y'' x' y' P g f h).
Proof. exact (MK_COMB (@lem3579568 _91760 _91764 _91765 P g y'' x' f y') (@lem3579523 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579600 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h : _91760) : (term496 _91760 _91764 _91765 P y g f x h) = (term496 _91760 _91764 _91765 P y g f x h).
Proof. exact (eq_refl (term496 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579601 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term498 _91760 _91764 _91765 P y g f x) = (term498 _91760 _91764 _91765 P y g f x).
Proof. exact (fun_ext (fun h : _91760 => @lem3579600 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579602 {_91760 : Type'} : (@all _91760) = (@all _91760).
Proof. exact (eq_refl (@all _91760)). Qed.
Lemma lem3579603 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term500 _91760 _91764 _91765 P y g f x) = (term500 _91760 _91764 _91765 P y g f x).
Proof. exact (MK_COMB (@lem3579602 _91760) (@lem3579601 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579612 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3579649 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term351 _91764 _91765 P x g y y') = (term351 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term351 _91764 _91765 P x g y y')). Qed.
Lemma lem3579650 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term439 _91764 _91765 P x g y) = (term439 _91764 _91765 P x g y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579649 _91764 _91765 P x g y y')). Qed.
Lemma lem3579651 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579652 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term448 _91764 _91765 P x g y) = (term448 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3579651 _91765) (@lem3579650 _91764 _91765 P x g y)). Qed.
Lemma lem3579653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579654 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term450 _91764 _91765 P x g y) = (term450 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3579653) (@lem3579652 _91764 _91765 P x g y)). Qed.
Lemma lem3579655 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term451 _91760 _91764 _91765 P g x f y) = (term451 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579654 _91764 _91765 P x g y) (@lem3579612 _91760 _91765 x f y)). Qed.
Lemma lem3579656 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term452 _91760 _91764 _91765 P g x f) = (term452 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579655 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579657 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579658 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term453 _91760 _91764 _91765 P g x f) = (term453 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3579657 _91765) (@lem3579656 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579659 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term454 _91760 _91764 _91765 P g f) = (term454 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579658 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579660 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579661 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term455 _91760 _91764 _91765 P g f) = (term455 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579660 _91765) (@lem3579659 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3579663 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term456 _91760 _91764 _91765 P g f) = (term456 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579662) (@lem3579661 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579664 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term529 _91760 _91764 _91765 P y g f x) = (term529 _91760 _91764 _91765 P y g f x).
Proof. exact (MK_COMB (@lem3579663 _91760 _91764 _91765 P g f) (@lem3579603 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579665 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579666 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term652 _91760 _91764 _91765 P y g f x) = (term652 _91760 _91764 _91765 P y g f x).
Proof. exact (MK_COMB (@lem3579665) (@lem3579664 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579667 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term706 _91760 _91764 _91765 y x y'' x' y' P g f h) = (term706 _91760 _91764 _91765 y x y'' x' y' P g f h).
Proof. exact (MK_COMB (@lem3579666 _91760 _91764 _91765 P y g f x) (@lem3579569 _91760 _91764 _91765 y'' x' y' P g f h)). Qed.
Lemma lem3579668 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term706 _91760 _91764 _91765 y x y'' x' y' P g f h) : term706 _91760 _91764 _91765 y x y'' x' y' P g f h.
Proof. exact (EQ_MP (@lem3579667 _91760 _91764 _91765 y x y'' x' y' P g f h) (@lem3579488 _91760 _91764 _91765 y x y'' x' y' P g f h h1)). Qed.
Lemma lem3579669 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term529 _91760 _91764 _91765 P y g f x.
Proof. exact (h1). Qed.
Lemma lem3579670 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term615 _91760 _91764 _91765 y'' x' y' P g f h.
Proof. exact (h1). Qed.
Lemma lem3579671 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term500 _91760 _91764 _91765 P y g f x.
Proof. exact (proj2 (@lem3579669 _91760 _91764 _91765 P y g f x h1)). Qed.
Lemma lem3579672 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term455 _91760 _91764 _91765 P g f.
Proof. exact (proj1 (@lem3579669 _91760 _91764 _91765 P y g f x h1)). Qed.
Lemma lem3579673 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term555 _91760 _91764 _91765 P g f h.
Proof. exact (proj2 (@lem3579670 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579674 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term354 _91760 _91764 _91765 P g y'' x' f y'.
Proof. exact (proj1 (@lem3579670 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579676 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term264 _91764 _91765 P x' g y' y''.
Proof. exact (proj1 (@lem3579674 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579678 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term246 _91764 _91765 P x' g y''.
Proof. exact (proj1 (@lem3579676 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579679 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term346 _91764 _91765 P x' g y''.
Proof. exact (proj2 (@lem3579678 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579684 {A : Type'} (P : A -> Prop) (Q : Prop) : (term436 A P Q) = (term435 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3579685 {_91765 : Type'} (P : _91765 -> Prop) (Q : Prop) : (term436 _91765 P Q) = (term435 _91765 P Q).
Proof. exact (@lem3579684 _91765 P Q). Qed.
Lemma lem3579686 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term438 _91760 _91764 _91765 P g x f y) = (term437 _91760 _91764 _91765 P g x f y).
Proof. exact (@lem3579685 _91765 (term439 _91764 _91765 P x g y) ((f x) = (f y))). Qed.
Lemma lem3579687 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term440 _91764 _91765 P x g y y') = (term351 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term440 _91764 _91765 P x g y y')). Qed.
Lemma lem3579688 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term446 _91764 _91765 P x g y) = (term439 _91764 _91765 P x g y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579687 _91764 _91765 P x g y y')). Qed.
Lemma lem3579689 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579690 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term447 _91764 _91765 P x g y) = (term448 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3579689 _91765) (@lem3579688 _91764 _91765 P x g y)). Qed.
Lemma lem3579691 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579692 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) : (term449 _91764 _91765 P x g y) = (term450 _91764 _91765 P x g y).
Proof. exact (MK_COMB (@lem3579691) (@lem3579690 _91764 _91765 P x g y)). Qed.
Lemma lem3579693 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3579694 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term438 _91760 _91764 _91765 P g x f y) = (term451 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579692 _91764 _91765 P x g y) (@lem3579693 _91760 _91765 x f y)). Qed.
Lemma lem3579695 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579696 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term722 _91760 _91764 _91765 P g x f y) = (term723 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579695) (@lem3579694 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579697 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term440 _91764 _91765 P x g y y') = (term351 _91764 _91765 P x g y y').
Proof. exact (eq_refl (term440 _91764 _91765 P x g y y')). Qed.
Lemma lem3579698 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3579699 {_91764 _91765 : Type'} (P : _91765 -> Prop) (x : _91765) (g : _91765 -> _91764) (y : _91765) (y' : _91765) : (term441 _91764 _91765 P x g y y') = (term356 _91764 _91765 P x g y y').
Proof. exact (MK_COMB (@lem3579698) (@lem3579697 _91764 _91765 P x g y y')). Qed.
Lemma lem3579700 {_91760 _91765 : Type'} (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem3579701 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term442 _91760 _91764 _91765 P g y' x f y) = (term358 _91760 _91764 _91765 P g y' x f y).
Proof. exact (MK_COMB (@lem3579699 _91764 _91765 P x g y y') (@lem3579700 _91760 _91765 x f y)). Qed.
Lemma lem3579702 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term443 _91760 _91764 _91765 P g x f y) = (term366 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579701 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579703 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579704 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term437 _91760 _91764 _91765 P g x f y) = (term367 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579703 _91765) (@lem3579702 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579705 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : ((term438 _91760 _91764 _91765 P g x f y) = (term437 _91760 _91764 _91765 P g x f y)) = ((term451 _91760 _91764 _91765 P g x f y) = (term367 _91760 _91764 _91765 P g x f y)).
Proof. exact (MK_COMB (@lem3579696 _91760 _91764 _91765 P g x f y) (@lem3579704 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579706 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term451 _91760 _91764 _91765 P g x f y) = (term367 _91760 _91764 _91765 P g x f y).
Proof. exact (EQ_MP (@lem3579705 _91760 _91764 _91765 P g x f y) (@lem3579686 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579707 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term452 _91760 _91764 _91765 P g x f) = (term375 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579706 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579708 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579709 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term453 _91760 _91764 _91765 P g x f) = (term376 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3579708 _91765) (@lem3579707 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579710 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term454 _91760 _91764 _91765 P g f) = (term384 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579709 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579711 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579712 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term455 _91760 _91764 _91765 P g f) = (term385 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579711 _91765) (@lem3579710 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579737 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (y' : _91765) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term358 _91760 _91764 _91765 P g y' x f y) = (term358 _91760 _91764 _91765 P g y' x f y).
Proof. exact (eq_refl (term358 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579738 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term366 _91760 _91764 _91765 P g x f y) = (term366 _91760 _91764 _91765 P g x f y).
Proof. exact (fun_ext (fun y' : _91765 => @lem3579737 _91760 _91764 _91765 P g y' x f y)). Qed.
Lemma lem3579739 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579740 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) (y : _91765) : (term367 _91760 _91764 _91765 P g x f y) = (term367 _91760 _91764 _91765 P g x f y).
Proof. exact (MK_COMB (@lem3579739 _91765) (@lem3579738 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579741 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term375 _91760 _91764 _91765 P g x f) = (term375 _91760 _91764 _91765 P g x f).
Proof. exact (fun_ext (fun y : _91765 => @lem3579740 _91760 _91764 _91765 P g x f y)). Qed.
Lemma lem3579742 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579743 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (x : _91765) (f : _91765 -> _91760) : (term376 _91760 _91764 _91765 P g x f) = (term376 _91760 _91764 _91765 P g x f).
Proof. exact (MK_COMB (@lem3579742 _91765) (@lem3579741 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579744 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term384 _91760 _91764 _91765 P g f) = (term384 _91760 _91764 _91765 P g f).
Proof. exact (fun_ext (fun x : _91765 => @lem3579743 _91760 _91764 _91765 P g x f)). Qed.
Lemma lem3579745 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579746 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term385 _91760 _91764 _91765 P g f) = (term385 _91760 _91764 _91765 P g f).
Proof. exact (MK_COMB (@lem3579745 _91765) (@lem3579744 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579747 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term455 _91760 _91764 _91765 P g f) = (term385 _91760 _91764 _91765 P g f).
Proof. exact (TRANS (@lem3579712 _91760 _91764 _91765 P g f) (@lem3579746 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3579748 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term385 _91760 _91764 _91765 P g f.
Proof. exact (EQ_MP (@lem3579747 _91760 _91764 _91765 P g f) (@lem3579672 _91760 _91764 _91765 P y g f x h1)). Qed.
Lemma lem3579758 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h : _91760) : (term496 _91760 _91764 _91765 P y g f x h) = (term496 _91760 _91764 _91765 P y g f x h).
Proof. exact (eq_refl (term496 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579759 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term498 _91760 _91764 _91765 P y g f x) = (term498 _91760 _91764 _91765 P y g f x).
Proof. exact (fun_ext (fun h : _91760 => @lem3579758 _91760 _91764 _91765 P y g f x h)). Qed.
Lemma lem3579760 {_91760 : Type'} : (@all _91760) = (@all _91760).
Proof. exact (eq_refl (@all _91760)). Qed.
Lemma lem3579762 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) : (term500 _91760 _91764 _91765 P y g f x) = (term500 _91760 _91764 _91765 P y g f x).
Proof. exact (MK_COMB (@lem3579760 _91760) (@lem3579759 _91760 _91764 _91765 P y g f x)). Qed.
Lemma lem3579763 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term500 _91760 _91764 _91765 P y g f x.
Proof. exact (EQ_MP (@lem3579762 _91760 _91764 _91765 P y g f x) (@lem3579671 _91760 _91764 _91765 P y g f x h1)). Qed.
Lemma lem3579777 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91765) (h : _91764 -> _91760) (y : _91764) : (term720 _91760 _91764 _91765 P g f x h y) = (term720 _91760 _91764 _91765 P g f x h y).
Proof. exact (eq_refl (term720 _91760 _91764 _91765 P g f x h y)). Qed.
Lemma lem3579778 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term721 _91760 _91764 _91765 P g f h y) = (term721 _91760 _91764 _91765 P g f h y).
Proof. exact (fun_ext (fun x : _91765 => @lem3579777 _91760 _91764 _91765 P g f x h y)). Qed.
Lemma lem3579779 {_91765 : Type'} : (@all _91765) = (@all _91765).
Proof. exact (eq_refl (@all _91765)). Qed.
Lemma lem3579780 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (y : _91764) : (term551 _91760 _91764 _91765 P g f h y) = (term551 _91760 _91764 _91765 P g f h y).
Proof. exact (MK_COMB (@lem3579779 _91765) (@lem3579778 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3579781 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term553 _91760 _91764 _91765 P g f h) = (term553 _91760 _91764 _91765 P g f h).
Proof. exact (fun_ext (fun y : _91764 => @lem3579780 _91760 _91764 _91765 P g f h y)). Qed.
Lemma lem3579782 {_91764 : Type'} : (@all _91764) = (@all _91764).
Proof. exact (eq_refl (@all _91764)). Qed.
Lemma lem3579784 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) : (term555 _91760 _91764 _91765 P g f h) = (term555 _91760 _91764 _91765 P g f h).
Proof. exact (MK_COMB (@lem3579782 _91764) (@lem3579781 _91760 _91764 _91765 P g f h)). Qed.
Lemma lem3579785 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term555 _91760 _91764 _91765 P g f h.
Proof. exact (EQ_MP (@lem3579784 _91760 _91764 _91765 P g f h) (@lem3579673 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579806 {_91760 _91764 _91765 : Type'} (_38624 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term724 _91760 _91764 _91765 P g f _38624.
Proof. exact (@lem3579748 _91760 _91764 _91765 P y g f x h1 _38624). Qed.
Lemma lem3579807 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38624 : _91765) (f : _91765 -> _91760) : (term724 _91760 _91764 _91765 P g f _38624) = (term376 _91760 _91764 _91765 P g _38624 f).
Proof. exact (eq_refl (term724 _91760 _91764 _91765 P g f _38624)). Qed.
Lemma lem3579808 {_91760 _91764 _91765 : Type'} (_38624 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term376 _91760 _91764 _91765 P g _38624 f.
Proof. exact (EQ_MP (@lem3579807 _91760 _91764 _91765 P g _38624 f) (@lem3579806 _91760 _91764 _91765 _38624 P y g f x h1)). Qed.
Lemma lem3579809 {_91760 _91764 _91765 : Type'} (_38624 : _91765) (_38625 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term725 _91760 _91764 _91765 P g _38624 f _38625.
Proof. exact (@lem3579808 _91760 _91764 _91765 _38624 P y g f x h1 _38625). Qed.
Lemma lem3579810 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term725 _91760 _91764 _91765 P g _38624 f _38625) = (term367 _91760 _91764 _91765 P g _38624 f _38625).
Proof. exact (eq_refl (term725 _91760 _91764 _91765 P g _38624 f _38625)). Qed.
Lemma lem3579811 {_91760 _91764 _91765 : Type'} (_38624 : _91765) (_38625 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term367 _91760 _91764 _91765 P g _38624 f _38625.
Proof. exact (EQ_MP (@lem3579810 _91760 _91764 _91765 P g _38624 f _38625) (@lem3579809 _91760 _91764 _91765 _38624 _38625 P y g f x h1)). Qed.
Lemma lem3579812 {_91760 _91764 _91765 : Type'} (_38624 : _91765) (_38625 : _91765) (_38626 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term726 _91760 _91764 _91765 P g _38624 f _38625 _38626.
Proof. exact (@lem3579811 _91760 _91764 _91765 _38624 _38625 P y g f x h1 _38626). Qed.
Lemma lem3579813 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term726 _91760 _91764 _91765 P g _38624 f _38625 _38626) = (term358 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (eq_refl (term726 _91760 _91764 _91765 P g _38624 f _38625 _38626)). Qed.
Lemma lem3579814 {_91760 _91764 _91765 : Type'} (_38626 : _91765) (_38624 : _91765) (_38625 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term358 _91760 _91764 _91765 P g _38626 _38624 f _38625.
Proof. exact (EQ_MP (@lem3579813 _91760 _91764 _91765 P g _38626 _38624 f _38625) (@lem3579812 _91760 _91764 _91765 _38624 _38625 _38626 P y g f x h1)). Qed.
Lemma lem3579815 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term727 _91760 _91764 _91765 P y g f x _38627.
Proof. exact (@lem3579763 _91760 _91764 _91765 P y g f x h1 _38627). Qed.
Lemma lem3579816 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (_38627 : _91760) : (term727 _91760 _91764 _91765 P y g f x _38627) = (term496 _91760 _91764 _91765 P y g f x _38627).
Proof. exact (eq_refl (term727 _91760 _91764 _91765 P y g f x _38627)). Qed.
Lemma lem3579817 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term496 _91760 _91764 _91765 P y g f x _38627.
Proof. exact (EQ_MP (@lem3579816 _91760 _91764 _91765 P y g f x _38627) (@lem3579815 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3579818 {_91760 _91764 _91765 : Type'} (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term728 _91760 _91764 _91765 P g f h _38628.
Proof. exact (@lem3579785 _91760 _91764 _91765 y'' x' y' P g f h h1 _38628). Qed.
Lemma lem3579819 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (_38628 : _91764) : (term728 _91760 _91764 _91765 P g f h _38628) = (term551 _91760 _91764 _91765 P g f h _38628).
Proof. exact (eq_refl (term728 _91760 _91764 _91765 P g f h _38628)). Qed.
Lemma lem3579820 {_91760 _91764 _91765 : Type'} (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term551 _91760 _91764 _91765 P g f h _38628.
Proof. exact (EQ_MP (@lem3579819 _91760 _91764 _91765 P g f h _38628) (@lem3579818 _91760 _91764 _91765 _38628 y'' x' y' P g f h h1)). Qed.
Lemma lem3579821 {_91760 _91764 _91765 : Type'} (_38628 : _91764) (_38629 : _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term729 _91760 _91764 _91765 P g f h _38628 _38629.
Proof. exact (@lem3579820 _91760 _91764 _91765 _38628 y'' x' y' P g f h h1 _38629). Qed.
Lemma lem3579822 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (_38629 : _91765) (h : _91764 -> _91760) (_38628 : _91764) : (term729 _91760 _91764 _91765 P g f h _38628 _38629) = (term720 _91760 _91764 _91765 P g f _38629 h _38628).
Proof. exact (eq_refl (term729 _91760 _91764 _91765 P g f h _38628 _38629)). Qed.
Lemma lem3579823 {_91760 _91764 _91765 : Type'} (_38629 : _91765) (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term720 _91760 _91764 _91765 P g f _38629 h _38628.
Proof. exact (EQ_MP (@lem3579822 _91760 _91764 _91765 P g f _38629 h _38628) (@lem3579821 _91760 _91764 _91765 _38628 _38629 y'' x' y' P g f h h1)). Qed.
Lemma lem3579825 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term730 _91760 _91764 _91765 P y g x _38627.
Proof. exact (proj1 (@lem3579817 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3579831 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term358 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term731 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (@lem3576810 (term344 _91764 _91765 P _38624 g _38626) (term347 _91765 _38625 _38626) ((f _38624) = (f _38625))). Qed.
Lemma lem3579835 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term731 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term732 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (@lem3576810 (term192 _91765 P _38624) (term342 _91764 _91765 P _38624 g _38626) (term733 _91760 _91765 _38626 _38624 f _38625)). Qed.
Lemma lem3579842 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term734 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term735 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (@lem3576810 (term192 _91765 P _38626) (term462 _91764 _91765 _38624 g _38626) (term733 _91760 _91765 _38626 _38624 f _38625)). Qed.
Lemma lem3579843 {_91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) : (term217 _91765 P _38624) = (term217 _91765 P _38624).
Proof. exact (eq_refl (term217 _91765 P _38624)). Qed.
Lemma lem3579846 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term732 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term736 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (MK_COMB (@lem3579843 _91765 P _38624) (@lem3579842 _91760 _91764 _91765 P g _38626 _38624 f _38625)). Qed.
Lemma lem3579848 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term731 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term736 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (TRANS (@lem3579835 _91760 _91764 _91765 P g _38626 _38624 f _38625) (@lem3579846 _91760 _91764 _91765 P g _38626 _38624 f _38625)). Qed.
Lemma lem3579850 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term358 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term736 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (TRANS (@lem3579831 _91760 _91764 _91765 P g _38626 _38624 f _38625) (@lem3579848 _91760 _91764 _91765 P g _38626 _38624 f _38625)). Qed.
Lemma lem3579851 {_91760 _91764 _91765 : Type'} (_38626 : _91765) (_38624 : _91765) (_38625 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term736 _91760 _91764 _91765 P g _38626 _38624 f _38625.
Proof. exact (EQ_MP (@lem3579850 _91760 _91764 _91765 P g _38626 _38624 f _38625) (@lem3579814 _91760 _91764 _91765 _38626 _38624 _38625 P y g f x h1)). Qed.
Lemma lem3579853 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term737 _91760 _91765 f x _38627.
Proof. exact (proj2 (@lem3579817 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3579868 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (_38629 : _91765) (h : _91764 -> _91760) (_38628 : _91764) : (term720 _91760 _91764 _91765 P g f _38629 h _38628) = (term738 _91760 _91764 _91765 P g f _38629 h _38628).
Proof. exact (@lem3576810 (term192 _91765 P _38629) (term739 _91764 _91765 _38628 g _38629) ((f _38629) = (h _38628))). Qed.
Lemma lem3579871 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term462 _91760 _91765 x' f y'.
Proof. exact (proj2 (@lem3579674 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579873 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : y' = y''.
Proof. exact (proj2 (@lem3579676 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579907 {_91760 _91764 _91765 : Type'} (_38629 : _91765) (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term738 _91760 _91764 _91765 P g f _38629 h _38628.
Proof. exact (EQ_MP (@lem3579868 _91760 _91764 _91765 P g f _38629 h _38628) (@lem3579823 _91760 _91764 _91765 _38629 _38628 y'' x' y' P g f h h1)). Qed.
Lemma lem3579908 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) : (term740 _91760 _91765 x' f) = (term740 _91760 _91765 x' f).
Proof. exact (eq_refl (term740 _91760 _91765 x' f)). Qed.
Lemma lem3579909 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (term741 _91760 _91765 x' f y') = (term741 _91760 _91765 x' f y'').
Proof. exact (MK_COMB (@lem3579908 _91760 _91765 x' f) (@lem3579873 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579910 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : (term741 _91760 _91765 x' f y'') = (term462 _91760 _91765 x' f y'').
Proof. exact (eq_refl (term741 _91760 _91765 x' f y'')). Qed.
Lemma lem3579911 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) (y' : _91765) : (term742 _91760 _91765 x' f y') = (term742 _91760 _91765 x' f y').
Proof. exact (eq_refl (term742 _91760 _91765 x' f y')). Qed.
Lemma lem3579912 {_91760 _91765 : Type'} (y' : _91765) (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : ((term741 _91760 _91765 x' f y') = (term741 _91760 _91765 x' f y'')) = ((term741 _91760 _91765 x' f y') = (term462 _91760 _91765 x' f y'')).
Proof. exact (MK_COMB (@lem3579911 _91760 _91765 x' f y') (@lem3579910 _91760 _91765 x' f y'')). Qed.
Lemma lem3579913 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) (y' : _91765) : (term741 _91760 _91765 x' f y') = (term462 _91760 _91765 x' f y').
Proof. exact (eq_refl (term741 _91760 _91765 x' f y')). Qed.
Lemma lem3579914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3579915 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) (y' : _91765) : (term742 _91760 _91765 x' f y') = (term743 _91760 _91765 x' f y').
Proof. exact (MK_COMB (@lem3579914) (@lem3579913 _91760 _91765 x' f y')). Qed.
Lemma lem3579916 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : (term462 _91760 _91765 x' f y'') = (term462 _91760 _91765 x' f y'').
Proof. exact (eq_refl (term462 _91760 _91765 x' f y'')). Qed.
Lemma lem3579917 {_91760 _91765 : Type'} (y' : _91765) (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : ((term741 _91760 _91765 x' f y') = (term462 _91760 _91765 x' f y'')) = ((term462 _91760 _91765 x' f y') = (term462 _91760 _91765 x' f y'')).
Proof. exact (MK_COMB (@lem3579915 _91760 _91765 x' f y') (@lem3579916 _91760 _91765 x' f y'')). Qed.
Lemma lem3579918 {_91760 _91765 : Type'} (y' : _91765) (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : ((term741 _91760 _91765 x' f y') = (term741 _91760 _91765 x' f y'')) = ((term462 _91760 _91765 x' f y') = (term462 _91760 _91765 x' f y'')).
Proof. exact (TRANS (@lem3579912 _91760 _91765 y' x' f y'') (@lem3579917 _91760 _91765 y' x' f y'')). Qed.
Lemma lem3579919 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (term462 _91760 _91765 x' f y') = (term462 _91760 _91765 x' f y'').
Proof. exact (EQ_MP (@lem3579918 _91760 _91765 y' x' f y'') (@lem3579909 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3579920 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term462 _91760 _91765 x' f y''.
Proof. exact (EQ_MP (@lem3579919 _91760 _91764 _91765 y'' x' y' P g f h h1) (@lem3579871 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580004 {_91764 : Type'} (x : _91764) (y : _91764) (z : _91764) : term744 _91764 x y z.
Proof. exact (@lem21385 _91764 x y z). Qed.
Lemma lem3580006 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term745 _91760 _91765 P x _38627.
Proof. exact (proj1 (@lem3579825 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3580007 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term745 _91760 _91765 P x _38627.
Proof. exact (@lem3580006 _91760 _91764 _91765 _38627 P y g f x h1). Qed.
Lemma lem3580008 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term746 _91760 _91765 P f x _38650.
Proof. exact (@lem3580007 _91760 _91764 _91765 (term747 _91760 _91765 f x _38650) P y g f x h1). Qed.
Lemma lem3580009 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term748 _91760 _91765 P f x _38650.
Proof. exact (fun h0 : term749 _91760 _91765 P f x _38650 => @lem3580008 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580011 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580012 {_91760 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) (x : _91760 -> _91765) (_38650 : _91760) : (term748 _91760 _91765 P f x _38650) = (term746 _91760 _91765 P f x _38650).
Proof. exact (@lem3580011 (term746 _91760 _91765 P f x _38650)). Qed.
Lemma lem3580013 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term746 _91760 _91765 P f x _38650.
Proof. exact (EQ_MP (@lem3580012 _91760 _91765 P f x _38650) (@lem3580009 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580015 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term745 _91760 _91765 P x _38627.
Proof. exact (proj1 (@lem3579825 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3580016 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term745 _91760 _91765 P x _38627.
Proof. exact (@lem3580015 _91760 _91764 _91765 _38627 P y g f x h1). Qed.
Lemma lem3580017 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term745 _91760 _91765 P x _38650.
Proof. exact (@lem3580016 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580018 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term750 _91760 _91765 P x _38650.
Proof. exact (fun h0 : term751 _91760 _91765 P x _38650 => @lem3580017 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580020 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580021 {_91760 _91765 : Type'} (P : _91765 -> Prop) (x : _91760 -> _91765) (_38650 : _91760) : (term750 _91760 _91765 P x _38650) = (term745 _91760 _91765 P x _38650).
Proof. exact (@lem3580020 (term745 _91760 _91765 P x _38650)). Qed.
Lemma lem3580022 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term745 _91760 _91765 P x _38650.
Proof. exact (EQ_MP (@lem3580021 _91760 _91765 P x _38650) (@lem3580018 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580024 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term752 _91760 _91764 _91765 g x _38627).
Proof. exact (proj2 (@lem3579825 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3580025 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term752 _91760 _91764 _91765 g x _38627).
Proof. exact (@lem3580024 _91760 _91764 _91765 _38627 P y g f x h1). Qed.
Lemma lem3580026 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term753 _91760 _91764 _91765 g f x _38650).
Proof. exact (@lem3580025 _91760 _91764 _91765 (term747 _91760 _91765 f x _38650) P y g f x h1). Qed.
Lemma lem3580027 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term754 _91760 _91764 _91765 y g f x _38650.
Proof. exact (fun h0 : term755 _91760 _91764 _91765 y g f x _38650 => @lem3580026 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580029 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580030 {_91760 _91764 _91765 : Type'} (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (_38650 : _91760) : (term754 _91760 _91764 _91765 y g f x _38650) = (y = (term753 _91760 _91764 _91765 g f x _38650)).
Proof. exact (@lem3580029 (y = (term753 _91760 _91764 _91765 g f x _38650))). Qed.
Lemma lem3580031 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term753 _91760 _91764 _91765 g f x _38650).
Proof. exact (EQ_MP (@lem3580030 _91760 _91764 _91765 y g f x _38650) (@lem3580027 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580033 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term752 _91760 _91764 _91765 g x _38627).
Proof. exact (proj2 (@lem3579825 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3580034 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term752 _91760 _91764 _91765 g x _38627).
Proof. exact (@lem3580033 _91760 _91764 _91765 _38627 P y g f x h1). Qed.
Lemma lem3580035 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term752 _91760 _91764 _91765 g x _38650).
Proof. exact (@lem3580034 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580036 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term756 _91760 _91764 _91765 y g x _38650.
Proof. exact (fun h0 : term757 _91760 _91764 _91765 y g x _38650 => @lem3580035 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580038 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580039 {_91760 _91764 _91765 : Type'} (y : _91764) (g : _91765 -> _91764) (x : _91760 -> _91765) (_38650 : _91760) : (term756 _91760 _91764 _91765 y g x _38650) = (y = (term752 _91760 _91764 _91765 g x _38650)).
Proof. exact (@lem3580038 (y = (term752 _91760 _91764 _91765 g x _38650))). Qed.
Lemma lem3580040 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : y = (term752 _91760 _91764 _91765 g x _38650).
Proof. exact (EQ_MP (@lem3580039 _91760 _91764 _91765 y g x _38650) (@lem3580036 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580058 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3580059 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term758 _91764 x y z) = (term759 _91764 y x z).
Proof. exact (@lem3580058 (y = z) (term347 _91764 x z)). Qed.
Lemma lem3580069 {_91764 : Type'} (x : _91764) (y : _91764) : (term760 _91764 x y) = (term760 _91764 x y).
Proof. exact (eq_refl (term760 _91764 x y)). Qed.
Lemma lem3580070 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term744 _91764 x y z) = (term761 _91764 y x z).
Proof. exact (MK_COMB (@lem3580069 _91764 x y) (@lem3580059 _91764 y x z)). Qed.
Lemma lem3580074 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3580075 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term761 _91764 y x z) = (term762 _91764 y x z).
Proof. exact (@lem3580074 (y = z) (term347 _91764 x y) (term347 _91764 x z)). Qed.
Lemma lem3580097 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term744 _91764 x y z) = (term762 _91764 y x z).
Proof. exact (TRANS (@lem3580070 _91764 y x z) (@lem3580075 _91764 y x z)). Qed.
Lemma lem3580098 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3580099 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term763 _91764 x y z) = (term764 _91764 y x z).
Proof. exact (MK_COMB (@lem3580098) (@lem3580097 _91764 y x z)). Qed.
Lemma lem3580121 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term762 _91764 y x z) = (term762 _91764 y x z).
Proof. exact (eq_refl (term762 _91764 y x z)). Qed.
Lemma lem3580122 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : ((term744 _91764 x y z) = (term762 _91764 y x z)) = ((term762 _91764 y x z) = (term762 _91764 y x z)).
Proof. exact (MK_COMB (@lem3580099 _91764 y x z) (@lem3580121 _91764 y x z)). Qed.
Lemma lem3580124 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3580125 (x : Prop) : (x = x) = True.
Proof. exact (@lem3580124 Prop x). Qed.
Lemma lem3580126 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : ((term762 _91764 y x z) = (term762 _91764 y x z)) = True.
Proof. exact (@lem3580125 (term762 _91764 y x z)). Qed.
Lemma lem3580127 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : ((term744 _91764 x y z) = (term762 _91764 y x z)) = True.
Proof. exact (TRANS (@lem3580122 _91764 y x z) (@lem3580126 _91764 y x z)). Qed.
Lemma lem3580128 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : True = ((term744 _91764 x y z) = (term762 _91764 y x z)).
Proof. exact (SYM (@lem3580127 _91764 y x z)). Qed.
Lemma lem3580129 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term744 _91764 x y z) = (term762 _91764 y x z).
Proof. exact (EQ_MP (@lem3580128 _91764 y x z) (@lem0)). Qed.
Lemma lem3580130 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : term762 _91764 y x z.
Proof. exact (EQ_MP (@lem3580129 _91764 y x z) (@lem3580004 _91764 x y z)). Qed.
Lemma lem3580132 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3580133 {_91764 : Type'} (x : _91764) (y : _91764) (z : _91764) : (term762 _91764 y x z) = (term765 _91764 x y z).
Proof. exact (@lem3580132 (term766 _91764 y x z) (y = z)). Qed.
Lemma lem3580135 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3580136 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term767 _91764 y x z) = (term768 _91764 y x z).
Proof. exact (@lem3580135 (term347 _91764 x y) (term347 _91764 x z)). Qed.
Lemma lem3580138 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580139 {_91764 : Type'} (x : _91764) (y : _91764) : (term769 _91764 x y) = (x = y).
Proof. exact (@lem3580138 (x = y)). Qed.
Lemma lem3580140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580141 {_91764 : Type'} (x : _91764) (y : _91764) : (term770 _91764 x y) = (term771 _91764 x y).
Proof. exact (MK_COMB (@lem3580140) (@lem3580139 _91764 x y)). Qed.
Lemma lem3580143 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580144 {_91764 : Type'} (x : _91764) (z : _91764) : (term769 _91764 x z) = (x = z).
Proof. exact (@lem3580143 (x = z)). Qed.
Lemma lem3580145 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term768 _91764 y x z) = (term772 _91764 y x z).
Proof. exact (MK_COMB (@lem3580141 _91764 x y) (@lem3580144 _91764 x z)). Qed.
Lemma lem3580146 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term767 _91764 y x z) = (term772 _91764 y x z).
Proof. exact (TRANS (@lem3580136 _91764 y x z) (@lem3580145 _91764 y x z)). Qed.
Lemma lem3580147 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3580148 {_91764 : Type'} (y : _91764) (x : _91764) (z : _91764) : (term773 _91764 y x z) = (term774 _91764 y x z).
Proof. exact (MK_COMB (@lem3580147) (@lem3580146 _91764 y x z)). Qed.
Lemma lem3580149 {_91764 : Type'} (y : _91764) (z : _91764) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3580150 {_91764 : Type'} (x : _91764) (y : _91764) (z : _91764) : (term765 _91764 x y z) = (term775 _91764 x y z).
Proof. exact (MK_COMB (@lem3580148 _91764 y x z) (@lem3580149 _91764 y z)). Qed.
Lemma lem3580151 {_91764 : Type'} (x : _91764) (y : _91764) (z : _91764) : (term762 _91764 y x z) = (term775 _91764 x y z).
Proof. exact (TRANS (@lem3580133 _91764 x y z) (@lem3580150 _91764 x y z)). Qed.
Lemma lem3580153 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term776 _91760 _91764 _91765 f y g x _38650.
Proof. exact (conj (@lem3580031 _91760 _91764 _91765 _38650 P y g f x h1) (@lem3580040 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580155 {_91764 : Type'} (x : _91764) (y : _91764) (z : _91764) : term775 _91764 x y z.
Proof. exact (EQ_MP (@lem3580151 _91764 x y z) (@lem3580130 _91764 y x z)). Qed.
Lemma lem3580156 {_91764 : Type'} (x : _91764) (y : _91764) (z : _91764) : term775 _91764 x y z.
Proof. exact (@lem3580155 _91764 x y z). Qed.
Lemma lem3580157 {_91760 _91764 _91765 : Type'} (y : _91764) (f : _91765 -> _91760) (g : _91765 -> _91764) (x : _91760 -> _91765) (_38650 : _91760) : term777 _91760 _91764 _91765 y f g x _38650.
Proof. exact (@lem3580156 _91764 y (term753 _91760 _91764 _91765 g f x _38650) (term752 _91760 _91764 _91765 g x _38650)). Qed.
Lemma lem3580160 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : (term753 _91760 _91764 _91765 g f x _38650) = (term752 _91760 _91764 _91765 g x _38650).
Proof. exact (@lem3580157 _91760 _91764 _91765 y f g x _38650 (@lem3580153 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580161 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : (term753 _91760 _91764 _91765 g f x _38650) = (term752 _91760 _91764 _91765 g x _38650).
Proof. exact (@lem3580160 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580162 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term778 _91760 _91764 _91765 f g x _38650.
Proof. exact (fun h0 : term779 _91760 _91764 _91765 f g x _38650 => @lem3580161 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580164 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580165 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (g : _91765 -> _91764) (x : _91760 -> _91765) (_38650 : _91760) : (term778 _91760 _91764 _91765 f g x _38650) = ((term753 _91760 _91764 _91765 g f x _38650) = (term752 _91760 _91764 _91765 g x _38650)).
Proof. exact (@lem3580164 ((term753 _91760 _91764 _91765 g f x _38650) = (term752 _91760 _91764 _91765 g x _38650))). Qed.
Lemma lem3580166 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : (term753 _91760 _91764 _91765 g f x _38650) = (term752 _91760 _91764 _91765 g x _38650).
Proof. exact (EQ_MP (@lem3580165 _91760 _91764 _91765 f g x _38650) (@lem3580162 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580168 {_91765 : Type'} (x : _91765) : x = x.
Proof. exact (@lem21386 _91765 x). Qed.
Lemma lem3580169 {_91765 : Type'} (x : _91765) : x = x.
Proof. exact (@lem3580168 _91765 x). Qed.
Lemma lem3580170 {_91760 _91765 : Type'} (x : _91760 -> _91765) (_38650 : _91760) : (x _38650) = (x _38650).
Proof. exact (@lem3580169 _91765 (x _38650)). Qed.
Lemma lem3580171 {_91760 _91765 : Type'} (x : _91760 -> _91765) (_38650 : _91760) : term213 _91760 _91765 x _38650.
Proof. exact (fun h0 : term214 _91760 _91765 x _38650 => @lem3580170 _91760 _91765 x _38650). Qed.
Lemma lem3580173 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580174 {_91760 _91765 : Type'} (x : _91760 -> _91765) (_38650 : _91760) : (term213 _91760 _91765 x _38650) = ((x _38650) = (x _38650)).
Proof. exact (@lem3580173 ((x _38650) = (x _38650))). Qed.
Lemma lem3580175 {_91760 _91765 : Type'} (x : _91760 -> _91765) (_38650 : _91760) : (x _38650) = (x _38650).
Proof. exact (EQ_MP (@lem3580174 _91760 _91765 x _38650) (@lem3580171 _91760 _91765 x _38650)). Qed.
Lemma lem3580213 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3580214 {_91760 _91765 : Type'} (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) (_38626 : _91765) : (term733 _91760 _91765 _38626 _38624 f _38625) = (term780 _91760 _91765 _38624 f _38625 _38626).
Proof. exact (@lem3580213 ((f _38624) = (f _38625)) (term347 _91765 _38625 _38626)). Qed.
Lemma lem3580224 {_91764 _91765 : Type'} (_38624 : _91765) (g : _91765 -> _91764) (_38626 : _91765) : (term781 _91764 _91765 _38624 g _38626) = (term781 _91764 _91765 _38624 g _38626).
Proof. exact (eq_refl (term781 _91764 _91765 _38624 g _38626)). Qed.
Lemma lem3580225 {_91760 _91764 _91765 : Type'} (g : _91765 -> _91764) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) (_38626 : _91765) : (term782 _91760 _91764 _91765 g _38626 _38624 f _38625) = (term783 _91760 _91764 _91765 g _38624 f _38625 _38626).
Proof. exact (MK_COMB (@lem3580224 _91764 _91765 _38624 g _38626) (@lem3580214 _91760 _91765 _38624 f _38625 _38626)). Qed.
Lemma lem3580229 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3580230 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term783 _91760 _91764 _91765 g _38624 f _38625 _38626) = (term784 _91760 _91764 _91765 f _38624 g _38625 _38626).
Proof. exact (@lem3580229 ((f _38624) = (f _38625)) (term462 _91764 _91765 _38624 g _38626) (term347 _91765 _38625 _38626)). Qed.
Lemma lem3580252 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term782 _91760 _91764 _91765 g _38626 _38624 f _38625) = (term784 _91760 _91764 _91765 f _38624 g _38625 _38626).
Proof. exact (TRANS (@lem3580225 _91760 _91764 _91765 g _38624 f _38625 _38626) (@lem3580230 _91760 _91764 _91765 f _38624 g _38625 _38626)). Qed.
Lemma lem3580253 {_91765 : Type'} (P : _91765 -> Prop) (_38626 : _91765) : (term217 _91765 P _38626) = (term217 _91765 P _38626).
Proof. exact (eq_refl (term217 _91765 P _38626)). Qed.
Lemma lem3580254 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term735 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term785 _91760 _91764 _91765 P f _38624 g _38625 _38626).
Proof. exact (MK_COMB (@lem3580253 _91765 P _38626) (@lem3580252 _91760 _91764 _91765 f _38624 g _38625 _38626)). Qed.
Lemma lem3580258 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3580259 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term785 _91760 _91764 _91765 P f _38624 g _38625 _38626) = (term786 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (@lem3580258 ((f _38624) = (f _38625)) (term192 _91765 P _38626) (term787 _91764 _91765 _38624 g _38625 _38626)). Qed.
Lemma lem3580291 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term735 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term786 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (TRANS (@lem3580254 _91760 _91764 _91765 P f _38624 g _38625 _38626) (@lem3580259 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580292 {_91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) : (term217 _91765 P _38624) = (term217 _91765 P _38624).
Proof. exact (eq_refl (term217 _91765 P _38624)). Qed.
Lemma lem3580293 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term736 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term788 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (MK_COMB (@lem3580292 _91765 P _38624) (@lem3580291 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580297 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3580298 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term788 _91760 _91764 _91765 f P _38624 g _38625 _38626) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (@lem3580297 ((f _38624) = (f _38625)) (term192 _91765 P _38624) (term790 _91764 _91765 P _38624 g _38625 _38626)). Qed.
Lemma lem3580340 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term736 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (TRANS (@lem3580293 _91760 _91764 _91765 f P _38624 g _38625 _38626) (@lem3580298 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3580342 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term791 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term792 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (MK_COMB (@lem3580341) (@lem3580340 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580384 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (eq_refl (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580385 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : ((term736 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626)) = ((term789 _91760 _91764 _91765 f P _38624 g _38625 _38626) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626)).
Proof. exact (MK_COMB (@lem3580342 _91760 _91764 _91765 f P _38624 g _38625 _38626) (@lem3580384 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580387 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3580388 (x : Prop) : (x = x) = True.
Proof. exact (@lem3580387 Prop x). Qed.
Lemma lem3580389 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : ((term789 _91760 _91764 _91765 f P _38624 g _38625 _38626) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626)) = True.
Proof. exact (@lem3580388 (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580390 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : ((term736 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626)) = True.
Proof. exact (TRANS (@lem3580385 _91760 _91764 _91765 f P _38624 g _38625 _38626) (@lem3580389 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580391 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : True = ((term736 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626)).
Proof. exact (SYM (@lem3580390 _91760 _91764 _91765 f P _38624 g _38625 _38626)). Qed.
Lemma lem3580392 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term736 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626).
Proof. exact (EQ_MP (@lem3580391 _91760 _91764 _91765 f P _38624 g _38625 _38626) (@lem0)). Qed.
Lemma lem3580393 {_91760 _91764 _91765 : Type'} (_38624 : _91765) (_38625 : _91765) (_38626 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term789 _91760 _91764 _91765 f P _38624 g _38625 _38626.
Proof. exact (EQ_MP (@lem3580392 _91760 _91764 _91765 f P _38624 g _38625 _38626) (@lem3579851 _91760 _91764 _91765 _38626 _38624 _38625 P y g f x h1)). Qed.
Lemma lem3580395 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3580396 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626) = (term793 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (@lem3580395 (term794 _91764 _91765 P _38624 g _38625 _38626) ((f _38624) = (f _38625))). Qed.
Lemma lem3580398 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3580399 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term795 _91764 _91765 P _38624 g _38625 _38626) = (term796 _91764 _91765 P _38624 g _38625 _38626).
Proof. exact (@lem3580398 (term192 _91765 P _38624) (term790 _91764 _91765 P _38624 g _38625 _38626)). Qed.
Lemma lem3580401 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580402 {_91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) : (term207 _91765 P _38624) = (P _38624).
Proof. exact (@lem3580401 (P _38624)). Qed.
Lemma lem3580403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580404 {_91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) : (term227 _91765 P _38624) = (term228 _91765 P _38624).
Proof. exact (MK_COMB (@lem3580403) (@lem3580402 _91765 P _38624)). Qed.
Lemma lem3580406 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3580407 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term797 _91764 _91765 P _38624 g _38625 _38626) = (term798 _91764 _91765 P _38624 g _38625 _38626).
Proof. exact (@lem3580406 (term192 _91765 P _38626) (term787 _91764 _91765 _38624 g _38625 _38626)). Qed.
Lemma lem3580409 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580410 {_91765 : Type'} (P : _91765 -> Prop) (_38626 : _91765) : (term207 _91765 P _38626) = (P _38626).
Proof. exact (@lem3580409 (P _38626)). Qed.
Lemma lem3580411 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580412 {_91765 : Type'} (P : _91765 -> Prop) (_38626 : _91765) : (term227 _91765 P _38626) = (term228 _91765 P _38626).
Proof. exact (MK_COMB (@lem3580411) (@lem3580410 _91765 P _38626)). Qed.
Lemma lem3580414 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3580415 {_91764 _91765 : Type'} (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term799 _91764 _91765 _38624 g _38625 _38626) = (term800 _91764 _91765 _38624 g _38625 _38626).
Proof. exact (@lem3580414 (term462 _91764 _91765 _38624 g _38626) (term347 _91765 _38625 _38626)). Qed.
Lemma lem3580417 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580418 {_91764 _91765 : Type'} (_38624 : _91765) (g : _91765 -> _91764) (_38626 : _91765) : (term801 _91764 _91765 _38624 g _38626) = ((g _38624) = (g _38626)).
Proof. exact (@lem3580417 ((g _38624) = (g _38626))). Qed.
Lemma lem3580419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580420 {_91764 _91765 : Type'} (_38624 : _91765) (g : _91765 -> _91764) (_38626 : _91765) : (term802 _91764 _91765 _38624 g _38626) = (term803 _91764 _91765 _38624 g _38626).
Proof. exact (MK_COMB (@lem3580419) (@lem3580418 _91764 _91765 _38624 g _38626)). Qed.
Lemma lem3580422 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580423 {_91765 : Type'} (_38625 : _91765) (_38626 : _91765) : (term769 _91765 _38625 _38626) = (_38625 = _38626).
Proof. exact (@lem3580422 (_38625 = _38626)). Qed.
Lemma lem3580424 {_91764 _91765 : Type'} (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term800 _91764 _91765 _38624 g _38625 _38626) = (term804 _91764 _91765 _38624 g _38625 _38626).
Proof. exact (MK_COMB (@lem3580420 _91764 _91765 _38624 g _38626) (@lem3580423 _91765 _38625 _38626)). Qed.
Lemma lem3580425 {_91764 _91765 : Type'} (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term799 _91764 _91765 _38624 g _38625 _38626) = (term804 _91764 _91765 _38624 g _38625 _38626).
Proof. exact (TRANS (@lem3580415 _91764 _91765 _38624 g _38625 _38626) (@lem3580424 _91764 _91765 _38624 g _38625 _38626)). Qed.
Lemma lem3580426 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term798 _91764 _91765 P _38624 g _38625 _38626) = (term805 _91764 _91765 P _38624 g _38625 _38626).
Proof. exact (MK_COMB (@lem3580412 _91765 P _38626) (@lem3580425 _91764 _91765 _38624 g _38625 _38626)). Qed.
Lemma lem3580427 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term797 _91764 _91765 P _38624 g _38625 _38626) = (term805 _91764 _91765 P _38624 g _38625 _38626).
Proof. exact (TRANS (@lem3580407 _91764 _91765 P _38624 g _38625 _38626) (@lem3580426 _91764 _91765 P _38624 g _38625 _38626)). Qed.
Lemma lem3580428 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term796 _91764 _91765 P _38624 g _38625 _38626) = (term806 _91764 _91765 P _38624 g _38625 _38626).
Proof. exact (MK_COMB (@lem3580404 _91765 P _38624) (@lem3580427 _91764 _91765 P _38624 g _38625 _38626)). Qed.
Lemma lem3580429 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term795 _91764 _91765 P _38624 g _38625 _38626) = (term806 _91764 _91765 P _38624 g _38625 _38626).
Proof. exact (TRANS (@lem3580399 _91764 _91765 P _38624 g _38625 _38626) (@lem3580428 _91764 _91765 P _38624 g _38625 _38626)). Qed.
Lemma lem3580430 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3580431 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38624 : _91765) (g : _91765 -> _91764) (_38625 : _91765) (_38626 : _91765) : (term807 _91764 _91765 P _38624 g _38625 _38626) = (term808 _91764 _91765 P _38624 g _38625 _38626).
Proof. exact (MK_COMB (@lem3580430) (@lem3580429 _91764 _91765 P _38624 g _38625 _38626)). Qed.
Lemma lem3580432 {_91760 _91765 : Type'} (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : ((f _38624) = (f _38625)) = ((f _38624) = (f _38625)).
Proof. exact (eq_refl ((f _38624) = (f _38625))). Qed.
Lemma lem3580433 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term793 _91760 _91764 _91765 P g _38626 _38624 f _38625) = (term809 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (MK_COMB (@lem3580431 _91764 _91765 P _38624 g _38625 _38626) (@lem3580432 _91760 _91765 _38624 f _38625)). Qed.
Lemma lem3580434 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (_38626 : _91765) (_38624 : _91765) (f : _91765 -> _91760) (_38625 : _91765) : (term789 _91760 _91764 _91765 f P _38624 g _38625 _38626) = (term809 _91760 _91764 _91765 P g _38626 _38624 f _38625).
Proof. exact (TRANS (@lem3580396 _91760 _91764 _91765 P g _38626 _38624 f _38625) (@lem3580433 _91760 _91764 _91765 P g _38626 _38624 f _38625)). Qed.
Lemma lem3580436 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term810 _91760 _91764 _91765 f g x _38650.
Proof. exact (conj (@lem3580166 _91760 _91764 _91765 _38650 P y g f x h1) (@lem3580175 _91760 _91765 x _38650)). Qed.
Lemma lem3580437 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term811 _91760 _91764 _91765 P f g x _38650.
Proof. exact (conj (@lem3580022 _91760 _91764 _91765 _38650 P y g f x h1) (@lem3580436 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580438 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term812 _91760 _91764 _91765 P f g x _38650.
Proof. exact (conj (@lem3580013 _91760 _91764 _91765 _38650 P y g f x h1) (@lem3580437 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580440 {_91760 _91764 _91765 : Type'} (_38626 : _91765) (_38624 : _91765) (_38625 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term809 _91760 _91764 _91765 P g _38626 _38624 f _38625.
Proof. exact (EQ_MP (@lem3580434 _91760 _91764 _91765 P g _38626 _38624 f _38625) (@lem3580393 _91760 _91764 _91765 _38624 _38625 _38626 P y g f x h1)). Qed.
Lemma lem3580441 {_91760 _91764 _91765 : Type'} (_38626 : _91765) (_38624 : _91765) (_38625 : _91765) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term809 _91760 _91764 _91765 P g _38626 _38624 f _38625.
Proof. exact (@lem3580440 _91760 _91764 _91765 _38626 _38624 _38625 P y g f x h1). Qed.
Lemma lem3580442 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term813 _91760 _91764 _91765 P g f x _38650.
Proof. exact (@lem3580441 _91760 _91764 _91765 (x _38650) (term814 _91760 _91765 f x _38650) (x _38650) P y g f x h1). Qed.
Lemma lem3580445 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : (term815 _91760 _91765 f x _38650) = (term747 _91760 _91765 f x _38650).
Proof. exact (@lem3580442 _91760 _91764 _91765 _38650 P y g f x h1 (@lem3580438 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580446 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : (term815 _91760 _91765 f x _38650) = (term747 _91760 _91765 f x _38650).
Proof. exact (@lem3580445 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580447 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term816 _91760 _91765 f x _38650.
Proof. exact (fun h0 : term817 _91760 _91765 f x _38650 => @lem3580446 _91760 _91764 _91765 _38650 P y g f x h1). Qed.
Lemma lem3580449 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580450 {_91760 _91765 : Type'} (f : _91765 -> _91760) (x : _91760 -> _91765) (_38650 : _91760) : (term816 _91760 _91765 f x _38650) = ((term815 _91760 _91765 f x _38650) = (term747 _91760 _91765 f x _38650)).
Proof. exact (@lem3580449 ((term815 _91760 _91765 f x _38650) = (term747 _91760 _91765 f x _38650))). Qed.
Lemma lem3580451 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : (term815 _91760 _91765 f x _38650) = (term747 _91760 _91765 f x _38650).
Proof. exact (EQ_MP (@lem3580450 _91760 _91765 f x _38650) (@lem3580447 _91760 _91764 _91765 _38650 P y g f x h1)). Qed.
Lemma lem3580454 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3580456 {_91760 _91765 : Type'} (f : _91765 -> _91760) (x : _91760 -> _91765) (_38627 : _91760) : (term737 _91760 _91765 f x _38627) = (term818 _91760 _91765 f x _38627).
Proof. exact (@lem3580454 ((term747 _91760 _91765 f x _38627) = _38627)). Qed.
Lemma lem3580459 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term818 _91760 _91765 f x _38627.
Proof. exact (EQ_MP (@lem3580456 _91760 _91765 f x _38627) (@lem3579853 _91760 _91764 _91765 _38627 P y g f x h1)). Qed.
Lemma lem3580460 {_91760 _91764 _91765 : Type'} (_38627 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term818 _91760 _91765 f x _38627.
Proof. exact (@lem3580459 _91760 _91764 _91765 _38627 P y g f x h1). Qed.
Lemma lem3580461 {_91760 _91764 _91765 : Type'} (_38650 : _91760) (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term819 _91760 _91765 f x _38650.
Proof. exact (@lem3580460 _91760 _91764 _91765 (term747 _91760 _91765 f x _38650) P y g f x h1). Qed.
Lemma lem3580464 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : False.
Proof. exact (@lem3580461 _91760 _91764 _91765 (@el _91760) P y g f x h1 (@lem3580451 _91760 _91764 _91765 (@el _91760) P y g f x h1)). Qed.
Lemma lem3580465 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : term212.
Proof. exact (fun h0 : ~ False => @lem3580464 _91760 _91764 _91765 P y g f x h1). Qed.
Lemma lem3580467 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580468 : term212 = False.
Proof. exact (@lem3580467 False). Qed.
Lemma lem3580469 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (y : _91764) (g : _91765 -> _91764) (f : _91765 -> _91760) (x : _91760 -> _91765) (h1 : term529 _91760 _91764 _91765 P y g f x) : False.
Proof. exact (EQ_MP (@lem3580468) (@lem3580465 _91760 _91764 _91765 P y g f x h1)). Qed.
Lemma lem3580507 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : term744 _91760 x y z.
Proof. exact (@lem21385 _91760 x y z). Qed.
Lemma lem3580513 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : P x'.
Proof. exact (proj1 (@lem3579678 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580514 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term200 _91765 P x'.
Proof. exact (fun h0 : term192 _91765 P x' => @lem3580513 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580516 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580517 {_91765 : Type'} (P : _91765 -> Prop) (x' : _91765) : (term200 _91765 P x') = (P x').
Proof. exact (@lem3580516 (P x')). Qed.
Lemma lem3580518 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : P x'.
Proof. exact (EQ_MP (@lem3580517 _91765 P x') (@lem3580514 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580520 {_91764 : Type'} (x : _91764) : x = x.
Proof. exact (@lem21386 _91764 x). Qed.
Lemma lem3580521 {_91764 : Type'} (x : _91764) : x = x.
Proof. exact (@lem3580520 _91764 x). Qed.
Lemma lem3580522 {_91764 _91765 : Type'} (g : _91765 -> _91764) (x' : _91765) : (g x') = (g x').
Proof. exact (@lem3580521 _91764 (g x')). Qed.
Lemma lem3580523 {_91764 _91765 : Type'} (g : _91765 -> _91764) (x' : _91765) : term820 _91764 _91765 g x'.
Proof. exact (fun h0 : term821 _91764 _91765 g x' => @lem3580522 _91764 _91765 g x'). Qed.
Lemma lem3580525 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580526 {_91764 _91765 : Type'} (g : _91765 -> _91764) (x' : _91765) : (term820 _91764 _91765 g x') = ((g x') = (g x')).
Proof. exact (@lem3580525 ((g x') = (g x'))). Qed.
Lemma lem3580527 {_91764 _91765 : Type'} (g : _91765 -> _91764) (x' : _91765) : (g x') = (g x').
Proof. exact (EQ_MP (@lem3580526 _91764 _91765 g x') (@lem3580523 _91764 _91765 g x')). Qed.
Lemma lem3580543 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3580544 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term822 _91760 _91764 _91765 g f _38629 h _38628) = (term823 _91760 _91764 _91765 f h _38628 g _38629).
Proof. exact (@lem3580543 ((f _38629) = (h _38628)) (term739 _91764 _91765 _38628 g _38629)). Qed.
Lemma lem3580554 {_91765 : Type'} (P : _91765 -> Prop) (_38629 : _91765) : (term217 _91765 P _38629) = (term217 _91765 P _38629).
Proof. exact (eq_refl (term217 _91765 P _38629)). Qed.
Lemma lem3580555 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) (h : _91764 -> _91760) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term738 _91760 _91764 _91765 P g f _38629 h _38628) = (term824 _91760 _91764 _91765 P f h _38628 g _38629).
Proof. exact (MK_COMB (@lem3580554 _91765 P _38629) (@lem3580544 _91760 _91764 _91765 f h _38628 g _38629)). Qed.
Lemma lem3580559 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3580560 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term824 _91760 _91764 _91765 P f h _38628 g _38629) = (term825 _91760 _91764 _91765 f h P _38628 g _38629).
Proof. exact (@lem3580559 ((f _38629) = (h _38628)) (term192 _91765 P _38629) (term739 _91764 _91765 _38628 g _38629)). Qed.
Lemma lem3580580 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term738 _91760 _91764 _91765 P g f _38629 h _38628) = (term825 _91760 _91764 _91765 f h P _38628 g _38629).
Proof. exact (TRANS (@lem3580555 _91760 _91764 _91765 P f h _38628 g _38629) (@lem3580560 _91760 _91764 _91765 f h P _38628 g _38629)). Qed.
Lemma lem3580581 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3580582 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term826 _91760 _91764 _91765 P g f _38629 h _38628) = (term827 _91760 _91764 _91765 f h P _38628 g _38629).
Proof. exact (MK_COMB (@lem3580581) (@lem3580580 _91760 _91764 _91765 f h P _38628 g _38629)). Qed.
Lemma lem3580602 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term825 _91760 _91764 _91765 f h P _38628 g _38629) = (term825 _91760 _91764 _91765 f h P _38628 g _38629).
Proof. exact (eq_refl (term825 _91760 _91764 _91765 f h P _38628 g _38629)). Qed.
Lemma lem3580603 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : ((term738 _91760 _91764 _91765 P g f _38629 h _38628) = (term825 _91760 _91764 _91765 f h P _38628 g _38629)) = ((term825 _91760 _91764 _91765 f h P _38628 g _38629) = (term825 _91760 _91764 _91765 f h P _38628 g _38629)).
Proof. exact (MK_COMB (@lem3580582 _91760 _91764 _91765 f h P _38628 g _38629) (@lem3580602 _91760 _91764 _91765 f h P _38628 g _38629)). Qed.
Lemma lem3580605 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3580606 (x : Prop) : (x = x) = True.
Proof. exact (@lem3580605 Prop x). Qed.
Lemma lem3580607 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : ((term825 _91760 _91764 _91765 f h P _38628 g _38629) = (term825 _91760 _91764 _91765 f h P _38628 g _38629)) = True.
Proof. exact (@lem3580606 (term825 _91760 _91764 _91765 f h P _38628 g _38629)). Qed.
Lemma lem3580608 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : ((term738 _91760 _91764 _91765 P g f _38629 h _38628) = (term825 _91760 _91764 _91765 f h P _38628 g _38629)) = True.
Proof. exact (TRANS (@lem3580603 _91760 _91764 _91765 f h P _38628 g _38629) (@lem3580607 _91760 _91764 _91765 f h P _38628 g _38629)). Qed.
Lemma lem3580609 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : True = ((term738 _91760 _91764 _91765 P g f _38629 h _38628) = (term825 _91760 _91764 _91765 f h P _38628 g _38629)).
Proof. exact (SYM (@lem3580608 _91760 _91764 _91765 f h P _38628 g _38629)). Qed.
Lemma lem3580610 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term738 _91760 _91764 _91765 P g f _38629 h _38628) = (term825 _91760 _91764 _91765 f h P _38628 g _38629).
Proof. exact (EQ_MP (@lem3580609 _91760 _91764 _91765 f h P _38628 g _38629) (@lem0)). Qed.
Lemma lem3580611 {_91760 _91764 _91765 : Type'} (_38628 : _91764) (_38629 : _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term825 _91760 _91764 _91765 f h P _38628 g _38629.
Proof. exact (EQ_MP (@lem3580610 _91760 _91764 _91765 f h P _38628 g _38629) (@lem3579907 _91760 _91764 _91765 _38629 _38628 y'' x' y' P g f h h1)). Qed.
Lemma lem3580613 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3580614 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (_38629 : _91765) (h : _91764 -> _91760) (_38628 : _91764) : (term825 _91760 _91764 _91765 f h P _38628 g _38629) = (term828 _91760 _91764 _91765 P g f _38629 h _38628).
Proof. exact (@lem3580613 (term387 _91764 _91765 P _38628 g _38629) ((f _38629) = (h _38628))). Qed.
Lemma lem3580616 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3580617 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term829 _91764 _91765 P _38628 g _38629) = (term830 _91764 _91765 P _38628 g _38629).
Proof. exact (@lem3580616 (term192 _91765 P _38629) (term739 _91764 _91765 _38628 g _38629)). Qed.
Lemma lem3580619 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580620 {_91765 : Type'} (P : _91765 -> Prop) (_38629 : _91765) : (term207 _91765 P _38629) = (P _38629).
Proof. exact (@lem3580619 (P _38629)). Qed.
Lemma lem3580621 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580622 {_91765 : Type'} (P : _91765 -> Prop) (_38629 : _91765) : (term227 _91765 P _38629) = (term228 _91765 P _38629).
Proof. exact (MK_COMB (@lem3580621) (@lem3580620 _91765 P _38629)). Qed.
Lemma lem3580624 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580625 {_91764 _91765 : Type'} (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term831 _91764 _91765 _38628 g _38629) = (_38628 = (g _38629)).
Proof. exact (@lem3580624 (_38628 = (g _38629))). Qed.
Lemma lem3580626 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term830 _91764 _91765 P _38628 g _38629) = (term390 _91764 _91765 P _38628 g _38629).
Proof. exact (MK_COMB (@lem3580622 _91765 P _38629) (@lem3580625 _91764 _91765 _38628 g _38629)). Qed.
Lemma lem3580627 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term829 _91764 _91765 P _38628 g _38629) = (term390 _91764 _91765 P _38628 g _38629).
Proof. exact (TRANS (@lem3580617 _91764 _91765 P _38628 g _38629) (@lem3580626 _91764 _91765 P _38628 g _38629)). Qed.
Lemma lem3580628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3580629 {_91764 _91765 : Type'} (P : _91765 -> Prop) (_38628 : _91764) (g : _91765 -> _91764) (_38629 : _91765) : (term832 _91764 _91765 P _38628 g _38629) = (term833 _91764 _91765 P _38628 g _38629).
Proof. exact (MK_COMB (@lem3580628) (@lem3580627 _91764 _91765 P _38628 g _38629)). Qed.
Lemma lem3580630 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (_38629 : _91765) (h : _91764 -> _91760) (_38628 : _91764) : ((f _38629) = (h _38628)) = ((f _38629) = (h _38628)).
Proof. exact (eq_refl ((f _38629) = (h _38628))). Qed.
Lemma lem3580631 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (_38629 : _91765) (h : _91764 -> _91760) (_38628 : _91764) : (term828 _91760 _91764 _91765 P g f _38629 h _38628) = (term834 _91760 _91764 _91765 P g f _38629 h _38628).
Proof. exact (MK_COMB (@lem3580629 _91764 _91765 P _38628 g _38629) (@lem3580630 _91760 _91764 _91765 f _38629 h _38628)). Qed.
Lemma lem3580632 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (_38629 : _91765) (h : _91764 -> _91760) (_38628 : _91764) : (term825 _91760 _91764 _91765 f h P _38628 g _38629) = (term834 _91760 _91764 _91765 P g f _38629 h _38628).
Proof. exact (TRANS (@lem3580614 _91760 _91764 _91765 P g f _38629 h _38628) (@lem3580631 _91760 _91764 _91765 P g f _38629 h _38628)). Qed.
Lemma lem3580634 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term835 _91764 _91765 P g x'.
Proof. exact (conj (@lem3580518 _91760 _91764 _91765 y'' x' y' P g f h h1) (@lem3580527 _91764 _91765 g x')). Qed.
Lemma lem3580636 {_91760 _91764 _91765 : Type'} (_38629 : _91765) (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term834 _91760 _91764 _91765 P g f _38629 h _38628.
Proof. exact (EQ_MP (@lem3580632 _91760 _91764 _91765 P g f _38629 h _38628) (@lem3580611 _91760 _91764 _91765 _38628 _38629 y'' x' y' P g f h h1)). Qed.
Lemma lem3580637 {_91760 _91764 _91765 : Type'} (_38629 : _91765) (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term834 _91760 _91764 _91765 P g f _38629 h _38628.
Proof. exact (@lem3580636 _91760 _91764 _91765 _38629 _38628 y'' x' y' P g f h h1). Qed.
Lemma lem3580638 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term836 _91760 _91764 _91765 P f h g x'.
Proof. exact (@lem3580637 _91760 _91764 _91765 x' (g x') y'' x' y' P g f h h1). Qed.
Lemma lem3580641 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (f x') = (term837 _91760 _91764 _91765 h g x').
Proof. exact (@lem3580638 _91760 _91764 _91765 y'' x' y' P g f h h1 (@lem3580634 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580642 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term838 _91760 _91764 _91765 f h g x'.
Proof. exact (fun h0 : term839 _91760 _91764 _91765 f h g x' => @lem3580641 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580644 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580645 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (h : _91764 -> _91760) (g : _91765 -> _91764) (x' : _91765) : (term838 _91760 _91764 _91765 f h g x') = ((f x') = (term837 _91760 _91764 _91765 h g x')).
Proof. exact (@lem3580644 ((f x') = (term837 _91760 _91764 _91765 h g x'))). Qed.
Lemma lem3580646 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (f x') = (term837 _91760 _91764 _91765 h g x').
Proof. exact (EQ_MP (@lem3580645 _91760 _91764 _91765 f h g x') (@lem3580642 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580648 {_91760 : Type'} (x : _91760) : x = x.
Proof. exact (@lem21386 _91760 x). Qed.
Lemma lem3580649 {_91760 : Type'} (x : _91760) : x = x.
Proof. exact (@lem3580648 _91760 x). Qed.
Lemma lem3580650 {_91760 _91765 : Type'} (f : _91765 -> _91760) (x' : _91765) : (f x') = (f x').
Proof. exact (@lem3580649 _91760 (f x')). Qed.
Lemma lem3580651 {_91760 _91765 : Type'} (f : _91765 -> _91760) (x' : _91765) : term820 _91760 _91765 f x'.
Proof. exact (fun h0 : term821 _91760 _91765 f x' => @lem3580650 _91760 _91765 f x'). Qed.
Lemma lem3580653 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580654 {_91760 _91765 : Type'} (f : _91765 -> _91760) (x' : _91765) : (term820 _91760 _91765 f x') = ((f x') = (f x')).
Proof. exact (@lem3580653 ((f x') = (f x'))). Qed.
Lemma lem3580655 {_91760 _91765 : Type'} (f : _91765 -> _91760) (x' : _91765) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3580654 _91760 _91765 f x') (@lem3580651 _91760 _91765 f x')). Qed.
Lemma lem3580673 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3580674 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term758 _91760 x y z) = (term759 _91760 y x z).
Proof. exact (@lem3580673 (y = z) (term347 _91760 x z)). Qed.
Lemma lem3580684 {_91760 : Type'} (x : _91760) (y : _91760) : (term760 _91760 x y) = (term760 _91760 x y).
Proof. exact (eq_refl (term760 _91760 x y)). Qed.
Lemma lem3580685 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term744 _91760 x y z) = (term761 _91760 y x z).
Proof. exact (MK_COMB (@lem3580684 _91760 x y) (@lem3580674 _91760 y x z)). Qed.
Lemma lem3580689 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3580690 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term761 _91760 y x z) = (term762 _91760 y x z).
Proof. exact (@lem3580689 (y = z) (term347 _91760 x y) (term347 _91760 x z)). Qed.
Lemma lem3580712 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term744 _91760 x y z) = (term762 _91760 y x z).
Proof. exact (TRANS (@lem3580685 _91760 y x z) (@lem3580690 _91760 y x z)). Qed.
Lemma lem3580713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3580714 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term763 _91760 x y z) = (term764 _91760 y x z).
Proof. exact (MK_COMB (@lem3580713) (@lem3580712 _91760 y x z)). Qed.
Lemma lem3580736 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term762 _91760 y x z) = (term762 _91760 y x z).
Proof. exact (eq_refl (term762 _91760 y x z)). Qed.
Lemma lem3580737 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : ((term744 _91760 x y z) = (term762 _91760 y x z)) = ((term762 _91760 y x z) = (term762 _91760 y x z)).
Proof. exact (MK_COMB (@lem3580714 _91760 y x z) (@lem3580736 _91760 y x z)). Qed.
Lemma lem3580739 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3580740 (x : Prop) : (x = x) = True.
Proof. exact (@lem3580739 Prop x). Qed.
Lemma lem3580741 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : ((term762 _91760 y x z) = (term762 _91760 y x z)) = True.
Proof. exact (@lem3580740 (term762 _91760 y x z)). Qed.
Lemma lem3580742 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : ((term744 _91760 x y z) = (term762 _91760 y x z)) = True.
Proof. exact (TRANS (@lem3580737 _91760 y x z) (@lem3580741 _91760 y x z)). Qed.
Lemma lem3580743 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : True = ((term744 _91760 x y z) = (term762 _91760 y x z)).
Proof. exact (SYM (@lem3580742 _91760 y x z)). Qed.
Lemma lem3580744 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term744 _91760 x y z) = (term762 _91760 y x z).
Proof. exact (EQ_MP (@lem3580743 _91760 y x z) (@lem0)). Qed.
Lemma lem3580745 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : term762 _91760 y x z.
Proof. exact (EQ_MP (@lem3580744 _91760 y x z) (@lem3580507 _91760 x y z)). Qed.
Lemma lem3580747 (b : Prop) (a : Prop) : (a \/ b) = (term205 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3580748 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : (term762 _91760 y x z) = (term765 _91760 x y z).
Proof. exact (@lem3580747 (term766 _91760 y x z) (y = z)). Qed.
Lemma lem3580750 (a : Prop) (b : Prop) : (term223 a b) = (term224 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3580751 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term767 _91760 y x z) = (term768 _91760 y x z).
Proof. exact (@lem3580750 (term347 _91760 x y) (term347 _91760 x z)). Qed.
Lemma lem3580753 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580754 {_91760 : Type'} (x : _91760) (y : _91760) : (term769 _91760 x y) = (x = y).
Proof. exact (@lem3580753 (x = y)). Qed.
Lemma lem3580755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3580756 {_91760 : Type'} (x : _91760) (y : _91760) : (term770 _91760 x y) = (term771 _91760 x y).
Proof. exact (MK_COMB (@lem3580755) (@lem3580754 _91760 x y)). Qed.
Lemma lem3580758 (a : Prop) : (term23 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3580759 {_91760 : Type'} (x : _91760) (z : _91760) : (term769 _91760 x z) = (x = z).
Proof. exact (@lem3580758 (x = z)). Qed.
Lemma lem3580760 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term768 _91760 y x z) = (term772 _91760 y x z).
Proof. exact (MK_COMB (@lem3580756 _91760 x y) (@lem3580759 _91760 x z)). Qed.
Lemma lem3580761 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term767 _91760 y x z) = (term772 _91760 y x z).
Proof. exact (TRANS (@lem3580751 _91760 y x z) (@lem3580760 _91760 y x z)). Qed.
Lemma lem3580762 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3580763 {_91760 : Type'} (y : _91760) (x : _91760) (z : _91760) : (term773 _91760 y x z) = (term774 _91760 y x z).
Proof. exact (MK_COMB (@lem3580762) (@lem3580761 _91760 y x z)). Qed.
Lemma lem3580764 {_91760 : Type'} (y : _91760) (z : _91760) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3580765 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : (term765 _91760 x y z) = (term775 _91760 x y z).
Proof. exact (MK_COMB (@lem3580763 _91760 y x z) (@lem3580764 _91760 y z)). Qed.
Lemma lem3580766 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : (term762 _91760 y x z) = (term775 _91760 x y z).
Proof. exact (TRANS (@lem3580748 _91760 x y z) (@lem3580765 _91760 x y z)). Qed.
Lemma lem3580768 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term840 _91760 _91764 _91765 h g f x'.
Proof. exact (conj (@lem3580646 _91760 _91764 _91765 y'' x' y' P g f h h1) (@lem3580655 _91760 _91765 f x')). Qed.
Lemma lem3580770 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : term775 _91760 x y z.
Proof. exact (EQ_MP (@lem3580766 _91760 x y z) (@lem3580745 _91760 y x z)). Qed.
Lemma lem3580771 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : term775 _91760 x y z.
Proof. exact (@lem3580770 _91760 x y z). Qed.
Lemma lem3580772 {_91760 _91764 _91765 : Type'} (h : _91764 -> _91760) (g : _91765 -> _91764) (f : _91765 -> _91760) (x' : _91765) : term841 _91760 _91764 _91765 h g f x'.
Proof. exact (@lem3580771 _91760 (f x') (term837 _91760 _91764 _91765 h g x') (f x')). Qed.
Lemma lem3580775 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (term837 _91760 _91764 _91765 h g x') = (f x').
Proof. exact (@lem3580772 _91760 _91764 _91765 h g f x' (@lem3580768 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580776 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term842 _91760 _91764 _91765 h g f x'.
Proof. exact (fun h0 : term843 _91760 _91764 _91765 h g f x' => @lem3580775 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580778 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580779 {_91760 _91764 _91765 : Type'} (h : _91764 -> _91760) (g : _91765 -> _91764) (f : _91765 -> _91760) (x' : _91765) : (term842 _91760 _91764 _91765 h g f x') = ((term837 _91760 _91764 _91765 h g x') = (f x')).
Proof. exact (@lem3580778 ((term837 _91760 _91764 _91765 h g x') = (f x'))). Qed.
Lemma lem3580780 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (term837 _91760 _91764 _91765 h g x') = (f x').
Proof. exact (EQ_MP (@lem3580779 _91760 _91764 _91765 h g f x') (@lem3580776 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580782 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : P y''.
Proof. exact (proj1 (@lem3579679 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580783 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term200 _91765 P y''.
Proof. exact (fun h0 : term192 _91765 P y'' => @lem3580782 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580785 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580786 {_91765 : Type'} (P : _91765 -> Prop) (y'' : _91765) : (term200 _91765 P y'') = (P y'').
Proof. exact (@lem3580785 (P y'')). Qed.
Lemma lem3580787 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : P y''.
Proof. exact (EQ_MP (@lem3580786 _91765 P y'') (@lem3580783 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580789 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (g x') = (g y'').
Proof. exact (proj2 (@lem3579679 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580790 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term844 _91764 _91765 x' g y''.
Proof. exact (fun h0 : term462 _91764 _91765 x' g y'' => @lem3580789 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580792 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580793 {_91764 _91765 : Type'} (x' : _91765) (g : _91765 -> _91764) (y'' : _91765) : (term844 _91764 _91765 x' g y'') = ((g x') = (g y'')).
Proof. exact (@lem3580792 ((g x') = (g y''))). Qed.
Lemma lem3580794 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (g x') = (g y'').
Proof. exact (EQ_MP (@lem3580793 _91764 _91765 x' g y'') (@lem3580790 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580795 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term346 _91764 _91765 P x' g y''.
Proof. exact (conj (@lem3580787 _91760 _91764 _91765 y'' x' y' P g f h h1) (@lem3580794 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580797 {_91760 _91764 _91765 : Type'} (_38629 : _91765) (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term834 _91760 _91764 _91765 P g f _38629 h _38628.
Proof. exact (EQ_MP (@lem3580632 _91760 _91764 _91765 P g f _38629 h _38628) (@lem3580611 _91760 _91764 _91765 _38628 _38629 y'' x' y' P g f h h1)). Qed.
Lemma lem3580798 {_91760 _91764 _91765 : Type'} (_38629 : _91765) (_38628 : _91764) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term834 _91760 _91764 _91765 P g f _38629 h _38628.
Proof. exact (@lem3580797 _91760 _91764 _91765 _38629 _38628 y'' x' y' P g f h h1). Qed.
Lemma lem3580799 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term845 _91760 _91764 _91765 P f y'' h g x'.
Proof. exact (@lem3580798 _91760 _91764 _91765 y'' (g x') y'' x' y' P g f h h1). Qed.
Lemma lem3580802 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (f y'') = (term837 _91760 _91764 _91765 h g x').
Proof. exact (@lem3580799 _91760 _91764 _91765 y'' x' y' P g f h h1 (@lem3580795 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580803 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term846 _91760 _91764 _91765 f y'' h g x'.
Proof. exact (fun h0 : term847 _91760 _91764 _91765 f y'' h g x' => @lem3580802 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580805 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580806 {_91760 _91764 _91765 : Type'} (f : _91765 -> _91760) (y'' : _91765) (h : _91764 -> _91760) (g : _91765 -> _91764) (x' : _91765) : (term846 _91760 _91764 _91765 f y'' h g x') = ((f y'') = (term837 _91760 _91764 _91765 h g x')).
Proof. exact (@lem3580805 ((f y'') = (term837 _91760 _91764 _91765 h g x'))). Qed.
Lemma lem3580807 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (f y'') = (term837 _91760 _91764 _91765 h g x').
Proof. exact (EQ_MP (@lem3580806 _91760 _91764 _91765 f y'' h g x') (@lem3580803 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580809 {_91760 : Type'} (x : _91760) : x = x.
Proof. exact (@lem21386 _91760 x). Qed.
Lemma lem3580810 {_91760 : Type'} (x : _91760) : x = x.
Proof. exact (@lem3580809 _91760 x). Qed.
Lemma lem3580811 {_91760 _91765 : Type'} (f : _91765 -> _91760) (y'' : _91765) : (f y'') = (f y'').
Proof. exact (@lem3580810 _91760 (f y'')). Qed.
Lemma lem3580812 {_91760 _91765 : Type'} (f : _91765 -> _91760) (y'' : _91765) : term820 _91760 _91765 f y''.
Proof. exact (fun h0 : term821 _91760 _91765 f y'' => @lem3580811 _91760 _91765 f y''). Qed.
Lemma lem3580814 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580815 {_91760 _91765 : Type'} (f : _91765 -> _91760) (y'' : _91765) : (term820 _91760 _91765 f y'') = ((f y'') = (f y'')).
Proof. exact (@lem3580814 ((f y'') = (f y''))). Qed.
Lemma lem3580816 {_91760 _91765 : Type'} (f : _91765 -> _91760) (y'' : _91765) : (f y'') = (f y'').
Proof. exact (EQ_MP (@lem3580815 _91760 _91765 f y'') (@lem3580812 _91760 _91765 f y'')). Qed.
Lemma lem3580817 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term848 _91760 _91764 _91765 h g x' f y''.
Proof. exact (conj (@lem3580807 _91760 _91764 _91765 y'' x' y' P g f h h1) (@lem3580816 _91760 _91765 f y'')). Qed.
Lemma lem3580819 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : term775 _91760 x y z.
Proof. exact (EQ_MP (@lem3580766 _91760 x y z) (@lem3580745 _91760 y x z)). Qed.
Lemma lem3580820 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : term775 _91760 x y z.
Proof. exact (@lem3580819 _91760 x y z). Qed.
Lemma lem3580821 {_91760 _91764 _91765 : Type'} (h : _91764 -> _91760) (g : _91765 -> _91764) (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : term849 _91760 _91764 _91765 h g x' f y''.
Proof. exact (@lem3580820 _91760 (f y'') (term837 _91760 _91764 _91765 h g x') (f y'')). Qed.
Lemma lem3580824 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (term837 _91760 _91764 _91765 h g x') = (f y'').
Proof. exact (@lem3580821 _91760 _91764 _91765 h g x' f y'' (@lem3580817 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580825 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term850 _91760 _91764 _91765 h g x' f y''.
Proof. exact (fun h0 : term851 _91760 _91764 _91765 h g x' f y'' => @lem3580824 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580827 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580828 {_91760 _91764 _91765 : Type'} (h : _91764 -> _91760) (g : _91765 -> _91764) (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : (term850 _91760 _91764 _91765 h g x' f y'') = ((term837 _91760 _91764 _91765 h g x') = (f y'')).
Proof. exact (@lem3580827 ((term837 _91760 _91764 _91765 h g x') = (f y''))). Qed.
Lemma lem3580829 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (term837 _91760 _91764 _91765 h g x') = (f y'').
Proof. exact (EQ_MP (@lem3580828 _91760 _91764 _91765 h g x' f y'') (@lem3580825 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580830 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term852 _91760 _91764 _91765 h g x' f y''.
Proof. exact (conj (@lem3580780 _91760 _91764 _91765 y'' x' y' P g f h h1) (@lem3580829 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580832 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : term775 _91760 x y z.
Proof. exact (EQ_MP (@lem3580766 _91760 x y z) (@lem3580745 _91760 y x z)). Qed.
Lemma lem3580833 {_91760 : Type'} (x : _91760) (y : _91760) (z : _91760) : term775 _91760 x y z.
Proof. exact (@lem3580832 _91760 x y z). Qed.
Lemma lem3580834 {_91760 _91764 _91765 : Type'} (h : _91764 -> _91760) (g : _91765 -> _91764) (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : term853 _91760 _91764 _91765 h g x' f y''.
Proof. exact (@lem3580833 _91760 (term837 _91760 _91764 _91765 h g x') (f x') (f y'')). Qed.
Lemma lem3580837 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (f x') = (f y'').
Proof. exact (@lem3580834 _91760 _91764 _91765 h g x' f y'' (@lem3580830 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580838 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term844 _91760 _91765 x' f y''.
Proof. exact (fun h0 : term462 _91760 _91765 x' f y'' => @lem3580837 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580840 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580841 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : (term844 _91760 _91765 x' f y'') = ((f x') = (f y'')).
Proof. exact (@lem3580840 ((f x') = (f y''))). Qed.
Lemma lem3580842 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : (f x') = (f y'').
Proof. exact (EQ_MP (@lem3580841 _91760 _91765 x' f y'') (@lem3580838 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580845 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3580847 {_91760 _91765 : Type'} (x' : _91765) (f : _91765 -> _91760) (y'' : _91765) : (term462 _91760 _91765 x' f y'') = (term854 _91760 _91765 x' f y'').
Proof. exact (@lem3580845 ((f x') = (f y''))). Qed.
Lemma lem3580850 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term854 _91760 _91765 x' f y''.
Proof. exact (EQ_MP (@lem3580847 _91760 _91765 x' f y'') (@lem3579920 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580853 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : False.
Proof. exact (@lem3580850 _91760 _91764 _91765 y'' x' y' P g f h h1 (@lem3580842 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580854 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : term212.
Proof. exact (fun h0 : ~ False => @lem3580853 _91760 _91764 _91765 y'' x' y' P g f h h1). Qed.
Lemma lem3580856 (p : Prop) : (term201 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3580857 : term212 = False.
Proof. exact (@lem3580856 False). Qed.
Lemma lem3580859 {_91760 _91764 _91765 : Type'} (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term615 _91760 _91764 _91765 y'' x' y' P g f h) : False.
Proof. exact (EQ_MP (@lem3580857) (@lem3580854 _91760 _91764 _91765 y'' x' y' P g f h h1)). Qed.
Lemma lem3580860 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term706 _91760 _91764 _91765 y x y'' x' y' P g f h) : False.
Proof. exact (or_elim (@lem3579668 _91760 _91764 _91765 y x y'' x' y' P g f h h1) (fun h0 : term529 _91760 _91764 _91765 P y g f x => @lem3580469 _91760 _91764 _91765 P y g f x h0) (fun h0 : term615 _91760 _91764 _91765 y'' x' y' P g f h => @lem3580859 _91760 _91764 _91765 y'' x' y' P g f h h0)). Qed.
Lemma lem3580861 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term706 _91760 _91764 _91765 y x y'' x' y' P g f h) : (term706 _91760 _91764 _91765 y x y'' x' y' P g f h) = False.
Proof. exact (prop_ext (fun h2 : term706 _91760 _91764 _91765 y x y'' x' y' P g f h => @lem3580860 _91760 _91764 _91765 y x y'' x' y' P g f h h1) (fun h2 : False => @lem3579668 _91760 _91764 _91765 y x y'' x' y' P g f h h1)). Qed.
Lemma lem3580862 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h : _91764 -> _91760) (h1 : term706 _91760 _91764 _91765 y x y'' x' y' P g f h) : False.
Proof. exact (EQ_MP (@lem3580861 _91760 _91764 _91765 y x y'' x' y' P g f h h1) (@lem3579668 _91760 _91764 _91765 y x y'' x' y' P g f h h1)). Qed.
Lemma lem3580863 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (y'' : _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term709 _91760 _91764 _91765 y x y'' x' y' P g f) : False.
Proof. exact (ex_elim (@lem3579487 _91760 _91764 _91765 y x y'' x' y' P g f h1) (fun h : _91764 -> _91760 => fun h0 : term708 _91760 _91764 _91765 y x y'' x' y' P g f h => @lem3580862 _91760 _91764 _91765 y x y'' x' y' P g f h h0)). Qed.
Lemma lem3580864 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (y' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term711 _91760 _91764 _91765 y x x' y' P g f) : False.
Proof. exact (ex_elim (@lem3579486 _91760 _91764 _91765 y x x' y' P g f h1) (fun y'' : _91765 => fun h0 : term710 _91760 _91764 _91765 y x x' y' P g f y'' => @lem3580863 _91760 _91764 _91765 y x y'' x' y' P g f h0)). Qed.
Lemma lem3580865 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (x' : _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term713 _91760 _91764 _91765 y x x' P g f) : False.
Proof. exact (ex_elim (@lem3579485 _91760 _91764 _91765 y x x' P g f h1) (fun y' : _91765 => fun h0 : term712 _91760 _91764 _91765 y x x' P g f y' => @lem3580864 _91760 _91764 _91765 y x x' y' P g f h0)). Qed.
Lemma lem3580866 {_91760 _91764 _91765 : Type'} (y : _91764) (x : _91760 -> _91765) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term715 _91760 _91764 _91765 y x P g f) : False.
Proof. exact (ex_elim (@lem3579484 _91760 _91764 _91765 y x P g f h1) (fun x' : _91765 => fun h0 : term714 _91760 _91764 _91765 y x P g f x' => @lem3580865 _91760 _91764 _91765 y x x' P g f h0)). Qed.
Lemma lem3580867 {_91760 _91764 _91765 : Type'} (y : _91764) (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term717 _91760 _91764 _91765 y P g f) : False.
Proof. exact (ex_elim (@lem3579483 _91760 _91764 _91765 y P g f h1) (fun x : _91760 -> _91765 => fun h0 : term716 _91760 _91764 _91765 y P g f x => @lem3580866 _91760 _91764 _91765 y x P g f h0)). Qed.
Lemma lem3580868 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term340 _91760 _91764 _91765 P g f) : False.
Proof. exact (ex_elim (@lem3579482 _91760 _91764 _91765 P g f h1) (fun y : _91764 => fun h0 : term718 _91760 _91764 _91765 P g f y => @lem3580867 _91760 _91764 _91765 y P g f h0)). Qed.
Lemma lem3580869 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term340 _91760 _91764 _91765 P g f) : (term340 _91760 _91764 _91765 P g f) = False.
Proof. exact (prop_ext (fun h2 : term340 _91760 _91764 _91765 P g f => @lem3580868 _91760 _91764 _91765 P g f h1) (fun h2 : False => @lem3578479 _91760 _91764 _91765 P g f h1)). Qed.
Lemma lem3580870 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) (h1 : term340 _91760 _91764 _91765 P g f) : False.
Proof. exact (EQ_MP (@lem3580869 _91760 _91764 _91765 P g f h1) (@lem3578479 _91760 _91764 _91765 P g f h1)). Qed.
Lemma lem3580871 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : term339 _91760 _91764 _91765 P g f.
Proof. exact (fun h0 : term340 _91760 _91764 _91765 P g f => @lem3580870 _91760 _91764 _91765 P g f h0). Qed.
Lemma lem3580872 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (g : _91765 -> _91764) (f : _91765 -> _91760) : (term279 _91760 _91764 _91765 P g f) = (term324 _91760 _91764 _91765 P g f).
Proof. exact (EQ_MP (@lem3578478 _91760 _91764 _91765 P g f) (@lem3580871 _91760 _91764 _91765 P g f)). Qed.
Lemma lem3580877 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) (f : _91765 -> _91760) : term326 _91760 _91764 _91765 P f.
Proof. exact (fun g : _91765 -> _91764 => @lem3580872 _91760 _91764 _91765 P g f). Qed.
Lemma lem3580882 {_91760 _91764 _91765 : Type'} (P : _91765 -> Prop) : term328 _91760 _91764 _91765 P.
Proof. exact (fun f : _91765 -> _91760 => @lem3580877 _91760 _91764 _91765 P f). Qed.
Lemma lem3580887 {_91760 _91764 _91765 : Type'} : term330 _91760 _91764 _91765.
Proof. exact (fun P : _91765 -> Prop => @lem3580882 _91760 _91764 _91765 P). Qed.
Lemma lem3580888 {_91760 _91764 _91765 : Type'} : term331 _91760 _91764 _91765.
Proof. exact (EQ_MP (@lem3578474 _91760 _91764 _91765) (@lem3580887 _91760 _91764 _91765)). Qed.
Lemma lem3580890 {_91760 _91764 _91765 : Type'} : term331 _91760 _91764 _91765.
Proof. exact (@lem3578289 _91760 _91764 _91765 (@lem3580888 _91760 _91764 _91765)). Qed.
Lemma lem3580891 {_91760 _91764 _91765 : Type'} (h1 : term332 _91760 _91764 _91765) : False.
Proof. exact (@lem3580890 _91760 _91764 _91765 (@lem3578273 _91760 _91764 _91765 h1)). Qed.
Lemma lem3580892 {_91760 _91764 _91765 : Type'} (h1 : term332 _91760 _91764 _91765) : (term332 _91760 _91764 _91765) = False.
Proof. exact (prop_ext (fun h2 : term332 _91760 _91764 _91765 => @lem3580891 _91760 _91764 _91765 h1) (fun h2 : False => @lem3578273 _91760 _91764 _91765 h1)). Qed.
Lemma lem3580893 {_91760 _91764 _91765 : Type'} (h1 : term332 _91760 _91764 _91765) : False.
Proof. exact (EQ_MP (@lem3580892 _91760 _91764 _91765 h1) (@lem3578273 _91760 _91764 _91765 h1)). Qed.
Lemma lem3580894 {_91760 _91764 _91765 : Type'} : term331 _91760 _91764 _91765.
Proof. exact (fun h0 : term332 _91760 _91764 _91765 => @lem3580893 _91760 _91764 _91765 h0). Qed.
Lemma lem3580895 {_91760 _91764 _91765 : Type'} : term330 _91760 _91764 _91765.
Proof. exact (EQ_MP (@lem3578272 _91760 _91764 _91765) (@lem3580894 _91760 _91764 _91765)). Qed.
Lemma lem3580896 {_91760 _91764 _91765 : Type'} : term299 _91760 _91764 _91765.
Proof. exact (EQ_MP (@lem3578268 _91760 _91764 _91765) (@lem3580895 _91760 _91764 _91765)). Qed.
Lemma lem3580897 {_91760 _91764 _91765 : Type'} : term298 _91760 _91764 _91765.
Proof. exact (EQ_MP (@lem3578150 _91760 _91764 _91765) (@lem3580896 _91760 _91764 _91765)). Qed.
