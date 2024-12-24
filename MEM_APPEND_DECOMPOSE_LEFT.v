Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_APPEND_DECOMPOSE_LEFT_term_abbrevs.
Require Import APPEND_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import MEM_spec.
Require Import MEM_APPEND_spec.
Require Import list_INDUCT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16445_spec.
Require Import thm16446_spec.
Require Import thm16457_spec.
Require Import thm16458_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
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
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm4211_spec.
Require Import thm69_spec.
Require Import thm82_spec.
Lemma lem1208010 {_25376 : Type'} (h : _25376) (x : _25376) : term0 _25376 h x.
Proof. exact (fun t : list _25376 => @lem1103203 _25376 h x t). Qed.
Lemma lem1208011 {_25376 : Type'} (h : _25376) : term1 _25376 h.
Proof. exact (fun x : _25376 => @lem1208010 _25376 h x). Qed.
Lemma lem1208012 {_25376 : Type'} : term2 _25376.
Proof. exact (fun h : _25376 => @lem1208011 _25376 h). Qed.
Lemma lem1208013 {A : Type'} (x : A) (y : A) : term3 A x y.
Proof. exact (@lem9784 (x = y)). Qed.
Lemma lem1208014 {A : Type'} (x : A) (y : A) : (term3 A x y) = (term4 A x y).
Proof. exact (eq_refl (term3 A x y)). Qed.
Lemma lem1208015 {A : Type'} (x : A) (y : A) : term4 A x y.
Proof. exact (EQ_MP (@lem1208014 A x y) (@lem1208013 A x y)). Qed.
Lemma lem1208016 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1208017 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1208020 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem1208021 {A : Type'} (P : type1143 A) (h1 : term6 A) : term7 A P.
Proof. exact (@lem1208020 A h1 P). Qed.
Lemma lem1208022 {A : Type'} (P : type1143 A) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem1208023 {A : Type'} (P : type1143 A) (h1 : term6 A) : term8 A P.
Proof. exact (EQ_MP (@lem1208022 A P) (@lem1208021 A P h1)). Qed.
Lemma lem1208024 {A : Type'} (P : type1143 A) (h1 : term9 A P) : term9 A P.
Proof. exact (h1). Qed.
Lemma lem1208025 {A : Type'} (P : type1143 A) (h1 : term6 A) (h2 : term9 A P) : term10 A P.
Proof. exact (@lem1208023 A P h1 (@lem1208024 A P h2)). Qed.
Lemma lem1208026 {A : Type'} (P : type1143 A) (h1 : term9 A P) : term11 A P.
Proof. exact (fun h0 : term6 A => @lem1208025 A P h0 h1). Qed.
Lemma lem1208027 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem1208028 {A : Type'} (P : type1143 A) (h1 : term6 A) (h2 : term9 A P) : term10 A P.
Proof. exact (@lem1208026 A P h2 (@lem1208027 A h1)). Qed.
Lemma lem1208029 {A : Type'} (P : type1143 A) (h1 : term6 A) : term8 A P.
Proof. exact (fun h0 : term9 A P => @lem1208028 A P h1 h0). Qed.
Lemma lem1208030 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (fun P : type1143 A => @lem1208029 A P h1). Qed.
Lemma lem1208031 {A : Type'} : term12 A.
Proof. exact (fun h0 : term6 A => @lem1208030 A h0). Qed.
Lemma lem1208032 {A : Type'} : term6 A.
Proof. exact (@lem1208031 A (@lem1071853 A)). Qed.
Lemma lem1208033 {A : Type'} (P : type1143 A) : term7 A P.
Proof. exact (@lem1208032 A P). Qed.
Lemma lem1208034 {A : Type'} (P : type1143 A) : (term7 A P) = (term8 A P).
Proof. exact (eq_refl (term7 A P)). Qed.
Lemma lem1208038 {_26945 : Type'} (x : _26945) : term13 _26945 x.
Proof. exact (@lem1145802 _26945 x). Qed.
Lemma lem1208039 {_26945 : Type'} (x : _26945) : (term13 _26945 x) = (term14 _26945 x).
Proof. exact (eq_refl (term13 _26945 x)). Qed.
Lemma lem1208040 {_26945 : Type'} (x : _26945) : term14 _26945 x.
Proof. exact (EQ_MP (@lem1208039 _26945 x) (@lem1208038 _26945 x)). Qed.
Lemma lem1208041 {_26945 : Type'} (x : _26945) (l1 : list _26945) : term15 _26945 x l1.
Proof. exact (@lem1208040 _26945 x l1). Qed.
Lemma lem1208042 {_26945 : Type'} (l1 : list _26945) (x : _26945) : (term15 _26945 x l1) = (term16 _26945 l1 x).
Proof. exact (eq_refl (term15 _26945 x l1)). Qed.
Lemma lem1208043 {_26945 : Type'} (l1 : list _26945) (x : _26945) : term16 _26945 l1 x.
Proof. exact (EQ_MP (@lem1208042 _26945 l1 x) (@lem1208041 _26945 x l1)). Qed.
Lemma lem1208044 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : term17 _26945 l1 x l2.
Proof. exact (@lem1208043 _26945 l1 x l2). Qed.
Lemma lem1208045 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : (term17 _26945 l1 x l2) = ((term18 _26945 x l1 l2) = (term19 _26945 l1 x l2)).
Proof. exact (eq_refl (term17 _26945 l1 x l2)). Qed.
Lemma lem1208047 {A : Type'} (P : A -> Prop) : term20 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem1208048 {A : Type'} (P : A -> Prop) : (term20 A P) = (term21 A P).
Proof. exact (eq_refl (term20 A P)). Qed.
Lemma lem1208049 {A : Type'} (P : A -> Prop) : term21 A P.
Proof. exact (EQ_MP (@lem1208048 A P) (@lem1208047 A P)). Qed.
Lemma lem1208050 {A : Type'} (P : A -> Prop) (Q : Prop) : term22 A P Q.
Proof. exact (@lem1208049 A P Q). Qed.
Lemma lem1208051 {A : Type'} (P : A -> Prop) (Q : Prop) : (term22 A P Q) = ((term23 A P Q) = (term24 A P Q)).
Proof. exact (eq_refl (term22 A P Q)). Qed.
Lemma lem1208065 (p : Prop) : term25 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem1208066 (p : Prop) : (term25 p) = (term26 p).
Proof. exact (eq_refl (term25 p)). Qed.
Lemma lem1208067 (p : Prop) : term26 p.
Proof. exact (EQ_MP (@lem1208066 p) (@lem1208065 p)). Qed.
Lemma lem1208068 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem1208069 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem1208082 (q : Prop) : (term27 q) = (term27 q).
Proof. exact (eq_refl (term27 q)). Qed.
Lemma lem1208083 (q : Prop) (p : Prop) (h1 : p = True) : (term28 q p) = (term29 q).
Proof. exact (MK_COMB (@lem1208082 q) (@lem1208068 p h1)). Qed.
Lemma lem1208084 (q : Prop) : (term29 q) = ((True = q) = (term30 q)).
Proof. exact (eq_refl (term29 q)). Qed.
Lemma lem1208085 (q : Prop) (p : Prop) : (term31 q p) = (term31 q p).
Proof. exact (eq_refl (term31 q p)). Qed.
Lemma lem1208086 (p : Prop) (q : Prop) : ((term28 q p) = (term29 q)) = ((term28 q p) = ((True = q) = (term30 q))).
Proof. exact (MK_COMB (@lem1208085 q p) (@lem1208084 q)). Qed.
Lemma lem1208087 (q : Prop) (p : Prop) : (term28 q p) = ((p = q) = (term32 q p)).
Proof. exact (eq_refl (term28 q p)). Qed.
Lemma lem1208088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1208089 (q : Prop) (p : Prop) : (term31 q p) = (term33 q p).
Proof. exact (MK_COMB (@lem1208088) (@lem1208087 q p)). Qed.
Lemma lem1208090 (q : Prop) : ((True = q) = (term30 q)) = ((True = q) = (term30 q)).
Proof. exact (eq_refl ((True = q) = (term30 q))). Qed.
Lemma lem1208091 (p : Prop) (q : Prop) : ((term28 q p) = ((True = q) = (term30 q))) = (((p = q) = (term32 q p)) = ((True = q) = (term30 q))).
Proof. exact (MK_COMB (@lem1208089 q p) (@lem1208090 q)). Qed.
Lemma lem1208092 (p : Prop) (q : Prop) : ((term28 q p) = (term29 q)) = (((p = q) = (term32 q p)) = ((True = q) = (term30 q))).
Proof. exact (TRANS (@lem1208086 p q) (@lem1208091 p q)). Qed.
Lemma lem1208093 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = (term32 q p)) = ((True = q) = (term30 q)).
Proof. exact (EQ_MP (@lem1208092 p q) (@lem1208083 q p h1)). Qed.
Lemma lem1208094 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = (term30 q)) = ((p = q) = (term32 q p)).
Proof. exact (SYM (@lem1208093 q p h1)). Qed.
Lemma lem1208095 (q : Prop) : (term27 q) = (term27 q).
Proof. exact (eq_refl (term27 q)). Qed.
Lemma lem1208096 (q : Prop) (p : Prop) (h1 : p = False) : (term28 q p) = (term34 q).
Proof. exact (MK_COMB (@lem1208095 q) (@lem1208069 p h1)). Qed.
Lemma lem1208097 (q : Prop) : (term34 q) = ((False = q) = (term35 q)).
Proof. exact (eq_refl (term34 q)). Qed.
Lemma lem1208098 (q : Prop) (p : Prop) : (term31 q p) = (term31 q p).
Proof. exact (eq_refl (term31 q p)). Qed.
Lemma lem1208099 (p : Prop) (q : Prop) : ((term28 q p) = (term34 q)) = ((term28 q p) = ((False = q) = (term35 q))).
Proof. exact (MK_COMB (@lem1208098 q p) (@lem1208097 q)). Qed.
Lemma lem1208100 (q : Prop) (p : Prop) : (term28 q p) = ((p = q) = (term32 q p)).
Proof. exact (eq_refl (term28 q p)). Qed.
Lemma lem1208101 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1208102 (q : Prop) (p : Prop) : (term31 q p) = (term33 q p).
Proof. exact (MK_COMB (@lem1208101) (@lem1208100 q p)). Qed.
Lemma lem1208103 (q : Prop) : ((False = q) = (term35 q)) = ((False = q) = (term35 q)).
Proof. exact (eq_refl ((False = q) = (term35 q))). Qed.
Lemma lem1208104 (p : Prop) (q : Prop) : ((term28 q p) = ((False = q) = (term35 q))) = (((p = q) = (term32 q p)) = ((False = q) = (term35 q))).
Proof. exact (MK_COMB (@lem1208102 q p) (@lem1208103 q)). Qed.
Lemma lem1208105 (p : Prop) (q : Prop) : ((term28 q p) = (term34 q)) = (((p = q) = (term32 q p)) = ((False = q) = (term35 q))).
Proof. exact (TRANS (@lem1208099 p q) (@lem1208104 p q)). Qed.
Lemma lem1208106 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = (term32 q p)) = ((False = q) = (term35 q)).
Proof. exact (EQ_MP (@lem1208105 p q) (@lem1208096 q p h1)). Qed.
Lemma lem1208107 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = (term35 q)) = ((p = q) = (term32 q p)).
Proof. exact (SYM (@lem1208106 q p h1)). Qed.
Lemma lem1208111 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1208112 (q : Prop) : (True = q) = q.
Proof. exact (@lem1208111 q). Qed.
Lemma lem1208113 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1208114 (q : Prop) : (term36 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem1208113) (@lem1208112 q)). Qed.
Lemma lem1208118 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1208119 (q : Prop) : (True -> q) = q.
Proof. exact (@lem1208118 q). Qed.
Lemma lem1208120 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1208121 (q : Prop) : (term37 q) = (and q).
Proof. exact (MK_COMB (@lem1208120) (@lem1208119 q)). Qed.
Lemma lem1208123 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1208124 (q : Prop) : (q -> True) = True.
Proof. exact (@lem1208123 q). Qed.
Lemma lem1208125 (q : Prop) : (term30 q) = (q /\ True).
Proof. exact (MK_COMB (@lem1208121 q) (@lem1208124 q)). Qed.
Lemma lem1208127 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1208128 (q : Prop) : (q /\ True) = q.
Proof. exact (@lem1208127 q). Qed.
Lemma lem1208129 (q : Prop) : (term30 q) = q.
Proof. exact (TRANS (@lem1208125 q) (@lem1208128 q)). Qed.
Lemma lem1208130 (q : Prop) : ((True = q) = (term30 q)) = (q = q).
Proof. exact (MK_COMB (@lem1208114 q) (@lem1208129 q)). Qed.
Lemma lem1208132 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1208133 (x : Prop) : (x = x) = True.
Proof. exact (@lem1208132 Prop x). Qed.
Lemma lem1208134 (q : Prop) : (q = q) = True.
Proof. exact (@lem1208133 q). Qed.
Lemma lem1208135 (q : Prop) : ((True = q) = (term30 q)) = True.
Proof. exact (TRANS (@lem1208130 q) (@lem1208134 q)). Qed.
Lemma lem1208136 (q : Prop) : True = ((True = q) = (term30 q)).
Proof. exact (SYM (@lem1208135 q)). Qed.
Lemma lem1208137 (q : Prop) : (True = q) = (term30 q).
Proof. exact (EQ_MP (@lem1208136 q) (@lem0)). Qed.
Lemma lem1208141 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1208142 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem1208141 q). Qed.
Lemma lem1208143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1208144 (q : Prop) : (term38 q) = (term39 q).
Proof. exact (MK_COMB (@lem1208143) (@lem1208142 q)). Qed.
Lemma lem1208148 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1208149 (q : Prop) : (False -> q) = True.
Proof. exact (@lem1208148 q). Qed.
Lemma lem1208150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1208151 (q : Prop) : (term40 q) = (and True).
Proof. exact (MK_COMB (@lem1208150) (@lem1208149 q)). Qed.
Lemma lem1208153 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem1208154 (q : Prop) : (q -> False) = (~ q).
Proof. exact (@lem1208153 q). Qed.
Lemma lem1208155 (q : Prop) : (term35 q) = (term41 q).
Proof. exact (MK_COMB (@lem1208151 q) (@lem1208154 q)). Qed.
Lemma lem1208157 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1208158 (q : Prop) : (term41 q) = (~ q).
Proof. exact (@lem1208157 (~ q)). Qed.
Lemma lem1208159 (q : Prop) : (term35 q) = (~ q).
Proof. exact (TRANS (@lem1208155 q) (@lem1208158 q)). Qed.
Lemma lem1208160 (q : Prop) : ((False = q) = (term35 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem1208144 q) (@lem1208159 q)). Qed.
Lemma lem1208162 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1208163 (x : Prop) : (x = x) = True.
Proof. exact (@lem1208162 Prop x). Qed.
Lemma lem1208164 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem1208163 (~ q)). Qed.
Lemma lem1208165 (q : Prop) : ((False = q) = (term35 q)) = True.
Proof. exact (TRANS (@lem1208160 q) (@lem1208164 q)). Qed.
Lemma lem1208166 (q : Prop) : True = ((False = q) = (term35 q)).
Proof. exact (SYM (@lem1208165 q)). Qed.
Lemma lem1208167 (q : Prop) : (False = q) = (term35 q).
Proof. exact (EQ_MP (@lem1208166 q) (@lem0)). Qed.
Lemma lem1208168 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = (term32 q p).
Proof. exact (EQ_MP (@lem1208107 q p h1) (@lem1208167 q)). Qed.
Lemma lem1208169 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = (term32 q p).
Proof. exact (EQ_MP (@lem1208094 q p h1) (@lem1208137 q)). Qed.
Lemma lem1208184 (q : Prop) (p : Prop) : (p = q) = (term32 q p).
Proof. exact (or_elim (@lem1208067 p) (fun h0 : p = True => @lem1208169 q p h0) (fun h0 : p = False => @lem1208168 q p h0)). Qed.
Lemma lem1208185 {A : Type'} (x : A) (l : list A) : ((@List.In A x l) = (term42 A l x)) = (term43 A x l).
Proof. exact (@lem1208184 (term42 A l x) (@List.In A x l)). Qed.
Lemma lem1208220 {A : Type'} (x : A) : (term44 A x) = (term45 A x).
Proof. exact (fun_ext (fun l : list A => @lem1208185 A x l)). Qed.
Lemma lem1208221 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208222 {A : Type'} (x : A) : (term46 A x) = (term47 A x).
Proof. exact (MK_COMB (@lem1208221 A) (@lem1208220 A x)). Qed.
Lemma lem1208227 {A : Type'} : (term48 A) = (term49 A).
Proof. exact (fun_ext (fun x : A => @lem1208222 A x)). Qed.
Lemma lem1208228 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1208229 {A : Type'} : (term50 A) = (term51 A).
Proof. exact (MK_COMB (@lem1208228 A) (@lem1208227 A)). Qed.
Lemma lem1208234 {A : Type'} : (term51 A) = (term50 A).
Proof. exact (SYM (@lem1208229 A)). Qed.
Lemma lem1208293 {A : Type'} (P : A -> Prop) (Q : Prop) : (term23 A P Q) = (term24 A P Q).
Proof. exact (EQ_MP (@lem1208051 A P Q) (@lem1208050 A P Q)). Qed.
Lemma lem1208294 {A : Type'} (P : type1143 A) (Q : Prop) : (term52 A P Q) = (term53 A P Q).
Proof. exact (@lem1208293 (list A) P Q). Qed.
Lemma lem1208295 {A : Type'} (x : A) (l : list A) : (term54 A x l) = (term55 A x l).
Proof. exact (@lem1208294 A (term56 A l x) (@List.In A x l)). Qed.
Lemma lem1208296 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term57 A l x l1) = (term58 A l l1 x).
Proof. exact (eq_refl (term57 A l x l1)). Qed.
Lemma lem1208297 {A : Type'} (l : list A) (x : A) : (term59 A l x) = (term56 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1208296 A l l1 x)). Qed.
Lemma lem1208298 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1208299 {A : Type'} (l : list A) (x : A) : (term60 A l x) = (term42 A l x).
Proof. exact (MK_COMB (@lem1208298 A) (@lem1208297 A l x)). Qed.
Lemma lem1208300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208301 {A : Type'} (l : list A) (x : A) : (term61 A l x) = (term62 A l x).
Proof. exact (MK_COMB (@lem1208300) (@lem1208299 A l x)). Qed.
Lemma lem1208302 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1208303 {A : Type'} (x : A) (l : list A) : (term54 A x l) = (term63 A x l).
Proof. exact (MK_COMB (@lem1208301 A l x) (@lem1208302 A x l)). Qed.
Lemma lem1208304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1208305 {A : Type'} (x : A) (l : list A) : (term64 A x l) = (term65 A x l).
Proof. exact (MK_COMB (@lem1208304) (@lem1208303 A x l)). Qed.
Lemma lem1208306 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term57 A l x l1) = (term58 A l l1 x).
Proof. exact (eq_refl (term57 A l x l1)). Qed.
Lemma lem1208307 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208308 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term66 A l x l1) = (term67 A l l1 x).
Proof. exact (MK_COMB (@lem1208307) (@lem1208306 A l l1 x)). Qed.
Lemma lem1208309 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1208310 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term68 A l1 x l) = (term69 A l1 x l).
Proof. exact (MK_COMB (@lem1208308 A l l1 x) (@lem1208309 A x l)). Qed.
Lemma lem1208311 {A : Type'} (x : A) (l : list A) : (term70 A x l) = (term71 A x l).
Proof. exact (fun_ext (fun l1 : list A => @lem1208310 A l1 x l)). Qed.
Lemma lem1208312 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208313 {A : Type'} (x : A) (l : list A) : (term55 A x l) = (term72 A x l).
Proof. exact (MK_COMB (@lem1208312 A) (@lem1208311 A x l)). Qed.
Lemma lem1208314 {A : Type'} (x : A) (l : list A) : ((term54 A x l) = (term55 A x l)) = ((term63 A x l) = (term72 A x l)).
Proof. exact (MK_COMB (@lem1208305 A x l) (@lem1208313 A x l)). Qed.
Lemma lem1208315 {A : Type'} (x : A) (l : list A) : (term63 A x l) = (term72 A x l).
Proof. exact (EQ_MP (@lem1208314 A x l) (@lem1208295 A x l)). Qed.
Lemma lem1208321 {A : Type'} (P : A -> Prop) (Q : Prop) : (term23 A P Q) = (term24 A P Q).
Proof. exact (EQ_MP (@lem1208051 A P Q) (@lem1208050 A P Q)). Qed.
Lemma lem1208322 {A : Type'} (P : type1143 A) (Q : Prop) : (term52 A P Q) = (term53 A P Q).
Proof. exact (@lem1208321 (list A) P Q). Qed.
Lemma lem1208323 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term73 A l1 x l) = (term74 A l1 x l).
Proof. exact (@lem1208322 A (term75 A l l1 x) (@List.In A x l)). Qed.
Lemma lem1208324 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term76 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (eq_refl (term76 A l l1 x l2)). Qed.
Lemma lem1208325 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term78 A l l1 x) = (term75 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1208324 A l l1 x l2)). Qed.
Lemma lem1208326 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1208327 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term79 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1208326 A) (@lem1208325 A l l1 x)). Qed.
Lemma lem1208328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208329 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term80 A l l1 x) = (term67 A l l1 x).
Proof. exact (MK_COMB (@lem1208328) (@lem1208327 A l l1 x)). Qed.
Lemma lem1208330 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1208331 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term73 A l1 x l) = (term69 A l1 x l).
Proof. exact (MK_COMB (@lem1208329 A l l1 x) (@lem1208330 A x l)). Qed.
Lemma lem1208332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1208333 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term81 A l1 x l) = (term82 A l1 x l).
Proof. exact (MK_COMB (@lem1208332) (@lem1208331 A l1 x l)). Qed.
Lemma lem1208334 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term76 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (eq_refl (term76 A l l1 x l2)). Qed.
Lemma lem1208335 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208336 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term83 A l l1 x l2) = (term84 A l l1 x l2).
Proof. exact (MK_COMB (@lem1208335) (@lem1208334 A l l1 x l2)). Qed.
Lemma lem1208337 {A : Type'} (x : A) (l : list A) : (@List.In A x l) = (@List.In A x l).
Proof. exact (eq_refl (@List.In A x l)). Qed.
Lemma lem1208338 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : (term85 A l1 l2 x l) = (term86 A l1 l2 x l).
Proof. exact (MK_COMB (@lem1208336 A l l1 x l2) (@lem1208337 A x l)). Qed.
Lemma lem1208339 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term87 A l1 x l) = (term88 A l1 x l).
Proof. exact (fun_ext (fun l2 : list A => @lem1208338 A l1 l2 x l)). Qed.
Lemma lem1208340 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208341 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term74 A l1 x l) = (term89 A l1 x l).
Proof. exact (MK_COMB (@lem1208340 A) (@lem1208339 A l1 x l)). Qed.
Lemma lem1208342 {A : Type'} (l1 : list A) (x : A) (l : list A) : ((term73 A l1 x l) = (term74 A l1 x l)) = ((term69 A l1 x l) = (term89 A l1 x l)).
Proof. exact (MK_COMB (@lem1208333 A l1 x l) (@lem1208341 A l1 x l)). Qed.
Lemma lem1208343 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term69 A l1 x l) = (term89 A l1 x l).
Proof. exact (EQ_MP (@lem1208342 A l1 x l) (@lem1208323 A l1 x l)). Qed.
Lemma lem1208351 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term90 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem1208352 (p : Prop) (q : Prop) (p' : Prop) : term91 p q p'.
Proof. exact (fun q' : Prop => @lem1208351 p q p' q'). Qed.
Lemma lem1208353 (p : Prop) (q : Prop) : term92 p q.
Proof. exact (fun p' : Prop => @lem1208352 p q p'). Qed.
Lemma lem1208354 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : term93 A l1 l2 x l.
Proof. exact (@lem1208353 (term77 A l l1 x l2) (@List.In A x l)). Qed.
Lemma lem1208355 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) : term94 A l1 l2 x l p'.
Proof. exact (@lem1208354 A l1 l2 x l p'). Qed.
Lemma lem1208356 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) : (term94 A l1 l2 x l p') = (term95 A l1 l2 x l p').
Proof. exact (eq_refl (term94 A l1 l2 x l p')). Qed.
Lemma lem1208357 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) : term95 A l1 l2 x l p'.
Proof. exact (EQ_MP (@lem1208356 A l1 l2 x l p') (@lem1208355 A l1 l2 x l p')). Qed.
Lemma lem1208358 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) (q' : Prop) : term96 A l1 l2 x l p' q'.
Proof. exact (@lem1208357 A l1 l2 x l p' q'). Qed.
Lemma lem1208359 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) (q' : Prop) : (term96 A l1 l2 x l p' q') = (term97 A l1 l2 x l p' q').
Proof. exact (eq_refl (term96 A l1 l2 x l p' q')). Qed.
Lemma lem1208360 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) (p' : Prop) (q' : Prop) : term97 A l1 l2 x l p' q'.
Proof. exact (EQ_MP (@lem1208359 A l1 l2 x l p' q') (@lem1208358 A l1 l2 x l p' q')). Qed.
Lemma lem1208365 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term77 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (eq_refl (term77 A l l1 x l2)). Qed.
Lemma lem1208366 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (q' : Prop) : term98 A l l1 x l2 q'.
Proof. exact (@lem1208360 A l1 l2 x l (term77 A l l1 x l2) q'). Qed.
Lemma lem1208367 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (q' : Prop) : term99 A l l1 x l2 q'.
Proof. exact (@lem1208366 A l l1 x l2 q' (@lem1208365 A l l1 x l2)). Qed.
Lemma lem1208368 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : term77 A l l1 x l2.
Proof. exact (h1). Qed.
Lemma lem1208370 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : term100 A x l1.
Proof. exact (proj1 (@lem1208368 A l l1 x l2 h1)). Qed.
Lemma lem1208371 {A : Type'} (x : A) (l1 : list A) : term101 A x l1.
Proof. exact (@lem82 (@List.In A x l1)). Qed.
Lemma lem1208374 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : l = (term102 A l1 x l2).
Proof. exact (proj2 (@lem1208368 A l l1 x l2 h1)). Qed.
Lemma lem1208375 {A : Type'} (x : A) : (@List.In A x) = (@List.In A x).
Proof. exact (eq_refl (@List.In A x)). Qed.
Lemma lem1208376 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (@List.In A x l) = (term103 A l1 x l2).
Proof. exact (MK_COMB (@lem1208375 A x) (@lem1208374 A l l1 x l2 h1)). Qed.
Lemma lem1208378 {_26945 : Type'} (l1 : list _26945) (x : _26945) (l2 : list _26945) : (term18 _26945 x l1 l2) = (term19 _26945 l1 x l2).
Proof. exact (EQ_MP (@lem1208045 _26945 l1 x l2) (@lem1208044 _26945 l1 x l2)). Qed.
Lemma lem1208379 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term18 A x l1 l2) = (term19 A l1 x l2).
Proof. exact (@lem1208378 A l1 x l2). Qed.
Lemma lem1208380 {A : Type'} (l1 : list A) (x : A) (l2 : list A) : (term103 A l1 x l2) = (term104 A l1 x l2).
Proof. exact (@lem1208379 A l1 x (@cons A x l2)). Qed.
Lemma lem1208384 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (@List.In A x l1) = False.
Proof. exact (@lem1208371 A x l1 (@lem1208370 A l l1 x l2 h1)). Qed.
Lemma lem1208385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1208386 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term105 A x l1) = (or False).
Proof. exact (MK_COMB (@lem1208385) (@lem1208384 A l l1 x l2 h1)). Qed.
Lemma lem1208388 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term106 _25376 x h t) = (term107 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1208389 {A : Type'} (h : A) (x : A) (t : list A) : (term106 A x h t) = (term107 A h x t).
Proof. exact (@lem1208388 A h x t). Qed.
Lemma lem1208390 {A : Type'} (x : A) (l2 : list A) : (term108 A x l2) = (term109 A x l2).
Proof. exact (@lem1208389 A x x l2). Qed.
Lemma lem1208394 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1208395 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem1208394 A x). Qed.
Lemma lem1208396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1208397 {A : Type'} (x : A) : (term110 A x) = (or True).
Proof. exact (MK_COMB (@lem1208396) (@lem1208395 A x)). Qed.
Lemma lem1208398 {A : Type'} (x : A) (l2 : list A) : (@List.In A x l2) = (@List.In A x l2).
Proof. exact (eq_refl (@List.In A x l2)). Qed.
Lemma lem1208399 {A : Type'} (x : A) (l2 : list A) : (term109 A x l2) = (term111 A x l2).
Proof. exact (MK_COMB (@lem1208397 A x) (@lem1208398 A x l2)). Qed.
Lemma lem1208401 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem1208402 {A : Type'} (x : A) (l2 : list A) : (term111 A x l2) = True.
Proof. exact (@lem1208401 (@List.In A x l2)). Qed.
Lemma lem1208403 {A : Type'} (x : A) (l2 : list A) : (term109 A x l2) = True.
Proof. exact (TRANS (@lem1208399 A x l2) (@lem1208402 A x l2)). Qed.
Lemma lem1208404 {A : Type'} (x : A) (l2 : list A) : (term108 A x l2) = True.
Proof. exact (TRANS (@lem1208390 A x l2) (@lem1208403 A x l2)). Qed.
Lemma lem1208405 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term104 A l1 x l2) = (False \/ True).
Proof. exact (MK_COMB (@lem1208386 A l l1 x l2 h1) (@lem1208404 A x l2)). Qed.
Lemma lem1208407 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem1208408 : (False \/ True) = True.
Proof. exact (@lem1208407 True). Qed.
Lemma lem1208409 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term104 A l1 x l2) = True.
Proof. exact (TRANS (@lem1208405 A l l1 x l2 h1) (@lem1208408)). Qed.
Lemma lem1208410 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term103 A l1 x l2) = True.
Proof. exact (TRANS (@lem1208380 A l1 x l2) (@lem1208409 A l l1 x l2 h1)). Qed.
Lemma lem1208411 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (@List.In A x l) = True.
Proof. exact (TRANS (@lem1208376 A l l1 x l2 h1) (@lem1208410 A l l1 x l2 h1)). Qed.
Lemma lem1208412 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : term112 A l1 l2 x l.
Proof. exact (fun h0 : term77 A l l1 x l2 => @lem1208411 A l l1 x l2 h0). Qed.
Lemma lem1208413 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : term113 A l l1 x l2.
Proof. exact (@lem1208367 A l l1 x l2 True). Qed.
Lemma lem1208414 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term86 A l1 l2 x l) = (term114 A l l1 x l2).
Proof. exact (@lem1208413 A l l1 x l2 (@lem1208412 A l1 l2 x l)). Qed.
Lemma lem1208416 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem1208417 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term114 A l l1 x l2) = True.
Proof. exact (@lem1208416 (term77 A l l1 x l2)). Qed.
Lemma lem1208418 {A : Type'} (l1 : list A) (l2 : list A) (x : A) (l : list A) : (term86 A l1 l2 x l) = True.
Proof. exact (TRANS (@lem1208414 A l l1 x l2) (@lem1208417 A l l1 x l2)). Qed.
Lemma lem1208419 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term88 A l1 x l) = (term115 A).
Proof. exact (fun_ext (fun l2 : list A => @lem1208418 A l1 l2 x l)). Qed.
Lemma lem1208420 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208421 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term89 A l1 x l) = (term116 A).
Proof. exact (MK_COMB (@lem1208420 A) (@lem1208419 A l1 x l)). Qed.
Lemma lem1208423 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1208424 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (@lem1208423 (list A) t). Qed.
Lemma lem1208425 {A : Type'} : (term116 A) = True.
Proof. exact (@lem1208424 A True). Qed.
Lemma lem1208426 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term89 A l1 x l) = True.
Proof. exact (TRANS (@lem1208421 A l1 x l) (@lem1208425 A)). Qed.
Lemma lem1208427 {A : Type'} (l1 : list A) (x : A) (l : list A) : (term69 A l1 x l) = True.
Proof. exact (TRANS (@lem1208343 A l1 x l) (@lem1208426 A l1 x l)). Qed.
Lemma lem1208428 {A : Type'} (x : A) (l : list A) : (term71 A x l) = (term115 A).
Proof. exact (fun_ext (fun l1 : list A => @lem1208427 A l1 x l)). Qed.
Lemma lem1208429 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208430 {A : Type'} (x : A) (l : list A) : (term72 A x l) = (term116 A).
Proof. exact (MK_COMB (@lem1208429 A) (@lem1208428 A x l)). Qed.
Lemma lem1208432 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1208433 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (@lem1208432 (list A) t). Qed.
Lemma lem1208434 {A : Type'} : (term116 A) = True.
Proof. exact (@lem1208433 A True). Qed.
Lemma lem1208435 {A : Type'} (x : A) (l : list A) : (term72 A x l) = True.
Proof. exact (TRANS (@lem1208430 A x l) (@lem1208434 A)). Qed.
Lemma lem1208436 {A : Type'} (x : A) (l : list A) : (term63 A x l) = True.
Proof. exact (TRANS (@lem1208315 A x l) (@lem1208435 A x l)). Qed.
Lemma lem1208437 {A : Type'} (l : list A) (x : A) : (term119 A l x) = (term119 A l x).
Proof. exact (eq_refl (term119 A l x)). Qed.
Lemma lem1208438 {A : Type'} (l : list A) (x : A) : (term43 A x l) = (term120 A l x).
Proof. exact (MK_COMB (@lem1208437 A l x) (@lem1208436 A x l)). Qed.
Lemma lem1208440 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem1208441 {A : Type'} (l : list A) (x : A) : (term120 A l x) = (term121 A l x).
Proof. exact (@lem1208440 (term121 A l x)). Qed.
Lemma lem1208489 {A : Type'} (l : list A) (x : A) : (term43 A x l) = (term121 A l x).
Proof. exact (TRANS (@lem1208438 A l x) (@lem1208441 A l x)). Qed.
Lemma lem1208490 {A : Type'} (x : A) : (term45 A x) = (term122 A x).
Proof. exact (fun_ext (fun l : list A => @lem1208489 A l x)). Qed.
Lemma lem1208538 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208539 {A : Type'} (x : A) : (term47 A x) = (term123 A x).
Proof. exact (MK_COMB (@lem1208538 A) (@lem1208490 A x)). Qed.
Lemma lem1208591 {A : Type'} : (term49 A) = (term124 A).
Proof. exact (fun_ext (fun x : A => @lem1208539 A x)). Qed.
Lemma lem1208643 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1208644 {A : Type'} : (term51 A) = (term125 A).
Proof. exact (MK_COMB (@lem1208643 A) (@lem1208591 A)). Qed.
Lemma lem1208700 {A : Type'} : (term125 A) = (term51 A).
Proof. exact (SYM (@lem1208644 A)). Qed.
Lemma lem1208702 {A : Type'} (P : type1143 A) : term8 A P.
Proof. exact (EQ_MP (@lem1208034 A P) (@lem1208033 A P)). Qed.
Lemma lem1208703 {A : Type'} (P : type1143 A) : term8 A P.
Proof. exact (@lem1208702 A P). Qed.
Lemma lem1208704 {A : Type'} (x : A) : term126 A x.
Proof. exact (@lem1208703 A (term122 A x)). Qed.
Lemma lem1208705 {A : Type'} (x : A) : (term127 A x) = (term128 A x).
Proof. exact (eq_refl (term127 A x)). Qed.
Lemma lem1208706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1208707 {A : Type'} (x : A) : (term129 A x) = (term130 A x).
Proof. exact (MK_COMB (@lem1208706) (@lem1208705 A x)). Qed.
Lemma lem1208708 {A : Type'} (a1 : list A) (x : A) : (term131 A x a1) = (term121 A a1 x).
Proof. exact (eq_refl (term131 A x a1)). Qed.
Lemma lem1208709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208710 {A : Type'} (a1 : list A) (x : A) : (term132 A x a1) = (term133 A a1 x).
Proof. exact (MK_COMB (@lem1208709) (@lem1208708 A a1 x)). Qed.
Lemma lem1208711 {A : Type'} (a0 : A) (a1 : list A) (x : A) : (term134 A x a0 a1) = (term135 A a0 a1 x).
Proof. exact (eq_refl (term134 A x a0 a1)). Qed.
Lemma lem1208712 {A : Type'} (a0 : A) (a1 : list A) (x : A) : (term136 A x a0 a1) = (term137 A a0 a1 x).
Proof. exact (MK_COMB (@lem1208710 A a1 x) (@lem1208711 A a0 a1 x)). Qed.
Lemma lem1208713 {A : Type'} (a0 : A) (x : A) : (term138 A x a0) = (term139 A a0 x).
Proof. exact (fun_ext (fun a1 : list A => @lem1208712 A a0 a1 x)). Qed.
Lemma lem1208714 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208715 {A : Type'} (a0 : A) (x : A) : (term140 A x a0) = (term141 A a0 x).
Proof. exact (MK_COMB (@lem1208714 A) (@lem1208713 A a0 x)). Qed.
Lemma lem1208716 {A : Type'} (x : A) : (term142 A x) = (term143 A x).
Proof. exact (fun_ext (fun a0 : A => @lem1208715 A a0 x)). Qed.
Lemma lem1208717 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1208718 {A : Type'} (x : A) : (term144 A x) = (term145 A x).
Proof. exact (MK_COMB (@lem1208717 A) (@lem1208716 A x)). Qed.
Lemma lem1208719 {A : Type'} (x : A) : (term146 A x) = (term147 A x).
Proof. exact (MK_COMB (@lem1208707 A x) (@lem1208718 A x)). Qed.
Lemma lem1208720 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208721 {A : Type'} (x : A) : (term148 A x) = (term149 A x).
Proof. exact (MK_COMB (@lem1208720) (@lem1208719 A x)). Qed.
Lemma lem1208722 {A : Type'} (l : list A) (x : A) : (term131 A x l) = (term121 A l x).
Proof. exact (eq_refl (term131 A x l)). Qed.
Lemma lem1208723 {A : Type'} (x : A) : (term150 A x) = (term122 A x).
Proof. exact (fun_ext (fun l : list A => @lem1208722 A l x)). Qed.
Lemma lem1208724 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208725 {A : Type'} (x : A) : (term151 A x) = (term123 A x).
Proof. exact (MK_COMB (@lem1208724 A) (@lem1208723 A x)). Qed.
Lemma lem1208726 {A : Type'} (x : A) : (term126 A x) = (term152 A x).
Proof. exact (MK_COMB (@lem1208721 A x) (@lem1208725 A x)). Qed.
Lemma lem1208727 {A : Type'} (x : A) : term152 A x.
Proof. exact (EQ_MP (@lem1208726 A x) (@lem1208704 A x)). Qed.
Lemma lem1208733 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1208734 {A : Type'} (x : A) : (@List.In A x (@nil A)) = False.
Proof. exact (@lem1208733 A x). Qed.
Lemma lem1208735 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208736 {A : Type'} (x : A) : (term153 A x) = (imp False).
Proof. exact (MK_COMB (@lem1208735) (@lem1208734 A x)). Qed.
Lemma lem1208749 {A : Type'} (x : A) : (term154 A x) = (term154 A x).
Proof. exact (eq_refl (term154 A x)). Qed.
Lemma lem1208750 {A : Type'} (x : A) : (term128 A x) = (term155 A x).
Proof. exact (MK_COMB (@lem1208736 A x) (@lem1208749 A x)). Qed.
Lemma lem1208752 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1208753 {A : Type'} (x : A) : (term155 A x) = True.
Proof. exact (@lem1208752 (term154 A x)). Qed.
Lemma lem1208754 {A : Type'} (x : A) : (term128 A x) = True.
Proof. exact (TRANS (@lem1208750 A x) (@lem1208753 A x)). Qed.
Lemma lem1208755 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1208756 {A : Type'} (x : A) : (term130 A x) = (and True).
Proof. exact (MK_COMB (@lem1208755) (@lem1208754 A x)). Qed.
Lemma lem1208784 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term106 _25376 x h t) = (term107 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1208785 {A : Type'} (h : A) (x : A) (t : list A) : (term106 A x h t) = (term107 A h x t).
Proof. exact (@lem1208784 A h x t). Qed.
Lemma lem1208786 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term106 A x a0 a1) = (term107 A a0 x a1).
Proof. exact (@lem1208785 A a0 x a1). Qed.
Lemma lem1208791 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1208792 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term156 A x a0 a1) = (term157 A a0 x a1).
Proof. exact (MK_COMB (@lem1208791) (@lem1208786 A a0 x a1)). Qed.
Lemma lem1208805 {A : Type'} (a0 : A) (a1 : list A) (x : A) : (term158 A a0 a1 x) = (term158 A a0 a1 x).
Proof. exact (eq_refl (term158 A a0 a1 x)). Qed.
Lemma lem1208806 {A : Type'} (a0 : A) (a1 : list A) (x : A) : (term135 A a0 a1 x) = (term159 A a0 a1 x).
Proof. exact (MK_COMB (@lem1208792 A a0 x a1) (@lem1208805 A a0 a1 x)). Qed.
Lemma lem1208809 {A : Type'} (a1 : list A) (x : A) : (term133 A a1 x) = (term133 A a1 x).
Proof. exact (eq_refl (term133 A a1 x)). Qed.
Lemma lem1208810 {A : Type'} (a0 : A) (a1 : list A) (x : A) : (term137 A a0 a1 x) = (term160 A a0 a1 x).
Proof. exact (MK_COMB (@lem1208809 A a1 x) (@lem1208806 A a0 a1 x)). Qed.
Lemma lem1208813 {A : Type'} (a0 : A) (x : A) : (term139 A a0 x) = (term161 A a0 x).
Proof. exact (fun_ext (fun a1 : list A => @lem1208810 A a0 a1 x)). Qed.
Lemma lem1208814 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1208815 {A : Type'} (a0 : A) (x : A) : (term141 A a0 x) = (term162 A a0 x).
Proof. exact (MK_COMB (@lem1208814 A) (@lem1208813 A a0 x)). Qed.
Lemma lem1208820 {A : Type'} (x : A) : (term143 A x) = (term163 A x).
Proof. exact (fun_ext (fun a0 : A => @lem1208815 A a0 x)). Qed.
Lemma lem1208821 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1208822 {A : Type'} (x : A) : (term145 A x) = (term164 A x).
Proof. exact (MK_COMB (@lem1208821 A) (@lem1208820 A x)). Qed.
Lemma lem1208827 {A : Type'} (x : A) : (term147 A x) = (term165 A x).
Proof. exact (MK_COMB (@lem1208756 A x) (@lem1208822 A x)). Qed.
Lemma lem1208829 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1208830 {A : Type'} (x : A) : (term165 A x) = (term164 A x).
Proof. exact (@lem1208829 (term164 A x)). Qed.
Lemma lem1208873 {A : Type'} (x : A) : (term147 A x) = (term164 A x).
Proof. exact (TRANS (@lem1208827 A x) (@lem1208830 A x)). Qed.
Lemma lem1208874 {A : Type'} (x : A) : (term164 A x) = (term147 A x).
Proof. exact (SYM (@lem1208873 A x)). Qed.
Lemma lem1208876 (p : Prop) : p = (term166 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1208877 {A : Type'} (y : A) (l : list A) (x : A) : (term160 A y l x) = (term167 A y l x).
Proof. exact (@lem1208876 (term160 A y l x)). Qed.
Lemma lem1208878 {A : Type'} (y : A) (l : list A) (x : A) : (term167 A y l x) = (term160 A y l x).
Proof. exact (SYM (@lem1208877 A y l x)). Qed.
Lemma lem1208879 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term168 A y l x) : term168 A y l x.
Proof. exact (h1). Qed.
Lemma lem1208880 {A : Type'} : term2 A.
Proof. exact (@lem1208012 A). Qed.
Lemma lem1208883 {A : Type'} : term169 A.
Proof. exact (@lem1208012 (list A)). Qed.
Lemma lem1208884 {A : Type'} : term170 A.
Proof. exact (@lem1095965 A). Qed.
Lemma lem1208886 {A : Type'} : term171 A.
Proof. exact (@lem1095965 (list A)). Qed.
Lemma lem1208892 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term172 A y l x) : term172 A y l x.
Proof. exact (h1). Qed.
Lemma lem1208893 {A : Type'} (y : A) (l : list A) (x : A) : term173 A y l x.
Proof. exact (fun h0 : term172 A y l x => @lem1208892 A y l x h0). Qed.
Lemma lem1208894 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term173 A y l x) : term173 A y l x.
Proof. exact (h1). Qed.
Lemma lem1208895 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term172 A y l x) : term172 A y l x.
Proof. exact (h1). Qed.
Lemma lem1208896 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term172 A y l x) (h2 : term173 A y l x) : term172 A y l x.
Proof. exact (@lem1208894 A y l x h2 (@lem1208895 A y l x h1)). Qed.
Lemma lem1208897 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term172 A y l x) : term174 A y l x.
Proof. exact (fun h0 : term173 A y l x => @lem1208896 A y l x h1 h0). Qed.
Lemma lem1208898 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term173 A y l x) : term173 A y l x.
Proof. exact (h1). Qed.
Lemma lem1208899 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term172 A y l x) (h2 : term173 A y l x) : term172 A y l x.
Proof. exact (@lem1208897 A y l x h1 (@lem1208898 A y l x h2)). Qed.
Lemma lem1208900 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term173 A y l x) : term173 A y l x.
Proof. exact (fun h0 : term172 A y l x => @lem1208899 A y l x h0 h1). Qed.
Lemma lem1208901 {A : Type'} (y : A) (l : list A) (x : A) : term175 A y l x.
Proof. exact (fun h0 : term173 A y l x => @lem1208900 A y l x h0). Qed.
Lemma lem1208904 {A : Type'} (y : A) (l : list A) (x : A) : term173 A y l x.
Proof. exact (@lem1208901 A y l x (@lem1208893 A y l x)). Qed.
Lemma lem1208905 {A : Type'} (y : A) (l : list A) (x : A) : term173 A y l x.
Proof. exact (@lem1208904 A y l x). Qed.
Lemma lem1208931 {A : Type'} (P : Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem1208932 {A : Type'} (P : Prop) (Q : type1143 A) : (term178 A P Q) = (term179 A P Q).
Proof. exact (@lem1208931 (list A) P Q). Qed.
Lemma lem1208933 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term180 A l l1 x) = (term181 A l l1 x).
Proof. exact (@lem1208932 A (term100 A x l1) (term182 A l l1 x)). Qed.
Lemma lem1208934 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1208935 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1208936 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term185 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (MK_COMB (@lem1208935 A x l1) (@lem1208934 A l l1 x l2)). Qed.
Lemma lem1208937 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term186 A l l1 x) = (term75 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1208936 A l l1 x l2)). Qed.
Lemma lem1208938 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1208939 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term180 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1208938 A) (@lem1208937 A l l1 x)). Qed.
Lemma lem1208940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1208941 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term187 A l l1 x) = (term188 A l l1 x).
Proof. exact (MK_COMB (@lem1208940) (@lem1208939 A l l1 x)). Qed.
Lemma lem1208942 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1208943 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term189 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1208942 A l l1 x l2)). Qed.
Lemma lem1208944 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1208945 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term190 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1208944 A) (@lem1208943 A l l1 x)). Qed.
Lemma lem1208946 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1208947 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term181 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1208946 A x l1) (@lem1208945 A l l1 x)). Qed.
Lemma lem1208948 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term180 A l l1 x) = (term181 A l l1 x)) = ((term58 A l l1 x) = (term192 A l l1 x)).
Proof. exact (MK_COMB (@lem1208941 A l l1 x) (@lem1208947 A l l1 x)). Qed.
Lemma lem1208949 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term58 A l l1 x) = (term192 A l l1 x).
Proof. exact (EQ_MP (@lem1208948 A l l1 x) (@lem1208933 A l l1 x)). Qed.
Lemma lem1208956 {A : Type'} (l : list A) (x : A) : (term56 A l x) = (term193 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1208949 A l l1 x)). Qed.
Lemma lem1208957 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1208958 {A : Type'} (l : list A) (x : A) : (term42 A l x) = (term194 A l x).
Proof. exact (MK_COMB (@lem1208957 A) (@lem1208956 A l x)). Qed.
Lemma lem1209007 {A : Type'} (x : A) (l : list A) : (term195 A x l) = (term195 A x l).
Proof. exact (eq_refl (term195 A x l)). Qed.
Lemma lem1209008 {A : Type'} (l : list A) (x : A) : (term121 A l x) = (term196 A l x).
Proof. exact (MK_COMB (@lem1209007 A x l) (@lem1208958 A l x)). Qed.
Lemma lem1209011 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209012 {A : Type'} (l : list A) (x : A) : (term133 A l x) = (term197 A l x).
Proof. exact (MK_COMB (@lem1209011) (@lem1209008 A l x)). Qed.
Lemma lem1209022 {A : Type'} (P : Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem1209023 {A : Type'} (P : Prop) (Q : type1143 A) : (term178 A P Q) = (term179 A P Q).
Proof. exact (@lem1209022 (list A) P Q). Qed.
Lemma lem1209024 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term198 A y l l1 x) = (term199 A y l l1 x).
Proof. exact (@lem1209023 A (term100 A x l1) (term200 A y l l1 x)). Qed.
Lemma lem1209025 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term201 A y l l1 x l2) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl (term201 A y l l1 x l2)). Qed.
Lemma lem1209026 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1209027 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term202 A y l l1 x l2) = (term203 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1209026 A x l1) (@lem1209025 A y l l1 x l2)). Qed.
Lemma lem1209028 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term204 A y l l1 x) = (term205 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1209027 A y l l1 x l2)). Qed.
Lemma lem1209029 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209030 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term198 A y l l1 x) = (term206 A y l l1 x).
Proof. exact (MK_COMB (@lem1209029 A) (@lem1209028 A y l l1 x)). Qed.
Lemma lem1209031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1209032 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term207 A y l l1 x) = (term208 A y l l1 x).
Proof. exact (MK_COMB (@lem1209031) (@lem1209030 A y l l1 x)). Qed.
Lemma lem1209033 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term201 A y l l1 x l2) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl (term201 A y l l1 x l2)). Qed.
Lemma lem1209034 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term209 A y l l1 x) = (term200 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1209033 A y l l1 x l2)). Qed.
Lemma lem1209035 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209036 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term210 A y l l1 x) = (term211 A y l l1 x).
Proof. exact (MK_COMB (@lem1209035 A) (@lem1209034 A y l l1 x)). Qed.
Lemma lem1209037 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1209038 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term199 A y l l1 x) = (term212 A y l l1 x).
Proof. exact (MK_COMB (@lem1209037 A x l1) (@lem1209036 A y l l1 x)). Qed.
Lemma lem1209039 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : ((term198 A y l l1 x) = (term199 A y l l1 x)) = ((term206 A y l l1 x) = (term212 A y l l1 x)).
Proof. exact (MK_COMB (@lem1209032 A y l l1 x) (@lem1209038 A y l l1 x)). Qed.
Lemma lem1209040 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term206 A y l l1 x) = (term212 A y l l1 x).
Proof. exact (EQ_MP (@lem1209039 A y l l1 x) (@lem1209024 A y l l1 x)). Qed.
Lemma lem1209047 {A : Type'} (y : A) (l : list A) (x : A) : (term213 A y l x) = (term214 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1209040 A y l l1 x)). Qed.
Lemma lem1209048 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209049 {A : Type'} (y : A) (l : list A) (x : A) : (term158 A y l x) = (term215 A y l x).
Proof. exact (MK_COMB (@lem1209048 A) (@lem1209047 A y l x)). Qed.
Lemma lem1209098 {A : Type'} (y : A) (x : A) (l : list A) : (term157 A y x l) = (term157 A y x l).
Proof. exact (eq_refl (term157 A y x l)). Qed.
Lemma lem1209099 {A : Type'} (y : A) (l : list A) (x : A) : (term159 A y l x) = (term216 A y l x).
Proof. exact (MK_COMB (@lem1209098 A y x l) (@lem1209049 A y l x)). Qed.
Lemma lem1209102 {A : Type'} (y : A) (l : list A) (x : A) : (term160 A y l x) = (term217 A y l x).
Proof. exact (MK_COMB (@lem1209012 A l x) (@lem1209099 A y l x)). Qed.
Lemma lem1209105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1209106 {A : Type'} (y : A) (l : list A) (x : A) : (term168 A y l x) = (term218 A y l x).
Proof. exact (MK_COMB (@lem1209105) (@lem1209102 A y l x)). Qed.
Lemma lem1209107 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209108 {A : Type'} (y : A) (l : list A) (x : A) : (term219 A y l x) = (term220 A y l x).
Proof. exact (MK_COMB (@lem1209107) (@lem1209106 A y l x)). Qed.
Lemma lem1209160 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1209161 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1209160 (list A) P Q). Qed.
Lemma lem1209162 {A : Type'} (h : A) (x : A) : (term225 A h x) = (term226 A h x).
Proof. exact (@lem1209161 A (term227 A x) (term228 A h x)). Qed.
Lemma lem1209163 {A : Type'} (t : list A) (x : A) : (term229 A x t) = ((@List.In A x (@nil A)) = False).
Proof. exact (eq_refl (term229 A x t)). Qed.
Lemma lem1209164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209165 {A : Type'} (t : list A) (x : A) : (term230 A x t) = (term231 A x).
Proof. exact (MK_COMB (@lem1209164) (@lem1209163 A t x)). Qed.
Lemma lem1209166 {A : Type'} (h : A) (x : A) (t : list A) : (term232 A h x t) = ((term106 A x h t) = (term107 A h x t)).
Proof. exact (eq_refl (term232 A h x t)). Qed.
Lemma lem1209167 {A : Type'} (h : A) (x : A) (t : list A) : (term233 A h x t) = (term234 A h x t).
Proof. exact (MK_COMB (@lem1209165 A t x) (@lem1209166 A h x t)). Qed.
Lemma lem1209168 {A : Type'} (h : A) (x : A) : (term235 A h x) = (term236 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1209167 A h x t)). Qed.
Lemma lem1209169 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209170 {A : Type'} (h : A) (x : A) : (term225 A h x) = (term0 A h x).
Proof. exact (MK_COMB (@lem1209169 A) (@lem1209168 A h x)). Qed.
Lemma lem1209171 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1209172 {A : Type'} (h : A) (x : A) : (term237 A h x) = (term238 A h x).
Proof. exact (MK_COMB (@lem1209171) (@lem1209170 A h x)). Qed.
Lemma lem1209173 {A : Type'} (t : list A) (x : A) : (term229 A x t) = ((@List.In A x (@nil A)) = False).
Proof. exact (eq_refl (term229 A x t)). Qed.
Lemma lem1209174 {A : Type'} (x : A) : (term239 A x) = (term227 A x).
Proof. exact (fun_ext (fun t : list A => @lem1209173 A t x)). Qed.
Lemma lem1209175 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209176 {A : Type'} (x : A) : (term240 A x) = (term241 A x).
Proof. exact (MK_COMB (@lem1209175 A) (@lem1209174 A x)). Qed.
Lemma lem1209177 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209178 {A : Type'} (x : A) : (term242 A x) = (term243 A x).
Proof. exact (MK_COMB (@lem1209177) (@lem1209176 A x)). Qed.
Lemma lem1209179 {A : Type'} (h : A) (x : A) (t : list A) : (term232 A h x t) = ((term106 A x h t) = (term107 A h x t)).
Proof. exact (eq_refl (term232 A h x t)). Qed.
Lemma lem1209180 {A : Type'} (h : A) (x : A) : (term244 A h x) = (term228 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1209179 A h x t)). Qed.
Lemma lem1209181 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209182 {A : Type'} (h : A) (x : A) : (term245 A h x) = (term246 A h x).
Proof. exact (MK_COMB (@lem1209181 A) (@lem1209180 A h x)). Qed.
Lemma lem1209183 {A : Type'} (h : A) (x : A) : (term226 A h x) = (term247 A h x).
Proof. exact (MK_COMB (@lem1209178 A x) (@lem1209182 A h x)). Qed.
Lemma lem1209184 {A : Type'} (h : A) (x : A) : ((term225 A h x) = (term226 A h x)) = ((term0 A h x) = (term247 A h x)).
Proof. exact (MK_COMB (@lem1209172 A h x) (@lem1209183 A h x)). Qed.
Lemma lem1209185 {A : Type'} (h : A) (x : A) : (term0 A h x) = (term247 A h x).
Proof. exact (EQ_MP (@lem1209184 A h x) (@lem1209162 A h x)). Qed.
Lemma lem1209189 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1209190 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (@lem1209189 (list A) t). Qed.
Lemma lem1209191 {A : Type'} (x : A) : (term241 A x) = ((@List.In A x (@nil A)) = False).
Proof. exact (@lem1209190 A ((@List.In A x (@nil A)) = False)). Qed.
Lemma lem1209193 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem1209194 {A : Type'} (x : A) : ((@List.In A x (@nil A)) = False) = (term248 A x).
Proof. exact (@lem1209193 (@List.In A x (@nil A))). Qed.
Lemma lem1209195 {A : Type'} (x : A) : (term241 A x) = (term248 A x).
Proof. exact (TRANS (@lem1209191 A x) (@lem1209194 A x)). Qed.
Lemma lem1209196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209197 {A : Type'} (x : A) : (term243 A x) = (term249 A x).
Proof. exact (MK_COMB (@lem1209196) (@lem1209195 A x)). Qed.
Lemma lem1209204 {A : Type'} (h : A) (x : A) : (term246 A h x) = (term246 A h x).
Proof. exact (eq_refl (term246 A h x)). Qed.
Lemma lem1209205 {A : Type'} (h : A) (x : A) : (term247 A h x) = (term250 A h x).
Proof. exact (MK_COMB (@lem1209197 A x) (@lem1209204 A h x)). Qed.
Lemma lem1209208 {A : Type'} (h : A) (x : A) : (term0 A h x) = (term250 A h x).
Proof. exact (TRANS (@lem1209185 A h x) (@lem1209205 A h x)). Qed.
Lemma lem1209209 {A : Type'} (h : A) : (term251 A h) = (term252 A h).
Proof. exact (fun_ext (fun x : A => @lem1209208 A h x)). Qed.
Lemma lem1209210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209211 {A : Type'} (h : A) : (term1 A h) = (term253 A h).
Proof. exact (MK_COMB (@lem1209210 A) (@lem1209209 A h)). Qed.
Lemma lem1209213 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1209214 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1209213 A P Q). Qed.
Lemma lem1209215 {A : Type'} (h : A) : (term254 A h) = (term255 A h).
Proof. exact (@lem1209214 A (term256 A) (term257 A h)). Qed.
Lemma lem1209216 {A : Type'} (x : A) : (term258 A x) = (term248 A x).
Proof. exact (eq_refl (term258 A x)). Qed.
Lemma lem1209217 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209218 {A : Type'} (x : A) : (term259 A x) = (term249 A x).
Proof. exact (MK_COMB (@lem1209217) (@lem1209216 A x)). Qed.
Lemma lem1209219 {A : Type'} (h : A) (x : A) : (term260 A h x) = (term246 A h x).
Proof. exact (eq_refl (term260 A h x)). Qed.
Lemma lem1209220 {A : Type'} (h : A) (x : A) : (term261 A h x) = (term250 A h x).
Proof. exact (MK_COMB (@lem1209218 A x) (@lem1209219 A h x)). Qed.
Lemma lem1209221 {A : Type'} (h : A) : (term262 A h) = (term252 A h).
Proof. exact (fun_ext (fun x : A => @lem1209220 A h x)). Qed.
Lemma lem1209222 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209223 {A : Type'} (h : A) : (term254 A h) = (term253 A h).
Proof. exact (MK_COMB (@lem1209222 A) (@lem1209221 A h)). Qed.
Lemma lem1209224 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1209225 {A : Type'} (h : A) : (term263 A h) = (term264 A h).
Proof. exact (MK_COMB (@lem1209224) (@lem1209223 A h)). Qed.
Lemma lem1209226 {A : Type'} (x : A) : (term258 A x) = (term248 A x).
Proof. exact (eq_refl (term258 A x)). Qed.
Lemma lem1209227 {A : Type'} : (term265 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1209226 A x)). Qed.
Lemma lem1209228 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209229 {A : Type'} : (term266 A) = (term267 A).
Proof. exact (MK_COMB (@lem1209228 A) (@lem1209227 A)). Qed.
Lemma lem1209230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209231 {A : Type'} : (term268 A) = (term269 A).
Proof. exact (MK_COMB (@lem1209230) (@lem1209229 A)). Qed.
Lemma lem1209232 {A : Type'} (h : A) (x : A) : (term260 A h x) = (term246 A h x).
Proof. exact (eq_refl (term260 A h x)). Qed.
Lemma lem1209233 {A : Type'} (h : A) : (term270 A h) = (term257 A h).
Proof. exact (fun_ext (fun x : A => @lem1209232 A h x)). Qed.
Lemma lem1209234 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209235 {A : Type'} (h : A) : (term271 A h) = (term272 A h).
Proof. exact (MK_COMB (@lem1209234 A) (@lem1209233 A h)). Qed.
Lemma lem1209236 {A : Type'} (h : A) : (term255 A h) = (term273 A h).
Proof. exact (MK_COMB (@lem1209231 A) (@lem1209235 A h)). Qed.
Lemma lem1209237 {A : Type'} (h : A) : ((term254 A h) = (term255 A h)) = ((term253 A h) = (term273 A h)).
Proof. exact (MK_COMB (@lem1209225 A h) (@lem1209236 A h)). Qed.
Lemma lem1209238 {A : Type'} (h : A) : (term253 A h) = (term273 A h).
Proof. exact (EQ_MP (@lem1209237 A h) (@lem1209215 A h)). Qed.
Lemma lem1209255 {A : Type'} (h : A) : (term1 A h) = (term273 A h).
Proof. exact (TRANS (@lem1209211 A h) (@lem1209238 A h)). Qed.
Lemma lem1209256 {A : Type'} : (term274 A) = (term275 A).
Proof. exact (fun_ext (fun h : A => @lem1209255 A h)). Qed.
Lemma lem1209257 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209258 {A : Type'} : (term2 A) = (term276 A).
Proof. exact (MK_COMB (@lem1209257 A) (@lem1209256 A)). Qed.
Lemma lem1209260 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1209261 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1209260 A P Q). Qed.
Lemma lem1209262 {A : Type'} : (term277 A) = (term278 A).
Proof. exact (@lem1209261 A (term279 A) (term280 A)). Qed.
Lemma lem1209263 {A : Type'} (h : A) : (term281 A h) = (term267 A).
Proof. exact (eq_refl (term281 A h)). Qed.
Lemma lem1209264 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209265 {A : Type'} (h : A) : (term282 A h) = (term269 A).
Proof. exact (MK_COMB (@lem1209264) (@lem1209263 A h)). Qed.
Lemma lem1209266 {A : Type'} (h : A) : (term283 A h) = (term272 A h).
Proof. exact (eq_refl (term283 A h)). Qed.
Lemma lem1209267 {A : Type'} (h : A) : (term284 A h) = (term273 A h).
Proof. exact (MK_COMB (@lem1209265 A h) (@lem1209266 A h)). Qed.
Lemma lem1209268 {A : Type'} : (term285 A) = (term275 A).
Proof. exact (fun_ext (fun h : A => @lem1209267 A h)). Qed.
Lemma lem1209269 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209270 {A : Type'} : (term277 A) = (term276 A).
Proof. exact (MK_COMB (@lem1209269 A) (@lem1209268 A)). Qed.
Lemma lem1209271 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1209272 {A : Type'} : (term286 A) = (term287 A).
Proof. exact (MK_COMB (@lem1209271) (@lem1209270 A)). Qed.
Lemma lem1209273 {A : Type'} (h : A) : (term281 A h) = (term267 A).
Proof. exact (eq_refl (term281 A h)). Qed.
Lemma lem1209274 {A : Type'} : (term288 A) = (term279 A).
Proof. exact (fun_ext (fun h : A => @lem1209273 A h)). Qed.
Lemma lem1209275 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209276 {A : Type'} : (term289 A) = (term290 A).
Proof. exact (MK_COMB (@lem1209275 A) (@lem1209274 A)). Qed.
Lemma lem1209277 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209278 {A : Type'} : (term291 A) = (term292 A).
Proof. exact (MK_COMB (@lem1209277) (@lem1209276 A)). Qed.
Lemma lem1209279 {A : Type'} (h : A) : (term283 A h) = (term272 A h).
Proof. exact (eq_refl (term283 A h)). Qed.
Lemma lem1209280 {A : Type'} : (term293 A) = (term280 A).
Proof. exact (fun_ext (fun h : A => @lem1209279 A h)). Qed.
Lemma lem1209281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209282 {A : Type'} : (term294 A) = (term295 A).
Proof. exact (MK_COMB (@lem1209281 A) (@lem1209280 A)). Qed.
Lemma lem1209283 {A : Type'} : (term278 A) = (term296 A).
Proof. exact (MK_COMB (@lem1209278 A) (@lem1209282 A)). Qed.
Lemma lem1209284 {A : Type'} : ((term277 A) = (term278 A)) = ((term276 A) = (term296 A)).
Proof. exact (MK_COMB (@lem1209272 A) (@lem1209283 A)). Qed.
Lemma lem1209285 {A : Type'} : (term276 A) = (term296 A).
Proof. exact (EQ_MP (@lem1209284 A) (@lem1209262 A)). Qed.
Lemma lem1209289 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1209290 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (@lem1209289 A t). Qed.
Lemma lem1209291 {A : Type'} : (term290 A) = (term267 A).
Proof. exact (@lem1209290 A (term267 A)). Qed.
Lemma lem1209296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209297 {A : Type'} : (term292 A) = (term269 A).
Proof. exact (MK_COMB (@lem1209296) (@lem1209291 A)). Qed.
Lemma lem1209312 {A : Type'} : (term295 A) = (term295 A).
Proof. exact (eq_refl (term295 A)). Qed.
Lemma lem1209313 {A : Type'} : (term296 A) = (term297 A).
Proof. exact (MK_COMB (@lem1209297 A) (@lem1209312 A)). Qed.
Lemma lem1209316 {A : Type'} : (term276 A) = (term297 A).
Proof. exact (TRANS (@lem1209285 A) (@lem1209313 A)). Qed.
Lemma lem1209317 {A : Type'} : (term2 A) = (term297 A).
Proof. exact (TRANS (@lem1209258 A) (@lem1209316 A)). Qed.
Lemma lem1209318 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209319 {A : Type'} : (term298 A) = (term299 A).
Proof. exact (MK_COMB (@lem1209318) (@lem1209317 A)). Qed.
Lemma lem1209321 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1209322 {A : Type'} : (term300 A) = (term301 A).
Proof. exact (@lem1209321 (term169 A)). Qed.
Lemma lem1209332 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1209333 {A : Type'} (P : type1029 A) (Q : type1029 A) : (term302 A P Q) = (term303 A P Q).
Proof. exact (@lem1209332 (type1628 A) P Q). Qed.
Lemma lem1209334 {A : Type'} (h : list A) (x : list A) : (term304 A h x) = (term305 A h x).
Proof. exact (@lem1209333 A (term306 A x) (term307 A h x)). Qed.
Lemma lem1209335 {A : Type'} (t : type1628 A) (x : list A) : (term308 A x t) = ((@List.In (list A) x (@nil (list A))) = False).
Proof. exact (eq_refl (term308 A x t)). Qed.
Lemma lem1209336 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209337 {A : Type'} (t : type1628 A) (x : list A) : (term309 A x t) = (term310 A x).
Proof. exact (MK_COMB (@lem1209336) (@lem1209335 A t x)). Qed.
Lemma lem1209338 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : (term311 A h x t) = ((term312 A x h t) = (term313 A h x t)).
Proof. exact (eq_refl (term311 A h x t)). Qed.
Lemma lem1209339 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : (term314 A h x t) = (term315 A h x t).
Proof. exact (MK_COMB (@lem1209337 A t x) (@lem1209338 A h x t)). Qed.
Lemma lem1209340 {A : Type'} (h : list A) (x : list A) : (term316 A h x) = (term317 A h x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1209339 A h x t)). Qed.
Lemma lem1209341 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1209342 {A : Type'} (h : list A) (x : list A) : (term304 A h x) = (term318 A h x).
Proof. exact (MK_COMB (@lem1209341 A) (@lem1209340 A h x)). Qed.
Lemma lem1209343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1209344 {A : Type'} (h : list A) (x : list A) : (term319 A h x) = (term320 A h x).
Proof. exact (MK_COMB (@lem1209343) (@lem1209342 A h x)). Qed.
Lemma lem1209345 {A : Type'} (t : type1628 A) (x : list A) : (term308 A x t) = ((@List.In (list A) x (@nil (list A))) = False).
Proof. exact (eq_refl (term308 A x t)). Qed.
Lemma lem1209346 {A : Type'} (x : list A) : (term321 A x) = (term306 A x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1209345 A t x)). Qed.
Lemma lem1209347 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1209348 {A : Type'} (x : list A) : (term322 A x) = (term323 A x).
Proof. exact (MK_COMB (@lem1209347 A) (@lem1209346 A x)). Qed.
Lemma lem1209349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209350 {A : Type'} (x : list A) : (term324 A x) = (term325 A x).
Proof. exact (MK_COMB (@lem1209349) (@lem1209348 A x)). Qed.
Lemma lem1209351 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : (term311 A h x t) = ((term312 A x h t) = (term313 A h x t)).
Proof. exact (eq_refl (term311 A h x t)). Qed.
Lemma lem1209352 {A : Type'} (h : list A) (x : list A) : (term326 A h x) = (term307 A h x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1209351 A h x t)). Qed.
Lemma lem1209353 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1209354 {A : Type'} (h : list A) (x : list A) : (term327 A h x) = (term328 A h x).
Proof. exact (MK_COMB (@lem1209353 A) (@lem1209352 A h x)). Qed.
Lemma lem1209355 {A : Type'} (h : list A) (x : list A) : (term305 A h x) = (term329 A h x).
Proof. exact (MK_COMB (@lem1209350 A x) (@lem1209354 A h x)). Qed.
Lemma lem1209356 {A : Type'} (h : list A) (x : list A) : ((term304 A h x) = (term305 A h x)) = ((term318 A h x) = (term329 A h x)).
Proof. exact (MK_COMB (@lem1209344 A h x) (@lem1209355 A h x)). Qed.
Lemma lem1209357 {A : Type'} (h : list A) (x : list A) : (term318 A h x) = (term329 A h x).
Proof. exact (EQ_MP (@lem1209356 A h x) (@lem1209334 A h x)). Qed.
Lemma lem1209361 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1209362 {A : Type'} (t : Prop) : (term330 A t) = t.
Proof. exact (@lem1209361 (type1628 A) t). Qed.
Lemma lem1209363 {A : Type'} (x : list A) : (term323 A x) = ((@List.In (list A) x (@nil (list A))) = False).
Proof. exact (@lem1209362 A ((@List.In (list A) x (@nil (list A))) = False)). Qed.
Lemma lem1209365 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem1209366 {A : Type'} (x : list A) : ((@List.In (list A) x (@nil (list A))) = False) = (term331 A x).
Proof. exact (@lem1209365 (@List.In (list A) x (@nil (list A)))). Qed.
Lemma lem1209367 {A : Type'} (x : list A) : (term323 A x) = (term331 A x).
Proof. exact (TRANS (@lem1209363 A x) (@lem1209366 A x)). Qed.
Lemma lem1209368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209369 {A : Type'} (x : list A) : (term325 A x) = (term332 A x).
Proof. exact (MK_COMB (@lem1209368) (@lem1209367 A x)). Qed.
Lemma lem1209376 {A : Type'} (h : list A) (x : list A) : (term328 A h x) = (term328 A h x).
Proof. exact (eq_refl (term328 A h x)). Qed.
Lemma lem1209377 {A : Type'} (h : list A) (x : list A) : (term329 A h x) = (term333 A h x).
Proof. exact (MK_COMB (@lem1209369 A x) (@lem1209376 A h x)). Qed.
Lemma lem1209380 {A : Type'} (h : list A) (x : list A) : (term318 A h x) = (term333 A h x).
Proof. exact (TRANS (@lem1209357 A h x) (@lem1209377 A h x)). Qed.
Lemma lem1209381 {A : Type'} (h : list A) : (term334 A h) = (term335 A h).
Proof. exact (fun_ext (fun x : list A => @lem1209380 A h x)). Qed.
Lemma lem1209382 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209383 {A : Type'} (h : list A) : (term336 A h) = (term337 A h).
Proof. exact (MK_COMB (@lem1209382 A) (@lem1209381 A h)). Qed.
Lemma lem1209385 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1209386 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1209385 (list A) P Q). Qed.
Lemma lem1209387 {A : Type'} (h : list A) : (term338 A h) = (term339 A h).
Proof. exact (@lem1209386 A (term340 A) (term341 A h)). Qed.
Lemma lem1209388 {A : Type'} (x : list A) : (term342 A x) = (term331 A x).
Proof. exact (eq_refl (term342 A x)). Qed.
Lemma lem1209389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209390 {A : Type'} (x : list A) : (term343 A x) = (term332 A x).
Proof. exact (MK_COMB (@lem1209389) (@lem1209388 A x)). Qed.
Lemma lem1209391 {A : Type'} (h : list A) (x : list A) : (term344 A h x) = (term328 A h x).
Proof. exact (eq_refl (term344 A h x)). Qed.
Lemma lem1209392 {A : Type'} (h : list A) (x : list A) : (term345 A h x) = (term333 A h x).
Proof. exact (MK_COMB (@lem1209390 A x) (@lem1209391 A h x)). Qed.
Lemma lem1209393 {A : Type'} (h : list A) : (term346 A h) = (term335 A h).
Proof. exact (fun_ext (fun x : list A => @lem1209392 A h x)). Qed.
Lemma lem1209394 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209395 {A : Type'} (h : list A) : (term338 A h) = (term337 A h).
Proof. exact (MK_COMB (@lem1209394 A) (@lem1209393 A h)). Qed.
Lemma lem1209396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1209397 {A : Type'} (h : list A) : (term347 A h) = (term348 A h).
Proof. exact (MK_COMB (@lem1209396) (@lem1209395 A h)). Qed.
Lemma lem1209398 {A : Type'} (x : list A) : (term342 A x) = (term331 A x).
Proof. exact (eq_refl (term342 A x)). Qed.
Lemma lem1209399 {A : Type'} : (term349 A) = (term340 A).
Proof. exact (fun_ext (fun x : list A => @lem1209398 A x)). Qed.
Lemma lem1209400 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209401 {A : Type'} : (term350 A) = (term351 A).
Proof. exact (MK_COMB (@lem1209400 A) (@lem1209399 A)). Qed.
Lemma lem1209402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209403 {A : Type'} : (term352 A) = (term353 A).
Proof. exact (MK_COMB (@lem1209402) (@lem1209401 A)). Qed.
Lemma lem1209404 {A : Type'} (h : list A) (x : list A) : (term344 A h x) = (term328 A h x).
Proof. exact (eq_refl (term344 A h x)). Qed.
Lemma lem1209405 {A : Type'} (h : list A) : (term354 A h) = (term341 A h).
Proof. exact (fun_ext (fun x : list A => @lem1209404 A h x)). Qed.
Lemma lem1209406 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209407 {A : Type'} (h : list A) : (term355 A h) = (term356 A h).
Proof. exact (MK_COMB (@lem1209406 A) (@lem1209405 A h)). Qed.
Lemma lem1209408 {A : Type'} (h : list A) : (term339 A h) = (term357 A h).
Proof. exact (MK_COMB (@lem1209403 A) (@lem1209407 A h)). Qed.
Lemma lem1209409 {A : Type'} (h : list A) : ((term338 A h) = (term339 A h)) = ((term337 A h) = (term357 A h)).
Proof. exact (MK_COMB (@lem1209397 A h) (@lem1209408 A h)). Qed.
Lemma lem1209410 {A : Type'} (h : list A) : (term337 A h) = (term357 A h).
Proof. exact (EQ_MP (@lem1209409 A h) (@lem1209387 A h)). Qed.
Lemma lem1209427 {A : Type'} (h : list A) : (term336 A h) = (term357 A h).
Proof. exact (TRANS (@lem1209383 A h) (@lem1209410 A h)). Qed.
Lemma lem1209428 {A : Type'} : (term358 A) = (term359 A).
Proof. exact (fun_ext (fun h : list A => @lem1209427 A h)). Qed.
Lemma lem1209429 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209430 {A : Type'} : (term169 A) = (term360 A).
Proof. exact (MK_COMB (@lem1209429 A) (@lem1209428 A)). Qed.
Lemma lem1209432 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1209433 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1209432 (list A) P Q). Qed.
Lemma lem1209434 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (@lem1209433 A (term363 A) (term364 A)). Qed.
Lemma lem1209435 {A : Type'} (h : list A) : (term365 A h) = (term351 A).
Proof. exact (eq_refl (term365 A h)). Qed.
Lemma lem1209436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209437 {A : Type'} (h : list A) : (term366 A h) = (term353 A).
Proof. exact (MK_COMB (@lem1209436) (@lem1209435 A h)). Qed.
Lemma lem1209438 {A : Type'} (h : list A) : (term367 A h) = (term356 A h).
Proof. exact (eq_refl (term367 A h)). Qed.
Lemma lem1209439 {A : Type'} (h : list A) : (term368 A h) = (term357 A h).
Proof. exact (MK_COMB (@lem1209437 A h) (@lem1209438 A h)). Qed.
Lemma lem1209440 {A : Type'} : (term369 A) = (term359 A).
Proof. exact (fun_ext (fun h : list A => @lem1209439 A h)). Qed.
Lemma lem1209441 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209442 {A : Type'} : (term361 A) = (term360 A).
Proof. exact (MK_COMB (@lem1209441 A) (@lem1209440 A)). Qed.
Lemma lem1209443 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1209444 {A : Type'} : (term370 A) = (term371 A).
Proof. exact (MK_COMB (@lem1209443) (@lem1209442 A)). Qed.
Lemma lem1209445 {A : Type'} (h : list A) : (term365 A h) = (term351 A).
Proof. exact (eq_refl (term365 A h)). Qed.
Lemma lem1209446 {A : Type'} : (term372 A) = (term363 A).
Proof. exact (fun_ext (fun h : list A => @lem1209445 A h)). Qed.
Lemma lem1209447 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209448 {A : Type'} : (term373 A) = (term374 A).
Proof. exact (MK_COMB (@lem1209447 A) (@lem1209446 A)). Qed.
Lemma lem1209449 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209450 {A : Type'} : (term375 A) = (term376 A).
Proof. exact (MK_COMB (@lem1209449) (@lem1209448 A)). Qed.
Lemma lem1209451 {A : Type'} (h : list A) : (term367 A h) = (term356 A h).
Proof. exact (eq_refl (term367 A h)). Qed.
Lemma lem1209452 {A : Type'} : (term377 A) = (term364 A).
Proof. exact (fun_ext (fun h : list A => @lem1209451 A h)). Qed.
Lemma lem1209453 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209454 {A : Type'} : (term378 A) = (term379 A).
Proof. exact (MK_COMB (@lem1209453 A) (@lem1209452 A)). Qed.
Lemma lem1209455 {A : Type'} : (term362 A) = (term380 A).
Proof. exact (MK_COMB (@lem1209450 A) (@lem1209454 A)). Qed.
Lemma lem1209456 {A : Type'} : ((term361 A) = (term362 A)) = ((term360 A) = (term380 A)).
Proof. exact (MK_COMB (@lem1209444 A) (@lem1209455 A)). Qed.
Lemma lem1209457 {A : Type'} : (term360 A) = (term380 A).
Proof. exact (EQ_MP (@lem1209456 A) (@lem1209434 A)). Qed.
Lemma lem1209461 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1209462 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (@lem1209461 (list A) t). Qed.
Lemma lem1209463 {A : Type'} : (term374 A) = (term351 A).
Proof. exact (@lem1209462 A (term351 A)). Qed.
Lemma lem1209468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209469 {A : Type'} : (term376 A) = (term353 A).
Proof. exact (MK_COMB (@lem1209468) (@lem1209463 A)). Qed.
Lemma lem1209484 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (eq_refl (term379 A)). Qed.
Lemma lem1209485 {A : Type'} : (term380 A) = (term381 A).
Proof. exact (MK_COMB (@lem1209469 A) (@lem1209484 A)). Qed.
Lemma lem1209488 {A : Type'} : (term360 A) = (term381 A).
Proof. exact (TRANS (@lem1209457 A) (@lem1209485 A)). Qed.
Lemma lem1209489 {A : Type'} : (term169 A) = (term381 A).
Proof. exact (TRANS (@lem1209430 A) (@lem1209488 A)). Qed.
Lemma lem1209490 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1209491 {A : Type'} : (term301 A) = (term382 A).
Proof. exact (MK_COMB (@lem1209490) (@lem1209489 A)). Qed.
Lemma lem1209492 {A : Type'} : (term300 A) = (term382 A).
Proof. exact (TRANS (@lem1209322 A) (@lem1209491 A)). Qed.
Lemma lem1209493 {A : Type'} : (term383 A) = (term384 A).
Proof. exact (MK_COMB (@lem1209319 A) (@lem1209492 A)). Qed.
Lemma lem1209496 {A : Type'} : (term385 A) = (term385 A).
Proof. exact (eq_refl (term385 A)). Qed.
Lemma lem1209497 {A : Type'} : (term386 A) = (term387 A).
Proof. exact (MK_COMB (@lem1209496 A) (@lem1209493 A)). Qed.
Lemma lem1209500 {A : Type'} : (term388 A) = (term388 A).
Proof. exact (eq_refl (term388 A)). Qed.
Lemma lem1209501 {A : Type'} : (term389 A) = (term390 A).
Proof. exact (MK_COMB (@lem1209500 A) (@lem1209497 A)). Qed.
Lemma lem1209504 {A : Type'} (y : A) (l : list A) (x : A) : (term391 A y l x) = (term392 A y l x).
Proof. exact (MK_COMB (@lem1209108 A y l x) (@lem1209501 A)). Qed.
Lemma lem1209507 {A : Type'} (x : A) (y : A) : (term393 A x y) = (term393 A x y).
Proof. exact (eq_refl (term393 A x y)). Qed.
Lemma lem1209508 {A : Type'} (y : A) (l : list A) (x : A) : (term172 A y l x) = (term394 A y l x).
Proof. exact (MK_COMB (@lem1209507 A x y) (@lem1209504 A y l x)). Qed.
Lemma lem1209511 {A : Type'} (l : list A) (x : A) : (term395 A l x) = (term396 A l x).
Proof. exact (fun_ext (fun y : A => @lem1209508 A y l x)). Qed.
Lemma lem1209512 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209513 {A : Type'} (l : list A) (x : A) : (term397 A l x) = (term398 A l x).
Proof. exact (MK_COMB (@lem1209512 A) (@lem1209511 A l x)). Qed.
Lemma lem1209518 {A : Type'} (x : A) : (term399 A x) = (term400 A x).
Proof. exact (fun_ext (fun l : list A => @lem1209513 A l x)). Qed.
Lemma lem1209519 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209520 {A : Type'} (x : A) : (term401 A x) = (term402 A x).
Proof. exact (MK_COMB (@lem1209519 A) (@lem1209518 A x)). Qed.
Lemma lem1209525 {A : Type'} : (term403 A) = (term404 A).
Proof. exact (fun_ext (fun x : A => @lem1209520 A x)). Qed.
Lemma lem1209526 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209535 {A : Type'} : (term405 A) = (term406 A).
Proof. exact (MK_COMB (@lem1209526 A) (@lem1209525 A)). Qed.
Lemma lem1209544 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : ((term312 A x h t) = (term313 A h x t)) = ((term312 A x h t) = (term313 A h x t)).
Proof. exact (eq_refl ((term312 A x h t) = (term313 A h x t))). Qed.
Lemma lem1209545 {A : Type'} (h : list A) (x : list A) : (term307 A h x) = (term307 A h x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1209544 A h x t)). Qed.
Lemma lem1209546 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1209547 {A : Type'} (h : list A) (x : list A) : (term328 A h x) = (term328 A h x).
Proof. exact (MK_COMB (@lem1209546 A) (@lem1209545 A h x)). Qed.
Lemma lem1209548 {A : Type'} (h : list A) : (term341 A h) = (term341 A h).
Proof. exact (fun_ext (fun x : list A => @lem1209547 A h x)). Qed.
Lemma lem1209549 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209550 {A : Type'} (h : list A) : (term356 A h) = (term356 A h).
Proof. exact (MK_COMB (@lem1209549 A) (@lem1209548 A h)). Qed.
Lemma lem1209551 {A : Type'} : (term364 A) = (term364 A).
Proof. exact (fun_ext (fun h : list A => @lem1209550 A h)). Qed.
Lemma lem1209552 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209553 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (MK_COMB (@lem1209552 A) (@lem1209551 A)). Qed.
Lemma lem1209556 {A : Type'} (x : list A) : (term331 A x) = (term331 A x).
Proof. exact (eq_refl (term331 A x)). Qed.
Lemma lem1209557 {A : Type'} : (term340 A) = (term340 A).
Proof. exact (fun_ext (fun x : list A => @lem1209556 A x)). Qed.
Lemma lem1209558 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209559 {A : Type'} : (term351 A) = (term351 A).
Proof. exact (MK_COMB (@lem1209558 A) (@lem1209557 A)). Qed.
Lemma lem1209560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209561 {A : Type'} : (term353 A) = (term353 A).
Proof. exact (MK_COMB (@lem1209560) (@lem1209559 A)). Qed.
Lemma lem1209562 {A : Type'} : (term381 A) = (term381 A).
Proof. exact (MK_COMB (@lem1209561 A) (@lem1209553 A)). Qed.
Lemma lem1209563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1209564 {A : Type'} : (term382 A) = (term382 A).
Proof. exact (MK_COMB (@lem1209563) (@lem1209562 A)). Qed.
Lemma lem1209573 {A : Type'} (h : A) (x : A) (t : list A) : ((term106 A x h t) = (term107 A h x t)) = ((term106 A x h t) = (term107 A h x t)).
Proof. exact (eq_refl ((term106 A x h t) = (term107 A h x t))). Qed.
Lemma lem1209574 {A : Type'} (h : A) (x : A) : (term228 A h x) = (term228 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1209573 A h x t)). Qed.
Lemma lem1209575 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209576 {A : Type'} (h : A) (x : A) : (term246 A h x) = (term246 A h x).
Proof. exact (MK_COMB (@lem1209575 A) (@lem1209574 A h x)). Qed.
Lemma lem1209577 {A : Type'} (h : A) : (term257 A h) = (term257 A h).
Proof. exact (fun_ext (fun x : A => @lem1209576 A h x)). Qed.
Lemma lem1209578 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209579 {A : Type'} (h : A) : (term272 A h) = (term272 A h).
Proof. exact (MK_COMB (@lem1209578 A) (@lem1209577 A h)). Qed.
Lemma lem1209580 {A : Type'} : (term280 A) = (term280 A).
Proof. exact (fun_ext (fun h : A => @lem1209579 A h)). Qed.
Lemma lem1209581 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209582 {A : Type'} : (term295 A) = (term295 A).
Proof. exact (MK_COMB (@lem1209581 A) (@lem1209580 A)). Qed.
Lemma lem1209585 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1209586 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1209585 A x)). Qed.
Lemma lem1209587 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209588 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1209587 A) (@lem1209586 A)). Qed.
Lemma lem1209589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209590 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (MK_COMB (@lem1209589) (@lem1209588 A)). Qed.
Lemma lem1209591 {A : Type'} : (term297 A) = (term297 A).
Proof. exact (MK_COMB (@lem1209590 A) (@lem1209582 A)). Qed.
Lemma lem1209592 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209593 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (MK_COMB (@lem1209592) (@lem1209591 A)). Qed.
Lemma lem1209594 {A : Type'} : (term384 A) = (term384 A).
Proof. exact (MK_COMB (@lem1209593 A) (@lem1209564 A)). Qed.
Lemma lem1209595 {A : Type'} (h : list A) (t : type1628 A) (l : type1628 A) : ((term407 A h t l) = (term408 A h t l)) = ((term407 A h t l) = (term408 A h t l)).
Proof. exact (eq_refl ((term407 A h t l) = (term408 A h t l))). Qed.
Lemma lem1209596 {A : Type'} (h : list A) (t : type1628 A) : (term409 A h t) = (term409 A h t).
Proof. exact (fun_ext (fun l : type1628 A => @lem1209595 A h t l)). Qed.
Lemma lem1209597 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1209598 {A : Type'} (h : list A) (t : type1628 A) : (term410 A h t) = (term410 A h t).
Proof. exact (MK_COMB (@lem1209597 A) (@lem1209596 A h t)). Qed.
Lemma lem1209599 {A : Type'} (h : list A) : (term411 A h) = (term411 A h).
Proof. exact (fun_ext (fun t : type1628 A => @lem1209598 A h t)). Qed.
Lemma lem1209600 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1209601 {A : Type'} (h : list A) : (term412 A h) = (term412 A h).
Proof. exact (MK_COMB (@lem1209600 A) (@lem1209599 A h)). Qed.
Lemma lem1209602 {A : Type'} : (term413 A) = (term413 A).
Proof. exact (fun_ext (fun h : list A => @lem1209601 A h)). Qed.
Lemma lem1209603 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209604 {A : Type'} : (term414 A) = (term414 A).
Proof. exact (MK_COMB (@lem1209603 A) (@lem1209602 A)). Qed.
Lemma lem1209605 {A : Type'} (l : type1628 A) : ((@List.app (list A) (@nil (list A)) l) = l) = ((@List.app (list A) (@nil (list A)) l) = l).
Proof. exact (eq_refl ((@List.app (list A) (@nil (list A)) l) = l)). Qed.
Lemma lem1209606 {A : Type'} : (term415 A) = (term415 A).
Proof. exact (fun_ext (fun l : type1628 A => @lem1209605 A l)). Qed.
Lemma lem1209607 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1209608 {A : Type'} : (term416 A) = (term416 A).
Proof. exact (MK_COMB (@lem1209607 A) (@lem1209606 A)). Qed.
Lemma lem1209609 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209610 {A : Type'} : (term417 A) = (term417 A).
Proof. exact (MK_COMB (@lem1209609) (@lem1209608 A)). Qed.
Lemma lem1209611 {A : Type'} : (term171 A) = (term171 A).
Proof. exact (MK_COMB (@lem1209610 A) (@lem1209604 A)). Qed.
Lemma lem1209612 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209613 {A : Type'} : (term385 A) = (term385 A).
Proof. exact (MK_COMB (@lem1209612) (@lem1209611 A)). Qed.
Lemma lem1209614 {A : Type'} : (term387 A) = (term387 A).
Proof. exact (MK_COMB (@lem1209613 A) (@lem1209594 A)). Qed.
Lemma lem1209615 {A : Type'} (h : A) (t : list A) (l : list A) : ((term418 A h t l) = (term419 A h t l)) = ((term418 A h t l) = (term419 A h t l)).
Proof. exact (eq_refl ((term418 A h t l) = (term419 A h t l))). Qed.
Lemma lem1209616 {A : Type'} (h : A) (t : list A) : (term420 A h t) = (term420 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1209615 A h t l)). Qed.
Lemma lem1209617 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209618 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term421 A h t).
Proof. exact (MK_COMB (@lem1209617 A) (@lem1209616 A h t)). Qed.
Lemma lem1209619 {A : Type'} (h : A) : (term422 A h) = (term422 A h).
Proof. exact (fun_ext (fun t : list A => @lem1209618 A h t)). Qed.
Lemma lem1209620 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209621 {A : Type'} (h : A) : (term423 A h) = (term423 A h).
Proof. exact (MK_COMB (@lem1209620 A) (@lem1209619 A h)). Qed.
Lemma lem1209622 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun h : A => @lem1209621 A h)). Qed.
Lemma lem1209623 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209624 {A : Type'} : (term425 A) = (term425 A).
Proof. exact (MK_COMB (@lem1209623 A) (@lem1209622 A)). Qed.
Lemma lem1209625 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1209626 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1209625 A l)). Qed.
Lemma lem1209627 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209628 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1209627 A) (@lem1209626 A)). Qed.
Lemma lem1209629 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209630 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (MK_COMB (@lem1209629) (@lem1209628 A)). Qed.
Lemma lem1209631 {A : Type'} : (term170 A) = (term170 A).
Proof. exact (MK_COMB (@lem1209630 A) (@lem1209624 A)). Qed.
Lemma lem1209632 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209633 {A : Type'} : (term388 A) = (term388 A).
Proof. exact (MK_COMB (@lem1209632) (@lem1209631 A)). Qed.
Lemma lem1209634 {A : Type'} : (term390 A) = (term390 A).
Proof. exact (MK_COMB (@lem1209633 A) (@lem1209614 A)). Qed.
Lemma lem1209635 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : ((@cons A y l) = (term102 A l1 x l2)) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl ((@cons A y l) = (term102 A l1 x l2))). Qed.
Lemma lem1209636 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term200 A y l l1 x) = (term200 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1209635 A y l l1 x l2)). Qed.
Lemma lem1209637 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209638 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term211 A y l l1 x) = (term211 A y l l1 x).
Proof. exact (MK_COMB (@lem1209637 A) (@lem1209636 A y l l1 x)). Qed.
Lemma lem1209643 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1209644 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term212 A y l l1 x) = (term212 A y l l1 x).
Proof. exact (MK_COMB (@lem1209643 A x l1) (@lem1209638 A y l l1 x)). Qed.
Lemma lem1209645 {A : Type'} (y : A) (l : list A) (x : A) : (term214 A y l x) = (term214 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1209644 A y l l1 x)). Qed.
Lemma lem1209646 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209647 {A : Type'} (y : A) (l : list A) (x : A) : (term215 A y l x) = (term215 A y l x).
Proof. exact (MK_COMB (@lem1209646 A) (@lem1209645 A y l x)). Qed.
Lemma lem1209654 {A : Type'} (y : A) (x : A) (l : list A) : (term157 A y x l) = (term157 A y x l).
Proof. exact (eq_refl (term157 A y x l)). Qed.
Lemma lem1209655 {A : Type'} (y : A) (l : list A) (x : A) : (term216 A y l x) = (term216 A y l x).
Proof. exact (MK_COMB (@lem1209654 A y x l) (@lem1209647 A y l x)). Qed.
Lemma lem1209656 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term102 A l1 x l2)) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (l = (term102 A l1 x l2))). Qed.
Lemma lem1209657 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term182 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1209656 A l l1 x l2)). Qed.
Lemma lem1209658 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209659 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term191 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1209658 A) (@lem1209657 A l l1 x)). Qed.
Lemma lem1209664 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1209665 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term192 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1209664 A x l1) (@lem1209659 A l l1 x)). Qed.
Lemma lem1209666 {A : Type'} (l : list A) (x : A) : (term193 A l x) = (term193 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1209665 A l l1 x)). Qed.
Lemma lem1209667 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209668 {A : Type'} (l : list A) (x : A) : (term194 A l x) = (term194 A l x).
Proof. exact (MK_COMB (@lem1209667 A) (@lem1209666 A l x)). Qed.
Lemma lem1209671 {A : Type'} (x : A) (l : list A) : (term195 A x l) = (term195 A x l).
Proof. exact (eq_refl (term195 A x l)). Qed.
Lemma lem1209672 {A : Type'} (l : list A) (x : A) : (term196 A l x) = (term196 A l x).
Proof. exact (MK_COMB (@lem1209671 A x l) (@lem1209668 A l x)). Qed.
Lemma lem1209673 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209674 {A : Type'} (l : list A) (x : A) : (term197 A l x) = (term197 A l x).
Proof. exact (MK_COMB (@lem1209673) (@lem1209672 A l x)). Qed.
Lemma lem1209675 {A : Type'} (y : A) (l : list A) (x : A) : (term217 A y l x) = (term217 A y l x).
Proof. exact (MK_COMB (@lem1209674 A l x) (@lem1209655 A y l x)). Qed.
Lemma lem1209676 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1209677 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term218 A y l x).
Proof. exact (MK_COMB (@lem1209676) (@lem1209675 A y l x)). Qed.
Lemma lem1209678 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1209679 {A : Type'} (y : A) (l : list A) (x : A) : (term220 A y l x) = (term220 A y l x).
Proof. exact (MK_COMB (@lem1209678) (@lem1209677 A y l x)). Qed.
Lemma lem1209680 {A : Type'} (y : A) (l : list A) (x : A) : (term392 A y l x) = (term392 A y l x).
Proof. exact (MK_COMB (@lem1209679 A y l x) (@lem1209634 A)). Qed.
Lemma lem1209683 {A : Type'} (x : A) (y : A) : (term393 A x y) = (term393 A x y).
Proof. exact (eq_refl (term393 A x y)). Qed.
Lemma lem1209684 {A : Type'} (y : A) (l : list A) (x : A) : (term394 A y l x) = (term394 A y l x).
Proof. exact (MK_COMB (@lem1209683 A x y) (@lem1209680 A y l x)). Qed.
Lemma lem1209685 {A : Type'} (l : list A) (x : A) : (term396 A l x) = (term396 A l x).
Proof. exact (fun_ext (fun y : A => @lem1209684 A y l x)). Qed.
Lemma lem1209686 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209687 {A : Type'} (l : list A) (x : A) : (term398 A l x) = (term398 A l x).
Proof. exact (MK_COMB (@lem1209686 A) (@lem1209685 A l x)). Qed.
Lemma lem1209688 {A : Type'} (x : A) : (term400 A x) = (term400 A x).
Proof. exact (fun_ext (fun l : list A => @lem1209687 A l x)). Qed.
Lemma lem1209689 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209690 {A : Type'} (x : A) : (term402 A x) = (term402 A x).
Proof. exact (MK_COMB (@lem1209689 A) (@lem1209688 A x)). Qed.
Lemma lem1209691 {A : Type'} : (term404 A) = (term404 A).
Proof. exact (fun_ext (fun x : A => @lem1209690 A x)). Qed.
Lemma lem1209692 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1209693 {A : Type'} : (term406 A) = (term406 A).
Proof. exact (MK_COMB (@lem1209692 A) (@lem1209691 A)). Qed.
Lemma lem1209868 {A : Type'} : (term405 A) = (term406 A).
Proof. exact (TRANS (@lem1209535 A) (@lem1209693 A)). Qed.
Lemma lem1209869 {A : Type'} : (term406 A) = (term405 A).
Proof. exact (SYM (@lem1209868 A)). Qed.
Lemma lem1209871 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term218 A y l x) : term218 A y l x.
Proof. exact (h1). Qed.
Lemma lem1209872 {A : Type'} (h1 : term170 A) : term170 A.
Proof. exact (h1). Qed.
Lemma lem1209874 {A : Type'} (h1 : term297 A) : term297 A.
Proof. exact (h1). Qed.
Lemma lem1209881 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1209884 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term102 A l1 x l2)) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (l = (term102 A l1 x l2))). Qed.
Lemma lem1209885 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term182 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1209884 A l l1 x l2)). Qed.
Lemma lem1209886 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209887 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term191 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1209886 A) (@lem1209885 A l l1 x)). Qed.
Lemma lem1209889 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1209890 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term192 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1209889 A x l1) (@lem1209887 A l l1 x)). Qed.
Lemma lem1209891 {A : Type'} (l : list A) (x : A) : (term193 A l x) = (term193 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1209890 A l l1 x)). Qed.
Lemma lem1209892 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1209893 {A : Type'} (l : list A) (x : A) : (term194 A l x) = (term194 A l x).
Proof. exact (MK_COMB (@lem1209892 A) (@lem1209891 A l x)). Qed.
Lemma lem1209895 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1209896 {A : Type'} (l : list A) (x : A) : (term430 A l x) = (term430 A l x).
Proof. exact (MK_COMB (@lem1209895 A x l) (@lem1209893 A l x)). Qed.
Lemma lem1209897 {A : Type'} (l : list A) (x : A) : (term196 A l x) = (term430 A l x).
Proof. exact (@lem17265 (@List.In A x l) (term194 A l x)). Qed.
Lemma lem1209898 {A : Type'} (l : list A) (x : A) : (term196 A l x) = (term430 A l x).
Proof. exact (TRANS (@lem1209897 A l x) (@lem1209896 A l x)). Qed.
Lemma lem1209906 {A : Type'} (x : A) (l1 : list A) : (term431 A x l1) = (@List.In A x l1).
Proof. exact (@lem16933 (@List.In A x l1)). Qed.
Lemma lem1209908 {A : Type'} (P : type1143 A) : (term432 A P) = (term433 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1209909 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term434 A y l l1 x) = (term435 A y l l1 x).
Proof. exact (@lem1209908 A (term200 A y l l1 x)). Qed.
Lemma lem1209910 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term201 A y l l1 x l2) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl (term201 A y l l1 x l2)). Qed.
Lemma lem1209911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1209913 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term436 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1209911) (@lem1209910 A y l l1 x l2)). Qed.
Lemma lem1209914 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term438 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1209913 A y l l1 x l2)). Qed.
Lemma lem1209915 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209916 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term435 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1209915 A) (@lem1209914 A y l l1 x)). Qed.
Lemma lem1209917 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term434 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (TRANS (@lem1209909 A y l l1 x) (@lem1209916 A y l l1 x)). Qed.
Lemma lem1209918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1209919 {A : Type'} (x : A) (l1 : list A) : (term441 A x l1) = (term105 A x l1).
Proof. exact (MK_COMB (@lem1209918) (@lem1209906 A x l1)). Qed.
Lemma lem1209920 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term442 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1209919 A x l1) (@lem1209917 A y l l1 x)). Qed.
Lemma lem1209921 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term444 A y l l1 x) = (term442 A y l l1 x).
Proof. exact (@lem17045 (term100 A x l1) (term211 A y l l1 x)). Qed.
Lemma lem1209922 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term444 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (TRANS (@lem1209921 A y l l1 x) (@lem1209920 A y l l1 x)). Qed.
Lemma lem1209923 {A : Type'} (P : type1143 A) : (term432 A P) = (term433 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1209924 {A : Type'} (y : A) (l : list A) (x : A) : (term445 A y l x) = (term446 A y l x).
Proof. exact (@lem1209923 A (term214 A y l x)). Qed.
Lemma lem1209925 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term447 A y l x l1) = (term212 A y l l1 x).
Proof. exact (eq_refl (term447 A y l x l1)). Qed.
Lemma lem1209926 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1209927 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term448 A y l x l1) = (term444 A y l l1 x).
Proof. exact (MK_COMB (@lem1209926) (@lem1209925 A y l l1 x)). Qed.
Lemma lem1209928 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term448 A y l x l1) = (term443 A y l l1 x).
Proof. exact (TRANS (@lem1209927 A y l l1 x) (@lem1209922 A y l l1 x)). Qed.
Lemma lem1209929 {A : Type'} (y : A) (l : list A) (x : A) : (term449 A y l x) = (term450 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1209928 A y l l1 x)). Qed.
Lemma lem1209930 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1209931 {A : Type'} (y : A) (l : list A) (x : A) : (term446 A y l x) = (term451 A y l x).
Proof. exact (MK_COMB (@lem1209930 A) (@lem1209929 A y l x)). Qed.
Lemma lem1209932 {A : Type'} (y : A) (l : list A) (x : A) : (term445 A y l x) = (term451 A y l x).
Proof. exact (TRANS (@lem1209924 A y l x) (@lem1209931 A y l x)). Qed.
Lemma lem1209934 {A : Type'} (y : A) (x : A) (l : list A) : (term452 A y x l) = (term452 A y x l).
Proof. exact (eq_refl (term452 A y x l)). Qed.
Lemma lem1209935 {A : Type'} (y : A) (l : list A) (x : A) : (term453 A y l x) = (term454 A y l x).
Proof. exact (MK_COMB (@lem1209934 A y x l) (@lem1209932 A y l x)). Qed.
Lemma lem1209936 {A : Type'} (y : A) (l : list A) (x : A) : (term455 A y l x) = (term453 A y l x).
Proof. exact (@lem17362 (term107 A y x l) (term215 A y l x)). Qed.
Lemma lem1209937 {A : Type'} (y : A) (l : list A) (x : A) : (term455 A y l x) = (term454 A y l x).
Proof. exact (TRANS (@lem1209936 A y l x) (@lem1209935 A y l x)). Qed.
Lemma lem1209938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1209939 {A : Type'} (l : list A) (x : A) : (term456 A l x) = (term457 A l x).
Proof. exact (MK_COMB (@lem1209938) (@lem1209898 A l x)). Qed.
Lemma lem1209940 {A : Type'} (y : A) (l : list A) (x : A) : (term458 A y l x) = (term459 A y l x).
Proof. exact (MK_COMB (@lem1209939 A l x) (@lem1209937 A y l x)). Qed.
Lemma lem1209941 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term458 A y l x).
Proof. exact (@lem17362 (term196 A l x) (term216 A y l x)). Qed.
Lemma lem1209942 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term459 A y l x).
Proof. exact (TRANS (@lem1209941 A y l x) (@lem1209940 A y l x)). Qed.
Lemma lem1210049 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1210050 {A : Type'} (P : Prop) (Q : type1143 A) : (term179 A P Q) = (term178 A P Q).
Proof. exact (@lem1210049 (list A) P Q). Qed.
Lemma lem1210051 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term181 A l l1 x) = (term180 A l l1 x).
Proof. exact (@lem1210050 A (term100 A x l1) (term182 A l l1 x)). Qed.
Lemma lem1210052 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1210053 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term189 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1210052 A l l1 x l2)). Qed.
Lemma lem1210054 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210055 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term190 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1210054 A) (@lem1210053 A l l1 x)). Qed.
Lemma lem1210056 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1210057 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term181 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1210056 A x l1) (@lem1210055 A l l1 x)). Qed.
Lemma lem1210058 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210059 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term460 A l l1 x) = (term461 A l l1 x).
Proof. exact (MK_COMB (@lem1210058) (@lem1210057 A l l1 x)). Qed.
Lemma lem1210060 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1210061 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1210062 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term185 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (MK_COMB (@lem1210061 A x l1) (@lem1210060 A l l1 x l2)). Qed.
Lemma lem1210063 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term186 A l l1 x) = (term75 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1210062 A l l1 x l2)). Qed.
Lemma lem1210064 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210065 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term180 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1210064 A) (@lem1210063 A l l1 x)). Qed.
Lemma lem1210066 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term181 A l l1 x) = (term180 A l l1 x)) = ((term192 A l l1 x) = (term58 A l l1 x)).
Proof. exact (MK_COMB (@lem1210059 A l l1 x) (@lem1210065 A l l1 x)). Qed.
Lemma lem1210067 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term192 A l l1 x) = (term58 A l l1 x).
Proof. exact (EQ_MP (@lem1210066 A l l1 x) (@lem1210051 A l l1 x)). Qed.
Lemma lem1210068 {A : Type'} (l : list A) (x : A) : (term193 A l x) = (term56 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1210067 A l l1 x)). Qed.
Lemma lem1210069 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210070 {A : Type'} (l : list A) (x : A) : (term194 A l x) = (term42 A l x).
Proof. exact (MK_COMB (@lem1210069 A) (@lem1210068 A l x)). Qed.
Lemma lem1210071 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1210072 {A : Type'} (l : list A) (x : A) : (term430 A l x) = (term462 A l x).
Proof. exact (MK_COMB (@lem1210071 A x l) (@lem1210070 A l x)). Qed.
Lemma lem1210074 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1210075 {A : Type'} (P : Prop) (Q : type1143 A) : (term465 A P Q) = (term466 A P Q).
Proof. exact (@lem1210074 (list A) P Q). Qed.
Lemma lem1210076 {A : Type'} (l : list A) (x : A) : (term467 A l x) = (term468 A l x).
Proof. exact (@lem1210075 A (term100 A x l) (term56 A l x)). Qed.
Lemma lem1210077 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term57 A l x l1) = (term58 A l l1 x).
Proof. exact (eq_refl (term57 A l x l1)). Qed.
Lemma lem1210078 {A : Type'} (l : list A) (x : A) : (term59 A l x) = (term56 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1210077 A l l1 x)). Qed.
Lemma lem1210079 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210080 {A : Type'} (l : list A) (x : A) : (term60 A l x) = (term42 A l x).
Proof. exact (MK_COMB (@lem1210079 A) (@lem1210078 A l x)). Qed.
Lemma lem1210081 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1210082 {A : Type'} (l : list A) (x : A) : (term467 A l x) = (term462 A l x).
Proof. exact (MK_COMB (@lem1210081 A x l) (@lem1210080 A l x)). Qed.
Lemma lem1210083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210084 {A : Type'} (l : list A) (x : A) : (term469 A l x) = (term470 A l x).
Proof. exact (MK_COMB (@lem1210083) (@lem1210082 A l x)). Qed.
Lemma lem1210085 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term57 A l x l1) = (term58 A l l1 x).
Proof. exact (eq_refl (term57 A l x l1)). Qed.
Lemma lem1210086 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1210087 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term471 A l x l1) = (term472 A l l1 x).
Proof. exact (MK_COMB (@lem1210086 A x l) (@lem1210085 A l l1 x)). Qed.
Lemma lem1210088 {A : Type'} (l : list A) (x : A) : (term473 A l x) = (term474 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1210087 A l l1 x)). Qed.
Lemma lem1210089 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210090 {A : Type'} (l : list A) (x : A) : (term468 A l x) = (term475 A l x).
Proof. exact (MK_COMB (@lem1210089 A) (@lem1210088 A l x)). Qed.
Lemma lem1210091 {A : Type'} (l : list A) (x : A) : ((term467 A l x) = (term468 A l x)) = ((term462 A l x) = (term475 A l x)).
Proof. exact (MK_COMB (@lem1210084 A l x) (@lem1210090 A l x)). Qed.
Lemma lem1210092 {A : Type'} (l : list A) (x : A) : (term462 A l x) = (term475 A l x).
Proof. exact (EQ_MP (@lem1210091 A l x) (@lem1210076 A l x)). Qed.
Lemma lem1210094 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1210095 {A : Type'} (P : Prop) (Q : type1143 A) : (term465 A P Q) = (term466 A P Q).
Proof. exact (@lem1210094 (list A) P Q). Qed.
Lemma lem1210096 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term476 A l l1 x) = (term477 A l l1 x).
Proof. exact (@lem1210095 A (term100 A x l) (term75 A l l1 x)). Qed.
Lemma lem1210097 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term76 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (eq_refl (term76 A l l1 x l2)). Qed.
Lemma lem1210098 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term78 A l l1 x) = (term75 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1210097 A l l1 x l2)). Qed.
Lemma lem1210099 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210100 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term79 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1210099 A) (@lem1210098 A l l1 x)). Qed.
Lemma lem1210101 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1210102 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term476 A l l1 x) = (term472 A l l1 x).
Proof. exact (MK_COMB (@lem1210101 A x l) (@lem1210100 A l l1 x)). Qed.
Lemma lem1210103 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210104 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term478 A l l1 x) = (term479 A l l1 x).
Proof. exact (MK_COMB (@lem1210103) (@lem1210102 A l l1 x)). Qed.
Lemma lem1210105 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term76 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (eq_refl (term76 A l l1 x l2)). Qed.
Lemma lem1210106 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1210107 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term480 A l l1 x l2) = (term481 A l l1 x l2).
Proof. exact (MK_COMB (@lem1210106 A x l) (@lem1210105 A l l1 x l2)). Qed.
Lemma lem1210108 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term482 A l l1 x) = (term483 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1210107 A l l1 x l2)). Qed.
Lemma lem1210109 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210110 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term477 A l l1 x) = (term484 A l l1 x).
Proof. exact (MK_COMB (@lem1210109 A) (@lem1210108 A l l1 x)). Qed.
Lemma lem1210111 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term476 A l l1 x) = (term477 A l l1 x)) = ((term472 A l l1 x) = (term484 A l l1 x)).
Proof. exact (MK_COMB (@lem1210104 A l l1 x) (@lem1210110 A l l1 x)). Qed.
Lemma lem1210112 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term472 A l l1 x) = (term484 A l l1 x).
Proof. exact (EQ_MP (@lem1210111 A l l1 x) (@lem1210096 A l l1 x)). Qed.
Lemma lem1210113 {A : Type'} (l : list A) (x : A) : (term474 A l x) = (term485 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1210112 A l l1 x)). Qed.
Lemma lem1210114 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210115 {A : Type'} (l : list A) (x : A) : (term475 A l x) = (term486 A l x).
Proof. exact (MK_COMB (@lem1210114 A) (@lem1210113 A l x)). Qed.
Lemma lem1210116 {A : Type'} (l : list A) (x : A) : (term462 A l x) = (term486 A l x).
Proof. exact (TRANS (@lem1210092 A l x) (@lem1210115 A l x)). Qed.
Lemma lem1210117 {A : Type'} (l : list A) (x : A) : (term430 A l x) = (term486 A l x).
Proof. exact (TRANS (@lem1210072 A l x) (@lem1210116 A l x)). Qed.
Lemma lem1210118 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210119 {A : Type'} (l : list A) (x : A) : (term457 A l x) = (term487 A l x).
Proof. exact (MK_COMB (@lem1210118) (@lem1210117 A l x)). Qed.
Lemma lem1210120 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1210121 {A : Type'} (y : A) (l : list A) (x : A) : (term459 A y l x) = (term488 A y l x).
Proof. exact (MK_COMB (@lem1210119 A l x) (@lem1210120 A y l x)). Qed.
Lemma lem1210123 {A : Type'} (P : A -> Prop) (Q : Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1210124 {A : Type'} (P : type1143 A) (Q : Prop) : (term491 A P Q) = (term492 A P Q).
Proof. exact (@lem1210123 (list A) P Q). Qed.
Lemma lem1210125 {A : Type'} (y : A) (l : list A) (x : A) : (term493 A y l x) = (term494 A y l x).
Proof. exact (@lem1210124 A (term485 A l x) (term454 A y l x)). Qed.
Lemma lem1210126 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term495 A l x l1) = (term484 A l l1 x).
Proof. exact (eq_refl (term495 A l x l1)). Qed.
Lemma lem1210127 {A : Type'} (l : list A) (x : A) : (term496 A l x) = (term485 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1210126 A l l1 x)). Qed.
Lemma lem1210128 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210129 {A : Type'} (l : list A) (x : A) : (term497 A l x) = (term486 A l x).
Proof. exact (MK_COMB (@lem1210128 A) (@lem1210127 A l x)). Qed.
Lemma lem1210130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210131 {A : Type'} (l : list A) (x : A) : (term498 A l x) = (term487 A l x).
Proof. exact (MK_COMB (@lem1210130) (@lem1210129 A l x)). Qed.
Lemma lem1210132 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1210133 {A : Type'} (y : A) (l : list A) (x : A) : (term493 A y l x) = (term488 A y l x).
Proof. exact (MK_COMB (@lem1210131 A l x) (@lem1210132 A y l x)). Qed.
Lemma lem1210134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210135 {A : Type'} (y : A) (l : list A) (x : A) : (term499 A y l x) = (term500 A y l x).
Proof. exact (MK_COMB (@lem1210134) (@lem1210133 A y l x)). Qed.
Lemma lem1210136 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term495 A l x l1) = (term484 A l l1 x).
Proof. exact (eq_refl (term495 A l x l1)). Qed.
Lemma lem1210137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210138 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term501 A l x l1) = (term502 A l l1 x).
Proof. exact (MK_COMB (@lem1210137) (@lem1210136 A l l1 x)). Qed.
Lemma lem1210139 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1210140 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term503 A l1 y l x) = (term504 A l1 y l x).
Proof. exact (MK_COMB (@lem1210138 A l l1 x) (@lem1210139 A y l x)). Qed.
Lemma lem1210141 {A : Type'} (y : A) (l : list A) (x : A) : (term505 A y l x) = (term506 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1210140 A l1 y l x)). Qed.
Lemma lem1210142 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210143 {A : Type'} (y : A) (l : list A) (x : A) : (term494 A y l x) = (term507 A y l x).
Proof. exact (MK_COMB (@lem1210142 A) (@lem1210141 A y l x)). Qed.
Lemma lem1210144 {A : Type'} (y : A) (l : list A) (x : A) : ((term493 A y l x) = (term494 A y l x)) = ((term488 A y l x) = (term507 A y l x)).
Proof. exact (MK_COMB (@lem1210135 A y l x) (@lem1210143 A y l x)). Qed.
Lemma lem1210145 {A : Type'} (y : A) (l : list A) (x : A) : (term488 A y l x) = (term507 A y l x).
Proof. exact (EQ_MP (@lem1210144 A y l x) (@lem1210125 A y l x)). Qed.
Lemma lem1210147 {A : Type'} (P : A -> Prop) (Q : Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1210148 {A : Type'} (P : type1143 A) (Q : Prop) : (term491 A P Q) = (term492 A P Q).
Proof. exact (@lem1210147 (list A) P Q). Qed.
Lemma lem1210149 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term508 A l1 y l x) = (term509 A l1 y l x).
Proof. exact (@lem1210148 A (term483 A l l1 x) (term454 A y l x)). Qed.
Lemma lem1210150 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term510 A l l1 x l2) = (term481 A l l1 x l2).
Proof. exact (eq_refl (term510 A l l1 x l2)). Qed.
Lemma lem1210151 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term511 A l l1 x) = (term483 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1210150 A l l1 x l2)). Qed.
Lemma lem1210152 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210153 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term512 A l l1 x) = (term484 A l l1 x).
Proof. exact (MK_COMB (@lem1210152 A) (@lem1210151 A l l1 x)). Qed.
Lemma lem1210154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210155 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term513 A l l1 x) = (term502 A l l1 x).
Proof. exact (MK_COMB (@lem1210154) (@lem1210153 A l l1 x)). Qed.
Lemma lem1210156 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1210157 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term508 A l1 y l x) = (term504 A l1 y l x).
Proof. exact (MK_COMB (@lem1210155 A l l1 x) (@lem1210156 A y l x)). Qed.
Lemma lem1210158 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210159 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term514 A l1 y l x) = (term515 A l1 y l x).
Proof. exact (MK_COMB (@lem1210158) (@lem1210157 A l1 y l x)). Qed.
Lemma lem1210160 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term510 A l l1 x l2) = (term481 A l l1 x l2).
Proof. exact (eq_refl (term510 A l l1 x l2)). Qed.
Lemma lem1210161 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210162 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term516 A l l1 x l2) = (term517 A l l1 x l2).
Proof. exact (MK_COMB (@lem1210161) (@lem1210160 A l l1 x l2)). Qed.
Lemma lem1210163 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1210164 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) : (term518 A l1 l2 y l x) = (term519 A l1 l2 y l x).
Proof. exact (MK_COMB (@lem1210162 A l l1 x l2) (@lem1210163 A y l x)). Qed.
Lemma lem1210165 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term520 A l1 y l x) = (term521 A l1 y l x).
Proof. exact (fun_ext (fun l2 : list A => @lem1210164 A l1 l2 y l x)). Qed.
Lemma lem1210166 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210167 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term509 A l1 y l x) = (term522 A l1 y l x).
Proof. exact (MK_COMB (@lem1210166 A) (@lem1210165 A l1 y l x)). Qed.
Lemma lem1210168 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : ((term508 A l1 y l x) = (term509 A l1 y l x)) = ((term504 A l1 y l x) = (term522 A l1 y l x)).
Proof. exact (MK_COMB (@lem1210159 A l1 y l x) (@lem1210167 A l1 y l x)). Qed.
Lemma lem1210169 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term504 A l1 y l x) = (term522 A l1 y l x).
Proof. exact (EQ_MP (@lem1210168 A l1 y l x) (@lem1210149 A l1 y l x)). Qed.
Lemma lem1210170 {A : Type'} (y : A) (l : list A) (x : A) : (term506 A y l x) = (term523 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1210169 A l1 y l x)). Qed.
Lemma lem1210171 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1210172 {A : Type'} (y : A) (l : list A) (x : A) : (term507 A y l x) = (term524 A y l x).
Proof. exact (MK_COMB (@lem1210171 A) (@lem1210170 A y l x)). Qed.
Lemma lem1210173 {A : Type'} (y : A) (l : list A) (x : A) : (term488 A y l x) = (term524 A y l x).
Proof. exact (TRANS (@lem1210145 A y l x) (@lem1210172 A y l x)). Qed.
Lemma lem1210175 {A : Type'} (y : A) (l : list A) (x : A) : (term459 A y l x) = (term524 A y l x).
Proof. exact (TRANS (@lem1210121 A y l x) (@lem1210173 A y l x)). Qed.
Lemma lem1210176 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term524 A y l x).
Proof. exact (TRANS (@lem1209942 A y l x) (@lem1210175 A y l x)). Qed.
Lemma lem1210177 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term218 A y l x) : term524 A y l x.
Proof. exact (EQ_MP (@lem1210176 A y l x) (@lem1209871 A y l x h1)). Qed.
Lemma lem1210178 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1210179 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1210178 A l)). Qed.
Lemma lem1210180 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1210181 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1210180 A) (@lem1210179 A)). Qed.
Lemma lem1210182 {A : Type'} (h : A) (t : list A) (l : list A) : ((term418 A h t l) = (term419 A h t l)) = ((term418 A h t l) = (term419 A h t l)).
Proof. exact (eq_refl ((term418 A h t l) = (term419 A h t l))). Qed.
Lemma lem1210183 {A : Type'} (h : A) (t : list A) : (term420 A h t) = (term420 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1210182 A h t l)). Qed.
Lemma lem1210184 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1210185 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term421 A h t).
Proof. exact (MK_COMB (@lem1210184 A) (@lem1210183 A h t)). Qed.
Lemma lem1210186 {A : Type'} (h : A) : (term422 A h) = (term422 A h).
Proof. exact (fun_ext (fun t : list A => @lem1210185 A h t)). Qed.
Lemma lem1210187 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1210188 {A : Type'} (h : A) : (term423 A h) = (term423 A h).
Proof. exact (MK_COMB (@lem1210187 A) (@lem1210186 A h)). Qed.
Lemma lem1210189 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun h : A => @lem1210188 A h)). Qed.
Lemma lem1210190 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210191 {A : Type'} : (term425 A) = (term425 A).
Proof. exact (MK_COMB (@lem1210190 A) (@lem1210189 A)). Qed.
Lemma lem1210192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210193 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (MK_COMB (@lem1210192) (@lem1210181 A)). Qed.
Lemma lem1210214 {A : Type'} : (term170 A) = (term170 A).
Proof. exact (MK_COMB (@lem1210193 A) (@lem1210191 A)). Qed.
Lemma lem1210215 {A : Type'} (h1 : term170 A) : term170 A.
Proof. exact (EQ_MP (@lem1210214 A) (@lem1209872 A h1)). Qed.
Lemma lem1210254 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1210255 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1210254 A x)). Qed.
Lemma lem1210256 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210257 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1210256 A) (@lem1210255 A)). Qed.
Lemma lem1210268 {A : Type'} (h : A) (x : A) (t : list A) : (term525 A h x t) = (term526 A h x t).
Proof. exact (@lem17160 (x = h) (@List.In A x t)). Qed.
Lemma lem1210274 {A : Type'} (h : A) (x : A) (t : list A) : (term527 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term527 A h x t)). Qed.
Lemma lem1210276 {A : Type'} (x : A) (h : A) (t : list A) : (term528 A x h t) = (term528 A x h t).
Proof. exact (eq_refl (term528 A x h t)). Qed.
Lemma lem1210277 {A : Type'} (h : A) (x : A) (t : list A) : (term529 A h x t) = (term530 A h x t).
Proof. exact (MK_COMB (@lem1210276 A x h t) (@lem1210268 A h x t)). Qed.
Lemma lem1210278 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210279 {A : Type'} (h : A) (x : A) (t : list A) : (term531 A h x t) = (term532 A h x t).
Proof. exact (MK_COMB (@lem1210278) (@lem1210277 A h x t)). Qed.
Lemma lem1210280 {A : Type'} (h : A) (x : A) (t : list A) : (term533 A h x t) = (term534 A h x t).
Proof. exact (MK_COMB (@lem1210279 A h x t) (@lem1210274 A h x t)). Qed.
Lemma lem1210281 {A : Type'} (h : A) (x : A) (t : list A) : ((term106 A x h t) = (term107 A h x t)) = (term533 A h x t).
Proof. exact (@lem17784 (term106 A x h t) (term107 A h x t)). Qed.
Lemma lem1210282 {A : Type'} (h : A) (x : A) (t : list A) : ((term106 A x h t) = (term107 A h x t)) = (term534 A h x t).
Proof. exact (TRANS (@lem1210281 A h x t) (@lem1210280 A h x t)). Qed.
Lemma lem1210283 {A : Type'} (h : A) (x : A) : (term228 A h x) = (term535 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1210282 A h x t)). Qed.
Lemma lem1210284 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1210285 {A : Type'} (h : A) (x : A) : (term246 A h x) = (term536 A h x).
Proof. exact (MK_COMB (@lem1210284 A) (@lem1210283 A h x)). Qed.
Lemma lem1210286 {A : Type'} (h : A) : (term257 A h) = (term537 A h).
Proof. exact (fun_ext (fun x : A => @lem1210285 A h x)). Qed.
Lemma lem1210287 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210288 {A : Type'} (h : A) : (term272 A h) = (term538 A h).
Proof. exact (MK_COMB (@lem1210287 A) (@lem1210286 A h)). Qed.
Lemma lem1210289 {A : Type'} : (term280 A) = (term539 A).
Proof. exact (fun_ext (fun h : A => @lem1210288 A h)). Qed.
Lemma lem1210290 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210291 {A : Type'} : (term295 A) = (term540 A).
Proof. exact (MK_COMB (@lem1210290 A) (@lem1210289 A)). Qed.
Lemma lem1210292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210293 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (MK_COMB (@lem1210292) (@lem1210257 A)). Qed.
Lemma lem1210294 {A : Type'} : (term297 A) = (term541 A).
Proof. exact (MK_COMB (@lem1210293 A) (@lem1210291 A)). Qed.
Lemma lem1210308 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1210309 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1210308 (list A) P Q). Qed.
Lemma lem1210310 {A : Type'} (h : A) (x : A) : (term542 A h x) = (term543 A h x).
Proof. exact (@lem1210309 A (term544 A h x) (term545 A h x)). Qed.
Lemma lem1210311 {A : Type'} (h : A) (x : A) (t : list A) : (term546 A h x t) = (term530 A h x t).
Proof. exact (eq_refl (term546 A h x t)). Qed.
Lemma lem1210312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210313 {A : Type'} (h : A) (x : A) (t : list A) : (term547 A h x t) = (term532 A h x t).
Proof. exact (MK_COMB (@lem1210312) (@lem1210311 A h x t)). Qed.
Lemma lem1210314 {A : Type'} (h : A) (x : A) (t : list A) : (term548 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term548 A h x t)). Qed.
Lemma lem1210315 {A : Type'} (h : A) (x : A) (t : list A) : (term549 A h x t) = (term534 A h x t).
Proof. exact (MK_COMB (@lem1210313 A h x t) (@lem1210314 A h x t)). Qed.
Lemma lem1210316 {A : Type'} (h : A) (x : A) : (term550 A h x) = (term535 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1210315 A h x t)). Qed.
Lemma lem1210317 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1210318 {A : Type'} (h : A) (x : A) : (term542 A h x) = (term536 A h x).
Proof. exact (MK_COMB (@lem1210317 A) (@lem1210316 A h x)). Qed.
Lemma lem1210319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210320 {A : Type'} (h : A) (x : A) : (term551 A h x) = (term552 A h x).
Proof. exact (MK_COMB (@lem1210319) (@lem1210318 A h x)). Qed.
Lemma lem1210321 {A : Type'} (h : A) (x : A) (t : list A) : (term546 A h x t) = (term530 A h x t).
Proof. exact (eq_refl (term546 A h x t)). Qed.
Lemma lem1210322 {A : Type'} (h : A) (x : A) : (term553 A h x) = (term544 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1210321 A h x t)). Qed.
Lemma lem1210323 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1210324 {A : Type'} (h : A) (x : A) : (term554 A h x) = (term555 A h x).
Proof. exact (MK_COMB (@lem1210323 A) (@lem1210322 A h x)). Qed.
Lemma lem1210325 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210326 {A : Type'} (h : A) (x : A) : (term556 A h x) = (term557 A h x).
Proof. exact (MK_COMB (@lem1210325) (@lem1210324 A h x)). Qed.
Lemma lem1210327 {A : Type'} (h : A) (x : A) (t : list A) : (term548 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term548 A h x t)). Qed.
Lemma lem1210328 {A : Type'} (h : A) (x : A) : (term558 A h x) = (term545 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1210327 A h x t)). Qed.
Lemma lem1210329 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1210330 {A : Type'} (h : A) (x : A) : (term559 A h x) = (term560 A h x).
Proof. exact (MK_COMB (@lem1210329 A) (@lem1210328 A h x)). Qed.
Lemma lem1210331 {A : Type'} (h : A) (x : A) : (term543 A h x) = (term561 A h x).
Proof. exact (MK_COMB (@lem1210326 A h x) (@lem1210330 A h x)). Qed.
Lemma lem1210332 {A : Type'} (h : A) (x : A) : ((term542 A h x) = (term543 A h x)) = ((term536 A h x) = (term561 A h x)).
Proof. exact (MK_COMB (@lem1210320 A h x) (@lem1210331 A h x)). Qed.
Lemma lem1210333 {A : Type'} (h : A) (x : A) : (term536 A h x) = (term561 A h x).
Proof. exact (EQ_MP (@lem1210332 A h x) (@lem1210310 A h x)). Qed.
Lemma lem1210430 {A : Type'} (h : A) : (term537 A h) = (term562 A h).
Proof. exact (fun_ext (fun x : A => @lem1210333 A h x)). Qed.
Lemma lem1210431 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210432 {A : Type'} (h : A) : (term538 A h) = (term563 A h).
Proof. exact (MK_COMB (@lem1210431 A) (@lem1210430 A h)). Qed.
Lemma lem1210434 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1210435 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1210434 A P Q). Qed.
Lemma lem1210436 {A : Type'} (h : A) : (term564 A h) = (term565 A h).
Proof. exact (@lem1210435 A (term566 A h) (term567 A h)). Qed.
Lemma lem1210437 {A : Type'} (h : A) (x : A) : (term568 A h x) = (term555 A h x).
Proof. exact (eq_refl (term568 A h x)). Qed.
Lemma lem1210438 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210439 {A : Type'} (h : A) (x : A) : (term569 A h x) = (term557 A h x).
Proof. exact (MK_COMB (@lem1210438) (@lem1210437 A h x)). Qed.
Lemma lem1210440 {A : Type'} (h : A) (x : A) : (term570 A h x) = (term560 A h x).
Proof. exact (eq_refl (term570 A h x)). Qed.
Lemma lem1210441 {A : Type'} (h : A) (x : A) : (term571 A h x) = (term561 A h x).
Proof. exact (MK_COMB (@lem1210439 A h x) (@lem1210440 A h x)). Qed.
Lemma lem1210442 {A : Type'} (h : A) : (term572 A h) = (term562 A h).
Proof. exact (fun_ext (fun x : A => @lem1210441 A h x)). Qed.
Lemma lem1210443 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210444 {A : Type'} (h : A) : (term564 A h) = (term563 A h).
Proof. exact (MK_COMB (@lem1210443 A) (@lem1210442 A h)). Qed.
Lemma lem1210445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210446 {A : Type'} (h : A) : (term573 A h) = (term574 A h).
Proof. exact (MK_COMB (@lem1210445) (@lem1210444 A h)). Qed.
Lemma lem1210447 {A : Type'} (h : A) (x : A) : (term568 A h x) = (term555 A h x).
Proof. exact (eq_refl (term568 A h x)). Qed.
Lemma lem1210448 {A : Type'} (h : A) : (term575 A h) = (term566 A h).
Proof. exact (fun_ext (fun x : A => @lem1210447 A h x)). Qed.
Lemma lem1210449 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210450 {A : Type'} (h : A) : (term576 A h) = (term577 A h).
Proof. exact (MK_COMB (@lem1210449 A) (@lem1210448 A h)). Qed.
Lemma lem1210451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210452 {A : Type'} (h : A) : (term578 A h) = (term579 A h).
Proof. exact (MK_COMB (@lem1210451) (@lem1210450 A h)). Qed.
Lemma lem1210453 {A : Type'} (h : A) (x : A) : (term570 A h x) = (term560 A h x).
Proof. exact (eq_refl (term570 A h x)). Qed.
Lemma lem1210454 {A : Type'} (h : A) : (term580 A h) = (term567 A h).
Proof. exact (fun_ext (fun x : A => @lem1210453 A h x)). Qed.
Lemma lem1210455 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210456 {A : Type'} (h : A) : (term581 A h) = (term582 A h).
Proof. exact (MK_COMB (@lem1210455 A) (@lem1210454 A h)). Qed.
Lemma lem1210457 {A : Type'} (h : A) : (term565 A h) = (term583 A h).
Proof. exact (MK_COMB (@lem1210452 A h) (@lem1210456 A h)). Qed.
Lemma lem1210458 {A : Type'} (h : A) : ((term564 A h) = (term565 A h)) = ((term563 A h) = (term583 A h)).
Proof. exact (MK_COMB (@lem1210446 A h) (@lem1210457 A h)). Qed.
Lemma lem1210459 {A : Type'} (h : A) : (term563 A h) = (term583 A h).
Proof. exact (EQ_MP (@lem1210458 A h) (@lem1210436 A h)). Qed.
Lemma lem1210564 {A : Type'} (h : A) : (term538 A h) = (term583 A h).
Proof. exact (TRANS (@lem1210432 A h) (@lem1210459 A h)). Qed.
Lemma lem1210565 {A : Type'} : (term539 A) = (term584 A).
Proof. exact (fun_ext (fun h : A => @lem1210564 A h)). Qed.
Lemma lem1210566 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210567 {A : Type'} : (term540 A) = (term585 A).
Proof. exact (MK_COMB (@lem1210566 A) (@lem1210565 A)). Qed.
Lemma lem1210569 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1210570 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1210569 A P Q). Qed.
Lemma lem1210571 {A : Type'} : (term586 A) = (term587 A).
Proof. exact (@lem1210570 A (term588 A) (term589 A)). Qed.
Lemma lem1210572 {A : Type'} (h : A) : (term590 A h) = (term577 A h).
Proof. exact (eq_refl (term590 A h)). Qed.
Lemma lem1210573 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210574 {A : Type'} (h : A) : (term591 A h) = (term579 A h).
Proof. exact (MK_COMB (@lem1210573) (@lem1210572 A h)). Qed.
Lemma lem1210575 {A : Type'} (h : A) : (term592 A h) = (term582 A h).
Proof. exact (eq_refl (term592 A h)). Qed.
Lemma lem1210576 {A : Type'} (h : A) : (term593 A h) = (term583 A h).
Proof. exact (MK_COMB (@lem1210574 A h) (@lem1210575 A h)). Qed.
Lemma lem1210577 {A : Type'} : (term594 A) = (term584 A).
Proof. exact (fun_ext (fun h : A => @lem1210576 A h)). Qed.
Lemma lem1210578 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210579 {A : Type'} : (term586 A) = (term585 A).
Proof. exact (MK_COMB (@lem1210578 A) (@lem1210577 A)). Qed.
Lemma lem1210580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1210581 {A : Type'} : (term595 A) = (term596 A).
Proof. exact (MK_COMB (@lem1210580) (@lem1210579 A)). Qed.
Lemma lem1210582 {A : Type'} (h : A) : (term590 A h) = (term577 A h).
Proof. exact (eq_refl (term590 A h)). Qed.
Lemma lem1210583 {A : Type'} : (term597 A) = (term588 A).
Proof. exact (fun_ext (fun h : A => @lem1210582 A h)). Qed.
Lemma lem1210584 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210585 {A : Type'} : (term598 A) = (term599 A).
Proof. exact (MK_COMB (@lem1210584 A) (@lem1210583 A)). Qed.
Lemma lem1210586 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1210587 {A : Type'} : (term600 A) = (term601 A).
Proof. exact (MK_COMB (@lem1210586) (@lem1210585 A)). Qed.
Lemma lem1210588 {A : Type'} (h : A) : (term592 A h) = (term582 A h).
Proof. exact (eq_refl (term592 A h)). Qed.
Lemma lem1210589 {A : Type'} : (term602 A) = (term589 A).
Proof. exact (fun_ext (fun h : A => @lem1210588 A h)). Qed.
Lemma lem1210590 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1210591 {A : Type'} : (term603 A) = (term604 A).
Proof. exact (MK_COMB (@lem1210590 A) (@lem1210589 A)). Qed.
Lemma lem1210592 {A : Type'} : (term587 A) = (term605 A).
Proof. exact (MK_COMB (@lem1210587 A) (@lem1210591 A)). Qed.
Lemma lem1210593 {A : Type'} : ((term586 A) = (term587 A)) = ((term585 A) = (term605 A)).
Proof. exact (MK_COMB (@lem1210581 A) (@lem1210592 A)). Qed.
Lemma lem1210594 {A : Type'} : (term585 A) = (term605 A).
Proof. exact (EQ_MP (@lem1210593 A) (@lem1210571 A)). Qed.
Lemma lem1210707 {A : Type'} : (term540 A) = (term605 A).
Proof. exact (TRANS (@lem1210567 A) (@lem1210594 A)). Qed.
Lemma lem1210708 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (eq_refl (term269 A)). Qed.
Lemma lem1210711 {A : Type'} : (term541 A) = (term606 A).
Proof. exact (MK_COMB (@lem1210708 A) (@lem1210707 A)). Qed.
Lemma lem1210712 {A : Type'} : (term297 A) = (term606 A).
Proof. exact (TRANS (@lem1210294 A) (@lem1210711 A)). Qed.
Lemma lem1210713 {A : Type'} (h1 : term297 A) : term606 A.
Proof. exact (EQ_MP (@lem1210712 A) (@lem1209874 A h1)). Qed.
Lemma lem1211174 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) (h1 : term522 A l1 y l x) : term522 A l1 y l x.
Proof. exact (h1). Qed.
Lemma lem1211175 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term519 A l1 l2 y l x.
Proof. exact (h1). Qed.
Lemma lem1211181 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1211202 {A : Type'} (h : A) (t : list A) (l : list A) : ((term418 A h t l) = (term419 A h t l)) = ((term418 A h t l) = (term419 A h t l)).
Proof. exact (eq_refl ((term418 A h t l) = (term419 A h t l))). Qed.
Lemma lem1211203 {A : Type'} (h : A) (t : list A) : (term420 A h t) = (term420 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1211202 A h t l)). Qed.
Lemma lem1211204 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211205 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term421 A h t).
Proof. exact (MK_COMB (@lem1211204 A) (@lem1211203 A h t)). Qed.
Lemma lem1211206 {A : Type'} (h : A) : (term422 A h) = (term422 A h).
Proof. exact (fun_ext (fun t : list A => @lem1211205 A h t)). Qed.
Lemma lem1211207 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211208 {A : Type'} (h : A) : (term423 A h) = (term423 A h).
Proof. exact (MK_COMB (@lem1211207 A) (@lem1211206 A h)). Qed.
Lemma lem1211209 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun h : A => @lem1211208 A h)). Qed.
Lemma lem1211210 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211211 {A : Type'} : (term425 A) = (term425 A).
Proof. exact (MK_COMB (@lem1211210 A) (@lem1211209 A)). Qed.
Lemma lem1211220 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1211221 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1211220 A l)). Qed.
Lemma lem1211222 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211223 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1211222 A) (@lem1211221 A)). Qed.
Lemma lem1211224 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1211225 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (MK_COMB (@lem1211224) (@lem1211223 A)). Qed.
Lemma lem1211226 {A : Type'} : (term170 A) = (term170 A).
Proof. exact (MK_COMB (@lem1211225 A) (@lem1211211 A)). Qed.
Lemma lem1211227 {A : Type'} (h1 : term170 A) : term170 A.
Proof. exact (EQ_MP (@lem1211226 A) (@lem1210215 A h1)). Qed.
Lemma lem1211300 {A : Type'} (h : A) (x : A) (t : list A) : (term527 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term527 A h x t)). Qed.
Lemma lem1211301 {A : Type'} (h : A) (x : A) : (term545 A h x) = (term545 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1211300 A h x t)). Qed.
Lemma lem1211302 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211303 {A : Type'} (h : A) (x : A) : (term560 A h x) = (term560 A h x).
Proof. exact (MK_COMB (@lem1211302 A) (@lem1211301 A h x)). Qed.
Lemma lem1211304 {A : Type'} (h : A) : (term567 A h) = (term567 A h).
Proof. exact (fun_ext (fun x : A => @lem1211303 A h x)). Qed.
Lemma lem1211305 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211306 {A : Type'} (h : A) : (term582 A h) = (term582 A h).
Proof. exact (MK_COMB (@lem1211305 A) (@lem1211304 A h)). Qed.
Lemma lem1211307 {A : Type'} : (term589 A) = (term589 A).
Proof. exact (fun_ext (fun h : A => @lem1211306 A h)). Qed.
Lemma lem1211308 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211309 {A : Type'} : (term604 A) = (term604 A).
Proof. exact (MK_COMB (@lem1211308 A) (@lem1211307 A)). Qed.
Lemma lem1211338 {A : Type'} (h : A) (x : A) (t : list A) : (term530 A h x t) = (term530 A h x t).
Proof. exact (eq_refl (term530 A h x t)). Qed.
Lemma lem1211339 {A : Type'} (h : A) (x : A) : (term544 A h x) = (term544 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1211338 A h x t)). Qed.
Lemma lem1211340 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211341 {A : Type'} (h : A) (x : A) : (term555 A h x) = (term555 A h x).
Proof. exact (MK_COMB (@lem1211340 A) (@lem1211339 A h x)). Qed.
Lemma lem1211342 {A : Type'} (h : A) : (term566 A h) = (term566 A h).
Proof. exact (fun_ext (fun x : A => @lem1211341 A h x)). Qed.
Lemma lem1211343 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211344 {A : Type'} (h : A) : (term577 A h) = (term577 A h).
Proof. exact (MK_COMB (@lem1211343 A) (@lem1211342 A h)). Qed.
Lemma lem1211345 {A : Type'} : (term588 A) = (term588 A).
Proof. exact (fun_ext (fun h : A => @lem1211344 A h)). Qed.
Lemma lem1211346 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211347 {A : Type'} : (term599 A) = (term599 A).
Proof. exact (MK_COMB (@lem1211346 A) (@lem1211345 A)). Qed.
Lemma lem1211348 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1211349 {A : Type'} : (term601 A) = (term601 A).
Proof. exact (MK_COMB (@lem1211348) (@lem1211347 A)). Qed.
Lemma lem1211350 {A : Type'} : (term605 A) = (term605 A).
Proof. exact (MK_COMB (@lem1211349 A) (@lem1211309 A)). Qed.
Lemma lem1211357 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1211358 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1211357 A x)). Qed.
Lemma lem1211359 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211360 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1211359 A) (@lem1211358 A)). Qed.
Lemma lem1211361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1211362 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (MK_COMB (@lem1211361) (@lem1211360 A)). Qed.
Lemma lem1211363 {A : Type'} : (term606 A) = (term606 A).
Proof. exact (MK_COMB (@lem1211362 A) (@lem1211350 A)). Qed.
Lemma lem1211364 {A : Type'} (h1 : term297 A) : term606 A.
Proof. exact (EQ_MP (@lem1211363 A) (@lem1210713 A h1)). Qed.
Lemma lem1211474 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term437 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term437 A y l l1 x l2)). Qed.
Lemma lem1211475 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term439 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1211474 A y l l1 x l2)). Qed.
Lemma lem1211476 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211477 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term440 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1211476 A) (@lem1211475 A y l l1 x)). Qed.
Lemma lem1211484 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1211485 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term443 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1211484 A x l1) (@lem1211477 A y l l1 x)). Qed.
Lemma lem1211486 {A : Type'} (y : A) (l : list A) (x : A) : (term450 A y l x) = (term450 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1211485 A y l l1 x)). Qed.
Lemma lem1211487 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211488 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term451 A y l x).
Proof. exact (MK_COMB (@lem1211487 A) (@lem1211486 A y l x)). Qed.
Lemma lem1211503 {A : Type'} (y : A) (x : A) (l : list A) : (term452 A y x l) = (term452 A y x l).
Proof. exact (eq_refl (term452 A y x l)). Qed.
Lemma lem1211504 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (MK_COMB (@lem1211503 A y x l) (@lem1211488 A y l x)). Qed.
Lemma lem1211539 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term517 A l l1 x l2) = (term517 A l l1 x l2).
Proof. exact (eq_refl (term517 A l l1 x l2)). Qed.
Lemma lem1211540 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) : (term519 A l1 l2 y l x) = (term519 A l1 l2 y l x).
Proof. exact (MK_COMB (@lem1211539 A l l1 x l2) (@lem1211504 A y l x)). Qed.
Lemma lem1211541 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term519 A l1 l2 y l x.
Proof. exact (EQ_MP (@lem1211540 A l1 l2 y l x) (@lem1211175 A l1 l2 y l x h1)). Qed.
Lemma lem1211542 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term454 A y l x.
Proof. exact (proj2 (@lem1211541 A l1 l2 y l x h1)). Qed.
Lemma lem1211543 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term481 A l l1 x l2.
Proof. exact (proj1 (@lem1211541 A l1 l2 y l x h1)). Qed.
Lemma lem1211544 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term451 A y l x.
Proof. exact (proj2 (@lem1211542 A l1 l2 y l x h1)). Qed.
Lemma lem1211545 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term107 A y x l.
Proof. exact (proj1 (@lem1211542 A l1 l2 y l x h1)). Qed.
Lemma lem1211551 {A : Type'} (h1 : term297 A) : term267 A.
Proof. exact (proj1 (@lem1211364 A h1)). Qed.
Lemma lem1211557 {A : Type'} (h1 : term170 A) : term427 A.
Proof. exact (proj1 (@lem1211227 A h1)). Qed.
Lemma lem1211561 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : term77 A l l1 x l2.
Proof. exact (h1). Qed.
Lemma lem1211565 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : term77 A l l1 x l2.
Proof. exact (h1). Qed.
Lemma lem1211571 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1211573 {A : Type'} (P : Prop) (Q : A -> Prop) : (term607 A P Q) = (term608 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1211574 {A : Type'} (P : Prop) (Q : type1143 A) : (term609 A P Q) = (term610 A P Q).
Proof. exact (@lem1211573 (list A) P Q). Qed.
Lemma lem1211575 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term612 A y l l1 x).
Proof. exact (@lem1211574 A (@List.In A x l1) (term439 A y l l1 x)). Qed.
Lemma lem1211576 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1211577 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term614 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1211576 A y l l1 x l2)). Qed.
Lemma lem1211578 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211579 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term615 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1211578 A) (@lem1211577 A y l l1 x)). Qed.
Lemma lem1211580 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1211581 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1211580 A x l1) (@lem1211579 A y l l1 x)). Qed.
Lemma lem1211582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1211583 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term616 A y l l1 x) = (term617 A y l l1 x).
Proof. exact (MK_COMB (@lem1211582) (@lem1211581 A y l l1 x)). Qed.
Lemma lem1211584 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1211585 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1211586 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term618 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1211585 A x l1) (@lem1211584 A y l l1 x l2)). Qed.
Lemma lem1211587 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term620 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1211586 A y l l1 x l2)). Qed.
Lemma lem1211588 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211589 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term612 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1211588 A) (@lem1211587 A y l l1 x)). Qed.
Lemma lem1211590 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : ((term611 A y l l1 x) = (term612 A y l l1 x)) = ((term443 A y l l1 x) = (term622 A y l l1 x)).
Proof. exact (MK_COMB (@lem1211583 A y l l1 x) (@lem1211589 A y l l1 x)). Qed.
Lemma lem1211591 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term443 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (EQ_MP (@lem1211590 A y l l1 x) (@lem1211575 A y l l1 x)). Qed.
Lemma lem1211592 {A : Type'} (y : A) (l : list A) (x : A) : (term450 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1211591 A y l l1 x)). Qed.
Lemma lem1211593 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211594 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1211593 A) (@lem1211592 A y l x)). Qed.
Lemma lem1211601 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term619 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (eq_refl (term619 A y l l1 x l2)). Qed.
Lemma lem1211602 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term621 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1211601 A y l l1 x l2)). Qed.
Lemma lem1211603 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211604 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term622 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1211603 A) (@lem1211602 A y l l1 x)). Qed.
Lemma lem1211605 {A : Type'} (y : A) (l : list A) (x : A) : (term623 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1211604 A y l l1 x)). Qed.
Lemma lem1211606 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211607 {A : Type'} (y : A) (l : list A) (x : A) : (term624 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1211606 A) (@lem1211605 A y l x)). Qed.
Lemma lem1211608 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (TRANS (@lem1211594 A y l x) (@lem1211607 A y l x)). Qed.
Lemma lem1211609 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term624 A y l x.
Proof. exact (EQ_MP (@lem1211608 A y l x) (@lem1211544 A l1 l2 y l x h1)). Qed.
Lemma lem1211672 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1211673 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1211672 A x)). Qed.
Lemma lem1211674 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211676 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1211674 A) (@lem1211673 A)). Qed.
Lemma lem1211677 {A : Type'} (h1 : term297 A) : term267 A.
Proof. exact (EQ_MP (@lem1211676 A) (@lem1211551 A h1)). Qed.
Lemma lem1211753 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1211754 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1211753 A l)). Qed.
Lemma lem1211755 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211757 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1211755 A) (@lem1211754 A)). Qed.
Lemma lem1211758 {A : Type'} (h1 : term170 A) : term427 A.
Proof. exact (EQ_MP (@lem1211757 A) (@lem1211557 A h1)). Qed.
Lemma lem1211775 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1211783 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1211785 {A : Type'} (P : Prop) (Q : A -> Prop) : (term607 A P Q) = (term608 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1211786 {A : Type'} (P : Prop) (Q : type1143 A) : (term609 A P Q) = (term610 A P Q).
Proof. exact (@lem1211785 (list A) P Q). Qed.
Lemma lem1211787 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term612 A y l l1 x).
Proof. exact (@lem1211786 A (@List.In A x l1) (term439 A y l l1 x)). Qed.
Lemma lem1211788 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1211789 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term614 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1211788 A y l l1 x l2)). Qed.
Lemma lem1211790 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211791 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term615 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1211790 A) (@lem1211789 A y l l1 x)). Qed.
Lemma lem1211792 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1211793 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1211792 A x l1) (@lem1211791 A y l l1 x)). Qed.
Lemma lem1211794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1211795 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term616 A y l l1 x) = (term617 A y l l1 x).
Proof. exact (MK_COMB (@lem1211794) (@lem1211793 A y l l1 x)). Qed.
Lemma lem1211796 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1211797 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1211798 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term618 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1211797 A x l1) (@lem1211796 A y l l1 x l2)). Qed.
Lemma lem1211799 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term620 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1211798 A y l l1 x l2)). Qed.
Lemma lem1211800 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211801 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term612 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1211800 A) (@lem1211799 A y l l1 x)). Qed.
Lemma lem1211802 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : ((term611 A y l l1 x) = (term612 A y l l1 x)) = ((term443 A y l l1 x) = (term622 A y l l1 x)).
Proof. exact (MK_COMB (@lem1211795 A y l l1 x) (@lem1211801 A y l l1 x)). Qed.
Lemma lem1211803 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term443 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (EQ_MP (@lem1211802 A y l l1 x) (@lem1211787 A y l l1 x)). Qed.
Lemma lem1211804 {A : Type'} (y : A) (l : list A) (x : A) : (term450 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1211803 A y l l1 x)). Qed.
Lemma lem1211805 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211806 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1211805 A) (@lem1211804 A y l x)). Qed.
Lemma lem1211813 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term619 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (eq_refl (term619 A y l l1 x l2)). Qed.
Lemma lem1211814 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term621 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1211813 A y l l1 x l2)). Qed.
Lemma lem1211815 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211816 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term622 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1211815 A) (@lem1211814 A y l l1 x)). Qed.
Lemma lem1211817 {A : Type'} (y : A) (l : list A) (x : A) : (term623 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1211816 A y l l1 x)). Qed.
Lemma lem1211818 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211819 {A : Type'} (y : A) (l : list A) (x : A) : (term624 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1211818 A) (@lem1211817 A y l x)). Qed.
Lemma lem1211820 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (TRANS (@lem1211806 A y l x) (@lem1211819 A y l x)). Qed.
Lemma lem1211821 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term624 A y l x.
Proof. exact (EQ_MP (@lem1211820 A y l x) (@lem1211544 A l1 l2 y l x h1)). Qed.
Lemma lem1211884 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1211885 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1211884 A x)). Qed.
Lemma lem1211886 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1211888 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1211886 A) (@lem1211885 A)). Qed.
Lemma lem1211889 {A : Type'} (h1 : term297 A) : term267 A.
Proof. exact (EQ_MP (@lem1211888 A) (@lem1211551 A h1)). Qed.
Lemma lem1211965 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1211966 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1211965 A l)). Qed.
Lemma lem1211967 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1211969 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1211967 A) (@lem1211966 A)). Qed.
Lemma lem1211970 {A : Type'} (h1 : term170 A) : term427 A.
Proof. exact (EQ_MP (@lem1211969 A) (@lem1211557 A h1)). Qed.
Lemma lem1211987 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1211999 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212203 {A : Type'} (x : A) (l : list A) (h1 : @List.In A x l) : @List.In A x l.
Proof. exact (h1). Qed.
Lemma lem1212207 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) : term100 A x l.
Proof. exact (h1). Qed.
Lemma lem1212211 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212213 {A : Type'} (P : Prop) (Q : A -> Prop) : (term607 A P Q) = (term608 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1212214 {A : Type'} (P : Prop) (Q : type1143 A) : (term609 A P Q) = (term610 A P Q).
Proof. exact (@lem1212213 (list A) P Q). Qed.
Lemma lem1212215 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term612 A y l l1 x).
Proof. exact (@lem1212214 A (@List.In A x l1) (term439 A y l l1 x)). Qed.
Lemma lem1212216 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1212217 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term614 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1212216 A y l l1 x l2)). Qed.
Lemma lem1212218 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1212219 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term615 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1212218 A) (@lem1212217 A y l l1 x)). Qed.
Lemma lem1212220 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1212221 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1212220 A x l1) (@lem1212219 A y l l1 x)). Qed.
Lemma lem1212222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1212223 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term616 A y l l1 x) = (term617 A y l l1 x).
Proof. exact (MK_COMB (@lem1212222) (@lem1212221 A y l l1 x)). Qed.
Lemma lem1212224 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1212225 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1212226 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term618 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1212225 A x l1) (@lem1212224 A y l l1 x l2)). Qed.
Lemma lem1212227 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term620 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1212226 A y l l1 x l2)). Qed.
Lemma lem1212228 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1212229 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term612 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1212228 A) (@lem1212227 A y l l1 x)). Qed.
Lemma lem1212230 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : ((term611 A y l l1 x) = (term612 A y l l1 x)) = ((term443 A y l l1 x) = (term622 A y l l1 x)).
Proof. exact (MK_COMB (@lem1212223 A y l l1 x) (@lem1212229 A y l l1 x)). Qed.
Lemma lem1212231 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term443 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (EQ_MP (@lem1212230 A y l l1 x) (@lem1212215 A y l l1 x)). Qed.
Lemma lem1212232 {A : Type'} (y : A) (l : list A) (x : A) : (term450 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1212231 A y l l1 x)). Qed.
Lemma lem1212233 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1212234 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1212233 A) (@lem1212232 A y l x)). Qed.
Lemma lem1212241 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term619 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (eq_refl (term619 A y l l1 x l2)). Qed.
Lemma lem1212242 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term621 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1212241 A y l l1 x l2)). Qed.
Lemma lem1212243 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1212244 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term622 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1212243 A) (@lem1212242 A y l l1 x)). Qed.
Lemma lem1212245 {A : Type'} (y : A) (l : list A) (x : A) : (term623 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1212244 A y l l1 x)). Qed.
Lemma lem1212246 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1212247 {A : Type'} (y : A) (l : list A) (x : A) : (term624 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1212246 A) (@lem1212245 A y l x)). Qed.
Lemma lem1212248 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (TRANS (@lem1212234 A y l x) (@lem1212247 A y l x)). Qed.
Lemma lem1212249 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term624 A y l x.
Proof. exact (EQ_MP (@lem1212248 A y l x) (@lem1211544 A l1 l2 y l x h1)). Qed.
Lemma lem1212312 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1212313 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1212312 A x)). Qed.
Lemma lem1212314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1212316 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1212314 A) (@lem1212313 A)). Qed.
Lemma lem1212317 {A : Type'} (h1 : term297 A) : term267 A.
Proof. exact (EQ_MP (@lem1212316 A) (@lem1211551 A h1)). Qed.
Lemma lem1212393 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1212394 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1212393 A l)). Qed.
Lemma lem1212395 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1212397 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1212395 A) (@lem1212394 A)). Qed.
Lemma lem1212398 {A : Type'} (h1 : term170 A) : term427 A.
Proof. exact (EQ_MP (@lem1212397 A) (@lem1211557 A h1)). Qed.
Lemma lem1212424 {A : Type'} (_21664 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term625 A y l x _21664.
Proof. exact (@lem1211609 A l1 l2 y l x h1 _21664). Qed.
Lemma lem1212425 {A : Type'} (y : A) (l : list A) (_21664 : list A) (x : A) : (term625 A y l x _21664) = (term622 A y l _21664 x).
Proof. exact (eq_refl (term625 A y l x _21664)). Qed.
Lemma lem1212426 {A : Type'} (_21664 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term622 A y l _21664 x.
Proof. exact (EQ_MP (@lem1212425 A y l _21664 x) (@lem1212424 A _21664 l1 l2 y l x h1)). Qed.
Lemma lem1212427 {A : Type'} (_21664 : list A) (_21665 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term626 A y l _21664 x _21665.
Proof. exact (@lem1212426 A _21664 l1 l2 y l x h1 _21665). Qed.
Lemma lem1212428 {A : Type'} (y : A) (l : list A) (_21664 : list A) (x : A) (_21665 : list A) : (term626 A y l _21664 x _21665) = (term619 A y l _21664 x _21665).
Proof. exact (eq_refl (term626 A y l _21664 x _21665)). Qed.
Lemma lem1212451 {A : Type'} (_21673 : A) (h1 : term297 A) : term258 A _21673.
Proof. exact (@lem1211677 A h1 _21673). Qed.
Lemma lem1212452 {A : Type'} (_21673 : A) : (term258 A _21673) = (term248 A _21673).
Proof. exact (eq_refl (term258 A _21673)). Qed.
Lemma lem1212484 {A : Type'} (_21684 : list A) (h1 : term170 A) : term627 A _21684.
Proof. exact (@lem1211758 A h1 _21684). Qed.
Lemma lem1212485 {A : Type'} (_21684 : list A) : (term627 A _21684) = ((@List.app A (@nil A) _21684) = _21684).
Proof. exact (eq_refl (term627 A _21684)). Qed.
Lemma lem1212496 {A : Type'} (_21688 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term625 A y l x _21688.
Proof. exact (@lem1211821 A l1 l2 y l x h1 _21688). Qed.
Lemma lem1212497 {A : Type'} (y : A) (l : list A) (_21688 : list A) (x : A) : (term625 A y l x _21688) = (term622 A y l _21688 x).
Proof. exact (eq_refl (term625 A y l x _21688)). Qed.
Lemma lem1212498 {A : Type'} (_21688 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term622 A y l _21688 x.
Proof. exact (EQ_MP (@lem1212497 A y l _21688 x) (@lem1212496 A _21688 l1 l2 y l x h1)). Qed.
Lemma lem1212499 {A : Type'} (_21688 : list A) (_21689 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term626 A y l _21688 x _21689.
Proof. exact (@lem1212498 A _21688 l1 l2 y l x h1 _21689). Qed.
Lemma lem1212500 {A : Type'} (y : A) (l : list A) (_21688 : list A) (x : A) (_21689 : list A) : (term626 A y l _21688 x _21689) = (term619 A y l _21688 x _21689).
Proof. exact (eq_refl (term626 A y l _21688 x _21689)). Qed.
Lemma lem1212523 {A : Type'} (_21697 : A) (h1 : term297 A) : term258 A _21697.
Proof. exact (@lem1211889 A h1 _21697). Qed.
Lemma lem1212524 {A : Type'} (_21697 : A) : (term258 A _21697) = (term248 A _21697).
Proof. exact (eq_refl (term258 A _21697)). Qed.
Lemma lem1212556 {A : Type'} (_21708 : list A) (h1 : term170 A) : term627 A _21708.
Proof. exact (@lem1211970 A h1 _21708). Qed.
Lemma lem1212557 {A : Type'} (_21708 : list A) : (term627 A _21708) = ((@List.app A (@nil A) _21708) = _21708).
Proof. exact (eq_refl (term627 A _21708)). Qed.
Lemma lem1212640 {A : Type'} (_21736 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term625 A y l x _21736.
Proof. exact (@lem1212249 A l1 l2 y l x h1 _21736). Qed.
Lemma lem1212641 {A : Type'} (y : A) (l : list A) (_21736 : list A) (x : A) : (term625 A y l x _21736) = (term622 A y l _21736 x).
Proof. exact (eq_refl (term625 A y l x _21736)). Qed.
Lemma lem1212642 {A : Type'} (_21736 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term622 A y l _21736 x.
Proof. exact (EQ_MP (@lem1212641 A y l _21736 x) (@lem1212640 A _21736 l1 l2 y l x h1)). Qed.
Lemma lem1212643 {A : Type'} (_21736 : list A) (_21737 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term626 A y l _21736 x _21737.
Proof. exact (@lem1212642 A _21736 l1 l2 y l x h1 _21737). Qed.
Lemma lem1212644 {A : Type'} (y : A) (l : list A) (_21736 : list A) (x : A) (_21737 : list A) : (term626 A y l _21736 x _21737) = (term619 A y l _21736 x _21737).
Proof. exact (eq_refl (term626 A y l _21736 x _21737)). Qed.
Lemma lem1212667 {A : Type'} (_21745 : A) (h1 : term297 A) : term258 A _21745.
Proof. exact (@lem1212317 A h1 _21745). Qed.
Lemma lem1212668 {A : Type'} (_21745 : A) : (term258 A _21745) = (term248 A _21745).
Proof. exact (eq_refl (term258 A _21745)). Qed.
Lemma lem1212700 {A : Type'} (_21756 : list A) (h1 : term170 A) : term627 A _21756.
Proof. exact (@lem1212398 A h1 _21756). Qed.
Lemma lem1212701 {A : Type'} (_21756 : list A) : (term627 A _21756) = ((@List.app A (@nil A) _21756) = _21756).
Proof. exact (eq_refl (term627 A _21756)). Qed.
Lemma lem1212729 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212735 {A : Type'} (_21664 : list A) (_21665 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term619 A y l _21664 x _21665.
Proof. exact (EQ_MP (@lem1212428 A y l _21664 x _21665) (@lem1212427 A _21664 _21665 l1 l2 y l x h1)). Qed.
Lemma lem1212769 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212797 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212803 {A : Type'} (_21688 : list A) (_21689 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term619 A y l _21688 x _21689.
Proof. exact (EQ_MP (@lem1212500 A y l _21688 x _21689) (@lem1212499 A _21688 _21689 l1 l2 y l x h1)). Qed.
Lemma lem1212837 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212841 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : l = (term102 A l1 x l2).
Proof. exact (proj2 (@lem1211561 A l l1 x l2 h1)). Qed.
Lemma lem1212867 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212907 {A : Type'} (x : A) (l : list A) (h1 : @List.In A x l) : @List.In A x l.
Proof. exact (h1). Qed.
Lemma lem1212909 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) : term100 A x l.
Proof. exact (h1). Qed.
Lemma lem1212935 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1212941 {A : Type'} (_21736 : list A) (_21737 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term619 A y l _21736 x _21737.
Proof. exact (EQ_MP (@lem1212644 A y l _21736 x _21737) (@lem1212643 A _21736 _21737 l1 l2 y l x h1)). Qed.
Lemma lem1212979 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : l = (term102 A l1 x l2).
Proof. exact (proj2 (@lem1211565 A l l1 x l2 h1)). Qed.
Lemma lem1213031 {A : Type'} (y : A) (l : list A) (_21664 : list A) (_21665 : list A) : (term628 A y l _21664 _21665) = (term628 A y l _21664 _21665).
Proof. exact (eq_refl (term628 A y l _21664 _21665)). Qed.
Lemma lem1213032 {A : Type'} (l : list A) (_21664 : list A) (_21665 : list A) (x : A) (y : A) (h1 : x = y) : (term629 A y l _21664 _21665 x) = (term630 A l _21664 _21665 y).
Proof. exact (MK_COMB (@lem1213031 A y l _21664 _21665) (@lem1212769 A x y h1)). Qed.
Lemma lem1213033 {A : Type'} (l : list A) (_21664 : list A) (y : A) (_21665 : list A) : (term630 A l _21664 _21665 y) = (term631 A l _21664 y _21665).
Proof. exact (eq_refl (term630 A l _21664 _21665 y)). Qed.
Lemma lem1213034 {A : Type'} (y : A) (l : list A) (_21664 : list A) (_21665 : list A) (x : A) : (term632 A y l _21664 _21665 x) = (term632 A y l _21664 _21665 x).
Proof. exact (eq_refl (term632 A y l _21664 _21665 x)). Qed.
Lemma lem1213035 {A : Type'} (x : A) (l : list A) (_21664 : list A) (y : A) (_21665 : list A) : ((term629 A y l _21664 _21665 x) = (term630 A l _21664 _21665 y)) = ((term629 A y l _21664 _21665 x) = (term631 A l _21664 y _21665)).
Proof. exact (MK_COMB (@lem1213034 A y l _21664 _21665 x) (@lem1213033 A l _21664 y _21665)). Qed.
Lemma lem1213036 {A : Type'} (y : A) (l : list A) (_21664 : list A) (x : A) (_21665 : list A) : (term629 A y l _21664 _21665 x) = (term619 A y l _21664 x _21665).
Proof. exact (eq_refl (term629 A y l _21664 _21665 x)). Qed.
Lemma lem1213037 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1213038 {A : Type'} (y : A) (l : list A) (_21664 : list A) (x : A) (_21665 : list A) : (term632 A y l _21664 _21665 x) = (term633 A y l _21664 x _21665).
Proof. exact (MK_COMB (@lem1213037) (@lem1213036 A y l _21664 x _21665)). Qed.
Lemma lem1213039 {A : Type'} (l : list A) (_21664 : list A) (y : A) (_21665 : list A) : (term631 A l _21664 y _21665) = (term631 A l _21664 y _21665).
Proof. exact (eq_refl (term631 A l _21664 y _21665)). Qed.
Lemma lem1213040 {A : Type'} (x : A) (l : list A) (_21664 : list A) (y : A) (_21665 : list A) : ((term629 A y l _21664 _21665 x) = (term631 A l _21664 y _21665)) = ((term619 A y l _21664 x _21665) = (term631 A l _21664 y _21665)).
Proof. exact (MK_COMB (@lem1213038 A y l _21664 x _21665) (@lem1213039 A l _21664 y _21665)). Qed.
Lemma lem1213041 {A : Type'} (x : A) (l : list A) (_21664 : list A) (y : A) (_21665 : list A) : ((term629 A y l _21664 _21665 x) = (term630 A l _21664 _21665 y)) = ((term619 A y l _21664 x _21665) = (term631 A l _21664 y _21665)).
Proof. exact (TRANS (@lem1213035 A x l _21664 y _21665) (@lem1213040 A x l _21664 y _21665)). Qed.
Lemma lem1213042 {A : Type'} (l : list A) (_21664 : list A) (_21665 : list A) (x : A) (y : A) (h1 : x = y) : (term619 A y l _21664 x _21665) = (term631 A l _21664 y _21665).
Proof. exact (EQ_MP (@lem1213041 A x l _21664 y _21665) (@lem1213032 A l _21664 _21665 x y h1)). Qed.
Lemma lem1213043 {A : Type'} (_21664 : list A) (_21665 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term519 A l1 l2 y l x) (h2 : x = y) : term631 A l _21664 y _21665.
Proof. exact (EQ_MP (@lem1213042 A l _21664 _21665 x y h2) (@lem1212735 A _21664 _21665 l1 l2 y l x h1)). Qed.
Lemma lem1213085 {A : Type'} (_21673 : A) (h1 : term297 A) : term248 A _21673.
Proof. exact (EQ_MP (@lem1212452 A _21673) (@lem1212451 A _21673 h1)). Qed.
Lemma lem1213252 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1213253 {A : Type'} (y : A) (_21688 : list A) (x : A) (_21689 : list A) : (term634 A y _21688 x _21689) = (term634 A y _21688 x _21689).
Proof. exact (eq_refl (term634 A y _21688 x _21689)). Qed.
Lemma lem1213254 {A : Type'} (y : A) (_21688 : list A) (_21689 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term635 A y _21688 x _21689 l) = (term636 A y _21688 _21689 l1 x l2).
Proof. exact (MK_COMB (@lem1213253 A y _21688 x _21689) (@lem1212841 A l l1 x l2 h1)). Qed.
Lemma lem1213255 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (x : A) (_21689 : list A) : (term636 A y _21688 _21689 l1 x l2) = (term637 A y l1 l2 _21688 x _21689).
Proof. exact (eq_refl (term636 A y _21688 _21689 l1 x l2)). Qed.
Lemma lem1213256 {A : Type'} (y : A) (_21688 : list A) (x : A) (_21689 : list A) (l : list A) : (term638 A y _21688 x _21689 l) = (term638 A y _21688 x _21689 l).
Proof. exact (eq_refl (term638 A y _21688 x _21689 l)). Qed.
Lemma lem1213257 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (x : A) (_21689 : list A) : ((term635 A y _21688 x _21689 l) = (term636 A y _21688 _21689 l1 x l2)) = ((term635 A y _21688 x _21689 l) = (term637 A y l1 l2 _21688 x _21689)).
Proof. exact (MK_COMB (@lem1213256 A y _21688 x _21689 l) (@lem1213255 A y l1 l2 _21688 x _21689)). Qed.
Lemma lem1213258 {A : Type'} (y : A) (l : list A) (_21688 : list A) (x : A) (_21689 : list A) : (term635 A y _21688 x _21689 l) = (term619 A y l _21688 x _21689).
Proof. exact (eq_refl (term635 A y _21688 x _21689 l)). Qed.
Lemma lem1213259 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1213260 {A : Type'} (y : A) (l : list A) (_21688 : list A) (x : A) (_21689 : list A) : (term638 A y _21688 x _21689 l) = (term633 A y l _21688 x _21689).
Proof. exact (MK_COMB (@lem1213259) (@lem1213258 A y l _21688 x _21689)). Qed.
Lemma lem1213261 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (x : A) (_21689 : list A) : (term637 A y l1 l2 _21688 x _21689) = (term637 A y l1 l2 _21688 x _21689).
Proof. exact (eq_refl (term637 A y l1 l2 _21688 x _21689)). Qed.
Lemma lem1213262 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (x : A) (_21689 : list A) : ((term635 A y _21688 x _21689 l) = (term637 A y l1 l2 _21688 x _21689)) = ((term619 A y l _21688 x _21689) = (term637 A y l1 l2 _21688 x _21689)).
Proof. exact (MK_COMB (@lem1213260 A y l _21688 x _21689) (@lem1213261 A y l1 l2 _21688 x _21689)). Qed.
Lemma lem1213263 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (x : A) (_21689 : list A) : ((term635 A y _21688 x _21689 l) = (term636 A y _21688 _21689 l1 x l2)) = ((term619 A y l _21688 x _21689) = (term637 A y l1 l2 _21688 x _21689)).
Proof. exact (TRANS (@lem1213257 A l y l1 l2 _21688 x _21689) (@lem1213262 A l y l1 l2 _21688 x _21689)). Qed.
Lemma lem1213264 {A : Type'} (y : A) (_21688 : list A) (_21689 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term619 A y l _21688 x _21689) = (term637 A y l1 l2 _21688 x _21689).
Proof. exact (EQ_MP (@lem1213263 A l y l1 l2 _21688 x _21689) (@lem1213254 A y _21688 _21689 l l1 x l2 h1)). Qed.
Lemma lem1213265 {A : Type'} (_21688 : list A) (_21689 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) : term637 A y l1 l2 _21688 x _21689.
Proof. exact (EQ_MP (@lem1213264 A y _21688 _21689 l l1 x l2 h1) (@lem1212803 A _21688 _21689 l1 l2 y l x h2)). Qed.
Lemma lem1213391 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1213489 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (_21689 : list A) : (term639 A y l1 l2 _21688 _21689) = (term639 A y l1 l2 _21688 _21689).
Proof. exact (eq_refl (term639 A y l1 l2 _21688 _21689)). Qed.
Lemma lem1213490 {A : Type'} (l1 : list A) (l2 : list A) (_21688 : list A) (_21689 : list A) (x : A) (y : A) (h1 : x = y) : (term640 A y l1 l2 _21688 _21689 x) = (term641 A l1 l2 _21688 _21689 y).
Proof. exact (MK_COMB (@lem1213489 A y l1 l2 _21688 _21689) (@lem1213391 A x y h1)). Qed.
Lemma lem1213491 {A : Type'} (l1 : list A) (l2 : list A) (_21688 : list A) (y : A) (_21689 : list A) : (term641 A l1 l2 _21688 _21689 y) = (term642 A l1 l2 _21688 y _21689).
Proof. exact (eq_refl (term641 A l1 l2 _21688 _21689 y)). Qed.
Lemma lem1213492 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (_21689 : list A) (x : A) : (term643 A y l1 l2 _21688 _21689 x) = (term643 A y l1 l2 _21688 _21689 x).
Proof. exact (eq_refl (term643 A y l1 l2 _21688 _21689 x)). Qed.
Lemma lem1213493 {A : Type'} (x : A) (l1 : list A) (l2 : list A) (_21688 : list A) (y : A) (_21689 : list A) : ((term640 A y l1 l2 _21688 _21689 x) = (term641 A l1 l2 _21688 _21689 y)) = ((term640 A y l1 l2 _21688 _21689 x) = (term642 A l1 l2 _21688 y _21689)).
Proof. exact (MK_COMB (@lem1213492 A y l1 l2 _21688 _21689 x) (@lem1213491 A l1 l2 _21688 y _21689)). Qed.
Lemma lem1213494 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (x : A) (_21689 : list A) : (term640 A y l1 l2 _21688 _21689 x) = (term637 A y l1 l2 _21688 x _21689).
Proof. exact (eq_refl (term640 A y l1 l2 _21688 _21689 x)). Qed.
Lemma lem1213495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1213496 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21688 : list A) (x : A) (_21689 : list A) : (term643 A y l1 l2 _21688 _21689 x) = (term644 A y l1 l2 _21688 x _21689).
Proof. exact (MK_COMB (@lem1213495) (@lem1213494 A y l1 l2 _21688 x _21689)). Qed.
Lemma lem1213497 {A : Type'} (l1 : list A) (l2 : list A) (_21688 : list A) (y : A) (_21689 : list A) : (term642 A l1 l2 _21688 y _21689) = (term642 A l1 l2 _21688 y _21689).
Proof. exact (eq_refl (term642 A l1 l2 _21688 y _21689)). Qed.
Lemma lem1213498 {A : Type'} (x : A) (l1 : list A) (l2 : list A) (_21688 : list A) (y : A) (_21689 : list A) : ((term640 A y l1 l2 _21688 _21689 x) = (term642 A l1 l2 _21688 y _21689)) = ((term637 A y l1 l2 _21688 x _21689) = (term642 A l1 l2 _21688 y _21689)).
Proof. exact (MK_COMB (@lem1213496 A y l1 l2 _21688 x _21689) (@lem1213497 A l1 l2 _21688 y _21689)). Qed.
Lemma lem1213499 {A : Type'} (x : A) (l1 : list A) (l2 : list A) (_21688 : list A) (y : A) (_21689 : list A) : ((term640 A y l1 l2 _21688 _21689 x) = (term641 A l1 l2 _21688 _21689 y)) = ((term637 A y l1 l2 _21688 x _21689) = (term642 A l1 l2 _21688 y _21689)).
Proof. exact (TRANS (@lem1213493 A x l1 l2 _21688 y _21689) (@lem1213498 A x l1 l2 _21688 y _21689)). Qed.
Lemma lem1213500 {A : Type'} (l1 : list A) (l2 : list A) (_21688 : list A) (_21689 : list A) (x : A) (y : A) (h1 : x = y) : (term637 A y l1 l2 _21688 x _21689) = (term642 A l1 l2 _21688 y _21689).
Proof. exact (EQ_MP (@lem1213499 A x l1 l2 _21688 y _21689) (@lem1213490 A l1 l2 _21688 _21689 x y h1)). Qed.
Lemma lem1213501 {A : Type'} (_21688 : list A) (_21689 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term642 A l1 l2 _21688 y _21689.
Proof. exact (EQ_MP (@lem1213500 A l1 l2 _21688 _21689 x y h3) (@lem1213265 A _21688 _21689 l1 l2 y l x h1 h2)). Qed.
Lemma lem1213543 {A : Type'} (_21697 : A) (h1 : term297 A) : term248 A _21697.
Proof. exact (EQ_MP (@lem1212524 A _21697) (@lem1212523 A _21697 h1)). Qed.
Lemma lem1213822 {A : Type'} (l : list A) : (term645 A l) = (term645 A l).
Proof. exact (eq_refl (term645 A l)). Qed.
Lemma lem1213823 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : (term646 A l x) = (term646 A l y).
Proof. exact (MK_COMB (@lem1213822 A l) (@lem1212867 A x y h1)). Qed.
Lemma lem1213824 {A : Type'} (y : A) (l : list A) : (term646 A l y) = (@List.In A y l).
Proof. exact (eq_refl (term646 A l y)). Qed.
Lemma lem1213825 {A : Type'} (l : list A) (x : A) : (term647 A l x) = (term647 A l x).
Proof. exact (eq_refl (term647 A l x)). Qed.
Lemma lem1213826 {A : Type'} (x : A) (y : A) (l : list A) : ((term646 A l x) = (term646 A l y)) = ((term646 A l x) = (@List.In A y l)).
Proof. exact (MK_COMB (@lem1213825 A l x) (@lem1213824 A y l)). Qed.
Lemma lem1213827 {A : Type'} (x : A) (l : list A) : (term646 A l x) = (@List.In A x l).
Proof. exact (eq_refl (term646 A l x)). Qed.
Lemma lem1213828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1213829 {A : Type'} (x : A) (l : list A) : (term647 A l x) = (term648 A x l).
Proof. exact (MK_COMB (@lem1213828) (@lem1213827 A x l)). Qed.
Lemma lem1213830 {A : Type'} (y : A) (l : list A) : (@List.In A y l) = (@List.In A y l).
Proof. exact (eq_refl (@List.In A y l)). Qed.
Lemma lem1213831 {A : Type'} (x : A) (y : A) (l : list A) : ((term646 A l x) = (@List.In A y l)) = ((@List.In A x l) = (@List.In A y l)).
Proof. exact (MK_COMB (@lem1213829 A x l) (@lem1213830 A y l)). Qed.
Lemma lem1213832 {A : Type'} (x : A) (y : A) (l : list A) : ((term646 A l x) = (term646 A l y)) = ((@List.In A x l) = (@List.In A y l)).
Proof. exact (TRANS (@lem1213826 A x y l) (@lem1213831 A x y l)). Qed.
Lemma lem1213833 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : (@List.In A x l) = (@List.In A y l).
Proof. exact (EQ_MP (@lem1213832 A x y l) (@lem1213823 A l x y h1)). Qed.
Lemma lem1213835 {A : Type'} (l : list A) : (term649 A l) = (term649 A l).
Proof. exact (eq_refl (term649 A l)). Qed.
Lemma lem1213836 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : (term650 A l x) = (term650 A l y).
Proof. exact (MK_COMB (@lem1213835 A l) (@lem1212867 A x y h1)). Qed.
Lemma lem1213837 {A : Type'} (y : A) (l : list A) : (term650 A l y) = (term100 A y l).
Proof. exact (eq_refl (term650 A l y)). Qed.
Lemma lem1213838 {A : Type'} (l : list A) (x : A) : (term651 A l x) = (term651 A l x).
Proof. exact (eq_refl (term651 A l x)). Qed.
Lemma lem1213839 {A : Type'} (x : A) (y : A) (l : list A) : ((term650 A l x) = (term650 A l y)) = ((term650 A l x) = (term100 A y l)).
Proof. exact (MK_COMB (@lem1213838 A l x) (@lem1213837 A y l)). Qed.
Lemma lem1213840 {A : Type'} (x : A) (l : list A) : (term650 A l x) = (term100 A x l).
Proof. exact (eq_refl (term650 A l x)). Qed.
Lemma lem1213841 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1213842 {A : Type'} (x : A) (l : list A) : (term651 A l x) = (term652 A x l).
Proof. exact (MK_COMB (@lem1213841) (@lem1213840 A x l)). Qed.
Lemma lem1213843 {A : Type'} (y : A) (l : list A) : (term100 A y l) = (term100 A y l).
Proof. exact (eq_refl (term100 A y l)). Qed.
Lemma lem1213844 {A : Type'} (x : A) (y : A) (l : list A) : ((term650 A l x) = (term100 A y l)) = ((term100 A x l) = (term100 A y l)).
Proof. exact (MK_COMB (@lem1213842 A x l) (@lem1213843 A y l)). Qed.
Lemma lem1213845 {A : Type'} (x : A) (y : A) (l : list A) : ((term650 A l x) = (term650 A l y)) = ((term100 A x l) = (term100 A y l)).
Proof. exact (TRANS (@lem1213839 A x y l) (@lem1213844 A x y l)). Qed.
Lemma lem1213846 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : (term100 A x l) = (term100 A y l).
Proof. exact (EQ_MP (@lem1213845 A x y l) (@lem1213836 A l x y h1)). Qed.
Lemma lem1213847 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term100 A x l) (h2 : x = y) : term100 A y l.
Proof. exact (EQ_MP (@lem1213846 A l x y h2) (@lem1212909 A x l h1)). Qed.
Lemma lem1213931 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1213932 {A : Type'} (y : A) (_21736 : list A) (x : A) (_21737 : list A) : (term634 A y _21736 x _21737) = (term634 A y _21736 x _21737).
Proof. exact (eq_refl (term634 A y _21736 x _21737)). Qed.
Lemma lem1213933 {A : Type'} (y : A) (_21736 : list A) (_21737 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term635 A y _21736 x _21737 l) = (term636 A y _21736 _21737 l1 x l2).
Proof. exact (MK_COMB (@lem1213932 A y _21736 x _21737) (@lem1212979 A l l1 x l2 h1)). Qed.
Lemma lem1213934 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (x : A) (_21737 : list A) : (term636 A y _21736 _21737 l1 x l2) = (term637 A y l1 l2 _21736 x _21737).
Proof. exact (eq_refl (term636 A y _21736 _21737 l1 x l2)). Qed.
Lemma lem1213935 {A : Type'} (y : A) (_21736 : list A) (x : A) (_21737 : list A) (l : list A) : (term638 A y _21736 x _21737 l) = (term638 A y _21736 x _21737 l).
Proof. exact (eq_refl (term638 A y _21736 x _21737 l)). Qed.
Lemma lem1213936 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (x : A) (_21737 : list A) : ((term635 A y _21736 x _21737 l) = (term636 A y _21736 _21737 l1 x l2)) = ((term635 A y _21736 x _21737 l) = (term637 A y l1 l2 _21736 x _21737)).
Proof. exact (MK_COMB (@lem1213935 A y _21736 x _21737 l) (@lem1213934 A y l1 l2 _21736 x _21737)). Qed.
Lemma lem1213937 {A : Type'} (y : A) (l : list A) (_21736 : list A) (x : A) (_21737 : list A) : (term635 A y _21736 x _21737 l) = (term619 A y l _21736 x _21737).
Proof. exact (eq_refl (term635 A y _21736 x _21737 l)). Qed.
Lemma lem1213938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1213939 {A : Type'} (y : A) (l : list A) (_21736 : list A) (x : A) (_21737 : list A) : (term638 A y _21736 x _21737 l) = (term633 A y l _21736 x _21737).
Proof. exact (MK_COMB (@lem1213938) (@lem1213937 A y l _21736 x _21737)). Qed.
Lemma lem1213940 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (x : A) (_21737 : list A) : (term637 A y l1 l2 _21736 x _21737) = (term637 A y l1 l2 _21736 x _21737).
Proof. exact (eq_refl (term637 A y l1 l2 _21736 x _21737)). Qed.
Lemma lem1213941 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (x : A) (_21737 : list A) : ((term635 A y _21736 x _21737 l) = (term637 A y l1 l2 _21736 x _21737)) = ((term619 A y l _21736 x _21737) = (term637 A y l1 l2 _21736 x _21737)).
Proof. exact (MK_COMB (@lem1213939 A y l _21736 x _21737) (@lem1213940 A y l1 l2 _21736 x _21737)). Qed.
Lemma lem1213942 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (x : A) (_21737 : list A) : ((term635 A y _21736 x _21737 l) = (term636 A y _21736 _21737 l1 x l2)) = ((term619 A y l _21736 x _21737) = (term637 A y l1 l2 _21736 x _21737)).
Proof. exact (TRANS (@lem1213936 A l y l1 l2 _21736 x _21737) (@lem1213941 A l y l1 l2 _21736 x _21737)). Qed.
Lemma lem1213943 {A : Type'} (y : A) (_21736 : list A) (_21737 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term619 A y l _21736 x _21737) = (term637 A y l1 l2 _21736 x _21737).
Proof. exact (EQ_MP (@lem1213942 A l y l1 l2 _21736 x _21737) (@lem1213933 A y _21736 _21737 l l1 x l2 h1)). Qed.
Lemma lem1213944 {A : Type'} (_21736 : list A) (_21737 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) : term637 A y l1 l2 _21736 x _21737.
Proof. exact (EQ_MP (@lem1213943 A y _21736 _21737 l l1 x l2 h1) (@lem1212941 A _21736 _21737 l1 l2 y l x h2)). Qed.
Lemma lem1214154 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (_21737 : list A) : (term639 A y l1 l2 _21736 _21737) = (term639 A y l1 l2 _21736 _21737).
Proof. exact (eq_refl (term639 A y l1 l2 _21736 _21737)). Qed.
Lemma lem1214155 {A : Type'} (l1 : list A) (l2 : list A) (_21736 : list A) (_21737 : list A) (x : A) (y : A) (h1 : x = y) : (term640 A y l1 l2 _21736 _21737 x) = (term641 A l1 l2 _21736 _21737 y).
Proof. exact (MK_COMB (@lem1214154 A y l1 l2 _21736 _21737) (@lem1213931 A x y h1)). Qed.
Lemma lem1214156 {A : Type'} (l1 : list A) (l2 : list A) (_21736 : list A) (y : A) (_21737 : list A) : (term641 A l1 l2 _21736 _21737 y) = (term642 A l1 l2 _21736 y _21737).
Proof. exact (eq_refl (term641 A l1 l2 _21736 _21737 y)). Qed.
Lemma lem1214157 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (_21737 : list A) (x : A) : (term643 A y l1 l2 _21736 _21737 x) = (term643 A y l1 l2 _21736 _21737 x).
Proof. exact (eq_refl (term643 A y l1 l2 _21736 _21737 x)). Qed.
Lemma lem1214158 {A : Type'} (x : A) (l1 : list A) (l2 : list A) (_21736 : list A) (y : A) (_21737 : list A) : ((term640 A y l1 l2 _21736 _21737 x) = (term641 A l1 l2 _21736 _21737 y)) = ((term640 A y l1 l2 _21736 _21737 x) = (term642 A l1 l2 _21736 y _21737)).
Proof. exact (MK_COMB (@lem1214157 A y l1 l2 _21736 _21737 x) (@lem1214156 A l1 l2 _21736 y _21737)). Qed.
Lemma lem1214159 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (x : A) (_21737 : list A) : (term640 A y l1 l2 _21736 _21737 x) = (term637 A y l1 l2 _21736 x _21737).
Proof. exact (eq_refl (term640 A y l1 l2 _21736 _21737 x)). Qed.
Lemma lem1214160 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1214161 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_21736 : list A) (x : A) (_21737 : list A) : (term643 A y l1 l2 _21736 _21737 x) = (term644 A y l1 l2 _21736 x _21737).
Proof. exact (MK_COMB (@lem1214160) (@lem1214159 A y l1 l2 _21736 x _21737)). Qed.
Lemma lem1214162 {A : Type'} (l1 : list A) (l2 : list A) (_21736 : list A) (y : A) (_21737 : list A) : (term642 A l1 l2 _21736 y _21737) = (term642 A l1 l2 _21736 y _21737).
Proof. exact (eq_refl (term642 A l1 l2 _21736 y _21737)). Qed.
Lemma lem1214163 {A : Type'} (x : A) (l1 : list A) (l2 : list A) (_21736 : list A) (y : A) (_21737 : list A) : ((term640 A y l1 l2 _21736 _21737 x) = (term642 A l1 l2 _21736 y _21737)) = ((term637 A y l1 l2 _21736 x _21737) = (term642 A l1 l2 _21736 y _21737)).
Proof. exact (MK_COMB (@lem1214161 A y l1 l2 _21736 x _21737) (@lem1214162 A l1 l2 _21736 y _21737)). Qed.
Lemma lem1214164 {A : Type'} (x : A) (l1 : list A) (l2 : list A) (_21736 : list A) (y : A) (_21737 : list A) : ((term640 A y l1 l2 _21736 _21737 x) = (term641 A l1 l2 _21736 _21737 y)) = ((term637 A y l1 l2 _21736 x _21737) = (term642 A l1 l2 _21736 y _21737)).
Proof. exact (TRANS (@lem1214158 A x l1 l2 _21736 y _21737) (@lem1214163 A x l1 l2 _21736 y _21737)). Qed.
Lemma lem1214165 {A : Type'} (l1 : list A) (l2 : list A) (_21736 : list A) (_21737 : list A) (x : A) (y : A) (h1 : x = y) : (term637 A y l1 l2 _21736 x _21737) = (term642 A l1 l2 _21736 y _21737).
Proof. exact (EQ_MP (@lem1214164 A x l1 l2 _21736 y _21737) (@lem1214155 A l1 l2 _21736 _21737 x y h1)). Qed.
Lemma lem1214166 {A : Type'} (_21736 : list A) (_21737 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term642 A l1 l2 _21736 y _21737.
Proof. exact (EQ_MP (@lem1214165 A l1 l2 _21736 _21737 x y h3) (@lem1213944 A _21736 _21737 l1 l2 y l x h1 h2)). Qed.
Lemma lem1214208 {A : Type'} (_21745 : A) (h1 : term297 A) : term248 A _21745.
Proof. exact (EQ_MP (@lem1212668 A _21745) (@lem1212667 A _21745 h1)). Qed.
Lemma lem1214460 {A : Type'} (x : list A) (y : list A) (z : list A) : term653 A x y z.
Proof. exact (@lem21385 (list A) x y z). Qed.
Lemma lem1214466 {A : Type'} (_21684 : list A) (h1 : term170 A) : (@List.app A (@nil A) _21684) = _21684.
Proof. exact (EQ_MP (@lem1212485 A _21684) (@lem1212484 A _21684 h1)). Qed.
Lemma lem1214467 {A : Type'} (_21684 : list A) (h1 : term170 A) : (@List.app A (@nil A) _21684) = _21684.
Proof. exact (@lem1214466 A _21684 h1). Qed.
Lemma lem1214468 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : (term654 A y l) = (@cons A y l).
Proof. exact (@lem1214467 A (@cons A y l) h1). Qed.
Lemma lem1214469 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : term655 A y l.
Proof. exact (fun h0 : term656 A y l => @lem1214468 A y l h1). Qed.
Lemma lem1214471 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214472 {A : Type'} (y : A) (l : list A) : (term655 A y l) = ((term654 A y l) = (@cons A y l)).
Proof. exact (@lem1214471 ((term654 A y l) = (@cons A y l))). Qed.
Lemma lem1214473 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : (term654 A y l) = (@cons A y l).
Proof. exact (EQ_MP (@lem1214472 A y l) (@lem1214469 A y l h1)). Qed.
Lemma lem1214475 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem21386 (list A) x). Qed.
Lemma lem1214476 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem1214475 A x). Qed.
Lemma lem1214477 {A : Type'} (y : A) (l : list A) : (term654 A y l) = (term654 A y l).
Proof. exact (@lem1214476 A (term654 A y l)). Qed.
Lemma lem1214478 {A : Type'} (y : A) (l : list A) : term658 A y l.
Proof. exact (fun h0 : term659 A y l => @lem1214477 A y l). Qed.
Lemma lem1214480 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214481 {A : Type'} (y : A) (l : list A) : (term658 A y l) = ((term654 A y l) = (term654 A y l)).
Proof. exact (@lem1214480 ((term654 A y l) = (term654 A y l))). Qed.
Lemma lem1214482 {A : Type'} (y : A) (l : list A) : (term654 A y l) = (term654 A y l).
Proof. exact (EQ_MP (@lem1214481 A y l) (@lem1214478 A y l)). Qed.
Lemma lem1214500 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1214501 {A : Type'} (y : list A) (x : list A) (z : list A) : (term660 A x y z) = (term661 A y x z).
Proof. exact (@lem1214500 (y = z) (term662 A x z)). Qed.
Lemma lem1214511 {A : Type'} (x : list A) (y : list A) : (term663 A x y) = (term663 A x y).
Proof. exact (eq_refl (term663 A x y)). Qed.
Lemma lem1214512 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term664 A y x z).
Proof. exact (MK_COMB (@lem1214511 A x y) (@lem1214501 A y x z)). Qed.
Lemma lem1214516 (q : Prop) (p : Prop) (r : Prop) : (term665 p q r) = (term665 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1214517 {A : Type'} (y : list A) (x : list A) (z : list A) : (term664 A y x z) = (term666 A y x z).
Proof. exact (@lem1214516 (y = z) (term662 A x y) (term662 A x z)). Qed.
Lemma lem1214539 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (TRANS (@lem1214512 A y x z) (@lem1214517 A y x z)). Qed.
Lemma lem1214540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1214541 {A : Type'} (y : list A) (x : list A) (z : list A) : (term667 A x y z) = (term668 A y x z).
Proof. exact (MK_COMB (@lem1214540) (@lem1214539 A y x z)). Qed.
Lemma lem1214563 {A : Type'} (y : list A) (x : list A) (z : list A) : (term666 A y x z) = (term666 A y x z).
Proof. exact (eq_refl (term666 A y x z)). Qed.
Lemma lem1214564 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = ((term666 A y x z) = (term666 A y x z)).
Proof. exact (MK_COMB (@lem1214541 A y x z) (@lem1214563 A y x z)). Qed.
Lemma lem1214566 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1214567 (x : Prop) : (x = x) = True.
Proof. exact (@lem1214566 Prop x). Qed.
Lemma lem1214568 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term666 A y x z) = (term666 A y x z)) = True.
Proof. exact (@lem1214567 (term666 A y x z)). Qed.
Lemma lem1214569 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = True.
Proof. exact (TRANS (@lem1214564 A y x z) (@lem1214568 A y x z)). Qed.
Lemma lem1214570 {A : Type'} (y : list A) (x : list A) (z : list A) : True = ((term653 A x y z) = (term666 A y x z)).
Proof. exact (SYM (@lem1214569 A y x z)). Qed.
Lemma lem1214571 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (EQ_MP (@lem1214570 A y x z) (@lem0)). Qed.
Lemma lem1214572 {A : Type'} (y : list A) (x : list A) (z : list A) : term666 A y x z.
Proof. exact (EQ_MP (@lem1214571 A y x z) (@lem1214460 A x y z)). Qed.
Lemma lem1214574 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1214575 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term670 A x y z).
Proof. exact (@lem1214574 (term671 A y x z) (y = z)). Qed.
Lemma lem1214577 (a : Prop) (b : Prop) : (term672 a b) = (term673 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1214578 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term675 A y x z).
Proof. exact (@lem1214577 (term662 A x y) (term662 A x z)). Qed.
Lemma lem1214580 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1214581 {A : Type'} (x : list A) (y : list A) : (term677 A x y) = (x = y).
Proof. exact (@lem1214580 (x = y)). Qed.
Lemma lem1214582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1214583 {A : Type'} (x : list A) (y : list A) : (term678 A x y) = (term679 A x y).
Proof. exact (MK_COMB (@lem1214582) (@lem1214581 A x y)). Qed.
Lemma lem1214585 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1214586 {A : Type'} (x : list A) (z : list A) : (term677 A x z) = (x = z).
Proof. exact (@lem1214585 (x = z)). Qed.
Lemma lem1214587 {A : Type'} (y : list A) (x : list A) (z : list A) : (term675 A y x z) = (term680 A y x z).
Proof. exact (MK_COMB (@lem1214583 A x y) (@lem1214586 A x z)). Qed.
Lemma lem1214588 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term680 A y x z).
Proof. exact (TRANS (@lem1214578 A y x z) (@lem1214587 A y x z)). Qed.
Lemma lem1214589 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1214590 {A : Type'} (y : list A) (x : list A) (z : list A) : (term681 A y x z) = (term682 A y x z).
Proof. exact (MK_COMB (@lem1214589) (@lem1214588 A y x z)). Qed.
Lemma lem1214591 {A : Type'} (y : list A) (z : list A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1214592 {A : Type'} (x : list A) (y : list A) (z : list A) : (term670 A x y z) = (term683 A x y z).
Proof. exact (MK_COMB (@lem1214590 A y x z) (@lem1214591 A y z)). Qed.
Lemma lem1214593 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term683 A x y z).
Proof. exact (TRANS (@lem1214575 A x y z) (@lem1214592 A x y z)). Qed.
Lemma lem1214595 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : term684 A y l.
Proof. exact (conj (@lem1214473 A y l h1) (@lem1214482 A y l)). Qed.
Lemma lem1214597 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (EQ_MP (@lem1214593 A x y z) (@lem1214572 A y x z)). Qed.
Lemma lem1214598 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (@lem1214597 A x y z). Qed.
Lemma lem1214599 {A : Type'} (y : A) (l : list A) : term685 A y l.
Proof. exact (@lem1214598 A (term654 A y l) (@cons A y l) (term654 A y l)). Qed.
Lemma lem1214602 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : (@cons A y l) = (term654 A y l).
Proof. exact (@lem1214599 A y l (@lem1214595 A y l h1)). Qed.
Lemma lem1214603 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : (@cons A y l) = (term654 A y l).
Proof. exact (@lem1214602 A y l h1). Qed.
Lemma lem1214604 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : term686 A y l.
Proof. exact (fun h0 : term687 A y l => @lem1214603 A y l h1). Qed.
Lemma lem1214606 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214607 {A : Type'} (y : A) (l : list A) : (term686 A y l) = ((@cons A y l) = (term654 A y l)).
Proof. exact (@lem1214606 ((@cons A y l) = (term654 A y l))). Qed.
Lemma lem1214608 {A : Type'} (y : A) (l : list A) (h1 : term170 A) : (@cons A y l) = (term654 A y l).
Proof. exact (EQ_MP (@lem1214607 A y l) (@lem1214604 A y l h1)). Qed.
Lemma lem1214610 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1214611 {A : Type'} (l : list A) (_21665 : list A) (y : A) (_21664 : list A) : (term631 A l _21664 y _21665) = (term688 A l _21665 y _21664).
Proof. exact (@lem1214610 (term689 A l _21664 y _21665) (@List.In A y _21664)). Qed.
Lemma lem1214613 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1214614 {A : Type'} (l : list A) (_21664 : list A) (y : A) (_21665 : list A) : (term690 A l _21664 y _21665) = ((@cons A y l) = (term102 A _21664 y _21665)).
Proof. exact (@lem1214613 ((@cons A y l) = (term102 A _21664 y _21665))). Qed.
Lemma lem1214615 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1214616 {A : Type'} (l : list A) (_21664 : list A) (y : A) (_21665 : list A) : (term691 A l _21664 y _21665) = (term692 A l _21664 y _21665).
Proof. exact (MK_COMB (@lem1214615) (@lem1214614 A l _21664 y _21665)). Qed.
Lemma lem1214617 {A : Type'} (y : A) (_21664 : list A) : (@List.In A y _21664) = (@List.In A y _21664).
Proof. exact (eq_refl (@List.In A y _21664)). Qed.
Lemma lem1214618 {A : Type'} (l : list A) (_21665 : list A) (y : A) (_21664 : list A) : (term688 A l _21665 y _21664) = (term693 A l _21665 y _21664).
Proof. exact (MK_COMB (@lem1214616 A l _21664 y _21665) (@lem1214617 A y _21664)). Qed.
Lemma lem1214619 {A : Type'} (l : list A) (_21665 : list A) (y : A) (_21664 : list A) : (term631 A l _21664 y _21665) = (term693 A l _21665 y _21664).
Proof. exact (TRANS (@lem1214611 A l _21665 y _21664) (@lem1214618 A l _21665 y _21664)). Qed.
Lemma lem1214622 {A : Type'} (_21665 : list A) (_21664 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term519 A l1 l2 y l x) (h2 : x = y) : term693 A l _21665 y _21664.
Proof. exact (EQ_MP (@lem1214619 A l _21665 y _21664) (@lem1213043 A _21664 _21665 l1 l2 l x y h1 h2)). Qed.
Lemma lem1214623 {A : Type'} (_21665 : list A) (_21664 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term519 A l1 l2 y l x) (h2 : x = y) : term693 A l _21665 y _21664.
Proof. exact (@lem1214622 A _21665 _21664 l1 l2 l x y h1 h2). Qed.
Lemma lem1214624 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term519 A l1 l2 y l x) (h2 : x = y) : term694 A l y.
Proof. exact (@lem1214623 A l (@nil A) l1 l2 l x y h1 h2). Qed.
Lemma lem1214627 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : @List.In A y (@nil A).
Proof. exact (@lem1214624 A l1 l2 l x y h2 h3 (@lem1214608 A y l h1)). Qed.
Lemma lem1214628 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term695 A y.
Proof. exact (fun h0 : term248 A y => @lem1214627 A l1 l2 l x y h1 h2 h3). Qed.
Lemma lem1214630 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214631 {A : Type'} (y : A) : (term695 A y) = (@List.In A y (@nil A)).
Proof. exact (@lem1214630 (@List.In A y (@nil A))). Qed.
Lemma lem1214632 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : @List.In A y (@nil A).
Proof. exact (EQ_MP (@lem1214631 A y) (@lem1214628 A l1 l2 l x y h1 h2 h3)). Qed.
Lemma lem1214635 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1214637 {A : Type'} (_21673 : A) : (term248 A _21673) = (term696 A _21673).
Proof. exact (@lem1214635 (@List.In A _21673 (@nil A))). Qed.
Lemma lem1214640 {A : Type'} (_21673 : A) (h1 : term297 A) : term696 A _21673.
Proof. exact (EQ_MP (@lem1214637 A _21673) (@lem1213085 A _21673 h1)). Qed.
Lemma lem1214641 {A : Type'} (_21673 : A) (h1 : term297 A) : term696 A _21673.
Proof. exact (@lem1214640 A _21673 h1). Qed.
Lemma lem1214642 {A : Type'} (y : A) (h1 : term297 A) : term696 A y.
Proof. exact (@lem1214641 A y h1). Qed.
Lemma lem1214645 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (@lem1214642 A y h1 (@lem1214632 A l1 l2 l x y h2 h3 h4)). Qed.
Lemma lem1214646 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : term697.
Proof. exact (fun h0 : ~ False => @lem1214645 A l1 l2 l x y h1 h2 h3 h4). Qed.
Lemma lem1214648 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214649 : term697 = False.
Proof. exact (@lem1214648 False). Qed.
Lemma lem1214750 {A : Type'} (x : list A) (y : list A) (z : list A) : term653 A x y z.
Proof. exact (@lem21385 (list A) x y z). Qed.
Lemma lem1214756 {A : Type'} (_21708 : list A) (h1 : term170 A) : (@List.app A (@nil A) _21708) = _21708.
Proof. exact (EQ_MP (@lem1212557 A _21708) (@lem1212556 A _21708 h1)). Qed.
Lemma lem1214757 {A : Type'} (_21708 : list A) (h1 : term170 A) : (@List.app A (@nil A) _21708) = _21708.
Proof. exact (@lem1214756 A _21708 h1). Qed.
Lemma lem1214758 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term698 A l1 y l2) = (term699 A l1 y l2).
Proof. exact (@lem1214757 A (term699 A l1 y l2) h1). Qed.
Lemma lem1214759 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : term700 A l1 y l2.
Proof. exact (fun h0 : term701 A l1 y l2 => @lem1214758 A l1 y l2 h1). Qed.
Lemma lem1214761 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214762 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term700 A l1 y l2) = ((term698 A l1 y l2) = (term699 A l1 y l2)).
Proof. exact (@lem1214761 ((term698 A l1 y l2) = (term699 A l1 y l2))). Qed.
Lemma lem1214763 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term698 A l1 y l2) = (term699 A l1 y l2).
Proof. exact (EQ_MP (@lem1214762 A l1 y l2) (@lem1214759 A l1 y l2 h1)). Qed.
Lemma lem1214765 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem21386 (list A) x). Qed.
Lemma lem1214766 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem1214765 A x). Qed.
Lemma lem1214767 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term698 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (@lem1214766 A (term698 A l1 y l2)). Qed.
Lemma lem1214768 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : term702 A l1 y l2.
Proof. exact (fun h0 : term703 A l1 y l2 => @lem1214767 A l1 y l2). Qed.
Lemma lem1214770 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214771 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term702 A l1 y l2) = ((term698 A l1 y l2) = (term698 A l1 y l2)).
Proof. exact (@lem1214770 ((term698 A l1 y l2) = (term698 A l1 y l2))). Qed.
Lemma lem1214772 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term698 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (EQ_MP (@lem1214771 A l1 y l2) (@lem1214768 A l1 y l2)). Qed.
Lemma lem1214790 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1214791 {A : Type'} (y : list A) (x : list A) (z : list A) : (term660 A x y z) = (term661 A y x z).
Proof. exact (@lem1214790 (y = z) (term662 A x z)). Qed.
Lemma lem1214801 {A : Type'} (x : list A) (y : list A) : (term663 A x y) = (term663 A x y).
Proof. exact (eq_refl (term663 A x y)). Qed.
Lemma lem1214802 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term664 A y x z).
Proof. exact (MK_COMB (@lem1214801 A x y) (@lem1214791 A y x z)). Qed.
Lemma lem1214806 (q : Prop) (p : Prop) (r : Prop) : (term665 p q r) = (term665 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1214807 {A : Type'} (y : list A) (x : list A) (z : list A) : (term664 A y x z) = (term666 A y x z).
Proof. exact (@lem1214806 (y = z) (term662 A x y) (term662 A x z)). Qed.
Lemma lem1214829 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (TRANS (@lem1214802 A y x z) (@lem1214807 A y x z)). Qed.
Lemma lem1214830 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1214831 {A : Type'} (y : list A) (x : list A) (z : list A) : (term667 A x y z) = (term668 A y x z).
Proof. exact (MK_COMB (@lem1214830) (@lem1214829 A y x z)). Qed.
Lemma lem1214853 {A : Type'} (y : list A) (x : list A) (z : list A) : (term666 A y x z) = (term666 A y x z).
Proof. exact (eq_refl (term666 A y x z)). Qed.
Lemma lem1214854 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = ((term666 A y x z) = (term666 A y x z)).
Proof. exact (MK_COMB (@lem1214831 A y x z) (@lem1214853 A y x z)). Qed.
Lemma lem1214856 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1214857 (x : Prop) : (x = x) = True.
Proof. exact (@lem1214856 Prop x). Qed.
Lemma lem1214858 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term666 A y x z) = (term666 A y x z)) = True.
Proof. exact (@lem1214857 (term666 A y x z)). Qed.
Lemma lem1214859 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = True.
Proof. exact (TRANS (@lem1214854 A y x z) (@lem1214858 A y x z)). Qed.
Lemma lem1214860 {A : Type'} (y : list A) (x : list A) (z : list A) : True = ((term653 A x y z) = (term666 A y x z)).
Proof. exact (SYM (@lem1214859 A y x z)). Qed.
Lemma lem1214861 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (EQ_MP (@lem1214860 A y x z) (@lem0)). Qed.
Lemma lem1214862 {A : Type'} (y : list A) (x : list A) (z : list A) : term666 A y x z.
Proof. exact (EQ_MP (@lem1214861 A y x z) (@lem1214750 A x y z)). Qed.
Lemma lem1214864 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1214865 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term670 A x y z).
Proof. exact (@lem1214864 (term671 A y x z) (y = z)). Qed.
Lemma lem1214867 (a : Prop) (b : Prop) : (term672 a b) = (term673 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1214868 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term675 A y x z).
Proof. exact (@lem1214867 (term662 A x y) (term662 A x z)). Qed.
Lemma lem1214870 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1214871 {A : Type'} (x : list A) (y : list A) : (term677 A x y) = (x = y).
Proof. exact (@lem1214870 (x = y)). Qed.
Lemma lem1214872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1214873 {A : Type'} (x : list A) (y : list A) : (term678 A x y) = (term679 A x y).
Proof. exact (MK_COMB (@lem1214872) (@lem1214871 A x y)). Qed.
Lemma lem1214875 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1214876 {A : Type'} (x : list A) (z : list A) : (term677 A x z) = (x = z).
Proof. exact (@lem1214875 (x = z)). Qed.
Lemma lem1214877 {A : Type'} (y : list A) (x : list A) (z : list A) : (term675 A y x z) = (term680 A y x z).
Proof. exact (MK_COMB (@lem1214873 A x y) (@lem1214876 A x z)). Qed.
Lemma lem1214878 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term680 A y x z).
Proof. exact (TRANS (@lem1214868 A y x z) (@lem1214877 A y x z)). Qed.
Lemma lem1214879 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1214880 {A : Type'} (y : list A) (x : list A) (z : list A) : (term681 A y x z) = (term682 A y x z).
Proof. exact (MK_COMB (@lem1214879) (@lem1214878 A y x z)). Qed.
Lemma lem1214881 {A : Type'} (y : list A) (z : list A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1214882 {A : Type'} (x : list A) (y : list A) (z : list A) : (term670 A x y z) = (term683 A x y z).
Proof. exact (MK_COMB (@lem1214880 A y x z) (@lem1214881 A y z)). Qed.
Lemma lem1214883 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term683 A x y z).
Proof. exact (TRANS (@lem1214865 A x y z) (@lem1214882 A x y z)). Qed.
Lemma lem1214885 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : term704 A l1 y l2.
Proof. exact (conj (@lem1214763 A l1 y l2 h1) (@lem1214772 A l1 y l2)). Qed.
Lemma lem1214887 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (EQ_MP (@lem1214883 A x y z) (@lem1214862 A y x z)). Qed.
Lemma lem1214888 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (@lem1214887 A x y z). Qed.
Lemma lem1214889 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : term705 A l1 y l2.
Proof. exact (@lem1214888 A (term698 A l1 y l2) (term699 A l1 y l2) (term698 A l1 y l2)). Qed.
Lemma lem1214892 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term699 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (@lem1214889 A l1 y l2 (@lem1214885 A l1 y l2 h1)). Qed.
Lemma lem1214893 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term699 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (@lem1214892 A l1 y l2 h1). Qed.
Lemma lem1214894 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : term706 A l1 y l2.
Proof. exact (fun h0 : term707 A l1 y l2 => @lem1214893 A l1 y l2 h1). Qed.
Lemma lem1214896 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214897 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term706 A l1 y l2) = ((term699 A l1 y l2) = (term698 A l1 y l2)).
Proof. exact (@lem1214896 ((term699 A l1 y l2) = (term698 A l1 y l2))). Qed.
Lemma lem1214898 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term699 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (EQ_MP (@lem1214897 A l1 y l2) (@lem1214894 A l1 y l2 h1)). Qed.
Lemma lem1214900 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1214901 {A : Type'} (l1 : list A) (l2 : list A) (_21689 : list A) (y : A) (_21688 : list A) : (term642 A l1 l2 _21688 y _21689) = (term708 A l1 l2 _21689 y _21688).
Proof. exact (@lem1214900 (term709 A l1 l2 _21688 y _21689) (@List.In A y _21688)). Qed.
Lemma lem1214903 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1214904 {A : Type'} (l1 : list A) (l2 : list A) (_21688 : list A) (y : A) (_21689 : list A) : (term710 A l1 l2 _21688 y _21689) = ((term699 A l1 y l2) = (term102 A _21688 y _21689)).
Proof. exact (@lem1214903 ((term699 A l1 y l2) = (term102 A _21688 y _21689))). Qed.
Lemma lem1214905 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1214906 {A : Type'} (l1 : list A) (l2 : list A) (_21688 : list A) (y : A) (_21689 : list A) : (term711 A l1 l2 _21688 y _21689) = (term712 A l1 l2 _21688 y _21689).
Proof. exact (MK_COMB (@lem1214905) (@lem1214904 A l1 l2 _21688 y _21689)). Qed.
Lemma lem1214907 {A : Type'} (y : A) (_21688 : list A) : (@List.In A y _21688) = (@List.In A y _21688).
Proof. exact (eq_refl (@List.In A y _21688)). Qed.
Lemma lem1214908 {A : Type'} (l1 : list A) (l2 : list A) (_21689 : list A) (y : A) (_21688 : list A) : (term708 A l1 l2 _21689 y _21688) = (term713 A l1 l2 _21689 y _21688).
Proof. exact (MK_COMB (@lem1214906 A l1 l2 _21688 y _21689) (@lem1214907 A y _21688)). Qed.
Lemma lem1214909 {A : Type'} (l1 : list A) (l2 : list A) (_21689 : list A) (y : A) (_21688 : list A) : (term642 A l1 l2 _21688 y _21689) = (term713 A l1 l2 _21689 y _21688).
Proof. exact (TRANS (@lem1214901 A l1 l2 _21689 y _21688) (@lem1214908 A l1 l2 _21689 y _21688)). Qed.
Lemma lem1214912 {A : Type'} (_21689 : list A) (_21688 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term713 A l1 l2 _21689 y _21688.
Proof. exact (EQ_MP (@lem1214909 A l1 l2 _21689 y _21688) (@lem1213501 A _21688 _21689 l1 l2 l x y h1 h2 h3)). Qed.
Lemma lem1214913 {A : Type'} (_21689 : list A) (_21688 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term713 A l1 l2 _21689 y _21688.
Proof. exact (@lem1214912 A _21689 _21688 l1 l2 l x y h1 h2 h3). Qed.
Lemma lem1214914 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term714 A l1 l2 y.
Proof. exact (@lem1214913 A (term102 A l1 y l2) (@nil A) l1 l2 l x y h1 h2 h3). Qed.
Lemma lem1214917 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : @List.In A y (@nil A).
Proof. exact (@lem1214914 A l1 l2 l x y h2 h3 h4 (@lem1214898 A l1 y l2 h1)). Qed.
Lemma lem1214918 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : term695 A y.
Proof. exact (fun h0 : term248 A y => @lem1214917 A l1 l2 l x y h1 h2 h3 h4). Qed.
Lemma lem1214920 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214921 {A : Type'} (y : A) : (term695 A y) = (@List.In A y (@nil A)).
Proof. exact (@lem1214920 (@List.In A y (@nil A))). Qed.
Lemma lem1214922 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : @List.In A y (@nil A).
Proof. exact (EQ_MP (@lem1214921 A y) (@lem1214918 A l1 l2 l x y h1 h2 h3 h4)). Qed.
Lemma lem1214925 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1214927 {A : Type'} (_21697 : A) : (term248 A _21697) = (term696 A _21697).
Proof. exact (@lem1214925 (@List.In A _21697 (@nil A))). Qed.
Lemma lem1214930 {A : Type'} (_21697 : A) (h1 : term297 A) : term696 A _21697.
Proof. exact (EQ_MP (@lem1214927 A _21697) (@lem1213543 A _21697 h1)). Qed.
Lemma lem1214931 {A : Type'} (_21697 : A) (h1 : term297 A) : term696 A _21697.
Proof. exact (@lem1214930 A _21697 h1). Qed.
Lemma lem1214932 {A : Type'} (y : A) (h1 : term297 A) : term696 A y.
Proof. exact (@lem1214931 A y h1). Qed.
Lemma lem1214935 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (@lem1214932 A y h1 (@lem1214922 A l1 l2 l x y h2 h3 h4 h5)). Qed.
Lemma lem1214936 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : term697.
Proof. exact (fun h0 : ~ False => @lem1214935 A l1 l2 l x y h1 h2 h3 h4 h5). Qed.
Lemma lem1214938 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1214939 : term697 = False.
Proof. exact (@lem1214938 False). Qed.
Lemma lem1215046 {A : Type'} (y : A) (x : A) (l : list A) (h1 : x = y) (h2 : @List.In A x l) : @List.In A y l.
Proof. exact (EQ_MP (@lem1213833 A l x y h1) (@lem1212907 A x l h2)). Qed.
Lemma lem1215047 {A : Type'} (y : A) (x : A) (l : list A) (h1 : x = y) (h2 : @List.In A x l) : term715 A y l.
Proof. exact (fun h0 : term100 A y l => @lem1215046 A y x l h1 h2). Qed.
Lemma lem1215049 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1215050 {A : Type'} (y : A) (l : list A) : (term715 A y l) = (@List.In A y l).
Proof. exact (@lem1215049 (@List.In A y l)). Qed.
Lemma lem1215051 {A : Type'} (y : A) (x : A) (l : list A) (h1 : x = y) (h2 : @List.In A x l) : @List.In A y l.
Proof. exact (EQ_MP (@lem1215050 A y l) (@lem1215047 A y x l h1 h2)). Qed.
Lemma lem1215054 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1215056 {A : Type'} (y : A) (l : list A) : (term100 A y l) = (term716 A y l).
Proof. exact (@lem1215054 (@List.In A y l)). Qed.
Lemma lem1215059 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term100 A x l) (h2 : x = y) : term716 A y l.
Proof. exact (EQ_MP (@lem1215056 A y l) (@lem1213847 A l x y h1 h2)). Qed.
Lemma lem1215062 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (@lem1215059 A l x y h1 h2 (@lem1215051 A y x l h2 h3)). Qed.
Lemma lem1215063 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : term697.
Proof. exact (fun h0 : ~ False => @lem1215062 A y x l h1 h2 h3). Qed.
Lemma lem1215065 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1215066 : term697 = False.
Proof. exact (@lem1215065 False). Qed.
Lemma lem1215167 {A : Type'} (x : list A) (y : list A) (z : list A) : term653 A x y z.
Proof. exact (@lem21385 (list A) x y z). Qed.
Lemma lem1215173 {A : Type'} (_21756 : list A) (h1 : term170 A) : (@List.app A (@nil A) _21756) = _21756.
Proof. exact (EQ_MP (@lem1212701 A _21756) (@lem1212700 A _21756 h1)). Qed.
Lemma lem1215174 {A : Type'} (_21756 : list A) (h1 : term170 A) : (@List.app A (@nil A) _21756) = _21756.
Proof. exact (@lem1215173 A _21756 h1). Qed.
Lemma lem1215175 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term698 A l1 y l2) = (term699 A l1 y l2).
Proof. exact (@lem1215174 A (term699 A l1 y l2) h1). Qed.
Lemma lem1215176 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : term700 A l1 y l2.
Proof. exact (fun h0 : term701 A l1 y l2 => @lem1215175 A l1 y l2 h1). Qed.
Lemma lem1215178 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1215179 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term700 A l1 y l2) = ((term698 A l1 y l2) = (term699 A l1 y l2)).
Proof. exact (@lem1215178 ((term698 A l1 y l2) = (term699 A l1 y l2))). Qed.
Lemma lem1215180 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term698 A l1 y l2) = (term699 A l1 y l2).
Proof. exact (EQ_MP (@lem1215179 A l1 y l2) (@lem1215176 A l1 y l2 h1)). Qed.
Lemma lem1215182 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem21386 (list A) x). Qed.
Lemma lem1215183 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem1215182 A x). Qed.
Lemma lem1215184 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term698 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (@lem1215183 A (term698 A l1 y l2)). Qed.
Lemma lem1215185 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : term702 A l1 y l2.
Proof. exact (fun h0 : term703 A l1 y l2 => @lem1215184 A l1 y l2). Qed.
Lemma lem1215187 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1215188 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term702 A l1 y l2) = ((term698 A l1 y l2) = (term698 A l1 y l2)).
Proof. exact (@lem1215187 ((term698 A l1 y l2) = (term698 A l1 y l2))). Qed.
Lemma lem1215189 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term698 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (EQ_MP (@lem1215188 A l1 y l2) (@lem1215185 A l1 y l2)). Qed.
Lemma lem1215207 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1215208 {A : Type'} (y : list A) (x : list A) (z : list A) : (term660 A x y z) = (term661 A y x z).
Proof. exact (@lem1215207 (y = z) (term662 A x z)). Qed.
Lemma lem1215218 {A : Type'} (x : list A) (y : list A) : (term663 A x y) = (term663 A x y).
Proof. exact (eq_refl (term663 A x y)). Qed.
Lemma lem1215219 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term664 A y x z).
Proof. exact (MK_COMB (@lem1215218 A x y) (@lem1215208 A y x z)). Qed.
Lemma lem1215223 (q : Prop) (p : Prop) (r : Prop) : (term665 p q r) = (term665 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1215224 {A : Type'} (y : list A) (x : list A) (z : list A) : (term664 A y x z) = (term666 A y x z).
Proof. exact (@lem1215223 (y = z) (term662 A x y) (term662 A x z)). Qed.
Lemma lem1215246 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (TRANS (@lem1215219 A y x z) (@lem1215224 A y x z)). Qed.
Lemma lem1215247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1215248 {A : Type'} (y : list A) (x : list A) (z : list A) : (term667 A x y z) = (term668 A y x z).
Proof. exact (MK_COMB (@lem1215247) (@lem1215246 A y x z)). Qed.
Lemma lem1215270 {A : Type'} (y : list A) (x : list A) (z : list A) : (term666 A y x z) = (term666 A y x z).
Proof. exact (eq_refl (term666 A y x z)). Qed.
Lemma lem1215271 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = ((term666 A y x z) = (term666 A y x z)).
Proof. exact (MK_COMB (@lem1215248 A y x z) (@lem1215270 A y x z)). Qed.
Lemma lem1215273 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1215274 (x : Prop) : (x = x) = True.
Proof. exact (@lem1215273 Prop x). Qed.
Lemma lem1215275 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term666 A y x z) = (term666 A y x z)) = True.
Proof. exact (@lem1215274 (term666 A y x z)). Qed.
Lemma lem1215276 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = True.
Proof. exact (TRANS (@lem1215271 A y x z) (@lem1215275 A y x z)). Qed.
Lemma lem1215277 {A : Type'} (y : list A) (x : list A) (z : list A) : True = ((term653 A x y z) = (term666 A y x z)).
Proof. exact (SYM (@lem1215276 A y x z)). Qed.
Lemma lem1215278 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (EQ_MP (@lem1215277 A y x z) (@lem0)). Qed.
Lemma lem1215279 {A : Type'} (y : list A) (x : list A) (z : list A) : term666 A y x z.
Proof. exact (EQ_MP (@lem1215278 A y x z) (@lem1215167 A x y z)). Qed.
Lemma lem1215281 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1215282 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term670 A x y z).
Proof. exact (@lem1215281 (term671 A y x z) (y = z)). Qed.
Lemma lem1215284 (a : Prop) (b : Prop) : (term672 a b) = (term673 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1215285 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term675 A y x z).
Proof. exact (@lem1215284 (term662 A x y) (term662 A x z)). Qed.
Lemma lem1215287 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1215288 {A : Type'} (x : list A) (y : list A) : (term677 A x y) = (x = y).
Proof. exact (@lem1215287 (x = y)). Qed.
Lemma lem1215289 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215290 {A : Type'} (x : list A) (y : list A) : (term678 A x y) = (term679 A x y).
Proof. exact (MK_COMB (@lem1215289) (@lem1215288 A x y)). Qed.
Lemma lem1215292 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1215293 {A : Type'} (x : list A) (z : list A) : (term677 A x z) = (x = z).
Proof. exact (@lem1215292 (x = z)). Qed.
Lemma lem1215294 {A : Type'} (y : list A) (x : list A) (z : list A) : (term675 A y x z) = (term680 A y x z).
Proof. exact (MK_COMB (@lem1215290 A x y) (@lem1215293 A x z)). Qed.
Lemma lem1215295 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term680 A y x z).
Proof. exact (TRANS (@lem1215285 A y x z) (@lem1215294 A y x z)). Qed.
Lemma lem1215296 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1215297 {A : Type'} (y : list A) (x : list A) (z : list A) : (term681 A y x z) = (term682 A y x z).
Proof. exact (MK_COMB (@lem1215296) (@lem1215295 A y x z)). Qed.
Lemma lem1215298 {A : Type'} (y : list A) (z : list A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1215299 {A : Type'} (x : list A) (y : list A) (z : list A) : (term670 A x y z) = (term683 A x y z).
Proof. exact (MK_COMB (@lem1215297 A y x z) (@lem1215298 A y z)). Qed.
Lemma lem1215300 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term683 A x y z).
Proof. exact (TRANS (@lem1215282 A x y z) (@lem1215299 A x y z)). Qed.
Lemma lem1215302 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : term704 A l1 y l2.
Proof. exact (conj (@lem1215180 A l1 y l2 h1) (@lem1215189 A l1 y l2)). Qed.
Lemma lem1215304 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (EQ_MP (@lem1215300 A x y z) (@lem1215279 A y x z)). Qed.
Lemma lem1215305 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (@lem1215304 A x y z). Qed.
Lemma lem1215306 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : term705 A l1 y l2.
Proof. exact (@lem1215305 A (term698 A l1 y l2) (term699 A l1 y l2) (term698 A l1 y l2)). Qed.
Lemma lem1215309 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term699 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (@lem1215306 A l1 y l2 (@lem1215302 A l1 y l2 h1)). Qed.
Lemma lem1215310 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term699 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (@lem1215309 A l1 y l2 h1). Qed.
Lemma lem1215311 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : term706 A l1 y l2.
Proof. exact (fun h0 : term707 A l1 y l2 => @lem1215310 A l1 y l2 h1). Qed.
Lemma lem1215313 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1215314 {A : Type'} (l1 : list A) (y : A) (l2 : list A) : (term706 A l1 y l2) = ((term699 A l1 y l2) = (term698 A l1 y l2)).
Proof. exact (@lem1215313 ((term699 A l1 y l2) = (term698 A l1 y l2))). Qed.
Lemma lem1215315 {A : Type'} (l1 : list A) (y : A) (l2 : list A) (h1 : term170 A) : (term699 A l1 y l2) = (term698 A l1 y l2).
Proof. exact (EQ_MP (@lem1215314 A l1 y l2) (@lem1215311 A l1 y l2 h1)). Qed.
Lemma lem1215317 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1215318 {A : Type'} (l1 : list A) (l2 : list A) (_21737 : list A) (y : A) (_21736 : list A) : (term642 A l1 l2 _21736 y _21737) = (term708 A l1 l2 _21737 y _21736).
Proof. exact (@lem1215317 (term709 A l1 l2 _21736 y _21737) (@List.In A y _21736)). Qed.
Lemma lem1215320 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1215321 {A : Type'} (l1 : list A) (l2 : list A) (_21736 : list A) (y : A) (_21737 : list A) : (term710 A l1 l2 _21736 y _21737) = ((term699 A l1 y l2) = (term102 A _21736 y _21737)).
Proof. exact (@lem1215320 ((term699 A l1 y l2) = (term102 A _21736 y _21737))). Qed.
Lemma lem1215322 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1215323 {A : Type'} (l1 : list A) (l2 : list A) (_21736 : list A) (y : A) (_21737 : list A) : (term711 A l1 l2 _21736 y _21737) = (term712 A l1 l2 _21736 y _21737).
Proof. exact (MK_COMB (@lem1215322) (@lem1215321 A l1 l2 _21736 y _21737)). Qed.
Lemma lem1215324 {A : Type'} (y : A) (_21736 : list A) : (@List.In A y _21736) = (@List.In A y _21736).
Proof. exact (eq_refl (@List.In A y _21736)). Qed.
Lemma lem1215325 {A : Type'} (l1 : list A) (l2 : list A) (_21737 : list A) (y : A) (_21736 : list A) : (term708 A l1 l2 _21737 y _21736) = (term713 A l1 l2 _21737 y _21736).
Proof. exact (MK_COMB (@lem1215323 A l1 l2 _21736 y _21737) (@lem1215324 A y _21736)). Qed.
Lemma lem1215326 {A : Type'} (l1 : list A) (l2 : list A) (_21737 : list A) (y : A) (_21736 : list A) : (term642 A l1 l2 _21736 y _21737) = (term713 A l1 l2 _21737 y _21736).
Proof. exact (TRANS (@lem1215318 A l1 l2 _21737 y _21736) (@lem1215325 A l1 l2 _21737 y _21736)). Qed.
Lemma lem1215329 {A : Type'} (_21737 : list A) (_21736 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term713 A l1 l2 _21737 y _21736.
Proof. exact (EQ_MP (@lem1215326 A l1 l2 _21737 y _21736) (@lem1214166 A _21736 _21737 l1 l2 l x y h1 h2 h3)). Qed.
Lemma lem1215330 {A : Type'} (_21737 : list A) (_21736 : list A) (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term713 A l1 l2 _21737 y _21736.
Proof. exact (@lem1215329 A _21737 _21736 l1 l2 l x y h1 h2 h3). Qed.
Lemma lem1215331 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : term714 A l1 l2 y.
Proof. exact (@lem1215330 A (term102 A l1 y l2) (@nil A) l1 l2 l x y h1 h2 h3). Qed.
Lemma lem1215334 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : @List.In A y (@nil A).
Proof. exact (@lem1215331 A l1 l2 l x y h2 h3 h4 (@lem1215315 A l1 y l2 h1)). Qed.
Lemma lem1215335 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : term695 A y.
Proof. exact (fun h0 : term248 A y => @lem1215334 A l1 l2 l x y h1 h2 h3 h4). Qed.
Lemma lem1215337 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1215338 {A : Type'} (y : A) : (term695 A y) = (@List.In A y (@nil A)).
Proof. exact (@lem1215337 (@List.In A y (@nil A))). Qed.
Lemma lem1215339 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : @List.In A y (@nil A).
Proof. exact (EQ_MP (@lem1215338 A y) (@lem1215335 A l1 l2 l x y h1 h2 h3 h4)). Qed.
Lemma lem1215342 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1215344 {A : Type'} (_21745 : A) : (term248 A _21745) = (term696 A _21745).
Proof. exact (@lem1215342 (@List.In A _21745 (@nil A))). Qed.
Lemma lem1215347 {A : Type'} (_21745 : A) (h1 : term297 A) : term696 A _21745.
Proof. exact (EQ_MP (@lem1215344 A _21745) (@lem1214208 A _21745 h1)). Qed.
Lemma lem1215348 {A : Type'} (_21745 : A) (h1 : term297 A) : term696 A _21745.
Proof. exact (@lem1215347 A _21745 h1). Qed.
Lemma lem1215349 {A : Type'} (y : A) (h1 : term297 A) : term696 A y.
Proof. exact (@lem1215348 A y h1). Qed.
Lemma lem1215352 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (@lem1215349 A y h1 (@lem1215339 A l1 l2 l x y h2 h3 h4 h5)). Qed.
Lemma lem1215353 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : term697.
Proof. exact (fun h0 : ~ False => @lem1215352 A l1 l2 l x y h1 h2 h3 h4 h5). Qed.
Lemma lem1215355 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1215356 : term697 = False.
Proof. exact (@lem1215355 False). Qed.
Lemma lem1215358 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215356) (@lem1215353 A l1 l2 l x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1215359 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215358 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1213931 A x y h5)). Qed.
Lemma lem1215361 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215359 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1213931 A x y h5)). Qed.
Lemma lem1215362 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215066) (@lem1215063 A y x l h1 h2 h3)). Qed.
Lemma lem1215363 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1214939) (@lem1214936 A l1 l2 l x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1215364 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215363 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1213391 A x y h5)). Qed.
Lemma lem1215365 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215364 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1213391 A x y h5)). Qed.
Lemma lem1215366 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215365 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1213252 A x y h5)). Qed.
Lemma lem1215368 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215366 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1213252 A x y h5)). Qed.
Lemma lem1215369 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1214649) (@lem1214646 A l1 l2 l x y h1 h2 h3 h4)). Qed.
Lemma lem1215370 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215361 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1212935 A x y h5)). Qed.
Lemma lem1215371 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215370 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1212935 A x y h5)). Qed.
Lemma lem1215372 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (term100 A x l) = False.
Proof. exact (prop_ext (fun h4 : term100 A x l => @lem1215362 A y x l h1 h2 h3) (fun h4 : False => @lem1212909 A x l h1)). Qed.
Lemma lem1215373 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215372 A y x l h1 h2 h3) (@lem1212909 A x l h1)). Qed.
Lemma lem1215374 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (@List.In A x l) = False.
Proof. exact (prop_ext (fun h4 : @List.In A x l => @lem1215373 A y x l h1 h2 h3) (fun h4 : False => @lem1212907 A x l h3)). Qed.
Lemma lem1215375 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215374 A y x l h1 h2 h3) (@lem1212907 A x l h3)). Qed.
Lemma lem1215376 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem1215375 A y x l h1 h2 h3) (fun h4 : False => @lem1212867 A x y h2)). Qed.
Lemma lem1215377 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215376 A y x l h1 h2 h3) (@lem1212867 A x y h2)). Qed.
Lemma lem1215378 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215368 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1212837 A x y h5)). Qed.
Lemma lem1215379 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215378 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1212837 A x y h5)). Qed.
Lemma lem1215380 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215379 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1212797 A x y h5)). Qed.
Lemma lem1215381 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215380 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1212797 A x y h5)). Qed.
Lemma lem1215382 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215369 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1212769 A x y h4)). Qed.
Lemma lem1215383 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215382 A l1 l2 l x y h1 h2 h3 h4) (@lem1212769 A x y h4)). Qed.
Lemma lem1215384 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215383 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1212729 A x y h4)). Qed.
Lemma lem1215385 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215384 A l1 l2 l x y h1 h2 h3 h4) (@lem1212729 A x y h4)). Qed.
Lemma lem1215386 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215371 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1212211 A x y h5)). Qed.
Lemma lem1215387 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215386 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1212211 A x y h5)). Qed.
Lemma lem1215388 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (term100 A x l) = False.
Proof. exact (prop_ext (fun h4 : term100 A x l => @lem1215377 A y x l h1 h2 h3) (fun h4 : False => @lem1212207 A x l h1)). Qed.
Lemma lem1215389 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215388 A y x l h1 h2 h3) (@lem1212207 A x l h1)). Qed.
Lemma lem1215390 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (@List.In A x l) = False.
Proof. exact (prop_ext (fun h4 : @List.In A x l => @lem1215389 A y x l h1 h2 h3) (fun h4 : False => @lem1212203 A x l h3)). Qed.
Lemma lem1215391 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215390 A y x l h1 h2 h3) (@lem1212203 A x l h3)). Qed.
Lemma lem1215392 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem1215391 A y x l h1 h2 h3) (fun h4 : False => @lem1211999 A x y h2)). Qed.
Lemma lem1215393 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215392 A y x l h1 h2 h3) (@lem1211999 A x y h2)). Qed.
Lemma lem1215394 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215381 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1211987 A x y h5)). Qed.
Lemma lem1215395 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215394 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1211987 A x y h5)). Qed.
Lemma lem1215396 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215395 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1211783 A x y h5)). Qed.
Lemma lem1215397 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215396 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1211783 A x y h5)). Qed.
Lemma lem1215398 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215385 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1211775 A x y h4)). Qed.
Lemma lem1215399 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215398 A l1 l2 l x y h1 h2 h3 h4) (@lem1211775 A x y h4)). Qed.
Lemma lem1215400 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215399 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1211571 A x y h4)). Qed.
Lemma lem1215401 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215400 A l1 l2 l x y h1 h2 h3 h4) (@lem1211571 A x y h4)). Qed.
Lemma lem1215402 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215387 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1212211 A x y h5)). Qed.
Lemma lem1215403 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215402 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1212211 A x y h5)). Qed.
Lemma lem1215404 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (term100 A x l) = False.
Proof. exact (prop_ext (fun h4 : term100 A x l => @lem1215393 A y x l h1 h2 h3) (fun h4 : False => @lem1212207 A x l h1)). Qed.
Lemma lem1215405 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215404 A y x l h1 h2 h3) (@lem1212207 A x l h1)). Qed.
Lemma lem1215406 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (@List.In A x l) = False.
Proof. exact (prop_ext (fun h4 : @List.In A x l => @lem1215405 A y x l h1 h2 h3) (fun h4 : False => @lem1212203 A x l h3)). Qed.
Lemma lem1215407 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215406 A y x l h1 h2 h3) (@lem1212203 A x l h3)). Qed.
Lemma lem1215408 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : (x = y) = False.
Proof. exact (prop_ext (fun h4 : x = y => @lem1215407 A y x l h1 h2 h3) (fun h4 : False => @lem1211999 A x y h2)). Qed.
Lemma lem1215409 {A : Type'} (y : A) (x : A) (l : list A) (h1 : term100 A x l) (h2 : x = y) (h3 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1215408 A y x l h1 h2 h3) (@lem1211999 A x y h2)). Qed.
Lemma lem1215410 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215397 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1211987 A x y h5)). Qed.
Lemma lem1215411 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215410 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1211987 A x y h5)). Qed.
Lemma lem1215412 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h6 : x = y => @lem1215411 A l1 l2 l x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1211783 A x y h5)). Qed.
Lemma lem1215413 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) (h5 : x = y) : False.
Proof. exact (EQ_MP (@lem1215412 A l1 l2 l x y h1 h2 h3 h4 h5) (@lem1211783 A x y h5)). Qed.
Lemma lem1215414 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215401 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1211775 A x y h4)). Qed.
Lemma lem1215415 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215414 A l1 l2 l x y h1 h2 h3 h4) (@lem1211775 A x y h4)). Qed.
Lemma lem1215416 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215415 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1211571 A x y h4)). Qed.
Lemma lem1215417 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215416 A l1 l2 l x y h1 h2 h3 h4) (@lem1211571 A x y h4)). Qed.
Lemma lem1215418 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (x : A) (l : list A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) (h5 : @List.In A x l) : False.
Proof. exact (or_elim (@lem1211543 A l1 l2 y l x h3) (fun h0 : term100 A x l => @lem1215409 A y x l h0 h4 h5) (fun h0 : term77 A l l1 x l2 => @lem1215403 A l1 l2 l x y h1 h2 h0 h3 h4)). Qed.
Lemma lem1215419 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (or_elim (@lem1211543 A l1 l2 y l x h3) (fun h0 : term100 A x l => @lem1215417 A l1 l2 l x y h1 h2 h3 h4) (fun h0 : term77 A l l1 x l2 => @lem1215413 A l1 l2 l x y h1 h2 h0 h3 h4)). Qed.
Lemma lem1215420 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (or_elim (@lem1211545 A l1 l2 y l x h3) (fun h0 : x = y => @lem1215419 A l1 l2 l x y h1 h2 h3 h4) (fun h0 : @List.In A x l => @lem1215418 A l1 l2 y x l h1 h2 h3 h4 h0)). Qed.
Lemma lem1215421 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (term519 A l1 l2 y l x) = False.
Proof. exact (prop_ext (fun h5 : term519 A l1 l2 y l x => @lem1215420 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1211541 A l1 l2 y l x h3)). Qed.
Lemma lem1215422 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215421 A l1 l2 l x y h1 h2 h3 h4) (@lem1211541 A l1 l2 y l x h3)). Qed.
Lemma lem1215423 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (term170 A) = False.
Proof. exact (prop_ext (fun h5 : term170 A => @lem1215422 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1211227 A h2)). Qed.
Lemma lem1215424 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215423 A l1 l2 l x y h1 h2 h3 h4) (@lem1211227 A h2)). Qed.
Lemma lem1215425 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215424 A l1 l2 l x y h1 h2 h3 h4) (fun h5 : False => @lem1211181 A x y h4)). Qed.
Lemma lem1215426 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term297 A) (h2 : term170 A) (h3 : term519 A l1 l2 y l x) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215425 A l1 l2 l x y h1 h2 h3 h4) (@lem1211181 A x y h4)). Qed.
Lemma lem1215427 {A : Type'} (l1 : list A) (l : list A) (x : A) (y : A) (h1 : term522 A l1 y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : False.
Proof. exact (ex_elim (@lem1211174 A l1 y l x h1) (fun l2 : list A => fun h0 : term521 A l1 y l x l2 => @lem1215426 A l1 l2 l x y h2 h3 h0 h4)). Qed.
Lemma lem1215428 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : False.
Proof. exact (ex_elim (@lem1210177 A y l x h1) (fun l1 : list A => fun h0 : term523 A y l x l1 => @lem1215427 A l1 l x y h0 h2 h3 h4)). Qed.
Lemma lem1215429 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : (term170 A) = False.
Proof. exact (prop_ext (fun h5 : term170 A => @lem1215428 A l x y h1 h2 h3 h4) (fun h5 : False => @lem1210215 A h3)). Qed.
Lemma lem1215430 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215429 A l x y h1 h2 h3 h4) (@lem1210215 A h3)). Qed.
Lemma lem1215431 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h5 : x = y => @lem1215430 A l x y h1 h2 h3 h4) (fun h5 : False => @lem1209881 A x y h4)). Qed.
Lemma lem1215432 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : False.
Proof. exact (EQ_MP (@lem1215431 A l x y h1 h2 h3 h4) (@lem1209881 A x y h4)). Qed.
Lemma lem1215433 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : term717 A.
Proof. exact (fun h0 : term381 A => @lem1215432 A l x y h1 h2 h3 h4). Qed.
Lemma lem1215434 {A : Type'} : (term717 A) = (term382 A).
Proof. exact (@lem69 (term381 A)). Qed.
Lemma lem1215435 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term297 A) (h3 : term170 A) (h4 : x = y) : term382 A.
Proof. exact (EQ_MP (@lem1215434 A) (@lem1215433 A l x y h1 h2 h3 h4)). Qed.
Lemma lem1215436 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term170 A) (h3 : x = y) : term384 A.
Proof. exact (fun h0 : term297 A => @lem1215435 A l x y h1 h0 h2 h3). Qed.
Lemma lem1215437 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : term170 A) (h3 : x = y) : term387 A.
Proof. exact (fun h0 : term171 A => @lem1215436 A l x y h1 h2 h3). Qed.
Lemma lem1215438 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term218 A y l x) (h2 : x = y) : term390 A.
Proof. exact (fun h0 : term170 A => @lem1215437 A l x y h1 h0 h2). Qed.
Lemma lem1215439 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : term392 A y l x.
Proof. exact (fun h0 : term218 A y l x => @lem1215438 A l x y h0 h1). Qed.
Lemma lem1215440 {A : Type'} (y : A) (l : list A) (x : A) : term394 A y l x.
Proof. exact (fun h0 : x = y => @lem1215439 A l x y h0). Qed.
Lemma lem1215445 {A : Type'} (l : list A) (x : A) : term398 A l x.
Proof. exact (fun y : A => @lem1215440 A y l x). Qed.
Lemma lem1215450 {A : Type'} (x : A) : term402 A x.
Proof. exact (fun l : list A => @lem1215445 A l x). Qed.
Lemma lem1215455 {A : Type'} : term406 A.
Proof. exact (fun x : A => @lem1215450 A x). Qed.
Lemma lem1215456 {A : Type'} : term405 A.
Proof. exact (EQ_MP (@lem1209869 A) (@lem1215455 A)). Qed.
Lemma lem1215457 {A : Type'} (x : A) : term718 A x.
Proof. exact (@lem1215456 A x). Qed.
Lemma lem1215458 {A : Type'} (x : A) : (term718 A x) = (term401 A x).
Proof. exact (eq_refl (term718 A x)). Qed.
Lemma lem1215459 {A : Type'} (x : A) : term401 A x.
Proof. exact (EQ_MP (@lem1215458 A x) (@lem1215457 A x)). Qed.
Lemma lem1215460 {A : Type'} (x : A) (l : list A) : term719 A x l.
Proof. exact (@lem1215459 A x l). Qed.
Lemma lem1215461 {A : Type'} (l : list A) (x : A) : (term719 A x l) = (term397 A l x).
Proof. exact (eq_refl (term719 A x l)). Qed.
Lemma lem1215462 {A : Type'} (l : list A) (x : A) : term397 A l x.
Proof. exact (EQ_MP (@lem1215461 A l x) (@lem1215460 A x l)). Qed.
Lemma lem1215463 {A : Type'} (l : list A) (x : A) (y : A) : term720 A l x y.
Proof. exact (@lem1215462 A l x y). Qed.
Lemma lem1215464 {A : Type'} (y : A) (l : list A) (x : A) : (term720 A l x y) = (term172 A y l x).
Proof. exact (eq_refl (term720 A l x y)). Qed.
Lemma lem1215465 {A : Type'} (y : A) (l : list A) (x : A) : term172 A y l x.
Proof. exact (EQ_MP (@lem1215464 A y l x) (@lem1215463 A l x y)). Qed.
Lemma lem1215467 {A : Type'} (y : A) (l : list A) (x : A) : term172 A y l x.
Proof. exact (@lem1208905 A y l x (@lem1215465 A y l x)). Qed.
Lemma lem1215468 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : term391 A y l x.
Proof. exact (@lem1215467 A y l x (@lem1208016 A x y h1)). Qed.
Lemma lem1215469 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term168 A y l x) (h2 : x = y) : term389 A.
Proof. exact (@lem1215468 A l x y h2 (@lem1208879 A y l x h1)). Qed.
Lemma lem1215470 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term168 A y l x) (h2 : x = y) : term386 A.
Proof. exact (@lem1215469 A l x y h1 h2 (@lem1208884 A)). Qed.
Lemma lem1215471 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term168 A y l x) (h2 : x = y) : term383 A.
Proof. exact (@lem1215470 A l x y h1 h2 (@lem1208886 A)). Qed.
Lemma lem1215472 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term168 A y l x) (h2 : x = y) : term300 A.
Proof. exact (@lem1215471 A l x y h1 h2 (@lem1208880 A)). Qed.
Lemma lem1215473 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term168 A y l x) (h2 : x = y) : False.
Proof. exact (@lem1215472 A l x y h1 h2 (@lem1208883 A)). Qed.
Lemma lem1215474 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term168 A y l x) (h2 : x = y) : (term168 A y l x) = False.
Proof. exact (prop_ext (fun h3 : term168 A y l x => @lem1215473 A l x y h1 h2) (fun h3 : False => @lem1208879 A y l x h1)). Qed.
Lemma lem1215475 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term168 A y l x) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1215474 A l x y h1 h2) (@lem1208879 A y l x h1)). Qed.
Lemma lem1215476 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : term167 A y l x.
Proof. exact (fun h0 : term168 A y l x => @lem1215475 A l x y h0 h1). Qed.
Lemma lem1215477 {A : Type'} (l : list A) (x : A) (y : A) (h1 : x = y) : term160 A y l x.
Proof. exact (EQ_MP (@lem1208878 A y l x) (@lem1215476 A l x y h1)). Qed.
Lemma lem1215479 (p : Prop) : p = (term166 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1215480 {A : Type'} (y : A) (l : list A) (x : A) : (term160 A y l x) = (term167 A y l x).
Proof. exact (@lem1215479 (term160 A y l x)). Qed.
Lemma lem1215481 {A : Type'} (y : A) (l : list A) (x : A) : (term167 A y l x) = (term160 A y l x).
Proof. exact (SYM (@lem1215480 A y l x)). Qed.
Lemma lem1215482 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term168 A y l x) : term168 A y l x.
Proof. exact (h1). Qed.
Lemma lem1215483 {A : Type'} : term2 A.
Proof. exact (@lem1208012 A). Qed.
Lemma lem1215486 {A : Type'} : term169 A.
Proof. exact (@lem1208012 (list A)). Qed.
Lemma lem1215487 {A : Type'} : term170 A.
Proof. exact (@lem1095965 A). Qed.
Lemma lem1215489 {A : Type'} : term171 A.
Proof. exact (@lem1095965 (list A)). Qed.
Lemma lem1215495 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term721 A y l x) : term721 A y l x.
Proof. exact (h1). Qed.
Lemma lem1215496 {A : Type'} (y : A) (l : list A) (x : A) : term722 A y l x.
Proof. exact (fun h0 : term721 A y l x => @lem1215495 A y l x h0). Qed.
Lemma lem1215497 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term722 A y l x) : term722 A y l x.
Proof. exact (h1). Qed.
Lemma lem1215498 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term721 A y l x) : term721 A y l x.
Proof. exact (h1). Qed.
Lemma lem1215499 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term721 A y l x) (h2 : term722 A y l x) : term721 A y l x.
Proof. exact (@lem1215497 A y l x h2 (@lem1215498 A y l x h1)). Qed.
Lemma lem1215500 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term721 A y l x) : term723 A y l x.
Proof. exact (fun h0 : term722 A y l x => @lem1215499 A y l x h1 h0). Qed.
Lemma lem1215501 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term722 A y l x) : term722 A y l x.
Proof. exact (h1). Qed.
Lemma lem1215502 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term721 A y l x) (h2 : term722 A y l x) : term721 A y l x.
Proof. exact (@lem1215500 A y l x h1 (@lem1215501 A y l x h2)). Qed.
Lemma lem1215503 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term722 A y l x) : term722 A y l x.
Proof. exact (fun h0 : term721 A y l x => @lem1215502 A y l x h0 h1). Qed.
Lemma lem1215504 {A : Type'} (y : A) (l : list A) (x : A) : term724 A y l x.
Proof. exact (fun h0 : term722 A y l x => @lem1215503 A y l x h0). Qed.
Lemma lem1215507 {A : Type'} (y : A) (l : list A) (x : A) : term722 A y l x.
Proof. exact (@lem1215504 A y l x (@lem1215496 A y l x)). Qed.
Lemma lem1215508 {A : Type'} (y : A) (l : list A) (x : A) : term722 A y l x.
Proof. exact (@lem1215507 A y l x). Qed.
Lemma lem1215534 {A : Type'} (P : Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem1215535 {A : Type'} (P : Prop) (Q : type1143 A) : (term178 A P Q) = (term179 A P Q).
Proof. exact (@lem1215534 (list A) P Q). Qed.
Lemma lem1215536 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term180 A l l1 x) = (term181 A l l1 x).
Proof. exact (@lem1215535 A (term100 A x l1) (term182 A l l1 x)). Qed.
Lemma lem1215537 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1215538 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1215539 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term185 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (MK_COMB (@lem1215538 A x l1) (@lem1215537 A l l1 x l2)). Qed.
Lemma lem1215540 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term186 A l l1 x) = (term75 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1215539 A l l1 x l2)). Qed.
Lemma lem1215541 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1215542 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term180 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1215541 A) (@lem1215540 A l l1 x)). Qed.
Lemma lem1215543 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1215544 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term187 A l l1 x) = (term188 A l l1 x).
Proof. exact (MK_COMB (@lem1215543) (@lem1215542 A l l1 x)). Qed.
Lemma lem1215545 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1215546 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term189 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1215545 A l l1 x l2)). Qed.
Lemma lem1215547 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1215548 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term190 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1215547 A) (@lem1215546 A l l1 x)). Qed.
Lemma lem1215549 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1215550 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term181 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1215549 A x l1) (@lem1215548 A l l1 x)). Qed.
Lemma lem1215551 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term180 A l l1 x) = (term181 A l l1 x)) = ((term58 A l l1 x) = (term192 A l l1 x)).
Proof. exact (MK_COMB (@lem1215544 A l l1 x) (@lem1215550 A l l1 x)). Qed.
Lemma lem1215552 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term58 A l l1 x) = (term192 A l l1 x).
Proof. exact (EQ_MP (@lem1215551 A l l1 x) (@lem1215536 A l l1 x)). Qed.
Lemma lem1215559 {A : Type'} (l : list A) (x : A) : (term56 A l x) = (term193 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1215552 A l l1 x)). Qed.
Lemma lem1215560 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1215561 {A : Type'} (l : list A) (x : A) : (term42 A l x) = (term194 A l x).
Proof. exact (MK_COMB (@lem1215560 A) (@lem1215559 A l x)). Qed.
Lemma lem1215610 {A : Type'} (x : A) (l : list A) : (term195 A x l) = (term195 A x l).
Proof. exact (eq_refl (term195 A x l)). Qed.
Lemma lem1215611 {A : Type'} (l : list A) (x : A) : (term121 A l x) = (term196 A l x).
Proof. exact (MK_COMB (@lem1215610 A x l) (@lem1215561 A l x)). Qed.
Lemma lem1215614 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1215615 {A : Type'} (l : list A) (x : A) : (term133 A l x) = (term197 A l x).
Proof. exact (MK_COMB (@lem1215614) (@lem1215611 A l x)). Qed.
Lemma lem1215625 {A : Type'} (P : Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem1215626 {A : Type'} (P : Prop) (Q : type1143 A) : (term178 A P Q) = (term179 A P Q).
Proof. exact (@lem1215625 (list A) P Q). Qed.
Lemma lem1215627 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term198 A y l l1 x) = (term199 A y l l1 x).
Proof. exact (@lem1215626 A (term100 A x l1) (term200 A y l l1 x)). Qed.
Lemma lem1215628 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term201 A y l l1 x l2) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl (term201 A y l l1 x l2)). Qed.
Lemma lem1215629 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1215630 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term202 A y l l1 x l2) = (term203 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1215629 A x l1) (@lem1215628 A y l l1 x l2)). Qed.
Lemma lem1215631 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term204 A y l l1 x) = (term205 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1215630 A y l l1 x l2)). Qed.
Lemma lem1215632 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1215633 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term198 A y l l1 x) = (term206 A y l l1 x).
Proof. exact (MK_COMB (@lem1215632 A) (@lem1215631 A y l l1 x)). Qed.
Lemma lem1215634 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1215635 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term207 A y l l1 x) = (term208 A y l l1 x).
Proof. exact (MK_COMB (@lem1215634) (@lem1215633 A y l l1 x)). Qed.
Lemma lem1215636 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term201 A y l l1 x l2) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl (term201 A y l l1 x l2)). Qed.
Lemma lem1215637 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term209 A y l l1 x) = (term200 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1215636 A y l l1 x l2)). Qed.
Lemma lem1215638 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1215639 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term210 A y l l1 x) = (term211 A y l l1 x).
Proof. exact (MK_COMB (@lem1215638 A) (@lem1215637 A y l l1 x)). Qed.
Lemma lem1215640 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1215641 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term199 A y l l1 x) = (term212 A y l l1 x).
Proof. exact (MK_COMB (@lem1215640 A x l1) (@lem1215639 A y l l1 x)). Qed.
Lemma lem1215642 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : ((term198 A y l l1 x) = (term199 A y l l1 x)) = ((term206 A y l l1 x) = (term212 A y l l1 x)).
Proof. exact (MK_COMB (@lem1215635 A y l l1 x) (@lem1215641 A y l l1 x)). Qed.
Lemma lem1215643 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term206 A y l l1 x) = (term212 A y l l1 x).
Proof. exact (EQ_MP (@lem1215642 A y l l1 x) (@lem1215627 A y l l1 x)). Qed.
Lemma lem1215650 {A : Type'} (y : A) (l : list A) (x : A) : (term213 A y l x) = (term214 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1215643 A y l l1 x)). Qed.
Lemma lem1215651 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1215652 {A : Type'} (y : A) (l : list A) (x : A) : (term158 A y l x) = (term215 A y l x).
Proof. exact (MK_COMB (@lem1215651 A) (@lem1215650 A y l x)). Qed.
Lemma lem1215701 {A : Type'} (y : A) (x : A) (l : list A) : (term157 A y x l) = (term157 A y x l).
Proof. exact (eq_refl (term157 A y x l)). Qed.
Lemma lem1215702 {A : Type'} (y : A) (l : list A) (x : A) : (term159 A y l x) = (term216 A y l x).
Proof. exact (MK_COMB (@lem1215701 A y x l) (@lem1215652 A y l x)). Qed.
Lemma lem1215705 {A : Type'} (y : A) (l : list A) (x : A) : (term160 A y l x) = (term217 A y l x).
Proof. exact (MK_COMB (@lem1215615 A l x) (@lem1215702 A y l x)). Qed.
Lemma lem1215708 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1215709 {A : Type'} (y : A) (l : list A) (x : A) : (term168 A y l x) = (term218 A y l x).
Proof. exact (MK_COMB (@lem1215708) (@lem1215705 A y l x)). Qed.
Lemma lem1215710 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1215711 {A : Type'} (y : A) (l : list A) (x : A) : (term219 A y l x) = (term220 A y l x).
Proof. exact (MK_COMB (@lem1215710) (@lem1215709 A y l x)). Qed.
Lemma lem1215763 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1215764 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1215763 (list A) P Q). Qed.
Lemma lem1215765 {A : Type'} (h : A) (x : A) : (term225 A h x) = (term226 A h x).
Proof. exact (@lem1215764 A (term227 A x) (term228 A h x)). Qed.
Lemma lem1215766 {A : Type'} (t : list A) (x : A) : (term229 A x t) = ((@List.In A x (@nil A)) = False).
Proof. exact (eq_refl (term229 A x t)). Qed.
Lemma lem1215767 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215768 {A : Type'} (t : list A) (x : A) : (term230 A x t) = (term231 A x).
Proof. exact (MK_COMB (@lem1215767) (@lem1215766 A t x)). Qed.
Lemma lem1215769 {A : Type'} (h : A) (x : A) (t : list A) : (term232 A h x t) = ((term106 A x h t) = (term107 A h x t)).
Proof. exact (eq_refl (term232 A h x t)). Qed.
Lemma lem1215770 {A : Type'} (h : A) (x : A) (t : list A) : (term233 A h x t) = (term234 A h x t).
Proof. exact (MK_COMB (@lem1215768 A t x) (@lem1215769 A h x t)). Qed.
Lemma lem1215771 {A : Type'} (h : A) (x : A) : (term235 A h x) = (term236 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1215770 A h x t)). Qed.
Lemma lem1215772 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1215773 {A : Type'} (h : A) (x : A) : (term225 A h x) = (term0 A h x).
Proof. exact (MK_COMB (@lem1215772 A) (@lem1215771 A h x)). Qed.
Lemma lem1215774 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1215775 {A : Type'} (h : A) (x : A) : (term237 A h x) = (term238 A h x).
Proof. exact (MK_COMB (@lem1215774) (@lem1215773 A h x)). Qed.
Lemma lem1215776 {A : Type'} (t : list A) (x : A) : (term229 A x t) = ((@List.In A x (@nil A)) = False).
Proof. exact (eq_refl (term229 A x t)). Qed.
Lemma lem1215777 {A : Type'} (x : A) : (term239 A x) = (term227 A x).
Proof. exact (fun_ext (fun t : list A => @lem1215776 A t x)). Qed.
Lemma lem1215778 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1215779 {A : Type'} (x : A) : (term240 A x) = (term241 A x).
Proof. exact (MK_COMB (@lem1215778 A) (@lem1215777 A x)). Qed.
Lemma lem1215780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215781 {A : Type'} (x : A) : (term242 A x) = (term243 A x).
Proof. exact (MK_COMB (@lem1215780) (@lem1215779 A x)). Qed.
Lemma lem1215782 {A : Type'} (h : A) (x : A) (t : list A) : (term232 A h x t) = ((term106 A x h t) = (term107 A h x t)).
Proof. exact (eq_refl (term232 A h x t)). Qed.
Lemma lem1215783 {A : Type'} (h : A) (x : A) : (term244 A h x) = (term228 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1215782 A h x t)). Qed.
Lemma lem1215784 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1215785 {A : Type'} (h : A) (x : A) : (term245 A h x) = (term246 A h x).
Proof. exact (MK_COMB (@lem1215784 A) (@lem1215783 A h x)). Qed.
Lemma lem1215786 {A : Type'} (h : A) (x : A) : (term226 A h x) = (term247 A h x).
Proof. exact (MK_COMB (@lem1215781 A x) (@lem1215785 A h x)). Qed.
Lemma lem1215787 {A : Type'} (h : A) (x : A) : ((term225 A h x) = (term226 A h x)) = ((term0 A h x) = (term247 A h x)).
Proof. exact (MK_COMB (@lem1215775 A h x) (@lem1215786 A h x)). Qed.
Lemma lem1215788 {A : Type'} (h : A) (x : A) : (term0 A h x) = (term247 A h x).
Proof. exact (EQ_MP (@lem1215787 A h x) (@lem1215765 A h x)). Qed.
Lemma lem1215792 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1215793 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (@lem1215792 (list A) t). Qed.
Lemma lem1215794 {A : Type'} (x : A) : (term241 A x) = ((@List.In A x (@nil A)) = False).
Proof. exact (@lem1215793 A ((@List.In A x (@nil A)) = False)). Qed.
Lemma lem1215796 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem1215797 {A : Type'} (x : A) : ((@List.In A x (@nil A)) = False) = (term248 A x).
Proof. exact (@lem1215796 (@List.In A x (@nil A))). Qed.
Lemma lem1215798 {A : Type'} (x : A) : (term241 A x) = (term248 A x).
Proof. exact (TRANS (@lem1215794 A x) (@lem1215797 A x)). Qed.
Lemma lem1215799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215800 {A : Type'} (x : A) : (term243 A x) = (term249 A x).
Proof. exact (MK_COMB (@lem1215799) (@lem1215798 A x)). Qed.
Lemma lem1215807 {A : Type'} (h : A) (x : A) : (term246 A h x) = (term246 A h x).
Proof. exact (eq_refl (term246 A h x)). Qed.
Lemma lem1215808 {A : Type'} (h : A) (x : A) : (term247 A h x) = (term250 A h x).
Proof. exact (MK_COMB (@lem1215800 A x) (@lem1215807 A h x)). Qed.
Lemma lem1215811 {A : Type'} (h : A) (x : A) : (term0 A h x) = (term250 A h x).
Proof. exact (TRANS (@lem1215788 A h x) (@lem1215808 A h x)). Qed.
Lemma lem1215812 {A : Type'} (h : A) : (term251 A h) = (term252 A h).
Proof. exact (fun_ext (fun x : A => @lem1215811 A h x)). Qed.
Lemma lem1215813 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215814 {A : Type'} (h : A) : (term1 A h) = (term253 A h).
Proof. exact (MK_COMB (@lem1215813 A) (@lem1215812 A h)). Qed.
Lemma lem1215816 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1215817 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1215816 A P Q). Qed.
Lemma lem1215818 {A : Type'} (h : A) : (term254 A h) = (term255 A h).
Proof. exact (@lem1215817 A (term256 A) (term257 A h)). Qed.
Lemma lem1215819 {A : Type'} (x : A) : (term258 A x) = (term248 A x).
Proof. exact (eq_refl (term258 A x)). Qed.
Lemma lem1215820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215821 {A : Type'} (x : A) : (term259 A x) = (term249 A x).
Proof. exact (MK_COMB (@lem1215820) (@lem1215819 A x)). Qed.
Lemma lem1215822 {A : Type'} (h : A) (x : A) : (term260 A h x) = (term246 A h x).
Proof. exact (eq_refl (term260 A h x)). Qed.
Lemma lem1215823 {A : Type'} (h : A) (x : A) : (term261 A h x) = (term250 A h x).
Proof. exact (MK_COMB (@lem1215821 A x) (@lem1215822 A h x)). Qed.
Lemma lem1215824 {A : Type'} (h : A) : (term262 A h) = (term252 A h).
Proof. exact (fun_ext (fun x : A => @lem1215823 A h x)). Qed.
Lemma lem1215825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215826 {A : Type'} (h : A) : (term254 A h) = (term253 A h).
Proof. exact (MK_COMB (@lem1215825 A) (@lem1215824 A h)). Qed.
Lemma lem1215827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1215828 {A : Type'} (h : A) : (term263 A h) = (term264 A h).
Proof. exact (MK_COMB (@lem1215827) (@lem1215826 A h)). Qed.
Lemma lem1215829 {A : Type'} (x : A) : (term258 A x) = (term248 A x).
Proof. exact (eq_refl (term258 A x)). Qed.
Lemma lem1215830 {A : Type'} : (term265 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1215829 A x)). Qed.
Lemma lem1215831 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215832 {A : Type'} : (term266 A) = (term267 A).
Proof. exact (MK_COMB (@lem1215831 A) (@lem1215830 A)). Qed.
Lemma lem1215833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215834 {A : Type'} : (term268 A) = (term269 A).
Proof. exact (MK_COMB (@lem1215833) (@lem1215832 A)). Qed.
Lemma lem1215835 {A : Type'} (h : A) (x : A) : (term260 A h x) = (term246 A h x).
Proof. exact (eq_refl (term260 A h x)). Qed.
Lemma lem1215836 {A : Type'} (h : A) : (term270 A h) = (term257 A h).
Proof. exact (fun_ext (fun x : A => @lem1215835 A h x)). Qed.
Lemma lem1215837 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215838 {A : Type'} (h : A) : (term271 A h) = (term272 A h).
Proof. exact (MK_COMB (@lem1215837 A) (@lem1215836 A h)). Qed.
Lemma lem1215839 {A : Type'} (h : A) : (term255 A h) = (term273 A h).
Proof. exact (MK_COMB (@lem1215834 A) (@lem1215838 A h)). Qed.
Lemma lem1215840 {A : Type'} (h : A) : ((term254 A h) = (term255 A h)) = ((term253 A h) = (term273 A h)).
Proof. exact (MK_COMB (@lem1215828 A h) (@lem1215839 A h)). Qed.
Lemma lem1215841 {A : Type'} (h : A) : (term253 A h) = (term273 A h).
Proof. exact (EQ_MP (@lem1215840 A h) (@lem1215818 A h)). Qed.
Lemma lem1215858 {A : Type'} (h : A) : (term1 A h) = (term273 A h).
Proof. exact (TRANS (@lem1215814 A h) (@lem1215841 A h)). Qed.
Lemma lem1215859 {A : Type'} : (term274 A) = (term275 A).
Proof. exact (fun_ext (fun h : A => @lem1215858 A h)). Qed.
Lemma lem1215860 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215861 {A : Type'} : (term2 A) = (term276 A).
Proof. exact (MK_COMB (@lem1215860 A) (@lem1215859 A)). Qed.
Lemma lem1215863 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1215864 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1215863 A P Q). Qed.
Lemma lem1215865 {A : Type'} : (term277 A) = (term278 A).
Proof. exact (@lem1215864 A (term279 A) (term280 A)). Qed.
Lemma lem1215866 {A : Type'} (h : A) : (term281 A h) = (term267 A).
Proof. exact (eq_refl (term281 A h)). Qed.
Lemma lem1215867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215868 {A : Type'} (h : A) : (term282 A h) = (term269 A).
Proof. exact (MK_COMB (@lem1215867) (@lem1215866 A h)). Qed.
Lemma lem1215869 {A : Type'} (h : A) : (term283 A h) = (term272 A h).
Proof. exact (eq_refl (term283 A h)). Qed.
Lemma lem1215870 {A : Type'} (h : A) : (term284 A h) = (term273 A h).
Proof. exact (MK_COMB (@lem1215868 A h) (@lem1215869 A h)). Qed.
Lemma lem1215871 {A : Type'} : (term285 A) = (term275 A).
Proof. exact (fun_ext (fun h : A => @lem1215870 A h)). Qed.
Lemma lem1215872 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215873 {A : Type'} : (term277 A) = (term276 A).
Proof. exact (MK_COMB (@lem1215872 A) (@lem1215871 A)). Qed.
Lemma lem1215874 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1215875 {A : Type'} : (term286 A) = (term287 A).
Proof. exact (MK_COMB (@lem1215874) (@lem1215873 A)). Qed.
Lemma lem1215876 {A : Type'} (h : A) : (term281 A h) = (term267 A).
Proof. exact (eq_refl (term281 A h)). Qed.
Lemma lem1215877 {A : Type'} : (term288 A) = (term279 A).
Proof. exact (fun_ext (fun h : A => @lem1215876 A h)). Qed.
Lemma lem1215878 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215879 {A : Type'} : (term289 A) = (term290 A).
Proof. exact (MK_COMB (@lem1215878 A) (@lem1215877 A)). Qed.
Lemma lem1215880 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215881 {A : Type'} : (term291 A) = (term292 A).
Proof. exact (MK_COMB (@lem1215880) (@lem1215879 A)). Qed.
Lemma lem1215882 {A : Type'} (h : A) : (term283 A h) = (term272 A h).
Proof. exact (eq_refl (term283 A h)). Qed.
Lemma lem1215883 {A : Type'} : (term293 A) = (term280 A).
Proof. exact (fun_ext (fun h : A => @lem1215882 A h)). Qed.
Lemma lem1215884 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1215885 {A : Type'} : (term294 A) = (term295 A).
Proof. exact (MK_COMB (@lem1215884 A) (@lem1215883 A)). Qed.
Lemma lem1215886 {A : Type'} : (term278 A) = (term296 A).
Proof. exact (MK_COMB (@lem1215881 A) (@lem1215885 A)). Qed.
Lemma lem1215887 {A : Type'} : ((term277 A) = (term278 A)) = ((term276 A) = (term296 A)).
Proof. exact (MK_COMB (@lem1215875 A) (@lem1215886 A)). Qed.
Lemma lem1215888 {A : Type'} : (term276 A) = (term296 A).
Proof. exact (EQ_MP (@lem1215887 A) (@lem1215865 A)). Qed.
Lemma lem1215892 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1215893 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (@lem1215892 A t). Qed.
Lemma lem1215894 {A : Type'} : (term290 A) = (term267 A).
Proof. exact (@lem1215893 A (term267 A)). Qed.
Lemma lem1215899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215900 {A : Type'} : (term292 A) = (term269 A).
Proof. exact (MK_COMB (@lem1215899) (@lem1215894 A)). Qed.
Lemma lem1215915 {A : Type'} : (term295 A) = (term295 A).
Proof. exact (eq_refl (term295 A)). Qed.
Lemma lem1215916 {A : Type'} : (term296 A) = (term297 A).
Proof. exact (MK_COMB (@lem1215900 A) (@lem1215915 A)). Qed.
Lemma lem1215919 {A : Type'} : (term276 A) = (term297 A).
Proof. exact (TRANS (@lem1215888 A) (@lem1215916 A)). Qed.
Lemma lem1215920 {A : Type'} : (term2 A) = (term297 A).
Proof. exact (TRANS (@lem1215861 A) (@lem1215919 A)). Qed.
Lemma lem1215921 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1215922 {A : Type'} : (term298 A) = (term299 A).
Proof. exact (MK_COMB (@lem1215921) (@lem1215920 A)). Qed.
Lemma lem1215924 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1215925 {A : Type'} : (term300 A) = (term301 A).
Proof. exact (@lem1215924 (term169 A)). Qed.
Lemma lem1215935 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1215936 {A : Type'} (P : type1029 A) (Q : type1029 A) : (term302 A P Q) = (term303 A P Q).
Proof. exact (@lem1215935 (type1628 A) P Q). Qed.
Lemma lem1215937 {A : Type'} (h : list A) (x : list A) : (term304 A h x) = (term305 A h x).
Proof. exact (@lem1215936 A (term306 A x) (term307 A h x)). Qed.
Lemma lem1215938 {A : Type'} (t : type1628 A) (x : list A) : (term308 A x t) = ((@List.In (list A) x (@nil (list A))) = False).
Proof. exact (eq_refl (term308 A x t)). Qed.
Lemma lem1215939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215940 {A : Type'} (t : type1628 A) (x : list A) : (term309 A x t) = (term310 A x).
Proof. exact (MK_COMB (@lem1215939) (@lem1215938 A t x)). Qed.
Lemma lem1215941 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : (term311 A h x t) = ((term312 A x h t) = (term313 A h x t)).
Proof. exact (eq_refl (term311 A h x t)). Qed.
Lemma lem1215942 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : (term314 A h x t) = (term315 A h x t).
Proof. exact (MK_COMB (@lem1215940 A t x) (@lem1215941 A h x t)). Qed.
Lemma lem1215943 {A : Type'} (h : list A) (x : list A) : (term316 A h x) = (term317 A h x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1215942 A h x t)). Qed.
Lemma lem1215944 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1215945 {A : Type'} (h : list A) (x : list A) : (term304 A h x) = (term318 A h x).
Proof. exact (MK_COMB (@lem1215944 A) (@lem1215943 A h x)). Qed.
Lemma lem1215946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1215947 {A : Type'} (h : list A) (x : list A) : (term319 A h x) = (term320 A h x).
Proof. exact (MK_COMB (@lem1215946) (@lem1215945 A h x)). Qed.
Lemma lem1215948 {A : Type'} (t : type1628 A) (x : list A) : (term308 A x t) = ((@List.In (list A) x (@nil (list A))) = False).
Proof. exact (eq_refl (term308 A x t)). Qed.
Lemma lem1215949 {A : Type'} (x : list A) : (term321 A x) = (term306 A x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1215948 A t x)). Qed.
Lemma lem1215950 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1215951 {A : Type'} (x : list A) : (term322 A x) = (term323 A x).
Proof. exact (MK_COMB (@lem1215950 A) (@lem1215949 A x)). Qed.
Lemma lem1215952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215953 {A : Type'} (x : list A) : (term324 A x) = (term325 A x).
Proof. exact (MK_COMB (@lem1215952) (@lem1215951 A x)). Qed.
Lemma lem1215954 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : (term311 A h x t) = ((term312 A x h t) = (term313 A h x t)).
Proof. exact (eq_refl (term311 A h x t)). Qed.
Lemma lem1215955 {A : Type'} (h : list A) (x : list A) : (term326 A h x) = (term307 A h x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1215954 A h x t)). Qed.
Lemma lem1215956 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1215957 {A : Type'} (h : list A) (x : list A) : (term327 A h x) = (term328 A h x).
Proof. exact (MK_COMB (@lem1215956 A) (@lem1215955 A h x)). Qed.
Lemma lem1215958 {A : Type'} (h : list A) (x : list A) : (term305 A h x) = (term329 A h x).
Proof. exact (MK_COMB (@lem1215953 A x) (@lem1215957 A h x)). Qed.
Lemma lem1215959 {A : Type'} (h : list A) (x : list A) : ((term304 A h x) = (term305 A h x)) = ((term318 A h x) = (term329 A h x)).
Proof. exact (MK_COMB (@lem1215947 A h x) (@lem1215958 A h x)). Qed.
Lemma lem1215960 {A : Type'} (h : list A) (x : list A) : (term318 A h x) = (term329 A h x).
Proof. exact (EQ_MP (@lem1215959 A h x) (@lem1215937 A h x)). Qed.
Lemma lem1215964 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1215965 {A : Type'} (t : Prop) : (term330 A t) = t.
Proof. exact (@lem1215964 (type1628 A) t). Qed.
Lemma lem1215966 {A : Type'} (x : list A) : (term323 A x) = ((@List.In (list A) x (@nil (list A))) = False).
Proof. exact (@lem1215965 A ((@List.In (list A) x (@nil (list A))) = False)). Qed.
Lemma lem1215968 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem1215969 {A : Type'} (x : list A) : ((@List.In (list A) x (@nil (list A))) = False) = (term331 A x).
Proof. exact (@lem1215968 (@List.In (list A) x (@nil (list A)))). Qed.
Lemma lem1215970 {A : Type'} (x : list A) : (term323 A x) = (term331 A x).
Proof. exact (TRANS (@lem1215966 A x) (@lem1215969 A x)). Qed.
Lemma lem1215971 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215972 {A : Type'} (x : list A) : (term325 A x) = (term332 A x).
Proof. exact (MK_COMB (@lem1215971) (@lem1215970 A x)). Qed.
Lemma lem1215979 {A : Type'} (h : list A) (x : list A) : (term328 A h x) = (term328 A h x).
Proof. exact (eq_refl (term328 A h x)). Qed.
Lemma lem1215980 {A : Type'} (h : list A) (x : list A) : (term329 A h x) = (term333 A h x).
Proof. exact (MK_COMB (@lem1215972 A x) (@lem1215979 A h x)). Qed.
Lemma lem1215983 {A : Type'} (h : list A) (x : list A) : (term318 A h x) = (term333 A h x).
Proof. exact (TRANS (@lem1215960 A h x) (@lem1215980 A h x)). Qed.
Lemma lem1215984 {A : Type'} (h : list A) : (term334 A h) = (term335 A h).
Proof. exact (fun_ext (fun x : list A => @lem1215983 A h x)). Qed.
Lemma lem1215985 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1215986 {A : Type'} (h : list A) : (term336 A h) = (term337 A h).
Proof. exact (MK_COMB (@lem1215985 A) (@lem1215984 A h)). Qed.
Lemma lem1215988 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1215989 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1215988 (list A) P Q). Qed.
Lemma lem1215990 {A : Type'} (h : list A) : (term338 A h) = (term339 A h).
Proof. exact (@lem1215989 A (term340 A) (term341 A h)). Qed.
Lemma lem1215991 {A : Type'} (x : list A) : (term342 A x) = (term331 A x).
Proof. exact (eq_refl (term342 A x)). Qed.
Lemma lem1215992 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1215993 {A : Type'} (x : list A) : (term343 A x) = (term332 A x).
Proof. exact (MK_COMB (@lem1215992) (@lem1215991 A x)). Qed.
Lemma lem1215994 {A : Type'} (h : list A) (x : list A) : (term344 A h x) = (term328 A h x).
Proof. exact (eq_refl (term344 A h x)). Qed.
Lemma lem1215995 {A : Type'} (h : list A) (x : list A) : (term345 A h x) = (term333 A h x).
Proof. exact (MK_COMB (@lem1215993 A x) (@lem1215994 A h x)). Qed.
Lemma lem1215996 {A : Type'} (h : list A) : (term346 A h) = (term335 A h).
Proof. exact (fun_ext (fun x : list A => @lem1215995 A h x)). Qed.
Lemma lem1215997 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1215998 {A : Type'} (h : list A) : (term338 A h) = (term337 A h).
Proof. exact (MK_COMB (@lem1215997 A) (@lem1215996 A h)). Qed.
Lemma lem1215999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216000 {A : Type'} (h : list A) : (term347 A h) = (term348 A h).
Proof. exact (MK_COMB (@lem1215999) (@lem1215998 A h)). Qed.
Lemma lem1216001 {A : Type'} (x : list A) : (term342 A x) = (term331 A x).
Proof. exact (eq_refl (term342 A x)). Qed.
Lemma lem1216002 {A : Type'} : (term349 A) = (term340 A).
Proof. exact (fun_ext (fun x : list A => @lem1216001 A x)). Qed.
Lemma lem1216003 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216004 {A : Type'} : (term350 A) = (term351 A).
Proof. exact (MK_COMB (@lem1216003 A) (@lem1216002 A)). Qed.
Lemma lem1216005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216006 {A : Type'} : (term352 A) = (term353 A).
Proof. exact (MK_COMB (@lem1216005) (@lem1216004 A)). Qed.
Lemma lem1216007 {A : Type'} (h : list A) (x : list A) : (term344 A h x) = (term328 A h x).
Proof. exact (eq_refl (term344 A h x)). Qed.
Lemma lem1216008 {A : Type'} (h : list A) : (term354 A h) = (term341 A h).
Proof. exact (fun_ext (fun x : list A => @lem1216007 A h x)). Qed.
Lemma lem1216009 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216010 {A : Type'} (h : list A) : (term355 A h) = (term356 A h).
Proof. exact (MK_COMB (@lem1216009 A) (@lem1216008 A h)). Qed.
Lemma lem1216011 {A : Type'} (h : list A) : (term339 A h) = (term357 A h).
Proof. exact (MK_COMB (@lem1216006 A) (@lem1216010 A h)). Qed.
Lemma lem1216012 {A : Type'} (h : list A) : ((term338 A h) = (term339 A h)) = ((term337 A h) = (term357 A h)).
Proof. exact (MK_COMB (@lem1216000 A h) (@lem1216011 A h)). Qed.
Lemma lem1216013 {A : Type'} (h : list A) : (term337 A h) = (term357 A h).
Proof. exact (EQ_MP (@lem1216012 A h) (@lem1215990 A h)). Qed.
Lemma lem1216030 {A : Type'} (h : list A) : (term336 A h) = (term357 A h).
Proof. exact (TRANS (@lem1215986 A h) (@lem1216013 A h)). Qed.
Lemma lem1216031 {A : Type'} : (term358 A) = (term359 A).
Proof. exact (fun_ext (fun h : list A => @lem1216030 A h)). Qed.
Lemma lem1216032 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216033 {A : Type'} : (term169 A) = (term360 A).
Proof. exact (MK_COMB (@lem1216032 A) (@lem1216031 A)). Qed.
Lemma lem1216035 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem16446 A P Q) (@lem16445 A P Q)). Qed.
Lemma lem1216036 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1216035 (list A) P Q). Qed.
Lemma lem1216037 {A : Type'} : (term361 A) = (term362 A).
Proof. exact (@lem1216036 A (term363 A) (term364 A)). Qed.
Lemma lem1216038 {A : Type'} (h : list A) : (term365 A h) = (term351 A).
Proof. exact (eq_refl (term365 A h)). Qed.
Lemma lem1216039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216040 {A : Type'} (h : list A) : (term366 A h) = (term353 A).
Proof. exact (MK_COMB (@lem1216039) (@lem1216038 A h)). Qed.
Lemma lem1216041 {A : Type'} (h : list A) : (term367 A h) = (term356 A h).
Proof. exact (eq_refl (term367 A h)). Qed.
Lemma lem1216042 {A : Type'} (h : list A) : (term368 A h) = (term357 A h).
Proof. exact (MK_COMB (@lem1216040 A h) (@lem1216041 A h)). Qed.
Lemma lem1216043 {A : Type'} : (term369 A) = (term359 A).
Proof. exact (fun_ext (fun h : list A => @lem1216042 A h)). Qed.
Lemma lem1216044 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216045 {A : Type'} : (term361 A) = (term360 A).
Proof. exact (MK_COMB (@lem1216044 A) (@lem1216043 A)). Qed.
Lemma lem1216046 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216047 {A : Type'} : (term370 A) = (term371 A).
Proof. exact (MK_COMB (@lem1216046) (@lem1216045 A)). Qed.
Lemma lem1216048 {A : Type'} (h : list A) : (term365 A h) = (term351 A).
Proof. exact (eq_refl (term365 A h)). Qed.
Lemma lem1216049 {A : Type'} : (term372 A) = (term363 A).
Proof. exact (fun_ext (fun h : list A => @lem1216048 A h)). Qed.
Lemma lem1216050 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216051 {A : Type'} : (term373 A) = (term374 A).
Proof. exact (MK_COMB (@lem1216050 A) (@lem1216049 A)). Qed.
Lemma lem1216052 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216053 {A : Type'} : (term375 A) = (term376 A).
Proof. exact (MK_COMB (@lem1216052) (@lem1216051 A)). Qed.
Lemma lem1216054 {A : Type'} (h : list A) : (term367 A h) = (term356 A h).
Proof. exact (eq_refl (term367 A h)). Qed.
Lemma lem1216055 {A : Type'} : (term377 A) = (term364 A).
Proof. exact (fun_ext (fun h : list A => @lem1216054 A h)). Qed.
Lemma lem1216056 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216057 {A : Type'} : (term378 A) = (term379 A).
Proof. exact (MK_COMB (@lem1216056 A) (@lem1216055 A)). Qed.
Lemma lem1216058 {A : Type'} : (term362 A) = (term380 A).
Proof. exact (MK_COMB (@lem1216053 A) (@lem1216057 A)). Qed.
Lemma lem1216059 {A : Type'} : ((term361 A) = (term362 A)) = ((term360 A) = (term380 A)).
Proof. exact (MK_COMB (@lem1216047 A) (@lem1216058 A)). Qed.
Lemma lem1216060 {A : Type'} : (term360 A) = (term380 A).
Proof. exact (EQ_MP (@lem1216059 A) (@lem1216037 A)). Qed.
Lemma lem1216064 {A : Type'} (t : Prop) : (term117 A t) = t.
Proof. exact (EQ_MP (@lem16458 A t) (@lem16457 A t)). Qed.
Lemma lem1216065 {A : Type'} (t : Prop) : (term118 A t) = t.
Proof. exact (@lem1216064 (list A) t). Qed.
Lemma lem1216066 {A : Type'} : (term374 A) = (term351 A).
Proof. exact (@lem1216065 A (term351 A)). Qed.
Lemma lem1216071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216072 {A : Type'} : (term376 A) = (term353 A).
Proof. exact (MK_COMB (@lem1216071) (@lem1216066 A)). Qed.
Lemma lem1216087 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (eq_refl (term379 A)). Qed.
Lemma lem1216088 {A : Type'} : (term380 A) = (term381 A).
Proof. exact (MK_COMB (@lem1216072 A) (@lem1216087 A)). Qed.
Lemma lem1216091 {A : Type'} : (term360 A) = (term381 A).
Proof. exact (TRANS (@lem1216060 A) (@lem1216088 A)). Qed.
Lemma lem1216092 {A : Type'} : (term169 A) = (term381 A).
Proof. exact (TRANS (@lem1216033 A) (@lem1216091 A)). Qed.
Lemma lem1216093 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1216094 {A : Type'} : (term301 A) = (term382 A).
Proof. exact (MK_COMB (@lem1216093) (@lem1216092 A)). Qed.
Lemma lem1216095 {A : Type'} : (term300 A) = (term382 A).
Proof. exact (TRANS (@lem1215925 A) (@lem1216094 A)). Qed.
Lemma lem1216096 {A : Type'} : (term383 A) = (term384 A).
Proof. exact (MK_COMB (@lem1215922 A) (@lem1216095 A)). Qed.
Lemma lem1216099 {A : Type'} : (term385 A) = (term385 A).
Proof. exact (eq_refl (term385 A)). Qed.
Lemma lem1216100 {A : Type'} : (term386 A) = (term387 A).
Proof. exact (MK_COMB (@lem1216099 A) (@lem1216096 A)). Qed.
Lemma lem1216103 {A : Type'} : (term388 A) = (term388 A).
Proof. exact (eq_refl (term388 A)). Qed.
Lemma lem1216104 {A : Type'} : (term389 A) = (term390 A).
Proof. exact (MK_COMB (@lem1216103 A) (@lem1216100 A)). Qed.
Lemma lem1216107 {A : Type'} (y : A) (l : list A) (x : A) : (term391 A y l x) = (term392 A y l x).
Proof. exact (MK_COMB (@lem1215711 A y l x) (@lem1216104 A)). Qed.
Lemma lem1216110 {A : Type'} (x : A) (y : A) : (term725 A x y) = (term725 A x y).
Proof. exact (eq_refl (term725 A x y)). Qed.
Lemma lem1216111 {A : Type'} (y : A) (l : list A) (x : A) : (term721 A y l x) = (term726 A y l x).
Proof. exact (MK_COMB (@lem1216110 A x y) (@lem1216107 A y l x)). Qed.
Lemma lem1216114 {A : Type'} (l : list A) (x : A) : (term727 A l x) = (term728 A l x).
Proof. exact (fun_ext (fun y : A => @lem1216111 A y l x)). Qed.
Lemma lem1216115 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216116 {A : Type'} (l : list A) (x : A) : (term729 A l x) = (term730 A l x).
Proof. exact (MK_COMB (@lem1216115 A) (@lem1216114 A l x)). Qed.
Lemma lem1216121 {A : Type'} (x : A) : (term731 A x) = (term732 A x).
Proof. exact (fun_ext (fun l : list A => @lem1216116 A l x)). Qed.
Lemma lem1216122 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216123 {A : Type'} (x : A) : (term733 A x) = (term734 A x).
Proof. exact (MK_COMB (@lem1216122 A) (@lem1216121 A x)). Qed.
Lemma lem1216128 {A : Type'} : (term735 A) = (term736 A).
Proof. exact (fun_ext (fun x : A => @lem1216123 A x)). Qed.
Lemma lem1216129 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216138 {A : Type'} : (term737 A) = (term738 A).
Proof. exact (MK_COMB (@lem1216129 A) (@lem1216128 A)). Qed.
Lemma lem1216147 {A : Type'} (h : list A) (x : list A) (t : type1628 A) : ((term312 A x h t) = (term313 A h x t)) = ((term312 A x h t) = (term313 A h x t)).
Proof. exact (eq_refl ((term312 A x h t) = (term313 A h x t))). Qed.
Lemma lem1216148 {A : Type'} (h : list A) (x : list A) : (term307 A h x) = (term307 A h x).
Proof. exact (fun_ext (fun t : type1628 A => @lem1216147 A h x t)). Qed.
Lemma lem1216149 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1216150 {A : Type'} (h : list A) (x : list A) : (term328 A h x) = (term328 A h x).
Proof. exact (MK_COMB (@lem1216149 A) (@lem1216148 A h x)). Qed.
Lemma lem1216151 {A : Type'} (h : list A) : (term341 A h) = (term341 A h).
Proof. exact (fun_ext (fun x : list A => @lem1216150 A h x)). Qed.
Lemma lem1216152 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216153 {A : Type'} (h : list A) : (term356 A h) = (term356 A h).
Proof. exact (MK_COMB (@lem1216152 A) (@lem1216151 A h)). Qed.
Lemma lem1216154 {A : Type'} : (term364 A) = (term364 A).
Proof. exact (fun_ext (fun h : list A => @lem1216153 A h)). Qed.
Lemma lem1216155 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216156 {A : Type'} : (term379 A) = (term379 A).
Proof. exact (MK_COMB (@lem1216155 A) (@lem1216154 A)). Qed.
Lemma lem1216159 {A : Type'} (x : list A) : (term331 A x) = (term331 A x).
Proof. exact (eq_refl (term331 A x)). Qed.
Lemma lem1216160 {A : Type'} : (term340 A) = (term340 A).
Proof. exact (fun_ext (fun x : list A => @lem1216159 A x)). Qed.
Lemma lem1216161 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216162 {A : Type'} : (term351 A) = (term351 A).
Proof. exact (MK_COMB (@lem1216161 A) (@lem1216160 A)). Qed.
Lemma lem1216163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216164 {A : Type'} : (term353 A) = (term353 A).
Proof. exact (MK_COMB (@lem1216163) (@lem1216162 A)). Qed.
Lemma lem1216165 {A : Type'} : (term381 A) = (term381 A).
Proof. exact (MK_COMB (@lem1216164 A) (@lem1216156 A)). Qed.
Lemma lem1216166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1216167 {A : Type'} : (term382 A) = (term382 A).
Proof. exact (MK_COMB (@lem1216166) (@lem1216165 A)). Qed.
Lemma lem1216176 {A : Type'} (h : A) (x : A) (t : list A) : ((term106 A x h t) = (term107 A h x t)) = ((term106 A x h t) = (term107 A h x t)).
Proof. exact (eq_refl ((term106 A x h t) = (term107 A h x t))). Qed.
Lemma lem1216177 {A : Type'} (h : A) (x : A) : (term228 A h x) = (term228 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1216176 A h x t)). Qed.
Lemma lem1216178 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216179 {A : Type'} (h : A) (x : A) : (term246 A h x) = (term246 A h x).
Proof. exact (MK_COMB (@lem1216178 A) (@lem1216177 A h x)). Qed.
Lemma lem1216180 {A : Type'} (h : A) : (term257 A h) = (term257 A h).
Proof. exact (fun_ext (fun x : A => @lem1216179 A h x)). Qed.
Lemma lem1216181 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216182 {A : Type'} (h : A) : (term272 A h) = (term272 A h).
Proof. exact (MK_COMB (@lem1216181 A) (@lem1216180 A h)). Qed.
Lemma lem1216183 {A : Type'} : (term280 A) = (term280 A).
Proof. exact (fun_ext (fun h : A => @lem1216182 A h)). Qed.
Lemma lem1216184 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216185 {A : Type'} : (term295 A) = (term295 A).
Proof. exact (MK_COMB (@lem1216184 A) (@lem1216183 A)). Qed.
Lemma lem1216188 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1216189 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1216188 A x)). Qed.
Lemma lem1216190 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216191 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1216190 A) (@lem1216189 A)). Qed.
Lemma lem1216192 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216193 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (MK_COMB (@lem1216192) (@lem1216191 A)). Qed.
Lemma lem1216194 {A : Type'} : (term297 A) = (term297 A).
Proof. exact (MK_COMB (@lem1216193 A) (@lem1216185 A)). Qed.
Lemma lem1216195 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1216196 {A : Type'} : (term299 A) = (term299 A).
Proof. exact (MK_COMB (@lem1216195) (@lem1216194 A)). Qed.
Lemma lem1216197 {A : Type'} : (term384 A) = (term384 A).
Proof. exact (MK_COMB (@lem1216196 A) (@lem1216167 A)). Qed.
Lemma lem1216198 {A : Type'} (h : list A) (t : type1628 A) (l : type1628 A) : ((term407 A h t l) = (term408 A h t l)) = ((term407 A h t l) = (term408 A h t l)).
Proof. exact (eq_refl ((term407 A h t l) = (term408 A h t l))). Qed.
Lemma lem1216199 {A : Type'} (h : list A) (t : type1628 A) : (term409 A h t) = (term409 A h t).
Proof. exact (fun_ext (fun l : type1628 A => @lem1216198 A h t l)). Qed.
Lemma lem1216200 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1216201 {A : Type'} (h : list A) (t : type1628 A) : (term410 A h t) = (term410 A h t).
Proof. exact (MK_COMB (@lem1216200 A) (@lem1216199 A h t)). Qed.
Lemma lem1216202 {A : Type'} (h : list A) : (term411 A h) = (term411 A h).
Proof. exact (fun_ext (fun t : type1628 A => @lem1216201 A h t)). Qed.
Lemma lem1216203 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1216204 {A : Type'} (h : list A) : (term412 A h) = (term412 A h).
Proof. exact (MK_COMB (@lem1216203 A) (@lem1216202 A h)). Qed.
Lemma lem1216205 {A : Type'} : (term413 A) = (term413 A).
Proof. exact (fun_ext (fun h : list A => @lem1216204 A h)). Qed.
Lemma lem1216206 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216207 {A : Type'} : (term414 A) = (term414 A).
Proof. exact (MK_COMB (@lem1216206 A) (@lem1216205 A)). Qed.
Lemma lem1216208 {A : Type'} (l : type1628 A) : ((@List.app (list A) (@nil (list A)) l) = l) = ((@List.app (list A) (@nil (list A)) l) = l).
Proof. exact (eq_refl ((@List.app (list A) (@nil (list A)) l) = l)). Qed.
Lemma lem1216209 {A : Type'} : (term415 A) = (term415 A).
Proof. exact (fun_ext (fun l : type1628 A => @lem1216208 A l)). Qed.
Lemma lem1216210 {A : Type'} : (@all (list (list A))) = (@all (list (list A))).
Proof. exact (eq_refl (@all (list (list A)))). Qed.
Lemma lem1216211 {A : Type'} : (term416 A) = (term416 A).
Proof. exact (MK_COMB (@lem1216210 A) (@lem1216209 A)). Qed.
Lemma lem1216212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216213 {A : Type'} : (term417 A) = (term417 A).
Proof. exact (MK_COMB (@lem1216212) (@lem1216211 A)). Qed.
Lemma lem1216214 {A : Type'} : (term171 A) = (term171 A).
Proof. exact (MK_COMB (@lem1216213 A) (@lem1216207 A)). Qed.
Lemma lem1216215 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1216216 {A : Type'} : (term385 A) = (term385 A).
Proof. exact (MK_COMB (@lem1216215) (@lem1216214 A)). Qed.
Lemma lem1216217 {A : Type'} : (term387 A) = (term387 A).
Proof. exact (MK_COMB (@lem1216216 A) (@lem1216197 A)). Qed.
Lemma lem1216218 {A : Type'} (h : A) (t : list A) (l : list A) : ((term418 A h t l) = (term419 A h t l)) = ((term418 A h t l) = (term419 A h t l)).
Proof. exact (eq_refl ((term418 A h t l) = (term419 A h t l))). Qed.
Lemma lem1216219 {A : Type'} (h : A) (t : list A) : (term420 A h t) = (term420 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1216218 A h t l)). Qed.
Lemma lem1216220 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216221 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term421 A h t).
Proof. exact (MK_COMB (@lem1216220 A) (@lem1216219 A h t)). Qed.
Lemma lem1216222 {A : Type'} (h : A) : (term422 A h) = (term422 A h).
Proof. exact (fun_ext (fun t : list A => @lem1216221 A h t)). Qed.
Lemma lem1216223 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216224 {A : Type'} (h : A) : (term423 A h) = (term423 A h).
Proof. exact (MK_COMB (@lem1216223 A) (@lem1216222 A h)). Qed.
Lemma lem1216225 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun h : A => @lem1216224 A h)). Qed.
Lemma lem1216226 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216227 {A : Type'} : (term425 A) = (term425 A).
Proof. exact (MK_COMB (@lem1216226 A) (@lem1216225 A)). Qed.
Lemma lem1216228 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1216229 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1216228 A l)). Qed.
Lemma lem1216230 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216231 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1216230 A) (@lem1216229 A)). Qed.
Lemma lem1216232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216233 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (MK_COMB (@lem1216232) (@lem1216231 A)). Qed.
Lemma lem1216234 {A : Type'} : (term170 A) = (term170 A).
Proof. exact (MK_COMB (@lem1216233 A) (@lem1216227 A)). Qed.
Lemma lem1216235 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1216236 {A : Type'} : (term388 A) = (term388 A).
Proof. exact (MK_COMB (@lem1216235) (@lem1216234 A)). Qed.
Lemma lem1216237 {A : Type'} : (term390 A) = (term390 A).
Proof. exact (MK_COMB (@lem1216236 A) (@lem1216217 A)). Qed.
Lemma lem1216238 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : ((@cons A y l) = (term102 A l1 x l2)) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl ((@cons A y l) = (term102 A l1 x l2))). Qed.
Lemma lem1216239 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term200 A y l l1 x) = (term200 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216238 A y l l1 x l2)). Qed.
Lemma lem1216240 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216241 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term211 A y l l1 x) = (term211 A y l l1 x).
Proof. exact (MK_COMB (@lem1216240 A) (@lem1216239 A y l l1 x)). Qed.
Lemma lem1216246 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1216247 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term212 A y l l1 x) = (term212 A y l l1 x).
Proof. exact (MK_COMB (@lem1216246 A x l1) (@lem1216241 A y l l1 x)). Qed.
Lemma lem1216248 {A : Type'} (y : A) (l : list A) (x : A) : (term214 A y l x) = (term214 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216247 A y l l1 x)). Qed.
Lemma lem1216249 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216250 {A : Type'} (y : A) (l : list A) (x : A) : (term215 A y l x) = (term215 A y l x).
Proof. exact (MK_COMB (@lem1216249 A) (@lem1216248 A y l x)). Qed.
Lemma lem1216257 {A : Type'} (y : A) (x : A) (l : list A) : (term157 A y x l) = (term157 A y x l).
Proof. exact (eq_refl (term157 A y x l)). Qed.
Lemma lem1216258 {A : Type'} (y : A) (l : list A) (x : A) : (term216 A y l x) = (term216 A y l x).
Proof. exact (MK_COMB (@lem1216257 A y x l) (@lem1216250 A y l x)). Qed.
Lemma lem1216259 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term102 A l1 x l2)) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (l = (term102 A l1 x l2))). Qed.
Lemma lem1216260 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term182 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216259 A l l1 x l2)). Qed.
Lemma lem1216261 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216262 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term191 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1216261 A) (@lem1216260 A l l1 x)). Qed.
Lemma lem1216267 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1216268 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term192 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1216267 A x l1) (@lem1216262 A l l1 x)). Qed.
Lemma lem1216269 {A : Type'} (l : list A) (x : A) : (term193 A l x) = (term193 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216268 A l l1 x)). Qed.
Lemma lem1216270 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216271 {A : Type'} (l : list A) (x : A) : (term194 A l x) = (term194 A l x).
Proof. exact (MK_COMB (@lem1216270 A) (@lem1216269 A l x)). Qed.
Lemma lem1216274 {A : Type'} (x : A) (l : list A) : (term195 A x l) = (term195 A x l).
Proof. exact (eq_refl (term195 A x l)). Qed.
Lemma lem1216275 {A : Type'} (l : list A) (x : A) : (term196 A l x) = (term196 A l x).
Proof. exact (MK_COMB (@lem1216274 A x l) (@lem1216271 A l x)). Qed.
Lemma lem1216276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1216277 {A : Type'} (l : list A) (x : A) : (term197 A l x) = (term197 A l x).
Proof. exact (MK_COMB (@lem1216276) (@lem1216275 A l x)). Qed.
Lemma lem1216278 {A : Type'} (y : A) (l : list A) (x : A) : (term217 A y l x) = (term217 A y l x).
Proof. exact (MK_COMB (@lem1216277 A l x) (@lem1216258 A y l x)). Qed.
Lemma lem1216279 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1216280 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term218 A y l x).
Proof. exact (MK_COMB (@lem1216279) (@lem1216278 A y l x)). Qed.
Lemma lem1216281 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1216282 {A : Type'} (y : A) (l : list A) (x : A) : (term220 A y l x) = (term220 A y l x).
Proof. exact (MK_COMB (@lem1216281) (@lem1216280 A y l x)). Qed.
Lemma lem1216283 {A : Type'} (y : A) (l : list A) (x : A) : (term392 A y l x) = (term392 A y l x).
Proof. exact (MK_COMB (@lem1216282 A y l x) (@lem1216237 A)). Qed.
Lemma lem1216288 {A : Type'} (x : A) (y : A) : (term725 A x y) = (term725 A x y).
Proof. exact (eq_refl (term725 A x y)). Qed.
Lemma lem1216289 {A : Type'} (y : A) (l : list A) (x : A) : (term726 A y l x) = (term726 A y l x).
Proof. exact (MK_COMB (@lem1216288 A x y) (@lem1216283 A y l x)). Qed.
Lemma lem1216290 {A : Type'} (l : list A) (x : A) : (term728 A l x) = (term728 A l x).
Proof. exact (fun_ext (fun y : A => @lem1216289 A y l x)). Qed.
Lemma lem1216291 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216292 {A : Type'} (l : list A) (x : A) : (term730 A l x) = (term730 A l x).
Proof. exact (MK_COMB (@lem1216291 A) (@lem1216290 A l x)). Qed.
Lemma lem1216293 {A : Type'} (x : A) : (term732 A x) = (term732 A x).
Proof. exact (fun_ext (fun l : list A => @lem1216292 A l x)). Qed.
Lemma lem1216294 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216295 {A : Type'} (x : A) : (term734 A x) = (term734 A x).
Proof. exact (MK_COMB (@lem1216294 A) (@lem1216293 A x)). Qed.
Lemma lem1216296 {A : Type'} : (term736 A) = (term736 A).
Proof. exact (fun_ext (fun x : A => @lem1216295 A x)). Qed.
Lemma lem1216297 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216298 {A : Type'} : (term738 A) = (term738 A).
Proof. exact (MK_COMB (@lem1216297 A) (@lem1216296 A)). Qed.
Lemma lem1216473 {A : Type'} : (term737 A) = (term738 A).
Proof. exact (TRANS (@lem1216138 A) (@lem1216298 A)). Qed.
Lemma lem1216474 {A : Type'} : (term738 A) = (term737 A).
Proof. exact (SYM (@lem1216473 A)). Qed.
Lemma lem1216476 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term218 A y l x) : term218 A y l x.
Proof. exact (h1). Qed.
Lemma lem1216477 {A : Type'} (h1 : term170 A) : term170 A.
Proof. exact (h1). Qed.
Lemma lem1216479 {A : Type'} (h1 : term297 A) : term297 A.
Proof. exact (h1). Qed.
Lemma lem1216486 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1216489 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (l = (term102 A l1 x l2)) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (l = (term102 A l1 x l2))). Qed.
Lemma lem1216490 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term182 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216489 A l l1 x l2)). Qed.
Lemma lem1216491 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216492 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term191 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1216491 A) (@lem1216490 A l l1 x)). Qed.
Lemma lem1216494 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1216495 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term192 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1216494 A x l1) (@lem1216492 A l l1 x)). Qed.
Lemma lem1216496 {A : Type'} (l : list A) (x : A) : (term193 A l x) = (term193 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216495 A l l1 x)). Qed.
Lemma lem1216497 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216498 {A : Type'} (l : list A) (x : A) : (term194 A l x) = (term194 A l x).
Proof. exact (MK_COMB (@lem1216497 A) (@lem1216496 A l x)). Qed.
Lemma lem1216500 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1216501 {A : Type'} (l : list A) (x : A) : (term430 A l x) = (term430 A l x).
Proof. exact (MK_COMB (@lem1216500 A x l) (@lem1216498 A l x)). Qed.
Lemma lem1216502 {A : Type'} (l : list A) (x : A) : (term196 A l x) = (term430 A l x).
Proof. exact (@lem17265 (@List.In A x l) (term194 A l x)). Qed.
Lemma lem1216503 {A : Type'} (l : list A) (x : A) : (term196 A l x) = (term430 A l x).
Proof. exact (TRANS (@lem1216502 A l x) (@lem1216501 A l x)). Qed.
Lemma lem1216511 {A : Type'} (x : A) (l1 : list A) : (term431 A x l1) = (@List.In A x l1).
Proof. exact (@lem16933 (@List.In A x l1)). Qed.
Lemma lem1216513 {A : Type'} (P : type1143 A) : (term432 A P) = (term433 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1216514 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term434 A y l l1 x) = (term435 A y l l1 x).
Proof. exact (@lem1216513 A (term200 A y l l1 x)). Qed.
Lemma lem1216515 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term201 A y l l1 x l2) = ((@cons A y l) = (term102 A l1 x l2)).
Proof. exact (eq_refl (term201 A y l l1 x l2)). Qed.
Lemma lem1216516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1216518 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term436 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1216516) (@lem1216515 A y l l1 x l2)). Qed.
Lemma lem1216519 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term438 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216518 A y l l1 x l2)). Qed.
Lemma lem1216520 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216521 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term435 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1216520 A) (@lem1216519 A y l l1 x)). Qed.
Lemma lem1216522 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term434 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (TRANS (@lem1216514 A y l l1 x) (@lem1216521 A y l l1 x)). Qed.
Lemma lem1216523 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1216524 {A : Type'} (x : A) (l1 : list A) : (term441 A x l1) = (term105 A x l1).
Proof. exact (MK_COMB (@lem1216523) (@lem1216511 A x l1)). Qed.
Lemma lem1216525 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term442 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1216524 A x l1) (@lem1216522 A y l l1 x)). Qed.
Lemma lem1216526 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term444 A y l l1 x) = (term442 A y l l1 x).
Proof. exact (@lem17045 (term100 A x l1) (term211 A y l l1 x)). Qed.
Lemma lem1216527 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term444 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (TRANS (@lem1216526 A y l l1 x) (@lem1216525 A y l l1 x)). Qed.
Lemma lem1216528 {A : Type'} (P : type1143 A) : (term432 A P) = (term433 A P).
Proof. exact (@lem18394 (list A) P). Qed.
Lemma lem1216529 {A : Type'} (y : A) (l : list A) (x : A) : (term445 A y l x) = (term446 A y l x).
Proof. exact (@lem1216528 A (term214 A y l x)). Qed.
Lemma lem1216530 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term447 A y l x l1) = (term212 A y l l1 x).
Proof. exact (eq_refl (term447 A y l x l1)). Qed.
Lemma lem1216531 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1216532 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term448 A y l x l1) = (term444 A y l l1 x).
Proof. exact (MK_COMB (@lem1216531) (@lem1216530 A y l l1 x)). Qed.
Lemma lem1216533 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term448 A y l x l1) = (term443 A y l l1 x).
Proof. exact (TRANS (@lem1216532 A y l l1 x) (@lem1216527 A y l l1 x)). Qed.
Lemma lem1216534 {A : Type'} (y : A) (l : list A) (x : A) : (term449 A y l x) = (term450 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216533 A y l l1 x)). Qed.
Lemma lem1216535 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216536 {A : Type'} (y : A) (l : list A) (x : A) : (term446 A y l x) = (term451 A y l x).
Proof. exact (MK_COMB (@lem1216535 A) (@lem1216534 A y l x)). Qed.
Lemma lem1216537 {A : Type'} (y : A) (l : list A) (x : A) : (term445 A y l x) = (term451 A y l x).
Proof. exact (TRANS (@lem1216529 A y l x) (@lem1216536 A y l x)). Qed.
Lemma lem1216539 {A : Type'} (y : A) (x : A) (l : list A) : (term452 A y x l) = (term452 A y x l).
Proof. exact (eq_refl (term452 A y x l)). Qed.
Lemma lem1216540 {A : Type'} (y : A) (l : list A) (x : A) : (term453 A y l x) = (term454 A y l x).
Proof. exact (MK_COMB (@lem1216539 A y x l) (@lem1216537 A y l x)). Qed.
Lemma lem1216541 {A : Type'} (y : A) (l : list A) (x : A) : (term455 A y l x) = (term453 A y l x).
Proof. exact (@lem17362 (term107 A y x l) (term215 A y l x)). Qed.
Lemma lem1216542 {A : Type'} (y : A) (l : list A) (x : A) : (term455 A y l x) = (term454 A y l x).
Proof. exact (TRANS (@lem1216541 A y l x) (@lem1216540 A y l x)). Qed.
Lemma lem1216543 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216544 {A : Type'} (l : list A) (x : A) : (term456 A l x) = (term457 A l x).
Proof. exact (MK_COMB (@lem1216543) (@lem1216503 A l x)). Qed.
Lemma lem1216545 {A : Type'} (y : A) (l : list A) (x : A) : (term458 A y l x) = (term459 A y l x).
Proof. exact (MK_COMB (@lem1216544 A l x) (@lem1216542 A y l x)). Qed.
Lemma lem1216546 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term458 A y l x).
Proof. exact (@lem17362 (term196 A l x) (term216 A y l x)). Qed.
Lemma lem1216547 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term459 A y l x).
Proof. exact (TRANS (@lem1216546 A y l x) (@lem1216545 A y l x)). Qed.
Lemma lem1216654 {A : Type'} (P : Prop) (Q : A -> Prop) : (term177 A P Q) = (term176 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1216655 {A : Type'} (P : Prop) (Q : type1143 A) : (term179 A P Q) = (term178 A P Q).
Proof. exact (@lem1216654 (list A) P Q). Qed.
Lemma lem1216656 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term181 A l l1 x) = (term180 A l l1 x).
Proof. exact (@lem1216655 A (term100 A x l1) (term182 A l l1 x)). Qed.
Lemma lem1216657 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1216658 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term189 A l l1 x) = (term182 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216657 A l l1 x l2)). Qed.
Lemma lem1216659 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216660 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term190 A l l1 x) = (term191 A l l1 x).
Proof. exact (MK_COMB (@lem1216659 A) (@lem1216658 A l l1 x)). Qed.
Lemma lem1216661 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1216662 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term181 A l l1 x) = (term192 A l l1 x).
Proof. exact (MK_COMB (@lem1216661 A x l1) (@lem1216660 A l l1 x)). Qed.
Lemma lem1216663 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216664 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term460 A l l1 x) = (term461 A l l1 x).
Proof. exact (MK_COMB (@lem1216663) (@lem1216662 A l l1 x)). Qed.
Lemma lem1216665 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term183 A l l1 x l2) = (l = (term102 A l1 x l2)).
Proof. exact (eq_refl (term183 A l l1 x l2)). Qed.
Lemma lem1216666 {A : Type'} (x : A) (l1 : list A) : (term184 A x l1) = (term184 A x l1).
Proof. exact (eq_refl (term184 A x l1)). Qed.
Lemma lem1216667 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term185 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (MK_COMB (@lem1216666 A x l1) (@lem1216665 A l l1 x l2)). Qed.
Lemma lem1216668 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term186 A l l1 x) = (term75 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216667 A l l1 x l2)). Qed.
Lemma lem1216669 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216670 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term180 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1216669 A) (@lem1216668 A l l1 x)). Qed.
Lemma lem1216671 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term181 A l l1 x) = (term180 A l l1 x)) = ((term192 A l l1 x) = (term58 A l l1 x)).
Proof. exact (MK_COMB (@lem1216664 A l l1 x) (@lem1216670 A l l1 x)). Qed.
Lemma lem1216672 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term192 A l l1 x) = (term58 A l l1 x).
Proof. exact (EQ_MP (@lem1216671 A l l1 x) (@lem1216656 A l l1 x)). Qed.
Lemma lem1216673 {A : Type'} (l : list A) (x : A) : (term193 A l x) = (term56 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216672 A l l1 x)). Qed.
Lemma lem1216674 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216675 {A : Type'} (l : list A) (x : A) : (term194 A l x) = (term42 A l x).
Proof. exact (MK_COMB (@lem1216674 A) (@lem1216673 A l x)). Qed.
Lemma lem1216676 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1216677 {A : Type'} (l : list A) (x : A) : (term430 A l x) = (term462 A l x).
Proof. exact (MK_COMB (@lem1216676 A x l) (@lem1216675 A l x)). Qed.
Lemma lem1216679 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1216680 {A : Type'} (P : Prop) (Q : type1143 A) : (term465 A P Q) = (term466 A P Q).
Proof. exact (@lem1216679 (list A) P Q). Qed.
Lemma lem1216681 {A : Type'} (l : list A) (x : A) : (term467 A l x) = (term468 A l x).
Proof. exact (@lem1216680 A (term100 A x l) (term56 A l x)). Qed.
Lemma lem1216682 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term57 A l x l1) = (term58 A l l1 x).
Proof. exact (eq_refl (term57 A l x l1)). Qed.
Lemma lem1216683 {A : Type'} (l : list A) (x : A) : (term59 A l x) = (term56 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216682 A l l1 x)). Qed.
Lemma lem1216684 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216685 {A : Type'} (l : list A) (x : A) : (term60 A l x) = (term42 A l x).
Proof. exact (MK_COMB (@lem1216684 A) (@lem1216683 A l x)). Qed.
Lemma lem1216686 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1216687 {A : Type'} (l : list A) (x : A) : (term467 A l x) = (term462 A l x).
Proof. exact (MK_COMB (@lem1216686 A x l) (@lem1216685 A l x)). Qed.
Lemma lem1216688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216689 {A : Type'} (l : list A) (x : A) : (term469 A l x) = (term470 A l x).
Proof. exact (MK_COMB (@lem1216688) (@lem1216687 A l x)). Qed.
Lemma lem1216690 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term57 A l x l1) = (term58 A l l1 x).
Proof. exact (eq_refl (term57 A l x l1)). Qed.
Lemma lem1216691 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1216692 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term471 A l x l1) = (term472 A l l1 x).
Proof. exact (MK_COMB (@lem1216691 A x l) (@lem1216690 A l l1 x)). Qed.
Lemma lem1216693 {A : Type'} (l : list A) (x : A) : (term473 A l x) = (term474 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216692 A l l1 x)). Qed.
Lemma lem1216694 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216695 {A : Type'} (l : list A) (x : A) : (term468 A l x) = (term475 A l x).
Proof. exact (MK_COMB (@lem1216694 A) (@lem1216693 A l x)). Qed.
Lemma lem1216696 {A : Type'} (l : list A) (x : A) : ((term467 A l x) = (term468 A l x)) = ((term462 A l x) = (term475 A l x)).
Proof. exact (MK_COMB (@lem1216689 A l x) (@lem1216695 A l x)). Qed.
Lemma lem1216697 {A : Type'} (l : list A) (x : A) : (term462 A l x) = (term475 A l x).
Proof. exact (EQ_MP (@lem1216696 A l x) (@lem1216681 A l x)). Qed.
Lemma lem1216699 {A : Type'} (P : Prop) (Q : A -> Prop) : (term463 A P Q) = (term464 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1216700 {A : Type'} (P : Prop) (Q : type1143 A) : (term465 A P Q) = (term466 A P Q).
Proof. exact (@lem1216699 (list A) P Q). Qed.
Lemma lem1216701 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term476 A l l1 x) = (term477 A l l1 x).
Proof. exact (@lem1216700 A (term100 A x l) (term75 A l l1 x)). Qed.
Lemma lem1216702 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term76 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (eq_refl (term76 A l l1 x l2)). Qed.
Lemma lem1216703 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term78 A l l1 x) = (term75 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216702 A l l1 x l2)). Qed.
Lemma lem1216704 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216705 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term79 A l l1 x) = (term58 A l l1 x).
Proof. exact (MK_COMB (@lem1216704 A) (@lem1216703 A l l1 x)). Qed.
Lemma lem1216706 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1216707 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term476 A l l1 x) = (term472 A l l1 x).
Proof. exact (MK_COMB (@lem1216706 A x l) (@lem1216705 A l l1 x)). Qed.
Lemma lem1216708 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216709 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term478 A l l1 x) = (term479 A l l1 x).
Proof. exact (MK_COMB (@lem1216708) (@lem1216707 A l l1 x)). Qed.
Lemma lem1216710 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term76 A l l1 x l2) = (term77 A l l1 x l2).
Proof. exact (eq_refl (term76 A l l1 x l2)). Qed.
Lemma lem1216711 {A : Type'} (x : A) (l : list A) : (term429 A x l) = (term429 A x l).
Proof. exact (eq_refl (term429 A x l)). Qed.
Lemma lem1216712 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term480 A l l1 x l2) = (term481 A l l1 x l2).
Proof. exact (MK_COMB (@lem1216711 A x l) (@lem1216710 A l l1 x l2)). Qed.
Lemma lem1216713 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term482 A l l1 x) = (term483 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216712 A l l1 x l2)). Qed.
Lemma lem1216714 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216715 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term477 A l l1 x) = (term484 A l l1 x).
Proof. exact (MK_COMB (@lem1216714 A) (@lem1216713 A l l1 x)). Qed.
Lemma lem1216716 {A : Type'} (l : list A) (l1 : list A) (x : A) : ((term476 A l l1 x) = (term477 A l l1 x)) = ((term472 A l l1 x) = (term484 A l l1 x)).
Proof. exact (MK_COMB (@lem1216709 A l l1 x) (@lem1216715 A l l1 x)). Qed.
Lemma lem1216717 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term472 A l l1 x) = (term484 A l l1 x).
Proof. exact (EQ_MP (@lem1216716 A l l1 x) (@lem1216701 A l l1 x)). Qed.
Lemma lem1216718 {A : Type'} (l : list A) (x : A) : (term474 A l x) = (term485 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216717 A l l1 x)). Qed.
Lemma lem1216719 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216720 {A : Type'} (l : list A) (x : A) : (term475 A l x) = (term486 A l x).
Proof. exact (MK_COMB (@lem1216719 A) (@lem1216718 A l x)). Qed.
Lemma lem1216721 {A : Type'} (l : list A) (x : A) : (term462 A l x) = (term486 A l x).
Proof. exact (TRANS (@lem1216697 A l x) (@lem1216720 A l x)). Qed.
Lemma lem1216722 {A : Type'} (l : list A) (x : A) : (term430 A l x) = (term486 A l x).
Proof. exact (TRANS (@lem1216677 A l x) (@lem1216721 A l x)). Qed.
Lemma lem1216723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216724 {A : Type'} (l : list A) (x : A) : (term457 A l x) = (term487 A l x).
Proof. exact (MK_COMB (@lem1216723) (@lem1216722 A l x)). Qed.
Lemma lem1216725 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1216726 {A : Type'} (y : A) (l : list A) (x : A) : (term459 A y l x) = (term488 A y l x).
Proof. exact (MK_COMB (@lem1216724 A l x) (@lem1216725 A y l x)). Qed.
Lemma lem1216728 {A : Type'} (P : A -> Prop) (Q : Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1216729 {A : Type'} (P : type1143 A) (Q : Prop) : (term491 A P Q) = (term492 A P Q).
Proof. exact (@lem1216728 (list A) P Q). Qed.
Lemma lem1216730 {A : Type'} (y : A) (l : list A) (x : A) : (term493 A y l x) = (term494 A y l x).
Proof. exact (@lem1216729 A (term485 A l x) (term454 A y l x)). Qed.
Lemma lem1216731 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term495 A l x l1) = (term484 A l l1 x).
Proof. exact (eq_refl (term495 A l x l1)). Qed.
Lemma lem1216732 {A : Type'} (l : list A) (x : A) : (term496 A l x) = (term485 A l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216731 A l l1 x)). Qed.
Lemma lem1216733 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216734 {A : Type'} (l : list A) (x : A) : (term497 A l x) = (term486 A l x).
Proof. exact (MK_COMB (@lem1216733 A) (@lem1216732 A l x)). Qed.
Lemma lem1216735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216736 {A : Type'} (l : list A) (x : A) : (term498 A l x) = (term487 A l x).
Proof. exact (MK_COMB (@lem1216735) (@lem1216734 A l x)). Qed.
Lemma lem1216737 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1216738 {A : Type'} (y : A) (l : list A) (x : A) : (term493 A y l x) = (term488 A y l x).
Proof. exact (MK_COMB (@lem1216736 A l x) (@lem1216737 A y l x)). Qed.
Lemma lem1216739 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216740 {A : Type'} (y : A) (l : list A) (x : A) : (term499 A y l x) = (term500 A y l x).
Proof. exact (MK_COMB (@lem1216739) (@lem1216738 A y l x)). Qed.
Lemma lem1216741 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term495 A l x l1) = (term484 A l l1 x).
Proof. exact (eq_refl (term495 A l x l1)). Qed.
Lemma lem1216742 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216743 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term501 A l x l1) = (term502 A l l1 x).
Proof. exact (MK_COMB (@lem1216742) (@lem1216741 A l l1 x)). Qed.
Lemma lem1216744 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1216745 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term503 A l1 y l x) = (term504 A l1 y l x).
Proof. exact (MK_COMB (@lem1216743 A l l1 x) (@lem1216744 A y l x)). Qed.
Lemma lem1216746 {A : Type'} (y : A) (l : list A) (x : A) : (term505 A y l x) = (term506 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216745 A l1 y l x)). Qed.
Lemma lem1216747 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216748 {A : Type'} (y : A) (l : list A) (x : A) : (term494 A y l x) = (term507 A y l x).
Proof. exact (MK_COMB (@lem1216747 A) (@lem1216746 A y l x)). Qed.
Lemma lem1216749 {A : Type'} (y : A) (l : list A) (x : A) : ((term493 A y l x) = (term494 A y l x)) = ((term488 A y l x) = (term507 A y l x)).
Proof. exact (MK_COMB (@lem1216740 A y l x) (@lem1216748 A y l x)). Qed.
Lemma lem1216750 {A : Type'} (y : A) (l : list A) (x : A) : (term488 A y l x) = (term507 A y l x).
Proof. exact (EQ_MP (@lem1216749 A y l x) (@lem1216730 A y l x)). Qed.
Lemma lem1216752 {A : Type'} (P : A -> Prop) (Q : Prop) : (term489 A P Q) = (term490 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1216753 {A : Type'} (P : type1143 A) (Q : Prop) : (term491 A P Q) = (term492 A P Q).
Proof. exact (@lem1216752 (list A) P Q). Qed.
Lemma lem1216754 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term508 A l1 y l x) = (term509 A l1 y l x).
Proof. exact (@lem1216753 A (term483 A l l1 x) (term454 A y l x)). Qed.
Lemma lem1216755 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term510 A l l1 x l2) = (term481 A l l1 x l2).
Proof. exact (eq_refl (term510 A l l1 x l2)). Qed.
Lemma lem1216756 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term511 A l l1 x) = (term483 A l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216755 A l l1 x l2)). Qed.
Lemma lem1216757 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216758 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term512 A l l1 x) = (term484 A l l1 x).
Proof. exact (MK_COMB (@lem1216757 A) (@lem1216756 A l l1 x)). Qed.
Lemma lem1216759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216760 {A : Type'} (l : list A) (l1 : list A) (x : A) : (term513 A l l1 x) = (term502 A l l1 x).
Proof. exact (MK_COMB (@lem1216759) (@lem1216758 A l l1 x)). Qed.
Lemma lem1216761 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1216762 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term508 A l1 y l x) = (term504 A l1 y l x).
Proof. exact (MK_COMB (@lem1216760 A l l1 x) (@lem1216761 A y l x)). Qed.
Lemma lem1216763 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216764 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term514 A l1 y l x) = (term515 A l1 y l x).
Proof. exact (MK_COMB (@lem1216763) (@lem1216762 A l1 y l x)). Qed.
Lemma lem1216765 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term510 A l l1 x l2) = (term481 A l l1 x l2).
Proof. exact (eq_refl (term510 A l l1 x l2)). Qed.
Lemma lem1216766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216767 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term516 A l l1 x l2) = (term517 A l l1 x l2).
Proof. exact (MK_COMB (@lem1216766) (@lem1216765 A l l1 x l2)). Qed.
Lemma lem1216768 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (eq_refl (term454 A y l x)). Qed.
Lemma lem1216769 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) : (term518 A l1 l2 y l x) = (term519 A l1 l2 y l x).
Proof. exact (MK_COMB (@lem1216767 A l l1 x l2) (@lem1216768 A y l x)). Qed.
Lemma lem1216770 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term520 A l1 y l x) = (term521 A l1 y l x).
Proof. exact (fun_ext (fun l2 : list A => @lem1216769 A l1 l2 y l x)). Qed.
Lemma lem1216771 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216772 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term509 A l1 y l x) = (term522 A l1 y l x).
Proof. exact (MK_COMB (@lem1216771 A) (@lem1216770 A l1 y l x)). Qed.
Lemma lem1216773 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : ((term508 A l1 y l x) = (term509 A l1 y l x)) = ((term504 A l1 y l x) = (term522 A l1 y l x)).
Proof. exact (MK_COMB (@lem1216764 A l1 y l x) (@lem1216772 A l1 y l x)). Qed.
Lemma lem1216774 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) : (term504 A l1 y l x) = (term522 A l1 y l x).
Proof. exact (EQ_MP (@lem1216773 A l1 y l x) (@lem1216754 A l1 y l x)). Qed.
Lemma lem1216775 {A : Type'} (y : A) (l : list A) (x : A) : (term506 A y l x) = (term523 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1216774 A l1 y l x)). Qed.
Lemma lem1216776 {A : Type'} : (@ex (list A)) = (@ex (list A)).
Proof. exact (eq_refl (@ex (list A))). Qed.
Lemma lem1216777 {A : Type'} (y : A) (l : list A) (x : A) : (term507 A y l x) = (term524 A y l x).
Proof. exact (MK_COMB (@lem1216776 A) (@lem1216775 A y l x)). Qed.
Lemma lem1216778 {A : Type'} (y : A) (l : list A) (x : A) : (term488 A y l x) = (term524 A y l x).
Proof. exact (TRANS (@lem1216750 A y l x) (@lem1216777 A y l x)). Qed.
Lemma lem1216780 {A : Type'} (y : A) (l : list A) (x : A) : (term459 A y l x) = (term524 A y l x).
Proof. exact (TRANS (@lem1216726 A y l x) (@lem1216778 A y l x)). Qed.
Lemma lem1216781 {A : Type'} (y : A) (l : list A) (x : A) : (term218 A y l x) = (term524 A y l x).
Proof. exact (TRANS (@lem1216547 A y l x) (@lem1216780 A y l x)). Qed.
Lemma lem1216782 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term218 A y l x) : term524 A y l x.
Proof. exact (EQ_MP (@lem1216781 A y l x) (@lem1216476 A y l x h1)). Qed.
Lemma lem1216783 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1216784 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1216783 A l)). Qed.
Lemma lem1216785 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216786 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1216785 A) (@lem1216784 A)). Qed.
Lemma lem1216787 {A : Type'} (h : A) (t : list A) (l : list A) : ((term418 A h t l) = (term419 A h t l)) = ((term418 A h t l) = (term419 A h t l)).
Proof. exact (eq_refl ((term418 A h t l) = (term419 A h t l))). Qed.
Lemma lem1216788 {A : Type'} (h : A) (t : list A) : (term420 A h t) = (term420 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1216787 A h t l)). Qed.
Lemma lem1216789 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216790 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term421 A h t).
Proof. exact (MK_COMB (@lem1216789 A) (@lem1216788 A h t)). Qed.
Lemma lem1216791 {A : Type'} (h : A) : (term422 A h) = (term422 A h).
Proof. exact (fun_ext (fun t : list A => @lem1216790 A h t)). Qed.
Lemma lem1216792 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216793 {A : Type'} (h : A) : (term423 A h) = (term423 A h).
Proof. exact (MK_COMB (@lem1216792 A) (@lem1216791 A h)). Qed.
Lemma lem1216794 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun h : A => @lem1216793 A h)). Qed.
Lemma lem1216795 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216796 {A : Type'} : (term425 A) = (term425 A).
Proof. exact (MK_COMB (@lem1216795 A) (@lem1216794 A)). Qed.
Lemma lem1216797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216798 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (MK_COMB (@lem1216797) (@lem1216786 A)). Qed.
Lemma lem1216819 {A : Type'} : (term170 A) = (term170 A).
Proof. exact (MK_COMB (@lem1216798 A) (@lem1216796 A)). Qed.
Lemma lem1216820 {A : Type'} (h1 : term170 A) : term170 A.
Proof. exact (EQ_MP (@lem1216819 A) (@lem1216477 A h1)). Qed.
Lemma lem1216859 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1216860 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1216859 A x)). Qed.
Lemma lem1216861 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216862 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1216861 A) (@lem1216860 A)). Qed.
Lemma lem1216873 {A : Type'} (h : A) (x : A) (t : list A) : (term525 A h x t) = (term526 A h x t).
Proof. exact (@lem17160 (x = h) (@List.In A x t)). Qed.
Lemma lem1216879 {A : Type'} (h : A) (x : A) (t : list A) : (term527 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term527 A h x t)). Qed.
Lemma lem1216881 {A : Type'} (x : A) (h : A) (t : list A) : (term528 A x h t) = (term528 A x h t).
Proof. exact (eq_refl (term528 A x h t)). Qed.
Lemma lem1216882 {A : Type'} (h : A) (x : A) (t : list A) : (term529 A h x t) = (term530 A h x t).
Proof. exact (MK_COMB (@lem1216881 A x h t) (@lem1216873 A h x t)). Qed.
Lemma lem1216883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216884 {A : Type'} (h : A) (x : A) (t : list A) : (term531 A h x t) = (term532 A h x t).
Proof. exact (MK_COMB (@lem1216883) (@lem1216882 A h x t)). Qed.
Lemma lem1216885 {A : Type'} (h : A) (x : A) (t : list A) : (term533 A h x t) = (term534 A h x t).
Proof. exact (MK_COMB (@lem1216884 A h x t) (@lem1216879 A h x t)). Qed.
Lemma lem1216886 {A : Type'} (h : A) (x : A) (t : list A) : ((term106 A x h t) = (term107 A h x t)) = (term533 A h x t).
Proof. exact (@lem17784 (term106 A x h t) (term107 A h x t)). Qed.
Lemma lem1216887 {A : Type'} (h : A) (x : A) (t : list A) : ((term106 A x h t) = (term107 A h x t)) = (term534 A h x t).
Proof. exact (TRANS (@lem1216886 A h x t) (@lem1216885 A h x t)). Qed.
Lemma lem1216888 {A : Type'} (h : A) (x : A) : (term228 A h x) = (term535 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1216887 A h x t)). Qed.
Lemma lem1216889 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216890 {A : Type'} (h : A) (x : A) : (term246 A h x) = (term536 A h x).
Proof. exact (MK_COMB (@lem1216889 A) (@lem1216888 A h x)). Qed.
Lemma lem1216891 {A : Type'} (h : A) : (term257 A h) = (term537 A h).
Proof. exact (fun_ext (fun x : A => @lem1216890 A h x)). Qed.
Lemma lem1216892 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216893 {A : Type'} (h : A) : (term272 A h) = (term538 A h).
Proof. exact (MK_COMB (@lem1216892 A) (@lem1216891 A h)). Qed.
Lemma lem1216894 {A : Type'} : (term280 A) = (term539 A).
Proof. exact (fun_ext (fun h : A => @lem1216893 A h)). Qed.
Lemma lem1216895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1216896 {A : Type'} : (term295 A) = (term540 A).
Proof. exact (MK_COMB (@lem1216895 A) (@lem1216894 A)). Qed.
Lemma lem1216897 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216898 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (MK_COMB (@lem1216897) (@lem1216862 A)). Qed.
Lemma lem1216899 {A : Type'} : (term297 A) = (term541 A).
Proof. exact (MK_COMB (@lem1216898 A) (@lem1216896 A)). Qed.
Lemma lem1216913 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1216914 {A : Type'} (P : type1143 A) (Q : type1143 A) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem1216913 (list A) P Q). Qed.
Lemma lem1216915 {A : Type'} (h : A) (x : A) : (term542 A h x) = (term543 A h x).
Proof. exact (@lem1216914 A (term544 A h x) (term545 A h x)). Qed.
Lemma lem1216916 {A : Type'} (h : A) (x : A) (t : list A) : (term546 A h x t) = (term530 A h x t).
Proof. exact (eq_refl (term546 A h x t)). Qed.
Lemma lem1216917 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216918 {A : Type'} (h : A) (x : A) (t : list A) : (term547 A h x t) = (term532 A h x t).
Proof. exact (MK_COMB (@lem1216917) (@lem1216916 A h x t)). Qed.
Lemma lem1216919 {A : Type'} (h : A) (x : A) (t : list A) : (term548 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term548 A h x t)). Qed.
Lemma lem1216920 {A : Type'} (h : A) (x : A) (t : list A) : (term549 A h x t) = (term534 A h x t).
Proof. exact (MK_COMB (@lem1216918 A h x t) (@lem1216919 A h x t)). Qed.
Lemma lem1216921 {A : Type'} (h : A) (x : A) : (term550 A h x) = (term535 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1216920 A h x t)). Qed.
Lemma lem1216922 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216923 {A : Type'} (h : A) (x : A) : (term542 A h x) = (term536 A h x).
Proof. exact (MK_COMB (@lem1216922 A) (@lem1216921 A h x)). Qed.
Lemma lem1216924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1216925 {A : Type'} (h : A) (x : A) : (term551 A h x) = (term552 A h x).
Proof. exact (MK_COMB (@lem1216924) (@lem1216923 A h x)). Qed.
Lemma lem1216926 {A : Type'} (h : A) (x : A) (t : list A) : (term546 A h x t) = (term530 A h x t).
Proof. exact (eq_refl (term546 A h x t)). Qed.
Lemma lem1216927 {A : Type'} (h : A) (x : A) : (term553 A h x) = (term544 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1216926 A h x t)). Qed.
Lemma lem1216928 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216929 {A : Type'} (h : A) (x : A) : (term554 A h x) = (term555 A h x).
Proof. exact (MK_COMB (@lem1216928 A) (@lem1216927 A h x)). Qed.
Lemma lem1216930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1216931 {A : Type'} (h : A) (x : A) : (term556 A h x) = (term557 A h x).
Proof. exact (MK_COMB (@lem1216930) (@lem1216929 A h x)). Qed.
Lemma lem1216932 {A : Type'} (h : A) (x : A) (t : list A) : (term548 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term548 A h x t)). Qed.
Lemma lem1216933 {A : Type'} (h : A) (x : A) : (term558 A h x) = (term545 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1216932 A h x t)). Qed.
Lemma lem1216934 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1216935 {A : Type'} (h : A) (x : A) : (term559 A h x) = (term560 A h x).
Proof. exact (MK_COMB (@lem1216934 A) (@lem1216933 A h x)). Qed.
Lemma lem1216936 {A : Type'} (h : A) (x : A) : (term543 A h x) = (term561 A h x).
Proof. exact (MK_COMB (@lem1216931 A h x) (@lem1216935 A h x)). Qed.
Lemma lem1216937 {A : Type'} (h : A) (x : A) : ((term542 A h x) = (term543 A h x)) = ((term536 A h x) = (term561 A h x)).
Proof. exact (MK_COMB (@lem1216925 A h x) (@lem1216936 A h x)). Qed.
Lemma lem1216938 {A : Type'} (h : A) (x : A) : (term536 A h x) = (term561 A h x).
Proof. exact (EQ_MP (@lem1216937 A h x) (@lem1216915 A h x)). Qed.
Lemma lem1217035 {A : Type'} (h : A) : (term537 A h) = (term562 A h).
Proof. exact (fun_ext (fun x : A => @lem1216938 A h x)). Qed.
Lemma lem1217036 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217037 {A : Type'} (h : A) : (term538 A h) = (term563 A h).
Proof. exact (MK_COMB (@lem1217036 A) (@lem1217035 A h)). Qed.
Lemma lem1217039 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1217040 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1217039 A P Q). Qed.
Lemma lem1217041 {A : Type'} (h : A) : (term564 A h) = (term565 A h).
Proof. exact (@lem1217040 A (term566 A h) (term567 A h)). Qed.
Lemma lem1217042 {A : Type'} (h : A) (x : A) : (term568 A h x) = (term555 A h x).
Proof. exact (eq_refl (term568 A h x)). Qed.
Lemma lem1217043 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1217044 {A : Type'} (h : A) (x : A) : (term569 A h x) = (term557 A h x).
Proof. exact (MK_COMB (@lem1217043) (@lem1217042 A h x)). Qed.
Lemma lem1217045 {A : Type'} (h : A) (x : A) : (term570 A h x) = (term560 A h x).
Proof. exact (eq_refl (term570 A h x)). Qed.
Lemma lem1217046 {A : Type'} (h : A) (x : A) : (term571 A h x) = (term561 A h x).
Proof. exact (MK_COMB (@lem1217044 A h x) (@lem1217045 A h x)). Qed.
Lemma lem1217047 {A : Type'} (h : A) : (term572 A h) = (term562 A h).
Proof. exact (fun_ext (fun x : A => @lem1217046 A h x)). Qed.
Lemma lem1217048 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217049 {A : Type'} (h : A) : (term564 A h) = (term563 A h).
Proof. exact (MK_COMB (@lem1217048 A) (@lem1217047 A h)). Qed.
Lemma lem1217050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1217051 {A : Type'} (h : A) : (term573 A h) = (term574 A h).
Proof. exact (MK_COMB (@lem1217050) (@lem1217049 A h)). Qed.
Lemma lem1217052 {A : Type'} (h : A) (x : A) : (term568 A h x) = (term555 A h x).
Proof. exact (eq_refl (term568 A h x)). Qed.
Lemma lem1217053 {A : Type'} (h : A) : (term575 A h) = (term566 A h).
Proof. exact (fun_ext (fun x : A => @lem1217052 A h x)). Qed.
Lemma lem1217054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217055 {A : Type'} (h : A) : (term576 A h) = (term577 A h).
Proof. exact (MK_COMB (@lem1217054 A) (@lem1217053 A h)). Qed.
Lemma lem1217056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1217057 {A : Type'} (h : A) : (term578 A h) = (term579 A h).
Proof. exact (MK_COMB (@lem1217056) (@lem1217055 A h)). Qed.
Lemma lem1217058 {A : Type'} (h : A) (x : A) : (term570 A h x) = (term560 A h x).
Proof. exact (eq_refl (term570 A h x)). Qed.
Lemma lem1217059 {A : Type'} (h : A) : (term580 A h) = (term567 A h).
Proof. exact (fun_ext (fun x : A => @lem1217058 A h x)). Qed.
Lemma lem1217060 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217061 {A : Type'} (h : A) : (term581 A h) = (term582 A h).
Proof. exact (MK_COMB (@lem1217060 A) (@lem1217059 A h)). Qed.
Lemma lem1217062 {A : Type'} (h : A) : (term565 A h) = (term583 A h).
Proof. exact (MK_COMB (@lem1217057 A h) (@lem1217061 A h)). Qed.
Lemma lem1217063 {A : Type'} (h : A) : ((term564 A h) = (term565 A h)) = ((term563 A h) = (term583 A h)).
Proof. exact (MK_COMB (@lem1217051 A h) (@lem1217062 A h)). Qed.
Lemma lem1217064 {A : Type'} (h : A) : (term563 A h) = (term583 A h).
Proof. exact (EQ_MP (@lem1217063 A h) (@lem1217041 A h)). Qed.
Lemma lem1217169 {A : Type'} (h : A) : (term538 A h) = (term583 A h).
Proof. exact (TRANS (@lem1217037 A h) (@lem1217064 A h)). Qed.
Lemma lem1217170 {A : Type'} : (term539 A) = (term584 A).
Proof. exact (fun_ext (fun h : A => @lem1217169 A h)). Qed.
Lemma lem1217171 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217172 {A : Type'} : (term540 A) = (term585 A).
Proof. exact (MK_COMB (@lem1217171 A) (@lem1217170 A)). Qed.
Lemma lem1217174 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1217175 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term221 A P Q) = (term222 A P Q).
Proof. exact (@lem1217174 A P Q). Qed.
Lemma lem1217176 {A : Type'} : (term586 A) = (term587 A).
Proof. exact (@lem1217175 A (term588 A) (term589 A)). Qed.
Lemma lem1217177 {A : Type'} (h : A) : (term590 A h) = (term577 A h).
Proof. exact (eq_refl (term590 A h)). Qed.
Lemma lem1217178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1217179 {A : Type'} (h : A) : (term591 A h) = (term579 A h).
Proof. exact (MK_COMB (@lem1217178) (@lem1217177 A h)). Qed.
Lemma lem1217180 {A : Type'} (h : A) : (term592 A h) = (term582 A h).
Proof. exact (eq_refl (term592 A h)). Qed.
Lemma lem1217181 {A : Type'} (h : A) : (term593 A h) = (term583 A h).
Proof. exact (MK_COMB (@lem1217179 A h) (@lem1217180 A h)). Qed.
Lemma lem1217182 {A : Type'} : (term594 A) = (term584 A).
Proof. exact (fun_ext (fun h : A => @lem1217181 A h)). Qed.
Lemma lem1217183 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217184 {A : Type'} : (term586 A) = (term585 A).
Proof. exact (MK_COMB (@lem1217183 A) (@lem1217182 A)). Qed.
Lemma lem1217185 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1217186 {A : Type'} : (term595 A) = (term596 A).
Proof. exact (MK_COMB (@lem1217185) (@lem1217184 A)). Qed.
Lemma lem1217187 {A : Type'} (h : A) : (term590 A h) = (term577 A h).
Proof. exact (eq_refl (term590 A h)). Qed.
Lemma lem1217188 {A : Type'} : (term597 A) = (term588 A).
Proof. exact (fun_ext (fun h : A => @lem1217187 A h)). Qed.
Lemma lem1217189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217190 {A : Type'} : (term598 A) = (term599 A).
Proof. exact (MK_COMB (@lem1217189 A) (@lem1217188 A)). Qed.
Lemma lem1217191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1217192 {A : Type'} : (term600 A) = (term601 A).
Proof. exact (MK_COMB (@lem1217191) (@lem1217190 A)). Qed.
Lemma lem1217193 {A : Type'} (h : A) : (term592 A h) = (term582 A h).
Proof. exact (eq_refl (term592 A h)). Qed.
Lemma lem1217194 {A : Type'} : (term602 A) = (term589 A).
Proof. exact (fun_ext (fun h : A => @lem1217193 A h)). Qed.
Lemma lem1217195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217196 {A : Type'} : (term603 A) = (term604 A).
Proof. exact (MK_COMB (@lem1217195 A) (@lem1217194 A)). Qed.
Lemma lem1217197 {A : Type'} : (term587 A) = (term605 A).
Proof. exact (MK_COMB (@lem1217192 A) (@lem1217196 A)). Qed.
Lemma lem1217198 {A : Type'} : ((term586 A) = (term587 A)) = ((term585 A) = (term605 A)).
Proof. exact (MK_COMB (@lem1217186 A) (@lem1217197 A)). Qed.
Lemma lem1217199 {A : Type'} : (term585 A) = (term605 A).
Proof. exact (EQ_MP (@lem1217198 A) (@lem1217176 A)). Qed.
Lemma lem1217312 {A : Type'} : (term540 A) = (term605 A).
Proof. exact (TRANS (@lem1217172 A) (@lem1217199 A)). Qed.
Lemma lem1217313 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (eq_refl (term269 A)). Qed.
Lemma lem1217316 {A : Type'} : (term541 A) = (term606 A).
Proof. exact (MK_COMB (@lem1217313 A) (@lem1217312 A)). Qed.
Lemma lem1217317 {A : Type'} : (term297 A) = (term606 A).
Proof. exact (TRANS (@lem1216899 A) (@lem1217316 A)). Qed.
Lemma lem1217318 {A : Type'} (h1 : term297 A) : term606 A.
Proof. exact (EQ_MP (@lem1217317 A) (@lem1216479 A h1)). Qed.
Lemma lem1217779 {A : Type'} (l1 : list A) (y : A) (l : list A) (x : A) (h1 : term522 A l1 y l x) : term522 A l1 y l x.
Proof. exact (h1). Qed.
Lemma lem1217780 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term519 A l1 l2 y l x.
Proof. exact (h1). Qed.
Lemma lem1217788 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1217809 {A : Type'} (h : A) (t : list A) (l : list A) : ((term418 A h t l) = (term419 A h t l)) = ((term418 A h t l) = (term419 A h t l)).
Proof. exact (eq_refl ((term418 A h t l) = (term419 A h t l))). Qed.
Lemma lem1217810 {A : Type'} (h : A) (t : list A) : (term420 A h t) = (term420 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1217809 A h t l)). Qed.
Lemma lem1217811 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1217812 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term421 A h t).
Proof. exact (MK_COMB (@lem1217811 A) (@lem1217810 A h t)). Qed.
Lemma lem1217813 {A : Type'} (h : A) : (term422 A h) = (term422 A h).
Proof. exact (fun_ext (fun t : list A => @lem1217812 A h t)). Qed.
Lemma lem1217814 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1217815 {A : Type'} (h : A) : (term423 A h) = (term423 A h).
Proof. exact (MK_COMB (@lem1217814 A) (@lem1217813 A h)). Qed.
Lemma lem1217816 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun h : A => @lem1217815 A h)). Qed.
Lemma lem1217817 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217818 {A : Type'} : (term425 A) = (term425 A).
Proof. exact (MK_COMB (@lem1217817 A) (@lem1217816 A)). Qed.
Lemma lem1217827 {A : Type'} (l : list A) : ((@List.app A (@nil A) l) = l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl ((@List.app A (@nil A) l) = l)). Qed.
Lemma lem1217828 {A : Type'} : (term426 A) = (term426 A).
Proof. exact (fun_ext (fun l : list A => @lem1217827 A l)). Qed.
Lemma lem1217829 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1217830 {A : Type'} : (term427 A) = (term427 A).
Proof. exact (MK_COMB (@lem1217829 A) (@lem1217828 A)). Qed.
Lemma lem1217831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1217832 {A : Type'} : (term428 A) = (term428 A).
Proof. exact (MK_COMB (@lem1217831) (@lem1217830 A)). Qed.
Lemma lem1217833 {A : Type'} : (term170 A) = (term170 A).
Proof. exact (MK_COMB (@lem1217832 A) (@lem1217818 A)). Qed.
Lemma lem1217834 {A : Type'} (h1 : term170 A) : term170 A.
Proof. exact (EQ_MP (@lem1217833 A) (@lem1216820 A h1)). Qed.
Lemma lem1217907 {A : Type'} (h : A) (x : A) (t : list A) : (term527 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term527 A h x t)). Qed.
Lemma lem1217908 {A : Type'} (h : A) (x : A) : (term545 A h x) = (term545 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1217907 A h x t)). Qed.
Lemma lem1217909 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1217910 {A : Type'} (h : A) (x : A) : (term560 A h x) = (term560 A h x).
Proof. exact (MK_COMB (@lem1217909 A) (@lem1217908 A h x)). Qed.
Lemma lem1217911 {A : Type'} (h : A) : (term567 A h) = (term567 A h).
Proof. exact (fun_ext (fun x : A => @lem1217910 A h x)). Qed.
Lemma lem1217912 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217913 {A : Type'} (h : A) : (term582 A h) = (term582 A h).
Proof. exact (MK_COMB (@lem1217912 A) (@lem1217911 A h)). Qed.
Lemma lem1217914 {A : Type'} : (term589 A) = (term589 A).
Proof. exact (fun_ext (fun h : A => @lem1217913 A h)). Qed.
Lemma lem1217915 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217916 {A : Type'} : (term604 A) = (term604 A).
Proof. exact (MK_COMB (@lem1217915 A) (@lem1217914 A)). Qed.
Lemma lem1217945 {A : Type'} (h : A) (x : A) (t : list A) : (term530 A h x t) = (term530 A h x t).
Proof. exact (eq_refl (term530 A h x t)). Qed.
Lemma lem1217946 {A : Type'} (h : A) (x : A) : (term544 A h x) = (term544 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1217945 A h x t)). Qed.
Lemma lem1217947 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1217948 {A : Type'} (h : A) (x : A) : (term555 A h x) = (term555 A h x).
Proof. exact (MK_COMB (@lem1217947 A) (@lem1217946 A h x)). Qed.
Lemma lem1217949 {A : Type'} (h : A) : (term566 A h) = (term566 A h).
Proof. exact (fun_ext (fun x : A => @lem1217948 A h x)). Qed.
Lemma lem1217950 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217951 {A : Type'} (h : A) : (term577 A h) = (term577 A h).
Proof. exact (MK_COMB (@lem1217950 A) (@lem1217949 A h)). Qed.
Lemma lem1217952 {A : Type'} : (term588 A) = (term588 A).
Proof. exact (fun_ext (fun h : A => @lem1217951 A h)). Qed.
Lemma lem1217953 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217954 {A : Type'} : (term599 A) = (term599 A).
Proof. exact (MK_COMB (@lem1217953 A) (@lem1217952 A)). Qed.
Lemma lem1217955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1217956 {A : Type'} : (term601 A) = (term601 A).
Proof. exact (MK_COMB (@lem1217955) (@lem1217954 A)). Qed.
Lemma lem1217957 {A : Type'} : (term605 A) = (term605 A).
Proof. exact (MK_COMB (@lem1217956 A) (@lem1217916 A)). Qed.
Lemma lem1217964 {A : Type'} (x : A) : (term248 A x) = (term248 A x).
Proof. exact (eq_refl (term248 A x)). Qed.
Lemma lem1217965 {A : Type'} : (term256 A) = (term256 A).
Proof. exact (fun_ext (fun x : A => @lem1217964 A x)). Qed.
Lemma lem1217966 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1217967 {A : Type'} : (term267 A) = (term267 A).
Proof. exact (MK_COMB (@lem1217966 A) (@lem1217965 A)). Qed.
Lemma lem1217968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1217969 {A : Type'} : (term269 A) = (term269 A).
Proof. exact (MK_COMB (@lem1217968) (@lem1217967 A)). Qed.
Lemma lem1217970 {A : Type'} : (term606 A) = (term606 A).
Proof. exact (MK_COMB (@lem1217969 A) (@lem1217957 A)). Qed.
Lemma lem1217971 {A : Type'} (h1 : term297 A) : term606 A.
Proof. exact (EQ_MP (@lem1217970 A) (@lem1217318 A h1)). Qed.
Lemma lem1218081 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term437 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term437 A y l l1 x l2)). Qed.
Lemma lem1218082 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term439 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1218081 A y l l1 x l2)). Qed.
Lemma lem1218083 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218084 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term440 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1218083 A) (@lem1218082 A y l l1 x)). Qed.
Lemma lem1218091 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1218092 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term443 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1218091 A x l1) (@lem1218084 A y l l1 x)). Qed.
Lemma lem1218093 {A : Type'} (y : A) (l : list A) (x : A) : (term450 A y l x) = (term450 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1218092 A y l l1 x)). Qed.
Lemma lem1218094 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218095 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term451 A y l x).
Proof. exact (MK_COMB (@lem1218094 A) (@lem1218093 A y l x)). Qed.
Lemma lem1218110 {A : Type'} (y : A) (x : A) (l : list A) : (term452 A y x l) = (term452 A y x l).
Proof. exact (eq_refl (term452 A y x l)). Qed.
Lemma lem1218111 {A : Type'} (y : A) (l : list A) (x : A) : (term454 A y l x) = (term454 A y l x).
Proof. exact (MK_COMB (@lem1218110 A y x l) (@lem1218095 A y l x)). Qed.
Lemma lem1218146 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term517 A l l1 x l2) = (term517 A l l1 x l2).
Proof. exact (eq_refl (term517 A l l1 x l2)). Qed.
Lemma lem1218147 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) : (term519 A l1 l2 y l x) = (term519 A l1 l2 y l x).
Proof. exact (MK_COMB (@lem1218146 A l l1 x l2) (@lem1218111 A y l x)). Qed.
Lemma lem1218148 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term519 A l1 l2 y l x.
Proof. exact (EQ_MP (@lem1218147 A l1 l2 y l x) (@lem1217780 A l1 l2 y l x h1)). Qed.
Lemma lem1218149 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term454 A y l x.
Proof. exact (proj2 (@lem1218148 A l1 l2 y l x h1)). Qed.
Lemma lem1218150 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term481 A l l1 x l2.
Proof. exact (proj1 (@lem1218148 A l1 l2 y l x h1)). Qed.
Lemma lem1218151 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term451 A y l x.
Proof. exact (proj2 (@lem1218149 A l1 l2 y l x h1)). Qed.
Lemma lem1218152 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term107 A y x l.
Proof. exact (proj1 (@lem1218149 A l1 l2 y l x h1)). Qed.
Lemma lem1218157 {A : Type'} (h1 : term297 A) : term605 A.
Proof. exact (proj2 (@lem1217971 A h1)). Qed.
Lemma lem1218159 {A : Type'} (h1 : term297 A) : term604 A.
Proof. exact (proj2 (@lem1218157 A h1)). Qed.
Lemma lem1218163 {A : Type'} (h1 : term170 A) : term425 A.
Proof. exact (proj2 (@lem1217834 A h1)). Qed.
Lemma lem1218172 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : term77 A l l1 x l2.
Proof. exact (h1). Qed.
Lemma lem1218178 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1218382 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1218390 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1218594 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1218810 {A : Type'} (x : A) (l : list A) (h1 : @List.In A x l) : @List.In A x l.
Proof. exact (h1). Qed.
Lemma lem1218814 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) : term100 A x l.
Proof. exact (h1). Qed.
Lemma lem1218818 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1218820 {A : Type'} (P : Prop) (Q : A -> Prop) : (term607 A P Q) = (term608 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem1218821 {A : Type'} (P : Prop) (Q : type1143 A) : (term609 A P Q) = (term610 A P Q).
Proof. exact (@lem1218820 (list A) P Q). Qed.
Lemma lem1218822 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term612 A y l l1 x).
Proof. exact (@lem1218821 A (@List.In A x l1) (term439 A y l l1 x)). Qed.
Lemma lem1218823 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1218824 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term614 A y l l1 x) = (term439 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1218823 A y l l1 x l2)). Qed.
Lemma lem1218825 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218826 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term615 A y l l1 x) = (term440 A y l l1 x).
Proof. exact (MK_COMB (@lem1218825 A) (@lem1218824 A y l l1 x)). Qed.
Lemma lem1218827 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1218828 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term611 A y l l1 x) = (term443 A y l l1 x).
Proof. exact (MK_COMB (@lem1218827 A x l1) (@lem1218826 A y l l1 x)). Qed.
Lemma lem1218829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1218830 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term616 A y l l1 x) = (term617 A y l l1 x).
Proof. exact (MK_COMB (@lem1218829) (@lem1218828 A y l l1 x)). Qed.
Lemma lem1218831 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term613 A y l l1 x l2) = (term437 A y l l1 x l2).
Proof. exact (eq_refl (term613 A y l l1 x l2)). Qed.
Lemma lem1218832 {A : Type'} (x : A) (l1 : list A) : (term105 A x l1) = (term105 A x l1).
Proof. exact (eq_refl (term105 A x l1)). Qed.
Lemma lem1218833 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term618 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (MK_COMB (@lem1218832 A x l1) (@lem1218831 A y l l1 x l2)). Qed.
Lemma lem1218834 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term620 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1218833 A y l l1 x l2)). Qed.
Lemma lem1218835 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218836 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term612 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1218835 A) (@lem1218834 A y l l1 x)). Qed.
Lemma lem1218837 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : ((term611 A y l l1 x) = (term612 A y l l1 x)) = ((term443 A y l l1 x) = (term622 A y l l1 x)).
Proof. exact (MK_COMB (@lem1218830 A y l l1 x) (@lem1218836 A y l l1 x)). Qed.
Lemma lem1218838 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term443 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (EQ_MP (@lem1218837 A y l l1 x) (@lem1218822 A y l l1 x)). Qed.
Lemma lem1218839 {A : Type'} (y : A) (l : list A) (x : A) : (term450 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1218838 A y l l1 x)). Qed.
Lemma lem1218840 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218841 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1218840 A) (@lem1218839 A y l x)). Qed.
Lemma lem1218848 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) (l2 : list A) : (term619 A y l l1 x l2) = (term619 A y l l1 x l2).
Proof. exact (eq_refl (term619 A y l l1 x l2)). Qed.
Lemma lem1218849 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term621 A y l l1 x) = (term621 A y l l1 x).
Proof. exact (fun_ext (fun l2 : list A => @lem1218848 A y l l1 x l2)). Qed.
Lemma lem1218850 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218851 {A : Type'} (y : A) (l : list A) (l1 : list A) (x : A) : (term622 A y l l1 x) = (term622 A y l l1 x).
Proof. exact (MK_COMB (@lem1218850 A) (@lem1218849 A y l l1 x)). Qed.
Lemma lem1218852 {A : Type'} (y : A) (l : list A) (x : A) : (term623 A y l x) = (term623 A y l x).
Proof. exact (fun_ext (fun l1 : list A => @lem1218851 A y l l1 x)). Qed.
Lemma lem1218853 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218854 {A : Type'} (y : A) (l : list A) (x : A) : (term624 A y l x) = (term624 A y l x).
Proof. exact (MK_COMB (@lem1218853 A) (@lem1218852 A y l x)). Qed.
Lemma lem1218855 {A : Type'} (y : A) (l : list A) (x : A) : (term451 A y l x) = (term624 A y l x).
Proof. exact (TRANS (@lem1218841 A y l x) (@lem1218854 A y l x)). Qed.
Lemma lem1218856 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term624 A y l x.
Proof. exact (EQ_MP (@lem1218855 A y l x) (@lem1218151 A l1 l2 y l x h1)). Qed.
Lemma lem1218967 {A : Type'} (h : A) (x : A) (t : list A) : (term527 A h x t) = (term527 A h x t).
Proof. exact (eq_refl (term527 A h x t)). Qed.
Lemma lem1218968 {A : Type'} (h : A) (x : A) : (term545 A h x) = (term545 A h x).
Proof. exact (fun_ext (fun t : list A => @lem1218967 A h x t)). Qed.
Lemma lem1218969 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1218970 {A : Type'} (h : A) (x : A) : (term560 A h x) = (term560 A h x).
Proof. exact (MK_COMB (@lem1218969 A) (@lem1218968 A h x)). Qed.
Lemma lem1218971 {A : Type'} (h : A) : (term567 A h) = (term567 A h).
Proof. exact (fun_ext (fun x : A => @lem1218970 A h x)). Qed.
Lemma lem1218972 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1218973 {A : Type'} (h : A) : (term582 A h) = (term582 A h).
Proof. exact (MK_COMB (@lem1218972 A) (@lem1218971 A h)). Qed.
Lemma lem1218974 {A : Type'} : (term589 A) = (term589 A).
Proof. exact (fun_ext (fun h : A => @lem1218973 A h)). Qed.
Lemma lem1218975 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1218977 {A : Type'} : (term604 A) = (term604 A).
Proof. exact (MK_COMB (@lem1218975 A) (@lem1218974 A)). Qed.
Lemma lem1218978 {A : Type'} (h1 : term297 A) : term604 A.
Proof. exact (EQ_MP (@lem1218977 A) (@lem1218159 A h1)). Qed.
Lemma lem1219007 {A : Type'} (h : A) (t : list A) (l : list A) : ((term418 A h t l) = (term419 A h t l)) = ((term418 A h t l) = (term419 A h t l)).
Proof. exact (eq_refl ((term418 A h t l) = (term419 A h t l))). Qed.
Lemma lem1219008 {A : Type'} (h : A) (t : list A) : (term420 A h t) = (term420 A h t).
Proof. exact (fun_ext (fun l : list A => @lem1219007 A h t l)). Qed.
Lemma lem1219009 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1219010 {A : Type'} (h : A) (t : list A) : (term421 A h t) = (term421 A h t).
Proof. exact (MK_COMB (@lem1219009 A) (@lem1219008 A h t)). Qed.
Lemma lem1219011 {A : Type'} (h : A) : (term422 A h) = (term422 A h).
Proof. exact (fun_ext (fun t : list A => @lem1219010 A h t)). Qed.
Lemma lem1219012 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1219013 {A : Type'} (h : A) : (term423 A h) = (term423 A h).
Proof. exact (MK_COMB (@lem1219012 A) (@lem1219011 A h)). Qed.
Lemma lem1219014 {A : Type'} : (term424 A) = (term424 A).
Proof. exact (fun_ext (fun h : A => @lem1219013 A h)). Qed.
Lemma lem1219015 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1219017 {A : Type'} : (term425 A) = (term425 A).
Proof. exact (MK_COMB (@lem1219015 A) (@lem1219014 A)). Qed.
Lemma lem1219018 {A : Type'} (h1 : term170 A) : term425 A.
Proof. exact (EQ_MP (@lem1219017 A) (@lem1218163 A h1)). Qed.
Lemma lem1219247 {A : Type'} (_22124 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term625 A y l x _22124.
Proof. exact (@lem1218856 A l1 l2 y l x h1 _22124). Qed.
Lemma lem1219248 {A : Type'} (y : A) (l : list A) (_22124 : list A) (x : A) : (term625 A y l x _22124) = (term622 A y l _22124 x).
Proof. exact (eq_refl (term625 A y l x _22124)). Qed.
Lemma lem1219249 {A : Type'} (_22124 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term622 A y l _22124 x.
Proof. exact (EQ_MP (@lem1219248 A y l _22124 x) (@lem1219247 A _22124 l1 l2 y l x h1)). Qed.
Lemma lem1219250 {A : Type'} (_22124 : list A) (_22125 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term626 A y l _22124 x _22125.
Proof. exact (@lem1219249 A _22124 l1 l2 y l x h1 _22125). Qed.
Lemma lem1219251 {A : Type'} (y : A) (l : list A) (_22124 : list A) (x : A) (_22125 : list A) : (term626 A y l _22124 x _22125) = (term619 A y l _22124 x _22125).
Proof. exact (eq_refl (term626 A y l _22124 x _22125)). Qed.
Lemma lem1219286 {A : Type'} (_22137 : A) (h1 : term297 A) : term592 A _22137.
Proof. exact (@lem1218978 A h1 _22137). Qed.
Lemma lem1219287 {A : Type'} (_22137 : A) : (term592 A _22137) = (term582 A _22137).
Proof. exact (eq_refl (term592 A _22137)). Qed.
Lemma lem1219288 {A : Type'} (_22137 : A) (h1 : term297 A) : term582 A _22137.
Proof. exact (EQ_MP (@lem1219287 A _22137) (@lem1219286 A _22137 h1)). Qed.
Lemma lem1219289 {A : Type'} (_22137 : A) (_22138 : A) (h1 : term297 A) : term570 A _22137 _22138.
Proof. exact (@lem1219288 A _22137 h1 _22138). Qed.
Lemma lem1219290 {A : Type'} (_22137 : A) (_22138 : A) : (term570 A _22137 _22138) = (term560 A _22137 _22138).
Proof. exact (eq_refl (term570 A _22137 _22138)). Qed.
Lemma lem1219291 {A : Type'} (_22137 : A) (_22138 : A) (h1 : term297 A) : term560 A _22137 _22138.
Proof. exact (EQ_MP (@lem1219290 A _22137 _22138) (@lem1219289 A _22137 _22138 h1)). Qed.
Lemma lem1219292 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) (h1 : term297 A) : term548 A _22137 _22138 _22139.
Proof. exact (@lem1219291 A _22137 _22138 h1 _22139). Qed.
Lemma lem1219293 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) : (term548 A _22137 _22138 _22139) = (term527 A _22137 _22138 _22139).
Proof. exact (eq_refl (term548 A _22137 _22138 _22139)). Qed.
Lemma lem1219310 {A : Type'} (_22145 : A) (h1 : term170 A) : term739 A _22145.
Proof. exact (@lem1219018 A h1 _22145). Qed.
Lemma lem1219311 {A : Type'} (_22145 : A) : (term739 A _22145) = (term423 A _22145).
Proof. exact (eq_refl (term739 A _22145)). Qed.
Lemma lem1219312 {A : Type'} (_22145 : A) (h1 : term170 A) : term423 A _22145.
Proof. exact (EQ_MP (@lem1219311 A _22145) (@lem1219310 A _22145 h1)). Qed.
Lemma lem1219313 {A : Type'} (_22145 : A) (_22146 : list A) (h1 : term170 A) : term740 A _22145 _22146.
Proof. exact (@lem1219312 A _22145 h1 _22146). Qed.
Lemma lem1219314 {A : Type'} (_22145 : A) (_22146 : list A) : (term740 A _22145 _22146) = (term421 A _22145 _22146).
Proof. exact (eq_refl (term740 A _22145 _22146)). Qed.
Lemma lem1219315 {A : Type'} (_22145 : A) (_22146 : list A) (h1 : term170 A) : term421 A _22145 _22146.
Proof. exact (EQ_MP (@lem1219314 A _22145 _22146) (@lem1219313 A _22145 _22146 h1)). Qed.
Lemma lem1219316 {A : Type'} (_22145 : A) (_22146 : list A) (_22147 : list A) (h1 : term170 A) : term741 A _22145 _22146 _22147.
Proof. exact (@lem1219315 A _22145 _22146 h1 _22147). Qed.
Lemma lem1219317 {A : Type'} (_22145 : A) (_22146 : list A) (_22147 : list A) : (term741 A _22145 _22146 _22147) = ((term418 A _22145 _22146 _22147) = (term419 A _22145 _22146 _22147)).
Proof. exact (eq_refl (term741 A _22145 _22146 _22147)). Qed.
Lemma lem1219336 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1219376 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1219404 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1219444 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1219514 {A : Type'} (x : A) (l : list A) (h1 : @List.In A x l) : @List.In A x l.
Proof. exact (h1). Qed.
Lemma lem1219516 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) : term100 A x l.
Proof. exact (h1). Qed.
Lemma lem1219542 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1219548 {A : Type'} (_22124 : list A) (_22125 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term519 A l1 l2 y l x) : term619 A y l _22124 x _22125.
Proof. exact (EQ_MP (@lem1219251 A y l _22124 x _22125) (@lem1219250 A _22124 _22125 l1 l2 y l x h1)). Qed.
Lemma lem1219586 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : l = (term102 A l1 x l2).
Proof. exact (proj2 (@lem1218172 A l l1 x l2 h1)). Qed.
Lemma lem1219625 {A : Type'} (y : A) : (term742 A y) = (term742 A y).
Proof. exact (eq_refl (term742 A y)). Qed.
Lemma lem1219626 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term743 A y x) = (term744 A y).
Proof. exact (MK_COMB (@lem1219625 A y) (@lem1219376 A x y h1)). Qed.
Lemma lem1219627 {A : Type'} (y : A) : (term744 A y) = (term745 A y).
Proof. exact (eq_refl (term744 A y)). Qed.
Lemma lem1219628 {A : Type'} (y : A) (x : A) : (term746 A y x) = (term746 A y x).
Proof. exact (eq_refl (term746 A y x)). Qed.
Lemma lem1219629 {A : Type'} (x : A) (y : A) : ((term743 A y x) = (term744 A y)) = ((term743 A y x) = (term745 A y)).
Proof. exact (MK_COMB (@lem1219628 A y x) (@lem1219627 A y)). Qed.
Lemma lem1219630 {A : Type'} (x : A) (y : A) : (term743 A y x) = (term5 A x y).
Proof. exact (eq_refl (term743 A y x)). Qed.
Lemma lem1219631 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1219632 {A : Type'} (x : A) (y : A) : (term746 A y x) = (term747 A x y).
Proof. exact (MK_COMB (@lem1219631) (@lem1219630 A x y)). Qed.
Lemma lem1219633 {A : Type'} (y : A) : (term745 A y) = (term745 A y).
Proof. exact (eq_refl (term745 A y)). Qed.
Lemma lem1219634 {A : Type'} (x : A) (y : A) : ((term743 A y x) = (term745 A y)) = ((term5 A x y) = (term745 A y)).
Proof. exact (MK_COMB (@lem1219632 A x y) (@lem1219633 A y)). Qed.
Lemma lem1219635 {A : Type'} (x : A) (y : A) : ((term743 A y x) = (term744 A y)) = ((term5 A x y) = (term745 A y)).
Proof. exact (TRANS (@lem1219629 A x y) (@lem1219634 A x y)). Qed.
Lemma lem1219636 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term5 A x y) = (term745 A y).
Proof. exact (EQ_MP (@lem1219635 A x y) (@lem1219626 A x y h1)). Qed.
Lemma lem1219637 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : term745 A y.
Proof. exact (EQ_MP (@lem1219636 A x y h2) (@lem1219336 A x y h1)). Qed.
Lemma lem1219859 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1219998 {A : Type'} (x : A) (y : A) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1220083 {A : Type'} (y : A) : (term742 A y) = (term742 A y).
Proof. exact (eq_refl (term742 A y)). Qed.
Lemma lem1220084 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term743 A y x) = (term744 A y).
Proof. exact (MK_COMB (@lem1220083 A y) (@lem1219998 A x y h1)). Qed.
Lemma lem1220085 {A : Type'} (y : A) : (term744 A y) = (term745 A y).
Proof. exact (eq_refl (term744 A y)). Qed.
Lemma lem1220086 {A : Type'} (y : A) (x : A) : (term746 A y x) = (term746 A y x).
Proof. exact (eq_refl (term746 A y x)). Qed.
Lemma lem1220087 {A : Type'} (x : A) (y : A) : ((term743 A y x) = (term744 A y)) = ((term743 A y x) = (term745 A y)).
Proof. exact (MK_COMB (@lem1220086 A y x) (@lem1220085 A y)). Qed.
Lemma lem1220088 {A : Type'} (x : A) (y : A) : (term743 A y x) = (term5 A x y).
Proof. exact (eq_refl (term743 A y x)). Qed.
Lemma lem1220089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1220090 {A : Type'} (x : A) (y : A) : (term746 A y x) = (term747 A x y).
Proof. exact (MK_COMB (@lem1220089) (@lem1220088 A x y)). Qed.
Lemma lem1220091 {A : Type'} (y : A) : (term745 A y) = (term745 A y).
Proof. exact (eq_refl (term745 A y)). Qed.
Lemma lem1220092 {A : Type'} (x : A) (y : A) : ((term743 A y x) = (term745 A y)) = ((term5 A x y) = (term745 A y)).
Proof. exact (MK_COMB (@lem1220090 A x y) (@lem1220091 A y)). Qed.
Lemma lem1220093 {A : Type'} (x : A) (y : A) : ((term743 A y x) = (term744 A y)) = ((term5 A x y) = (term745 A y)).
Proof. exact (TRANS (@lem1220087 A x y) (@lem1220092 A x y)). Qed.
Lemma lem1220094 {A : Type'} (x : A) (y : A) (h1 : x = y) : (term5 A x y) = (term745 A y).
Proof. exact (EQ_MP (@lem1220093 A x y) (@lem1220084 A x y h1)). Qed.
Lemma lem1220095 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : term745 A y.
Proof. exact (EQ_MP (@lem1220094 A x y h2) (@lem1219859 A x y h1)). Qed.
Lemma lem1220317 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1220318 {A : Type'} (y : A) (_22124 : list A) (x : A) (_22125 : list A) : (term634 A y _22124 x _22125) = (term634 A y _22124 x _22125).
Proof. exact (eq_refl (term634 A y _22124 x _22125)). Qed.
Lemma lem1220319 {A : Type'} (y : A) (_22124 : list A) (_22125 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term635 A y _22124 x _22125 l) = (term636 A y _22124 _22125 l1 x l2).
Proof. exact (MK_COMB (@lem1220318 A y _22124 x _22125) (@lem1219586 A l l1 x l2 h1)). Qed.
Lemma lem1220320 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_22124 : list A) (x : A) (_22125 : list A) : (term636 A y _22124 _22125 l1 x l2) = (term637 A y l1 l2 _22124 x _22125).
Proof. exact (eq_refl (term636 A y _22124 _22125 l1 x l2)). Qed.
Lemma lem1220321 {A : Type'} (y : A) (_22124 : list A) (x : A) (_22125 : list A) (l : list A) : (term638 A y _22124 x _22125 l) = (term638 A y _22124 x _22125 l).
Proof. exact (eq_refl (term638 A y _22124 x _22125 l)). Qed.
Lemma lem1220322 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_22124 : list A) (x : A) (_22125 : list A) : ((term635 A y _22124 x _22125 l) = (term636 A y _22124 _22125 l1 x l2)) = ((term635 A y _22124 x _22125 l) = (term637 A y l1 l2 _22124 x _22125)).
Proof. exact (MK_COMB (@lem1220321 A y _22124 x _22125 l) (@lem1220320 A y l1 l2 _22124 x _22125)). Qed.
Lemma lem1220323 {A : Type'} (y : A) (l : list A) (_22124 : list A) (x : A) (_22125 : list A) : (term635 A y _22124 x _22125 l) = (term619 A y l _22124 x _22125).
Proof. exact (eq_refl (term635 A y _22124 x _22125 l)). Qed.
Lemma lem1220324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1220325 {A : Type'} (y : A) (l : list A) (_22124 : list A) (x : A) (_22125 : list A) : (term638 A y _22124 x _22125 l) = (term633 A y l _22124 x _22125).
Proof. exact (MK_COMB (@lem1220324) (@lem1220323 A y l _22124 x _22125)). Qed.
Lemma lem1220326 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_22124 : list A) (x : A) (_22125 : list A) : (term637 A y l1 l2 _22124 x _22125) = (term637 A y l1 l2 _22124 x _22125).
Proof. exact (eq_refl (term637 A y l1 l2 _22124 x _22125)). Qed.
Lemma lem1220327 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_22124 : list A) (x : A) (_22125 : list A) : ((term635 A y _22124 x _22125 l) = (term637 A y l1 l2 _22124 x _22125)) = ((term619 A y l _22124 x _22125) = (term637 A y l1 l2 _22124 x _22125)).
Proof. exact (MK_COMB (@lem1220325 A y l _22124 x _22125) (@lem1220326 A y l1 l2 _22124 x _22125)). Qed.
Lemma lem1220328 {A : Type'} (l : list A) (y : A) (l1 : list A) (l2 : list A) (_22124 : list A) (x : A) (_22125 : list A) : ((term635 A y _22124 x _22125 l) = (term636 A y _22124 _22125 l1 x l2)) = ((term619 A y l _22124 x _22125) = (term637 A y l1 l2 _22124 x _22125)).
Proof. exact (TRANS (@lem1220322 A l y l1 l2 _22124 x _22125) (@lem1220327 A l y l1 l2 _22124 x _22125)). Qed.
Lemma lem1220329 {A : Type'} (y : A) (_22124 : list A) (_22125 : list A) (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : (term619 A y l _22124 x _22125) = (term637 A y l1 l2 _22124 x _22125).
Proof. exact (EQ_MP (@lem1220328 A l y l1 l2 _22124 x _22125) (@lem1220319 A y _22124 _22125 l l1 x l2 h1)). Qed.
Lemma lem1220330 {A : Type'} (_22124 : list A) (_22125 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) : term637 A y l1 l2 _22124 x _22125.
Proof. exact (EQ_MP (@lem1220329 A y _22124 _22125 l l1 x l2 h1) (@lem1219548 A _22124 _22125 l1 l2 y l x h2)). Qed.
Lemma lem1220386 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) (h1 : term297 A) : term527 A _22137 _22138 _22139.
Proof. exact (EQ_MP (@lem1219293 A _22137 _22138 _22139) (@lem1219292 A _22137 _22138 _22139 h1)). Qed.
Lemma lem1220469 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : term100 A x l1.
Proof. exact (proj1 (@lem1218172 A l l1 x l2 h1)). Qed.
Lemma lem1220631 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1220632 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1220631 A x). Qed.
Lemma lem1220633 {A : Type'} (y : A) : y = y.
Proof. exact (@lem1220632 A y). Qed.
Lemma lem1220634 {A : Type'} (y : A) : term748 A y.
Proof. exact (fun h0 : term745 A y => @lem1220633 A y). Qed.
Lemma lem1220636 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1220637 {A : Type'} (y : A) : (term748 A y) = (y = y).
Proof. exact (@lem1220636 (y = y)). Qed.
Lemma lem1220638 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem1220637 A y) (@lem1220634 A y)). Qed.
Lemma lem1220641 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1220643 {A : Type'} (y : A) : (term745 A y) = (term749 A y).
Proof. exact (@lem1220641 (y = y)). Qed.
Lemma lem1220646 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : term749 A y.
Proof. exact (EQ_MP (@lem1220643 A y) (@lem1219637 A x y h1 h2)). Qed.
Lemma lem1220649 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (@lem1220646 A x y h1 h2 (@lem1220638 A y)). Qed.
Lemma lem1220650 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : term697.
Proof. exact (fun h0 : ~ False => @lem1220649 A x y h1 h2). Qed.
Lemma lem1220652 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1220653 : term697 = False.
Proof. exact (@lem1220652 False). Qed.
Lemma lem1220760 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1220761 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1220760 A x). Qed.
Lemma lem1220762 {A : Type'} (y : A) : y = y.
Proof. exact (@lem1220761 A y). Qed.
Lemma lem1220763 {A : Type'} (y : A) : term748 A y.
Proof. exact (fun h0 : term745 A y => @lem1220762 A y). Qed.
Lemma lem1220765 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1220766 {A : Type'} (y : A) : (term748 A y) = (y = y).
Proof. exact (@lem1220765 (y = y)). Qed.
Lemma lem1220767 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem1220766 A y) (@lem1220763 A y)). Qed.
Lemma lem1220770 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1220772 {A : Type'} (y : A) : (term745 A y) = (term749 A y).
Proof. exact (@lem1220770 (y = y)). Qed.
Lemma lem1220775 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : term749 A y.
Proof. exact (EQ_MP (@lem1220772 A y) (@lem1220095 A x y h1 h2)). Qed.
Lemma lem1220778 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (@lem1220775 A x y h1 h2 (@lem1220767 A y)). Qed.
Lemma lem1220779 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : term697.
Proof. exact (fun h0 : ~ False => @lem1220778 A x y h1 h2). Qed.
Lemma lem1220781 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1220782 : term697 = False.
Proof. exact (@lem1220781 False). Qed.
Lemma lem1220889 {A : Type'} (x : A) (l : list A) (h1 : @List.In A x l) : @List.In A x l.
Proof. exact (h1). Qed.
Lemma lem1220890 {A : Type'} (x : A) (l : list A) (h1 : @List.In A x l) : term715 A x l.
Proof. exact (fun h0 : term100 A x l => @lem1220889 A x l h1). Qed.
Lemma lem1220892 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1220893 {A : Type'} (x : A) (l : list A) : (term715 A x l) = (@List.In A x l).
Proof. exact (@lem1220892 (@List.In A x l)). Qed.
Lemma lem1220894 {A : Type'} (x : A) (l : list A) (h1 : @List.In A x l) : @List.In A x l.
Proof. exact (EQ_MP (@lem1220893 A x l) (@lem1220890 A x l h1)). Qed.
Lemma lem1220897 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1220899 {A : Type'} (x : A) (l : list A) : (term100 A x l) = (term716 A x l).
Proof. exact (@lem1220897 (@List.In A x l)). Qed.
Lemma lem1220902 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) : term716 A x l.
Proof. exact (EQ_MP (@lem1220899 A x l) (@lem1219516 A x l h1)). Qed.
Lemma lem1220905 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (@lem1220902 A x l h1 (@lem1220894 A x l h2)). Qed.
Lemma lem1220906 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : term697.
Proof. exact (fun h0 : ~ False => @lem1220905 A x l h1 h2). Qed.
Lemma lem1220908 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1220909 : term697 = False.
Proof. exact (@lem1220908 False). Qed.
Lemma lem1220910 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1220909) (@lem1220906 A x l h1 h2)). Qed.
Lemma lem1221010 {A : Type'} (x : list A) (y : list A) (z : list A) : term653 A x y z.
Proof. exact (@lem21385 (list A) x y z). Qed.
Lemma lem1221016 {A : Type'} (_22145 : A) (_22146 : list A) (_22147 : list A) (h1 : term170 A) : (term418 A _22145 _22146 _22147) = (term419 A _22145 _22146 _22147).
Proof. exact (EQ_MP (@lem1219317 A _22145 _22146 _22147) (@lem1219316 A _22145 _22146 _22147 h1)). Qed.
Lemma lem1221017 {A : Type'} (_22145 : A) (_22146 : list A) (_22147 : list A) (h1 : term170 A) : (term418 A _22145 _22146 _22147) = (term419 A _22145 _22146 _22147).
Proof. exact (@lem1221016 A _22145 _22146 _22147 h1). Qed.
Lemma lem1221018 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : (term750 A y l1 x l2) = (term751 A y l1 x l2).
Proof. exact (@lem1221017 A y l1 (@cons A x l2) h1). Qed.
Lemma lem1221019 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : term752 A y l1 x l2.
Proof. exact (fun h0 : term753 A y l1 x l2 => @lem1221018 A y l1 x l2 h1). Qed.
Lemma lem1221021 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1221022 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) : (term752 A y l1 x l2) = ((term750 A y l1 x l2) = (term751 A y l1 x l2)).
Proof. exact (@lem1221021 ((term750 A y l1 x l2) = (term751 A y l1 x l2))). Qed.
Lemma lem1221023 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : (term750 A y l1 x l2) = (term751 A y l1 x l2).
Proof. exact (EQ_MP (@lem1221022 A y l1 x l2) (@lem1221019 A y l1 x l2 h1)). Qed.
Lemma lem1221025 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem21386 (list A) x). Qed.
Lemma lem1221026 {A : Type'} (x : list A) : x = x.
Proof. exact (@lem1221025 A x). Qed.
Lemma lem1221027 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) : (term750 A y l1 x l2) = (term750 A y l1 x l2).
Proof. exact (@lem1221026 A (term750 A y l1 x l2)). Qed.
Lemma lem1221028 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) : term754 A y l1 x l2.
Proof. exact (fun h0 : term755 A y l1 x l2 => @lem1221027 A y l1 x l2). Qed.
Lemma lem1221030 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1221031 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) : (term754 A y l1 x l2) = ((term750 A y l1 x l2) = (term750 A y l1 x l2)).
Proof. exact (@lem1221030 ((term750 A y l1 x l2) = (term750 A y l1 x l2))). Qed.
Lemma lem1221032 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) : (term750 A y l1 x l2) = (term750 A y l1 x l2).
Proof. exact (EQ_MP (@lem1221031 A y l1 x l2) (@lem1221028 A y l1 x l2)). Qed.
Lemma lem1221050 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1221051 {A : Type'} (y : list A) (x : list A) (z : list A) : (term660 A x y z) = (term661 A y x z).
Proof. exact (@lem1221050 (y = z) (term662 A x z)). Qed.
Lemma lem1221061 {A : Type'} (x : list A) (y : list A) : (term663 A x y) = (term663 A x y).
Proof. exact (eq_refl (term663 A x y)). Qed.
Lemma lem1221062 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term664 A y x z).
Proof. exact (MK_COMB (@lem1221061 A x y) (@lem1221051 A y x z)). Qed.
Lemma lem1221066 (q : Prop) (p : Prop) (r : Prop) : (term665 p q r) = (term665 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1221067 {A : Type'} (y : list A) (x : list A) (z : list A) : (term664 A y x z) = (term666 A y x z).
Proof. exact (@lem1221066 (y = z) (term662 A x y) (term662 A x z)). Qed.
Lemma lem1221089 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (TRANS (@lem1221062 A y x z) (@lem1221067 A y x z)). Qed.
Lemma lem1221090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221091 {A : Type'} (y : list A) (x : list A) (z : list A) : (term667 A x y z) = (term668 A y x z).
Proof. exact (MK_COMB (@lem1221090) (@lem1221089 A y x z)). Qed.
Lemma lem1221113 {A : Type'} (y : list A) (x : list A) (z : list A) : (term666 A y x z) = (term666 A y x z).
Proof. exact (eq_refl (term666 A y x z)). Qed.
Lemma lem1221114 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = ((term666 A y x z) = (term666 A y x z)).
Proof. exact (MK_COMB (@lem1221091 A y x z) (@lem1221113 A y x z)). Qed.
Lemma lem1221116 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1221117 (x : Prop) : (x = x) = True.
Proof. exact (@lem1221116 Prop x). Qed.
Lemma lem1221118 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term666 A y x z) = (term666 A y x z)) = True.
Proof. exact (@lem1221117 (term666 A y x z)). Qed.
Lemma lem1221119 {A : Type'} (y : list A) (x : list A) (z : list A) : ((term653 A x y z) = (term666 A y x z)) = True.
Proof. exact (TRANS (@lem1221114 A y x z) (@lem1221118 A y x z)). Qed.
Lemma lem1221120 {A : Type'} (y : list A) (x : list A) (z : list A) : True = ((term653 A x y z) = (term666 A y x z)).
Proof. exact (SYM (@lem1221119 A y x z)). Qed.
Lemma lem1221121 {A : Type'} (y : list A) (x : list A) (z : list A) : (term653 A x y z) = (term666 A y x z).
Proof. exact (EQ_MP (@lem1221120 A y x z) (@lem0)). Qed.
Lemma lem1221122 {A : Type'} (y : list A) (x : list A) (z : list A) : term666 A y x z.
Proof. exact (EQ_MP (@lem1221121 A y x z) (@lem1221010 A x y z)). Qed.
Lemma lem1221124 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1221125 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term670 A x y z).
Proof. exact (@lem1221124 (term671 A y x z) (y = z)). Qed.
Lemma lem1221127 (a : Prop) (b : Prop) : (term672 a b) = (term673 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1221128 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term675 A y x z).
Proof. exact (@lem1221127 (term662 A x y) (term662 A x z)). Qed.
Lemma lem1221130 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1221131 {A : Type'} (x : list A) (y : list A) : (term677 A x y) = (x = y).
Proof. exact (@lem1221130 (x = y)). Qed.
Lemma lem1221132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1221133 {A : Type'} (x : list A) (y : list A) : (term678 A x y) = (term679 A x y).
Proof. exact (MK_COMB (@lem1221132) (@lem1221131 A x y)). Qed.
Lemma lem1221135 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1221136 {A : Type'} (x : list A) (z : list A) : (term677 A x z) = (x = z).
Proof. exact (@lem1221135 (x = z)). Qed.
Lemma lem1221137 {A : Type'} (y : list A) (x : list A) (z : list A) : (term675 A y x z) = (term680 A y x z).
Proof. exact (MK_COMB (@lem1221133 A x y) (@lem1221136 A x z)). Qed.
Lemma lem1221138 {A : Type'} (y : list A) (x : list A) (z : list A) : (term674 A y x z) = (term680 A y x z).
Proof. exact (TRANS (@lem1221128 A y x z) (@lem1221137 A y x z)). Qed.
Lemma lem1221139 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1221140 {A : Type'} (y : list A) (x : list A) (z : list A) : (term681 A y x z) = (term682 A y x z).
Proof. exact (MK_COMB (@lem1221139) (@lem1221138 A y x z)). Qed.
Lemma lem1221141 {A : Type'} (y : list A) (z : list A) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1221142 {A : Type'} (x : list A) (y : list A) (z : list A) : (term670 A x y z) = (term683 A x y z).
Proof. exact (MK_COMB (@lem1221140 A y x z) (@lem1221141 A y z)). Qed.
Lemma lem1221143 {A : Type'} (x : list A) (y : list A) (z : list A) : (term666 A y x z) = (term683 A x y z).
Proof. exact (TRANS (@lem1221125 A x y z) (@lem1221142 A x y z)). Qed.
Lemma lem1221145 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : term756 A y l1 x l2.
Proof. exact (conj (@lem1221023 A y l1 x l2 h1) (@lem1221032 A y l1 x l2)). Qed.
Lemma lem1221147 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (EQ_MP (@lem1221143 A x y z) (@lem1221122 A y x z)). Qed.
Lemma lem1221148 {A : Type'} (x : list A) (y : list A) (z : list A) : term683 A x y z.
Proof. exact (@lem1221147 A x y z). Qed.
Lemma lem1221149 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) : term757 A y l1 x l2.
Proof. exact (@lem1221148 A (term750 A y l1 x l2) (term751 A y l1 x l2) (term750 A y l1 x l2)). Qed.
Lemma lem1221152 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : (term751 A y l1 x l2) = (term750 A y l1 x l2).
Proof. exact (@lem1221149 A y l1 x l2 (@lem1221145 A y l1 x l2 h1)). Qed.
Lemma lem1221153 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : (term751 A y l1 x l2) = (term750 A y l1 x l2).
Proof. exact (@lem1221152 A y l1 x l2 h1). Qed.
Lemma lem1221154 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : term758 A y l1 x l2.
Proof. exact (fun h0 : term759 A y l1 x l2 => @lem1221153 A y l1 x l2 h1). Qed.
Lemma lem1221156 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1221157 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) : (term758 A y l1 x l2) = ((term751 A y l1 x l2) = (term750 A y l1 x l2)).
Proof. exact (@lem1221156 ((term751 A y l1 x l2) = (term750 A y l1 x l2))). Qed.
Lemma lem1221158 {A : Type'} (y : A) (l1 : list A) (x : A) (l2 : list A) (h1 : term170 A) : (term751 A y l1 x l2) = (term750 A y l1 x l2).
Proof. exact (EQ_MP (@lem1221157 A y l1 x l2) (@lem1221154 A y l1 x l2 h1)). Qed.
Lemma lem1221160 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1221161 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_22125 : list A) (x : A) (_22124 : list A) : (term637 A y l1 l2 _22124 x _22125) = (term760 A y l1 l2 _22125 x _22124).
Proof. exact (@lem1221160 (term761 A y l1 l2 _22124 x _22125) (@List.In A x _22124)). Qed.
Lemma lem1221163 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1221164 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_22124 : list A) (x : A) (_22125 : list A) : (term762 A y l1 l2 _22124 x _22125) = ((term751 A y l1 x l2) = (term102 A _22124 x _22125)).
Proof. exact (@lem1221163 ((term751 A y l1 x l2) = (term102 A _22124 x _22125))). Qed.
Lemma lem1221165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1221166 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_22124 : list A) (x : A) (_22125 : list A) : (term763 A y l1 l2 _22124 x _22125) = (term764 A y l1 l2 _22124 x _22125).
Proof. exact (MK_COMB (@lem1221165) (@lem1221164 A y l1 l2 _22124 x _22125)). Qed.
Lemma lem1221167 {A : Type'} (x : A) (_22124 : list A) : (@List.In A x _22124) = (@List.In A x _22124).
Proof. exact (eq_refl (@List.In A x _22124)). Qed.
Lemma lem1221168 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_22125 : list A) (x : A) (_22124 : list A) : (term760 A y l1 l2 _22125 x _22124) = (term765 A y l1 l2 _22125 x _22124).
Proof. exact (MK_COMB (@lem1221166 A y l1 l2 _22124 x _22125) (@lem1221167 A x _22124)). Qed.
Lemma lem1221169 {A : Type'} (y : A) (l1 : list A) (l2 : list A) (_22125 : list A) (x : A) (_22124 : list A) : (term637 A y l1 l2 _22124 x _22125) = (term765 A y l1 l2 _22125 x _22124).
Proof. exact (TRANS (@lem1221161 A y l1 l2 _22125 x _22124) (@lem1221168 A y l1 l2 _22125 x _22124)). Qed.
Lemma lem1221172 {A : Type'} (_22125 : list A) (_22124 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) : term765 A y l1 l2 _22125 x _22124.
Proof. exact (EQ_MP (@lem1221169 A y l1 l2 _22125 x _22124) (@lem1220330 A _22124 _22125 l1 l2 y l x h1 h2)). Qed.
Lemma lem1221173 {A : Type'} (_22125 : list A) (_22124 : list A) (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) : term765 A y l1 l2 _22125 x _22124.
Proof. exact (@lem1221172 A _22125 _22124 l1 l2 y l x h1 h2). Qed.
Lemma lem1221174 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term77 A l l1 x l2) (h2 : term519 A l1 l2 y l x) : term766 A l2 x y l1.
Proof. exact (@lem1221173 A l2 (@cons A y l1) l1 l2 y l x h1 h2). Qed.
Lemma lem1221177 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) : term106 A x y l1.
Proof. exact (@lem1221174 A l1 l2 y l x h2 h3 (@lem1221158 A y l1 x l2 h1)). Qed.
Lemma lem1221178 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) : term767 A x y l1.
Proof. exact (fun h0 : term768 A x y l1 => @lem1221177 A l1 l2 y l x h1 h2 h3). Qed.
Lemma lem1221180 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1221181 {A : Type'} (x : A) (y : A) (l1 : list A) : (term767 A x y l1) = (term106 A x y l1).
Proof. exact (@lem1221180 (term106 A x y l1)). Qed.
Lemma lem1221182 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term170 A) (h2 : term77 A l l1 x l2) (h3 : term519 A l1 l2 y l x) : term106 A x y l1.
Proof. exact (EQ_MP (@lem1221181 A x y l1) (@lem1221178 A l1 l2 y l x h1 h2 h3)). Qed.
Lemma lem1221184 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (h1). Qed.
Lemma lem1221185 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term769 A x y.
Proof. exact (fun h0 : x = y => @lem1221184 A x y h1). Qed.
Lemma lem1221187 (p : Prop) : (term770 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1221188 {A : Type'} (x : A) (y : A) : (term769 A x y) = (term5 A x y).
Proof. exact (@lem1221187 (x = y)). Qed.
Lemma lem1221189 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) : term5 A x y.
Proof. exact (EQ_MP (@lem1221188 A x y) (@lem1221185 A x y h1)). Qed.
Lemma lem1221195 (q : Prop) (p : Prop) (r : Prop) : (term665 p q r) = (term665 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1221196 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) : (term527 A _22137 _22138 _22139) = (term771 A _22137 _22138 _22139).
Proof. exact (@lem1221195 (_22138 = _22137) (term768 A _22138 _22137 _22139) (@List.In A _22138 _22139)). Qed.
Lemma lem1221212 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1221213 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term772 A _22137 _22138 _22139) = (term773 A _22138 _22137 _22139).
Proof. exact (@lem1221212 (@List.In A _22138 _22139) (term768 A _22138 _22137 _22139)). Qed.
Lemma lem1221219 {A : Type'} (_22138 : A) (_22137 : A) : (term774 A _22138 _22137) = (term774 A _22138 _22137).
Proof. exact (eq_refl (term774 A _22138 _22137)). Qed.
Lemma lem1221220 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term771 A _22137 _22138 _22139) = (term775 A _22138 _22137 _22139).
Proof. exact (MK_COMB (@lem1221219 A _22138 _22137) (@lem1221213 A _22138 _22137 _22139)). Qed.
Lemma lem1221231 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term527 A _22137 _22138 _22139) = (term775 A _22138 _22137 _22139).
Proof. exact (TRANS (@lem1221196 A _22137 _22138 _22139) (@lem1221220 A _22138 _22137 _22139)). Qed.
Lemma lem1221232 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1221233 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term776 A _22137 _22138 _22139) = (term777 A _22138 _22137 _22139).
Proof. exact (MK_COMB (@lem1221232) (@lem1221231 A _22138 _22137 _22139)). Qed.
Lemma lem1221247 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1221248 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term778 A _22139 _22138 _22137) = (term779 A _22138 _22137 _22139).
Proof. exact (@lem1221247 (_22138 = _22137) (term768 A _22138 _22137 _22139)). Qed.
Lemma lem1221256 {A : Type'} (_22138 : A) (_22139 : list A) : (term105 A _22138 _22139) = (term105 A _22138 _22139).
Proof. exact (eq_refl (term105 A _22138 _22139)). Qed.
Lemma lem1221257 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term780 A _22139 _22138 _22137) = (term781 A _22138 _22137 _22139).
Proof. exact (MK_COMB (@lem1221256 A _22138 _22139) (@lem1221248 A _22138 _22137 _22139)). Qed.
Lemma lem1221261 (q : Prop) (p : Prop) (r : Prop) : (term665 p q r) = (term665 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1221262 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term781 A _22138 _22137 _22139) = (term775 A _22138 _22137 _22139).
Proof. exact (@lem1221261 (_22138 = _22137) (@List.In A _22138 _22139) (term768 A _22138 _22137 _22139)). Qed.
Lemma lem1221280 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term780 A _22139 _22138 _22137) = (term775 A _22138 _22137 _22139).
Proof. exact (TRANS (@lem1221257 A _22138 _22137 _22139) (@lem1221262 A _22138 _22137 _22139)). Qed.
Lemma lem1221281 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : ((term527 A _22137 _22138 _22139) = (term780 A _22139 _22138 _22137)) = ((term775 A _22138 _22137 _22139) = (term775 A _22138 _22137 _22139)).
Proof. exact (MK_COMB (@lem1221233 A _22138 _22137 _22139) (@lem1221280 A _22138 _22137 _22139)). Qed.
Lemma lem1221283 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1221284 (x : Prop) : (x = x) = True.
Proof. exact (@lem1221283 Prop x). Qed.
Lemma lem1221285 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : ((term775 A _22138 _22137 _22139) = (term775 A _22138 _22137 _22139)) = True.
Proof. exact (@lem1221284 (term775 A _22138 _22137 _22139)). Qed.
Lemma lem1221286 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) : ((term527 A _22137 _22138 _22139) = (term780 A _22139 _22138 _22137)) = True.
Proof. exact (TRANS (@lem1221281 A _22138 _22137 _22139) (@lem1221285 A _22138 _22137 _22139)). Qed.
Lemma lem1221287 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) : True = ((term527 A _22137 _22138 _22139) = (term780 A _22139 _22138 _22137)).
Proof. exact (SYM (@lem1221286 A _22139 _22138 _22137)). Qed.
Lemma lem1221288 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) : (term527 A _22137 _22138 _22139) = (term780 A _22139 _22138 _22137).
Proof. exact (EQ_MP (@lem1221287 A _22139 _22138 _22137) (@lem0)). Qed.
Lemma lem1221289 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) (h1 : term297 A) : term780 A _22139 _22138 _22137.
Proof. exact (EQ_MP (@lem1221288 A _22139 _22138 _22137) (@lem1220386 A _22137 _22138 _22139 h1)). Qed.
Lemma lem1221291 (b : Prop) (a : Prop) : (a \/ b) = (term669 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1221292 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) : (term780 A _22139 _22138 _22137) = (term782 A _22137 _22138 _22139).
Proof. exact (@lem1221291 (term778 A _22139 _22138 _22137) (@List.In A _22138 _22139)). Qed.
Lemma lem1221294 (a : Prop) (b : Prop) : (term672 a b) = (term673 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1221295 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) : (term783 A _22139 _22138 _22137) = (term784 A _22139 _22138 _22137).
Proof. exact (@lem1221294 (term768 A _22138 _22137 _22139) (_22138 = _22137)). Qed.
Lemma lem1221297 (a : Prop) : (term676 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1221298 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term785 A _22138 _22137 _22139) = (term106 A _22138 _22137 _22139).
Proof. exact (@lem1221297 (term106 A _22138 _22137 _22139)). Qed.
Lemma lem1221299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1221300 {A : Type'} (_22138 : A) (_22137 : A) (_22139 : list A) : (term786 A _22138 _22137 _22139) = (term787 A _22138 _22137 _22139).
Proof. exact (MK_COMB (@lem1221299) (@lem1221298 A _22138 _22137 _22139)). Qed.
Lemma lem1221301 {A : Type'} (_22138 : A) (_22137 : A) : (term5 A _22138 _22137) = (term5 A _22138 _22137).
Proof. exact (eq_refl (term5 A _22138 _22137)). Qed.
Lemma lem1221302 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) : (term784 A _22139 _22138 _22137) = (term788 A _22139 _22138 _22137).
Proof. exact (MK_COMB (@lem1221300 A _22138 _22137 _22139) (@lem1221301 A _22138 _22137)). Qed.
Lemma lem1221303 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) : (term783 A _22139 _22138 _22137) = (term788 A _22139 _22138 _22137).
Proof. exact (TRANS (@lem1221295 A _22139 _22138 _22137) (@lem1221302 A _22139 _22138 _22137)). Qed.
Lemma lem1221304 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1221305 {A : Type'} (_22139 : list A) (_22138 : A) (_22137 : A) : (term789 A _22139 _22138 _22137) = (term790 A _22139 _22138 _22137).
Proof. exact (MK_COMB (@lem1221304) (@lem1221303 A _22139 _22138 _22137)). Qed.
Lemma lem1221306 {A : Type'} (_22138 : A) (_22139 : list A) : (@List.In A _22138 _22139) = (@List.In A _22138 _22139).
Proof. exact (eq_refl (@List.In A _22138 _22139)). Qed.
Lemma lem1221307 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) : (term782 A _22137 _22138 _22139) = (term791 A _22137 _22138 _22139).
Proof. exact (MK_COMB (@lem1221305 A _22139 _22138 _22137) (@lem1221306 A _22138 _22139)). Qed.
Lemma lem1221308 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) : (term780 A _22139 _22138 _22137) = (term791 A _22137 _22138 _22139).
Proof. exact (TRANS (@lem1221292 A _22137 _22138 _22139) (@lem1221307 A _22137 _22138 _22139)). Qed.
Lemma lem1221310 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term170 A) (h3 : term77 A l l1 x l2) (h4 : term519 A l1 l2 y l x) : term788 A l1 x y.
Proof. exact (conj (@lem1221182 A l1 l2 y l x h2 h3 h4) (@lem1221189 A x y h1)). Qed.
Lemma lem1221312 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) (h1 : term297 A) : term791 A _22137 _22138 _22139.
Proof. exact (EQ_MP (@lem1221308 A _22137 _22138 _22139) (@lem1221289 A _22139 _22138 _22137 h1)). Qed.
Lemma lem1221313 {A : Type'} (_22137 : A) (_22138 : A) (_22139 : list A) (h1 : term297 A) : term791 A _22137 _22138 _22139.
Proof. exact (@lem1221312 A _22137 _22138 _22139 h1). Qed.
Lemma lem1221314 {A : Type'} (y : A) (x : A) (l1 : list A) (h1 : term297 A) : term791 A y x l1.
Proof. exact (@lem1221313 A y x l1 h1). Qed.
Lemma lem1221317 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : @List.In A x l1.
Proof. exact (@lem1221314 A y x l1 h2 (@lem1221310 A l1 l2 y l x h1 h3 h4 h5)). Qed.
Lemma lem1221318 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : term715 A x l1.
Proof. exact (fun h0 : term100 A x l1 => @lem1221317 A l1 l2 y l x h1 h2 h3 h4 h5). Qed.
Lemma lem1221320 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1221321 {A : Type'} (x : A) (l1 : list A) : (term715 A x l1) = (@List.In A x l1).
Proof. exact (@lem1221320 (@List.In A x l1)). Qed.
Lemma lem1221322 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : @List.In A x l1.
Proof. exact (EQ_MP (@lem1221321 A x l1) (@lem1221318 A l1 l2 y l x h1 h2 h3 h4 h5)). Qed.
Lemma lem1221325 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1221327 {A : Type'} (x : A) (l1 : list A) : (term100 A x l1) = (term716 A x l1).
Proof. exact (@lem1221325 (@List.In A x l1)). Qed.
Lemma lem1221330 {A : Type'} (l : list A) (l1 : list A) (x : A) (l2 : list A) (h1 : term77 A l l1 x l2) : term716 A x l1.
Proof. exact (EQ_MP (@lem1221327 A x l1) (@lem1220469 A l l1 x l2 h1)). Qed.
Lemma lem1221333 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : False.
Proof. exact (@lem1221330 A l l1 x l2 h4 (@lem1221322 A l1 l2 y l x h1 h2 h3 h4 h5)). Qed.
Lemma lem1221334 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : term697.
Proof. exact (fun h0 : ~ False => @lem1221333 A l1 l2 y l x h1 h2 h3 h4 h5). Qed.
Lemma lem1221336 (p : Prop) : (term657 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1221337 : term697 = False.
Proof. exact (@lem1221336 False). Qed.
Lemma lem1221338 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221337) (@lem1221334 A l1 l2 y l x h1 h2 h3 h4 h5)). Qed.
Lemma lem1221339 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h6 : term5 A x y => @lem1221338 A l1 l2 y l x h1 h2 h3 h4 h5) (fun h6 : False => @lem1220317 A x y h1)). Qed.
Lemma lem1221341 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221339 A l1 l2 y l x h1 h2 h3 h4 h5) (@lem1220317 A x y h1)). Qed.
Lemma lem1221342 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1220782) (@lem1220779 A x y h1 h2)). Qed.
Lemma lem1221343 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1221342 A x y h1 h2) (fun h3 : False => @lem1219998 A x y h2)). Qed.
Lemma lem1221344 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221343 A x y h1 h2) (@lem1219998 A x y h2)). Qed.
Lemma lem1221345 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h3 : term5 A x y => @lem1221344 A x y h1 h2) (fun h3 : False => @lem1219859 A x y h1)). Qed.
Lemma lem1221347 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221345 A x y h1 h2) (@lem1219859 A x y h1)). Qed.
Lemma lem1221348 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1220653) (@lem1220650 A x y h1 h2)). Qed.
Lemma lem1221349 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h6 : term5 A x y => @lem1221341 A l1 l2 y l x h1 h2 h3 h4 h5) (fun h6 : False => @lem1219542 A x y h1)). Qed.
Lemma lem1221350 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221349 A l1 l2 y l x h1 h2 h3 h4 h5) (@lem1219542 A x y h1)). Qed.
Lemma lem1221351 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : (term100 A x l) = False.
Proof. exact (prop_ext (fun h3 : term100 A x l => @lem1220910 A x l h1 h2) (fun h3 : False => @lem1219516 A x l h1)). Qed.
Lemma lem1221352 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1221351 A x l h1 h2) (@lem1219516 A x l h1)). Qed.
Lemma lem1221353 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : (@List.In A x l) = False.
Proof. exact (prop_ext (fun h3 : @List.In A x l => @lem1221352 A x l h1 h2) (fun h3 : False => @lem1219514 A x l h2)). Qed.
Lemma lem1221354 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1221353 A x l h1 h2) (@lem1219514 A x l h2)). Qed.
Lemma lem1221355 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1221347 A x y h1 h2) (fun h3 : False => @lem1219444 A x y h2)). Qed.
Lemma lem1221356 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221355 A x y h1 h2) (@lem1219444 A x y h2)). Qed.
Lemma lem1221357 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h3 : term5 A x y => @lem1221356 A x y h1 h2) (fun h3 : False => @lem1219404 A x y h1)). Qed.
Lemma lem1221358 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221357 A x y h1 h2) (@lem1219404 A x y h1)). Qed.
Lemma lem1221359 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1221348 A x y h1 h2) (fun h3 : False => @lem1219376 A x y h2)). Qed.
Lemma lem1221360 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221359 A x y h1 h2) (@lem1219376 A x y h2)). Qed.
Lemma lem1221361 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h3 : term5 A x y => @lem1221360 A x y h1 h2) (fun h3 : False => @lem1219336 A x y h1)). Qed.
Lemma lem1221362 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221361 A x y h1 h2) (@lem1219336 A x y h1)). Qed.
Lemma lem1221363 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h6 : term5 A x y => @lem1221350 A l1 l2 y l x h1 h2 h3 h4 h5) (fun h6 : False => @lem1218818 A x y h1)). Qed.
Lemma lem1221364 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221363 A l1 l2 y l x h1 h2 h3 h4 h5) (@lem1218818 A x y h1)). Qed.
Lemma lem1221365 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : (term100 A x l) = False.
Proof. exact (prop_ext (fun h3 : term100 A x l => @lem1221354 A x l h1 h2) (fun h3 : False => @lem1218814 A x l h1)). Qed.
Lemma lem1221366 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1221365 A x l h1 h2) (@lem1218814 A x l h1)). Qed.
Lemma lem1221367 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : (@List.In A x l) = False.
Proof. exact (prop_ext (fun h3 : @List.In A x l => @lem1221366 A x l h1 h2) (fun h3 : False => @lem1218810 A x l h2)). Qed.
Lemma lem1221368 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1221367 A x l h1 h2) (@lem1218810 A x l h2)). Qed.
Lemma lem1221369 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1221358 A x y h1 h2) (fun h3 : False => @lem1218594 A x y h2)). Qed.
Lemma lem1221370 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221369 A x y h1 h2) (@lem1218594 A x y h2)). Qed.
Lemma lem1221371 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h3 : term5 A x y => @lem1221370 A x y h1 h2) (fun h3 : False => @lem1218390 A x y h1)). Qed.
Lemma lem1221372 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221371 A x y h1 h2) (@lem1218390 A x y h1)). Qed.
Lemma lem1221373 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1221362 A x y h1 h2) (fun h3 : False => @lem1218382 A x y h2)). Qed.
Lemma lem1221374 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221373 A x y h1 h2) (@lem1218382 A x y h2)). Qed.
Lemma lem1221375 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h3 : term5 A x y => @lem1221374 A x y h1 h2) (fun h3 : False => @lem1218178 A x y h1)). Qed.
Lemma lem1221376 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221375 A x y h1 h2) (@lem1218178 A x y h1)). Qed.
Lemma lem1221377 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h6 : term5 A x y => @lem1221364 A l1 l2 y l x h1 h2 h3 h4 h5) (fun h6 : False => @lem1218818 A x y h1)). Qed.
Lemma lem1221378 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term77 A l l1 x l2) (h5 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221377 A l1 l2 y l x h1 h2 h3 h4 h5) (@lem1218818 A x y h1)). Qed.
Lemma lem1221379 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : (term100 A x l) = False.
Proof. exact (prop_ext (fun h3 : term100 A x l => @lem1221368 A x l h1 h2) (fun h3 : False => @lem1218814 A x l h1)). Qed.
Lemma lem1221380 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1221379 A x l h1 h2) (@lem1218814 A x l h1)). Qed.
Lemma lem1221381 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : (@List.In A x l) = False.
Proof. exact (prop_ext (fun h3 : @List.In A x l => @lem1221380 A x l h1 h2) (fun h3 : False => @lem1218810 A x l h2)). Qed.
Lemma lem1221382 {A : Type'} (x : A) (l : list A) (h1 : term100 A x l) (h2 : @List.In A x l) : False.
Proof. exact (EQ_MP (@lem1221381 A x l h1 h2) (@lem1218810 A x l h2)). Qed.
Lemma lem1221383 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1221372 A x y h1 h2) (fun h3 : False => @lem1218594 A x y h2)). Qed.
Lemma lem1221384 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221383 A x y h1 h2) (@lem1218594 A x y h2)). Qed.
Lemma lem1221385 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h3 : term5 A x y => @lem1221384 A x y h1 h2) (fun h3 : False => @lem1218390 A x y h1)). Qed.
Lemma lem1221386 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221385 A x y h1 h2) (@lem1218390 A x y h1)). Qed.
Lemma lem1221387 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (x = y) = False.
Proof. exact (prop_ext (fun h3 : x = y => @lem1221376 A x y h1 h2) (fun h3 : False => @lem1218382 A x y h2)). Qed.
Lemma lem1221388 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221387 A x y h1 h2) (@lem1218382 A x y h2)). Qed.
Lemma lem1221389 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h3 : term5 A x y => @lem1221388 A x y h1 h2) (fun h3 : False => @lem1218178 A x y h1)). Qed.
Lemma lem1221390 {A : Type'} (x : A) (y : A) (h1 : term5 A x y) (h2 : x = y) : False.
Proof. exact (EQ_MP (@lem1221389 A x y h1 h2) (@lem1218178 A x y h1)). Qed.
Lemma lem1221391 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (x : A) (l : list A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) (h5 : @List.In A x l) : False.
Proof. exact (or_elim (@lem1218150 A l1 l2 y l x h4) (fun h0 : term100 A x l => @lem1221382 A x l h0 h5) (fun h0 : term77 A l l1 x l2 => @lem1221378 A l1 l2 y l x h1 h2 h3 h0 h4)). Qed.
Lemma lem1221392 {A : Type'} (l1 : list A) (l2 : list A) (l : list A) (x : A) (y : A) (h1 : term5 A x y) (h2 : term519 A l1 l2 y l x) (h3 : x = y) : False.
Proof. exact (or_elim (@lem1218150 A l1 l2 y l x h2) (fun h0 : term100 A x l => @lem1221390 A x y h1 h3) (fun h0 : term77 A l l1 x l2 => @lem1221386 A x y h1 h3)). Qed.
Lemma lem1221393 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) : False.
Proof. exact (or_elim (@lem1218152 A l1 l2 y l x h4) (fun h0 : x = y => @lem1221392 A l1 l2 l x y h1 h4 h0) (fun h0 : @List.In A x l => @lem1221391 A l1 l2 y x l h1 h2 h3 h4 h0)). Qed.
Lemma lem1221394 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) : (term519 A l1 l2 y l x) = False.
Proof. exact (prop_ext (fun h5 : term519 A l1 l2 y l x => @lem1221393 A l1 l2 y l x h1 h2 h3 h4) (fun h5 : False => @lem1218148 A l1 l2 y l x h4)). Qed.
Lemma lem1221395 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221394 A l1 l2 y l x h1 h2 h3 h4) (@lem1218148 A l1 l2 y l x h4)). Qed.
Lemma lem1221396 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) : (term170 A) = False.
Proof. exact (prop_ext (fun h5 : term170 A => @lem1221395 A l1 l2 y l x h1 h2 h3 h4) (fun h5 : False => @lem1217834 A h3)). Qed.
Lemma lem1221397 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221396 A l1 l2 y l x h1 h2 h3 h4) (@lem1217834 A h3)). Qed.
Lemma lem1221398 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h5 : term5 A x y => @lem1221397 A l1 l2 y l x h1 h2 h3 h4) (fun h5 : False => @lem1217788 A x y h1)). Qed.
Lemma lem1221399 {A : Type'} (l1 : list A) (l2 : list A) (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term297 A) (h3 : term170 A) (h4 : term519 A l1 l2 y l x) : False.
Proof. exact (EQ_MP (@lem1221398 A l1 l2 y l x h1 h2 h3 h4) (@lem1217788 A x y h1)). Qed.
Lemma lem1221400 {A : Type'} (l1 : list A) (l : list A) (x : A) (y : A) (h1 : term522 A l1 y l x) (h2 : term5 A x y) (h3 : term297 A) (h4 : term170 A) : False.
Proof. exact (ex_elim (@lem1217779 A l1 y l x h1) (fun l2 : list A => fun h0 : term521 A l1 y l x l2 => @lem1221399 A l1 l2 y l x h2 h3 h4 h0)). Qed.
Lemma lem1221401 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term297 A) (h4 : term170 A) : False.
Proof. exact (ex_elim (@lem1216782 A y l x h2) (fun l1 : list A => fun h0 : term523 A y l x l1 => @lem1221400 A l1 l x y h0 h1 h3 h4)). Qed.
Lemma lem1221402 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term297 A) (h4 : term170 A) : (term170 A) = False.
Proof. exact (prop_ext (fun h5 : term170 A => @lem1221401 A y l x h1 h2 h3 h4) (fun h5 : False => @lem1216820 A h4)). Qed.
Lemma lem1221403 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term297 A) (h4 : term170 A) : False.
Proof. exact (EQ_MP (@lem1221402 A y l x h1 h2 h3 h4) (@lem1216820 A h4)). Qed.
Lemma lem1221404 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term297 A) (h4 : term170 A) : (term5 A x y) = False.
Proof. exact (prop_ext (fun h5 : term5 A x y => @lem1221403 A y l x h1 h2 h3 h4) (fun h5 : False => @lem1216486 A x y h1)). Qed.
Lemma lem1221405 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term297 A) (h4 : term170 A) : False.
Proof. exact (EQ_MP (@lem1221404 A y l x h1 h2 h3 h4) (@lem1216486 A x y h1)). Qed.
Lemma lem1221406 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term297 A) (h4 : term170 A) : term717 A.
Proof. exact (fun h0 : term381 A => @lem1221405 A y l x h1 h2 h3 h4). Qed.
Lemma lem1221407 {A : Type'} : (term717 A) = (term382 A).
Proof. exact (@lem69 (term381 A)). Qed.
Lemma lem1221408 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term297 A) (h4 : term170 A) : term382 A.
Proof. exact (EQ_MP (@lem1221407 A) (@lem1221406 A y l x h1 h2 h3 h4)). Qed.
Lemma lem1221409 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term170 A) : term384 A.
Proof. exact (fun h0 : term297 A => @lem1221408 A y l x h1 h2 h0 h3). Qed.
Lemma lem1221410 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) (h3 : term170 A) : term387 A.
Proof. exact (fun h0 : term171 A => @lem1221409 A y l x h1 h2 h3). Qed.
Lemma lem1221411 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term218 A y l x) : term390 A.
Proof. exact (fun h0 : term170 A => @lem1221410 A y l x h1 h2 h0). Qed.
Lemma lem1221412 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term5 A x y) : term392 A y l x.
Proof. exact (fun h0 : term218 A y l x => @lem1221411 A y l x h1 h0). Qed.
Lemma lem1221413 {A : Type'} (y : A) (l : list A) (x : A) : term726 A y l x.
Proof. exact (fun h0 : term5 A x y => @lem1221412 A l x y h0). Qed.
Lemma lem1221418 {A : Type'} (l : list A) (x : A) : term730 A l x.
Proof. exact (fun y : A => @lem1221413 A y l x). Qed.
Lemma lem1221423 {A : Type'} (x : A) : term734 A x.
Proof. exact (fun l : list A => @lem1221418 A l x). Qed.
Lemma lem1221428 {A : Type'} : term738 A.
Proof. exact (fun x : A => @lem1221423 A x). Qed.
Lemma lem1221429 {A : Type'} : term737 A.
Proof. exact (EQ_MP (@lem1216474 A) (@lem1221428 A)). Qed.
Lemma lem1221430 {A : Type'} (x : A) : term792 A x.
Proof. exact (@lem1221429 A x). Qed.
Lemma lem1221431 {A : Type'} (x : A) : (term792 A x) = (term733 A x).
Proof. exact (eq_refl (term792 A x)). Qed.
Lemma lem1221432 {A : Type'} (x : A) : term733 A x.
Proof. exact (EQ_MP (@lem1221431 A x) (@lem1221430 A x)). Qed.
Lemma lem1221433 {A : Type'} (x : A) (l : list A) : term793 A x l.
Proof. exact (@lem1221432 A x l). Qed.
Lemma lem1221434 {A : Type'} (l : list A) (x : A) : (term793 A x l) = (term729 A l x).
Proof. exact (eq_refl (term793 A x l)). Qed.
Lemma lem1221435 {A : Type'} (l : list A) (x : A) : term729 A l x.
Proof. exact (EQ_MP (@lem1221434 A l x) (@lem1221433 A x l)). Qed.
Lemma lem1221436 {A : Type'} (l : list A) (x : A) (y : A) : term794 A l x y.
Proof. exact (@lem1221435 A l x y). Qed.
Lemma lem1221437 {A : Type'} (y : A) (l : list A) (x : A) : (term794 A l x y) = (term721 A y l x).
Proof. exact (eq_refl (term794 A l x y)). Qed.
Lemma lem1221438 {A : Type'} (y : A) (l : list A) (x : A) : term721 A y l x.
Proof. exact (EQ_MP (@lem1221437 A y l x) (@lem1221436 A l x y)). Qed.
Lemma lem1221440 {A : Type'} (y : A) (l : list A) (x : A) : term721 A y l x.
Proof. exact (@lem1215508 A y l x (@lem1221438 A y l x)). Qed.
Lemma lem1221441 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term5 A x y) : term391 A y l x.
Proof. exact (@lem1221440 A y l x (@lem1208017 A x y h1)). Qed.
Lemma lem1221442 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term168 A y l x) : term389 A.
Proof. exact (@lem1221441 A l x y h1 (@lem1215482 A y l x h2)). Qed.
Lemma lem1221443 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term168 A y l x) : term386 A.
Proof. exact (@lem1221442 A y l x h1 h2 (@lem1215487 A)). Qed.
Lemma lem1221444 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term168 A y l x) : term383 A.
Proof. exact (@lem1221443 A y l x h1 h2 (@lem1215489 A)). Qed.
Lemma lem1221445 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term168 A y l x) : term300 A.
Proof. exact (@lem1221444 A y l x h1 h2 (@lem1215483 A)). Qed.
Lemma lem1221446 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term168 A y l x) : False.
Proof. exact (@lem1221445 A y l x h1 h2 (@lem1215486 A)). Qed.
Lemma lem1221447 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term168 A y l x) : (term168 A y l x) = False.
Proof. exact (prop_ext (fun h3 : term168 A y l x => @lem1221446 A y l x h1 h2) (fun h3 : False => @lem1215482 A y l x h2)). Qed.
Lemma lem1221448 {A : Type'} (y : A) (l : list A) (x : A) (h1 : term5 A x y) (h2 : term168 A y l x) : False.
Proof. exact (EQ_MP (@lem1221447 A y l x h1 h2) (@lem1215482 A y l x h2)). Qed.
Lemma lem1221449 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term5 A x y) : term167 A y l x.
Proof. exact (fun h0 : term168 A y l x => @lem1221448 A y l x h1 h0). Qed.
Lemma lem1221450 {A : Type'} (l : list A) (x : A) (y : A) (h1 : term5 A x y) : term160 A y l x.
Proof. exact (EQ_MP (@lem1215481 A y l x) (@lem1221449 A l x y h1)). Qed.
Lemma lem1221451 {A : Type'} (y : A) (l : list A) (x : A) : term160 A y l x.
Proof. exact (or_elim (@lem1208015 A x y) (fun h0 : x = y => @lem1215477 A l x y h0) (fun h0 : term5 A x y => @lem1221450 A l x y h0)). Qed.
Lemma lem1221456 {A : Type'} (y : A) (x : A) : term162 A y x.
Proof. exact (fun l : list A => @lem1221451 A y l x). Qed.
Lemma lem1221461 {A : Type'} (x : A) : term164 A x.
Proof. exact (fun y : A => @lem1221456 A y x). Qed.
Lemma lem1221462 {A : Type'} (x : A) : term147 A x.
Proof. exact (EQ_MP (@lem1208874 A x) (@lem1221461 A x)). Qed.
Lemma lem1221463 {A : Type'} (x : A) : term123 A x.
Proof. exact (@lem1208727 A x (@lem1221462 A x)). Qed.
Lemma lem1221468 {A : Type'} : term125 A.
Proof. exact (fun x : A => @lem1221463 A x). Qed.
Lemma lem1221469 {A : Type'} : term51 A.
Proof. exact (EQ_MP (@lem1208700 A) (@lem1221468 A)). Qed.
Lemma lem1221470 {A : Type'} : term50 A.
Proof. exact (EQ_MP (@lem1208234 A) (@lem1221469 A)). Qed.
