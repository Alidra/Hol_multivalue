Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_ALT_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FORALL_AND_THM_spec.
Require Import UNION_OF_spec.
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
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
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
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
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
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4845732_spec.
Require Import thm4848608_spec.
Lemma lem4853020 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4853021 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4853022 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4853021 A P) (@lem4853020 A P)). Qed.
Lemma lem4853023 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4853022 A P Q). Qed.
Lemma lem4853024 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@UNION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4853026 {A : Type'} (s : type686 A) : term4 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4853027 {A : Type'} (s : type686 A) : (term4 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term4 A s)). Qed.
Lemma lem4853039 {A : Type'} (s : type686 A) : term4 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4853040 {A : Type'} (s : type686 A) : (term4 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term4 A s)). Qed.
Lemma lem4853054 (p : Prop) : term5 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem4853055 (p : Prop) : (term5 p) = (term6 p).
Proof. exact (eq_refl (term5 p)). Qed.
Lemma lem4853056 (p : Prop) : term6 p.
Proof. exact (EQ_MP (@lem4853055 p) (@lem4853054 p)). Qed.
Lemma lem4853057 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem4853058 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem4853071 (q : Prop) : (term7 q) = (term7 q).
Proof. exact (eq_refl (term7 q)). Qed.
Lemma lem4853072 (q : Prop) (p : Prop) (h1 : p = True) : (term8 q p) = (term9 q).
Proof. exact (MK_COMB (@lem4853071 q) (@lem4853057 p h1)). Qed.
Lemma lem4853073 (q : Prop) : (term9 q) = ((True = q) = (term10 q)).
Proof. exact (eq_refl (term9 q)). Qed.
Lemma lem4853074 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem4853075 (p : Prop) (q : Prop) : ((term8 q p) = (term9 q)) = ((term8 q p) = ((True = q) = (term10 q))).
Proof. exact (MK_COMB (@lem4853074 q p) (@lem4853073 q)). Qed.
Lemma lem4853076 (q : Prop) (p : Prop) : (term8 q p) = ((p = q) = (term12 q p)).
Proof. exact (eq_refl (term8 q p)). Qed.
Lemma lem4853077 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4853078 (q : Prop) (p : Prop) : (term11 q p) = (term13 q p).
Proof. exact (MK_COMB (@lem4853077) (@lem4853076 q p)). Qed.
Lemma lem4853079 (q : Prop) : ((True = q) = (term10 q)) = ((True = q) = (term10 q)).
Proof. exact (eq_refl ((True = q) = (term10 q))). Qed.
Lemma lem4853080 (p : Prop) (q : Prop) : ((term8 q p) = ((True = q) = (term10 q))) = (((p = q) = (term12 q p)) = ((True = q) = (term10 q))).
Proof. exact (MK_COMB (@lem4853078 q p) (@lem4853079 q)). Qed.
Lemma lem4853081 (p : Prop) (q : Prop) : ((term8 q p) = (term9 q)) = (((p = q) = (term12 q p)) = ((True = q) = (term10 q))).
Proof. exact (TRANS (@lem4853075 p q) (@lem4853080 p q)). Qed.
Lemma lem4853082 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = (term12 q p)) = ((True = q) = (term10 q)).
Proof. exact (EQ_MP (@lem4853081 p q) (@lem4853072 q p h1)). Qed.
Lemma lem4853083 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = (term10 q)) = ((p = q) = (term12 q p)).
Proof. exact (SYM (@lem4853082 q p h1)). Qed.
Lemma lem4853084 (q : Prop) : (term7 q) = (term7 q).
Proof. exact (eq_refl (term7 q)). Qed.
Lemma lem4853085 (q : Prop) (p : Prop) (h1 : p = False) : (term8 q p) = (term14 q).
Proof. exact (MK_COMB (@lem4853084 q) (@lem4853058 p h1)). Qed.
Lemma lem4853086 (q : Prop) : (term14 q) = ((False = q) = (term15 q)).
Proof. exact (eq_refl (term14 q)). Qed.
Lemma lem4853087 (q : Prop) (p : Prop) : (term11 q p) = (term11 q p).
Proof. exact (eq_refl (term11 q p)). Qed.
Lemma lem4853088 (p : Prop) (q : Prop) : ((term8 q p) = (term14 q)) = ((term8 q p) = ((False = q) = (term15 q))).
Proof. exact (MK_COMB (@lem4853087 q p) (@lem4853086 q)). Qed.
Lemma lem4853089 (q : Prop) (p : Prop) : (term8 q p) = ((p = q) = (term12 q p)).
Proof. exact (eq_refl (term8 q p)). Qed.
Lemma lem4853090 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4853091 (q : Prop) (p : Prop) : (term11 q p) = (term13 q p).
Proof. exact (MK_COMB (@lem4853090) (@lem4853089 q p)). Qed.
Lemma lem4853092 (q : Prop) : ((False = q) = (term15 q)) = ((False = q) = (term15 q)).
Proof. exact (eq_refl ((False = q) = (term15 q))). Qed.
Lemma lem4853093 (p : Prop) (q : Prop) : ((term8 q p) = ((False = q) = (term15 q))) = (((p = q) = (term12 q p)) = ((False = q) = (term15 q))).
Proof. exact (MK_COMB (@lem4853091 q p) (@lem4853092 q)). Qed.
Lemma lem4853094 (p : Prop) (q : Prop) : ((term8 q p) = (term14 q)) = (((p = q) = (term12 q p)) = ((False = q) = (term15 q))).
Proof. exact (TRANS (@lem4853088 p q) (@lem4853093 p q)). Qed.
Lemma lem4853095 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = (term12 q p)) = ((False = q) = (term15 q)).
Proof. exact (EQ_MP (@lem4853094 p q) (@lem4853085 q p h1)). Qed.
Lemma lem4853096 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = (term15 q)) = ((p = q) = (term12 q p)).
Proof. exact (SYM (@lem4853095 q p h1)). Qed.
Lemma lem4853100 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4853101 (q : Prop) : (True = q) = q.
Proof. exact (@lem4853100 q). Qed.
Lemma lem4853102 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4853103 (q : Prop) : (term16 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem4853102) (@lem4853101 q)). Qed.
Lemma lem4853107 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4853108 (q : Prop) : (True -> q) = q.
Proof. exact (@lem4853107 q). Qed.
Lemma lem4853109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853110 (q : Prop) : (term17 q) = (and q).
Proof. exact (MK_COMB (@lem4853109) (@lem4853108 q)). Qed.
Lemma lem4853112 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4853113 (q : Prop) : (q -> True) = True.
Proof. exact (@lem4853112 q). Qed.
Lemma lem4853114 (q : Prop) : (term10 q) = (q /\ True).
Proof. exact (MK_COMB (@lem4853110 q) (@lem4853113 q)). Qed.
Lemma lem4853116 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4853117 (q : Prop) : (q /\ True) = q.
Proof. exact (@lem4853116 q). Qed.
Lemma lem4853118 (q : Prop) : (term10 q) = q.
Proof. exact (TRANS (@lem4853114 q) (@lem4853117 q)). Qed.
Lemma lem4853119 (q : Prop) : ((True = q) = (term10 q)) = (q = q).
Proof. exact (MK_COMB (@lem4853103 q) (@lem4853118 q)). Qed.
Lemma lem4853121 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4853122 (x : Prop) : (x = x) = True.
Proof. exact (@lem4853121 Prop x). Qed.
Lemma lem4853123 (q : Prop) : (q = q) = True.
Proof. exact (@lem4853122 q). Qed.
Lemma lem4853124 (q : Prop) : ((True = q) = (term10 q)) = True.
Proof. exact (TRANS (@lem4853119 q) (@lem4853123 q)). Qed.
Lemma lem4853125 (q : Prop) : True = ((True = q) = (term10 q)).
Proof. exact (SYM (@lem4853124 q)). Qed.
Lemma lem4853126 (q : Prop) : (True = q) = (term10 q).
Proof. exact (EQ_MP (@lem4853125 q) (@lem0)). Qed.
Lemma lem4853130 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4853131 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem4853130 q). Qed.
Lemma lem4853132 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4853133 (q : Prop) : (term18 q) = (term19 q).
Proof. exact (MK_COMB (@lem4853132) (@lem4853131 q)). Qed.
Lemma lem4853137 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4853138 (q : Prop) : (False -> q) = True.
Proof. exact (@lem4853137 q). Qed.
Lemma lem4853139 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853140 (q : Prop) : (term20 q) = (and True).
Proof. exact (MK_COMB (@lem4853139) (@lem4853138 q)). Qed.
Lemma lem4853142 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem4853143 (q : Prop) : (q -> False) = (~ q).
Proof. exact (@lem4853142 q). Qed.
Lemma lem4853144 (q : Prop) : (term15 q) = (term21 q).
Proof. exact (MK_COMB (@lem4853140 q) (@lem4853143 q)). Qed.
Lemma lem4853146 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4853147 (q : Prop) : (term21 q) = (~ q).
Proof. exact (@lem4853146 (~ q)). Qed.
Lemma lem4853148 (q : Prop) : (term15 q) = (~ q).
Proof. exact (TRANS (@lem4853144 q) (@lem4853147 q)). Qed.
Lemma lem4853149 (q : Prop) : ((False = q) = (term15 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem4853133 q) (@lem4853148 q)). Qed.
Lemma lem4853151 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4853152 (x : Prop) : (x = x) = True.
Proof. exact (@lem4853151 Prop x). Qed.
Lemma lem4853153 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem4853152 (~ q)). Qed.
Lemma lem4853154 (q : Prop) : ((False = q) = (term15 q)) = True.
Proof. exact (TRANS (@lem4853149 q) (@lem4853153 q)). Qed.
Lemma lem4853155 (q : Prop) : True = ((False = q) = (term15 q)).
Proof. exact (SYM (@lem4853154 q)). Qed.
Lemma lem4853156 (q : Prop) : (False = q) = (term15 q).
Proof. exact (EQ_MP (@lem4853155 q) (@lem0)). Qed.
Lemma lem4853157 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = (term12 q p).
Proof. exact (EQ_MP (@lem4853096 q p h1) (@lem4853156 q)). Qed.
Lemma lem4853158 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = (term12 q p).
Proof. exact (EQ_MP (@lem4853083 q p h1) (@lem4853126 q)). Qed.
Lemma lem4853162 {A : Type'} (P : A -> Prop) : term22 A P.
Proof. exact (@lem4997 A P). Qed.
Lemma lem4853163 {A : Type'} (P : A -> Prop) : (term22 A P) = (term23 A P).
Proof. exact (eq_refl (term22 A P)). Qed.
Lemma lem4853164 {A : Type'} (P : A -> Prop) : term23 A P.
Proof. exact (EQ_MP (@lem4853163 A P) (@lem4853162 A P)). Qed.
Lemma lem4853165 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term24 A P Q.
Proof. exact (@lem4853164 A P Q). Qed.
Lemma lem4853166 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term24 A P Q) = ((term25 A P Q) = (term26 A P Q)).
Proof. exact (eq_refl (term24 A P Q)). Qed.
Lemma lem4853175 (q : Prop) (p : Prop) : (p = q) = (term12 q p).
Proof. exact (or_elim (@lem4853056 p) (fun h0 : p = True => @lem4853158 q p h0) (fun h0 : p = False => @lem4853157 q p h0)). Qed.
Lemma lem4853176 {A : Type'} (B : type686 A) (s : A -> Prop) : ((@UNION_OF A (@ARBITRARY A) B s) = (term27 A B s)) = (term28 A B s).
Proof. exact (@lem4853175 (term27 A B s) (@UNION_OF A (@ARBITRARY A) B s)). Qed.
Lemma lem4853211 {A : Type'} (B : type686 A) : (term29 A B) = (term30 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4853176 A B s)). Qed.
Lemma lem4853212 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853213 {A : Type'} (B : type686 A) : (term31 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4853212 A) (@lem4853211 A B)). Qed.
Lemma lem4853215 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term25 A P Q) = (term26 A P Q).
Proof. exact (EQ_MP (@lem4853166 A P Q) (@lem4853165 A P Q)). Qed.
Lemma lem4853216 {A : Type'} (P : type686 A) (Q : type686 A) : (term33 A P Q) = (term34 A P Q).
Proof. exact (@lem4853215 (A -> Prop) P Q). Qed.
Lemma lem4853217 {A : Type'} (B : type686 A) : (term35 A B) = (term36 A B).
Proof. exact (@lem4853216 A (term37 A B) (term38 A B)). Qed.
Lemma lem4853218 {A : Type'} (B : type686 A) (s : A -> Prop) : (term39 A B s) = (term40 A B s).
Proof. exact (eq_refl (term39 A B s)). Qed.
Lemma lem4853219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853220 {A : Type'} (B : type686 A) (s : A -> Prop) : (term41 A B s) = (term42 A B s).
Proof. exact (MK_COMB (@lem4853219) (@lem4853218 A B s)). Qed.
Lemma lem4853221 {A : Type'} (B : type686 A) (s : A -> Prop) : (term43 A B s) = (term44 A B s).
Proof. exact (eq_refl (term43 A B s)). Qed.
Lemma lem4853222 {A : Type'} (B : type686 A) (s : A -> Prop) : (term45 A B s) = (term28 A B s).
Proof. exact (MK_COMB (@lem4853220 A B s) (@lem4853221 A B s)). Qed.
Lemma lem4853223 {A : Type'} (B : type686 A) : (term46 A B) = (term30 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4853222 A B s)). Qed.
Lemma lem4853224 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853225 {A : Type'} (B : type686 A) : (term35 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem4853224 A) (@lem4853223 A B)). Qed.
Lemma lem4853226 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4853227 {A : Type'} (B : type686 A) : (term47 A B) = (term48 A B).
Proof. exact (MK_COMB (@lem4853226) (@lem4853225 A B)). Qed.
Lemma lem4853228 {A : Type'} (B : type686 A) (s : A -> Prop) : (term39 A B s) = (term40 A B s).
Proof. exact (eq_refl (term39 A B s)). Qed.
Lemma lem4853229 {A : Type'} (B : type686 A) : (term49 A B) = (term37 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4853228 A B s)). Qed.
Lemma lem4853230 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853231 {A : Type'} (B : type686 A) : (term50 A B) = (term51 A B).
Proof. exact (MK_COMB (@lem4853230 A) (@lem4853229 A B)). Qed.
Lemma lem4853232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853233 {A : Type'} (B : type686 A) : (term52 A B) = (term53 A B).
Proof. exact (MK_COMB (@lem4853232) (@lem4853231 A B)). Qed.
Lemma lem4853234 {A : Type'} (B : type686 A) (s : A -> Prop) : (term43 A B s) = (term44 A B s).
Proof. exact (eq_refl (term43 A B s)). Qed.
Lemma lem4853235 {A : Type'} (B : type686 A) : (term54 A B) = (term38 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4853234 A B s)). Qed.
Lemma lem4853236 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853237 {A : Type'} (B : type686 A) : (term55 A B) = (term56 A B).
Proof. exact (MK_COMB (@lem4853236 A) (@lem4853235 A B)). Qed.
Lemma lem4853238 {A : Type'} (B : type686 A) : (term36 A B) = (term57 A B).
Proof. exact (MK_COMB (@lem4853233 A B) (@lem4853237 A B)). Qed.
Lemma lem4853239 {A : Type'} (B : type686 A) : ((term35 A B) = (term36 A B)) = ((term32 A B) = (term57 A B)).
Proof. exact (MK_COMB (@lem4853227 A B) (@lem4853238 A B)). Qed.
Lemma lem4853240 {A : Type'} (B : type686 A) : (term32 A B) = (term57 A B).
Proof. exact (EQ_MP (@lem4853239 A B) (@lem4853217 A B)). Qed.
Lemma lem4853283 {A : Type'} (B : type686 A) : (term31 A B) = (term57 A B).
Proof. exact (TRANS (@lem4853213 A B) (@lem4853240 A B)). Qed.
Lemma lem4853284 {A : Type'} (B : type686 A) : (term57 A B) = (term31 A B).
Proof. exact (SYM (@lem4853283 A B)). Qed.
Lemma lem4853288 {_111301 : Type'} (P : type180 _111301) (Q : type686 _111301) (R : type686 _111301) : (term58 _111301 P Q R) = (term59 _111301 P Q R).
Proof. exact (EQ_MP (@lem4845732 _111301 P Q R) (@lem4848608 _111301 P Q R)). Qed.
Lemma lem4853289 {A : Type'} (P : type180 A) (Q : type686 A) (R : type686 A) : (term58 A P Q R) = (term59 A P Q R).
Proof. exact (@lem4853288 A P Q R). Qed.
Lemma lem4853290 {A : Type'} (B : type686 A) : (term60 A B) = (term61 A B).
Proof. exact (@lem4853289 A (@ARBITRARY A) B (term62 A B)). Qed.
Lemma lem4853291 {A : Type'} (B : type686 A) (s : A -> Prop) : (term63 A B s) = (term27 A B s).
Proof. exact (eq_refl (term63 A B s)). Qed.
Lemma lem4853292 {A : Type'} (B : type686 A) (s : A -> Prop) : (term64 A B s) = (term64 A B s).
Proof. exact (eq_refl (term64 A B s)). Qed.
Lemma lem4853293 {A : Type'} (B : type686 A) (s : A -> Prop) : (term65 A B s) = (term40 A B s).
Proof. exact (MK_COMB (@lem4853292 A B s) (@lem4853291 A B s)). Qed.
Lemma lem4853294 {A : Type'} (B : type686 A) : (term66 A B) = (term37 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4853293 A B s)). Qed.
Lemma lem4853295 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853296 {A : Type'} (B : type686 A) : (term60 A B) = (term51 A B).
Proof. exact (MK_COMB (@lem4853295 A) (@lem4853294 A B)). Qed.
Lemma lem4853297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4853298 {A : Type'} (B : type686 A) : (term67 A B) = (term68 A B).
Proof. exact (MK_COMB (@lem4853297) (@lem4853296 A B)). Qed.
Lemma lem4853299 {A : Type'} (B : type686 A) (t : type686 A) : (term69 A B t) = (term70 A B t).
Proof. exact (eq_refl (term69 A B t)). Qed.
Lemma lem4853300 {A : Type'} (t : type686 A) (B : type686 A) : (term71 A t B) = (term71 A t B).
Proof. exact (eq_refl (term71 A t B)). Qed.
Lemma lem4853301 {A : Type'} (B : type686 A) (t : type686 A) : (term72 A B t) = (term73 A B t).
Proof. exact (MK_COMB (@lem4853300 A t B) (@lem4853299 A B t)). Qed.
Lemma lem4853302 {A : Type'} (B : type686 A) : (term74 A B) = (term75 A B).
Proof. exact (fun_ext (fun t : type686 A => @lem4853301 A B t)). Qed.
Lemma lem4853303 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4853304 {A : Type'} (B : type686 A) : (term61 A B) = (term76 A B).
Proof. exact (MK_COMB (@lem4853303 A) (@lem4853302 A B)). Qed.
Lemma lem4853305 {A : Type'} (B : type686 A) : ((term60 A B) = (term61 A B)) = ((term51 A B) = (term76 A B)).
Proof. exact (MK_COMB (@lem4853298 A B) (@lem4853304 A B)). Qed.
Lemma lem4853306 {A : Type'} (B : type686 A) : (term51 A B) = (term76 A B).
Proof. exact (EQ_MP (@lem4853305 A B) (@lem4853290 A B)). Qed.
Lemma lem4853316 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4853040 A s) (@lem4853039 A s)). Qed.
Lemma lem4853317 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4853316 A s). Qed.
Lemma lem4853318 {A : Type'} (t : type686 A) : (@ARBITRARY A t) = True.
Proof. exact (@lem4853317 A t). Qed.
Lemma lem4853319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853320 {A : Type'} (t : type686 A) : (term77 A t) = (and True).
Proof. exact (MK_COMB (@lem4853319) (@lem4853318 A t)). Qed.
Lemma lem4853327 {A : Type'} (t : type686 A) (B : type686 A) : (term78 A t B) = (term78 A t B).
Proof. exact (eq_refl (term78 A t B)). Qed.
Lemma lem4853328 {A : Type'} (t : type686 A) (B : type686 A) : (term79 A t B) = (term80 A t B).
Proof. exact (MK_COMB (@lem4853320 A t) (@lem4853327 A t B)). Qed.
Lemma lem4853330 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4853331 {A : Type'} (t : type686 A) (B : type686 A) : (term80 A t B) = (term78 A t B).
Proof. exact (@lem4853330 (term78 A t B)). Qed.
Lemma lem4853338 {A : Type'} (t : type686 A) (B : type686 A) : (term79 A t B) = (term78 A t B).
Proof. exact (TRANS (@lem4853328 A t B) (@lem4853331 A t B)). Qed.
Lemma lem4853339 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4853340 {A : Type'} (t : type686 A) (B : type686 A) : (term71 A t B) = (term81 A t B).
Proof. exact (MK_COMB (@lem4853339) (@lem4853338 A t B)). Qed.
Lemma lem4853355 {A : Type'} (B : type686 A) (t : type686 A) : (term70 A B t) = (term70 A B t).
Proof. exact (eq_refl (term70 A B t)). Qed.
Lemma lem4853356 {A : Type'} (B : type686 A) (t : type686 A) : (term73 A B t) = (term82 A B t).
Proof. exact (MK_COMB (@lem4853340 A t B) (@lem4853355 A B t)). Qed.
Lemma lem4853359 {A : Type'} (B : type686 A) : (term75 A B) = (term83 A B).
Proof. exact (fun_ext (fun t : type686 A => @lem4853356 A B t)). Qed.
Lemma lem4853360 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4853361 {A : Type'} (B : type686 A) : (term76 A B) = (term84 A B).
Proof. exact (MK_COMB (@lem4853360 A) (@lem4853359 A B)). Qed.
Lemma lem4853366 {A : Type'} (B : type686 A) : (term51 A B) = (term84 A B).
Proof. exact (TRANS (@lem4853306 A B) (@lem4853361 A B)). Qed.
Lemma lem4853367 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853368 {A : Type'} (B : type686 A) : (term53 A B) = (term85 A B).
Proof. exact (MK_COMB (@lem4853367) (@lem4853366 A B)). Qed.
Lemma lem4853389 {A : Type'} (B : type686 A) : (term56 A B) = (term56 A B).
Proof. exact (eq_refl (term56 A B)). Qed.
Lemma lem4853390 {A : Type'} (B : type686 A) : (term57 A B) = (term86 A B).
Proof. exact (MK_COMB (@lem4853368 A B) (@lem4853389 A B)). Qed.
Lemma lem4853393 {A : Type'} (B : type686 A) : (term86 A B) = (term57 A B).
Proof. exact (SYM (@lem4853390 A B)). Qed.
Lemma lem4853421 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4853422 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (@lem4853421 A s t). Qed.
Lemma lem4853423 {A : Type'} (u : A -> Prop) (t : type686 A) : (term88 A u t) = (term89 A u t).
Proof. exact (@lem4853422 A u (@UNIONS A t)). Qed.
Lemma lem4853430 {A : Type'} (x : A) (u : A -> Prop) : (term90 A x u) = (term90 A x u).
Proof. exact (eq_refl (term90 A x u)). Qed.
Lemma lem4853431 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term91 A x u t) = (term92 A x u t).
Proof. exact (MK_COMB (@lem4853430 A x u) (@lem4853423 A u t)). Qed.
Lemma lem4853434 {A : Type'} (u : A -> Prop) (B : type686 A) : (term93 A u B) = (term93 A u B).
Proof. exact (eq_refl (term93 A u B)). Qed.
Lemma lem4853435 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term94 A B x u t) = (term95 A B x u t).
Proof. exact (MK_COMB (@lem4853434 A u B) (@lem4853431 A x u t)). Qed.
Lemma lem4853438 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term96 A B x t) = (term97 A B x t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4853435 A B x u t)). Qed.
Lemma lem4853439 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4853440 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term98 A B x t) = (term99 A B x t).
Proof. exact (MK_COMB (@lem4853439 A) (@lem4853438 A B x t)). Qed.
Lemma lem4853445 {A : Type'} (x : A) (t : type686 A) : (term100 A x t) = (term100 A x t).
Proof. exact (eq_refl (term100 A x t)). Qed.
Lemma lem4853446 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term101 A B x t) = (term102 A B x t).
Proof. exact (MK_COMB (@lem4853445 A x t) (@lem4853440 A B x t)). Qed.
Lemma lem4853449 {A : Type'} (B : type686 A) (t : type686 A) : (term103 A B t) = (term104 A B t).
Proof. exact (fun_ext (fun x : A => @lem4853446 A B x t)). Qed.
Lemma lem4853450 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4853451 {A : Type'} (B : type686 A) (t : type686 A) : (term70 A B t) = (term105 A B t).
Proof. exact (MK_COMB (@lem4853450 A) (@lem4853449 A B t)). Qed.
Lemma lem4853456 {A : Type'} (t : type686 A) (B : type686 A) : (term81 A t B) = (term81 A t B).
Proof. exact (eq_refl (term81 A t B)). Qed.
Lemma lem4853457 {A : Type'} (B : type686 A) (t : type686 A) : (term82 A B t) = (term106 A B t).
Proof. exact (MK_COMB (@lem4853456 A t B) (@lem4853451 A B t)). Qed.
Lemma lem4853460 {A : Type'} (B : type686 A) : (term83 A B) = (term107 A B).
Proof. exact (fun_ext (fun t : type686 A => @lem4853457 A B t)). Qed.
Lemma lem4853461 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4853462 {A : Type'} (B : type686 A) : (term84 A B) = (term108 A B).
Proof. exact (MK_COMB (@lem4853461 A) (@lem4853460 A B)). Qed.
Lemma lem4853467 {A : Type'} (B : type686 A) : (term108 A B) = (term84 A B).
Proof. exact (SYM (@lem4853462 A B)). Qed.
Lemma lem4853481 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853482 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4853481 (A -> Prop) P x). Qed.
Lemma lem4853483 {A : Type'} (t : type686 A) (c : A -> Prop) : (@IN (A -> Prop) c t) = (t c).
Proof. exact (@lem4853482 A t c). Qed.
Lemma lem4853484 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4853485 {A : Type'} (t : type686 A) (c : A -> Prop) : (term109 A c t) = (term110 A t c).
Proof. exact (MK_COMB (@lem4853484) (@lem4853483 A t c)). Qed.
Lemma lem4853486 {A : Type'} (B : type686 A) (c : A -> Prop) : (B c) = (B c).
Proof. exact (eq_refl (B c)). Qed.
Lemma lem4853487 {A : Type'} (t : type686 A) (B : type686 A) (c : A -> Prop) : (term111 A t B c) = (term112 A t B c).
Proof. exact (MK_COMB (@lem4853485 A t c) (@lem4853486 A B c)). Qed.
Lemma lem4853490 {A : Type'} (t : type686 A) (B : type686 A) : (term113 A t B) = (term114 A t B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4853487 A t B c)). Qed.
Lemma lem4853491 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853492 {A : Type'} (t : type686 A) (B : type686 A) : (term78 A t B) = (term115 A t B).
Proof. exact (MK_COMB (@lem4853491 A) (@lem4853490 A t B)). Qed.
Lemma lem4853497 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4853498 {A : Type'} (t : type686 A) (B : type686 A) : (term81 A t B) = (term116 A t B).
Proof. exact (MK_COMB (@lem4853497) (@lem4853492 A t B)). Qed.
Lemma lem4853506 {A : Type'} (s : type686 A) (x : A) : (term117 A x s) = (term118 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4853507 {A : Type'} (s : type686 A) (x : A) : (term117 A x s) = (term118 A s x).
Proof. exact (@lem4853506 A s x). Qed.
Lemma lem4853508 {A : Type'} (t : type686 A) (x : A) : (term117 A x t) = (term118 A t x).
Proof. exact (@lem4853507 A t x). Qed.
Lemma lem4853516 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853517 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4853516 (A -> Prop) P x). Qed.
Lemma lem4853518 {A : Type'} (t : type686 A) (t' : A -> Prop) : (@IN (A -> Prop) t' t) = (t t').
Proof. exact (@lem4853517 A t t'). Qed.
Lemma lem4853519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853520 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term93 A t' t) = (term119 A t t').
Proof. exact (MK_COMB (@lem4853519) (@lem4853518 A t t')). Qed.
Lemma lem4853522 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853523 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4853522 A P x). Qed.
Lemma lem4853524 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4853523 A t x). Qed.
Lemma lem4853525 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term120 A t x t') = (term121 A t t' x).
Proof. exact (MK_COMB (@lem4853520 A t t') (@lem4853524 A t' x)). Qed.
Lemma lem4853528 {A : Type'} (t : type686 A) (x : A) : (term122 A t x) = (term123 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4853525 A t t' x)). Qed.
Lemma lem4853529 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4853530 {A : Type'} (t : type686 A) (x : A) : (term118 A t x) = (term124 A t x).
Proof. exact (MK_COMB (@lem4853529 A) (@lem4853528 A t x)). Qed.
Lemma lem4853535 {A : Type'} (t : type686 A) (x : A) : (term117 A x t) = (term124 A t x).
Proof. exact (TRANS (@lem4853508 A t x) (@lem4853530 A t x)). Qed.
Lemma lem4853536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4853537 {A : Type'} (t : type686 A) (x : A) : (term100 A x t) = (term125 A t x).
Proof. exact (MK_COMB (@lem4853536) (@lem4853535 A t x)). Qed.
Lemma lem4853545 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853546 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4853545 (A -> Prop) P x). Qed.
Lemma lem4853547 {A : Type'} (B : type686 A) (u : A -> Prop) : (@IN (A -> Prop) u B) = (B u).
Proof. exact (@lem4853546 A B u). Qed.
Lemma lem4853548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853549 {A : Type'} (B : type686 A) (u : A -> Prop) : (term93 A u B) = (term119 A B u).
Proof. exact (MK_COMB (@lem4853548) (@lem4853547 A B u)). Qed.
Lemma lem4853553 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853554 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4853553 A P x). Qed.
Lemma lem4853555 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem4853554 A u x). Qed.
Lemma lem4853556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853557 {A : Type'} (u : A -> Prop) (x : A) : (term90 A x u) = (term126 A u x).
Proof. exact (MK_COMB (@lem4853556) (@lem4853555 A u x)). Qed.
Lemma lem4853565 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853566 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4853565 A P x). Qed.
Lemma lem4853567 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem4853566 A u x). Qed.
Lemma lem4853568 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4853569 {A : Type'} (u : A -> Prop) (x : A) : (term127 A x u) = (term128 A u x).
Proof. exact (MK_COMB (@lem4853568) (@lem4853567 A u x)). Qed.
Lemma lem4853571 {A : Type'} (s : type686 A) (x : A) : (term117 A x s) = (term118 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4853572 {A : Type'} (s : type686 A) (x : A) : (term117 A x s) = (term118 A s x).
Proof. exact (@lem4853571 A s x). Qed.
Lemma lem4853573 {A : Type'} (t : type686 A) (x : A) : (term117 A x t) = (term118 A t x).
Proof. exact (@lem4853572 A t x). Qed.
Lemma lem4853581 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853582 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4853581 (A -> Prop) P x). Qed.
Lemma lem4853583 {A : Type'} (t : type686 A) (t' : A -> Prop) : (@IN (A -> Prop) t' t) = (t t').
Proof. exact (@lem4853582 A t t'). Qed.
Lemma lem4853584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4853585 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term93 A t' t) = (term119 A t t').
Proof. exact (MK_COMB (@lem4853584) (@lem4853583 A t t')). Qed.
Lemma lem4853587 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4853588 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4853587 A P x). Qed.
Lemma lem4853589 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4853588 A t x). Qed.
Lemma lem4853590 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term120 A t x t') = (term121 A t t' x).
Proof. exact (MK_COMB (@lem4853585 A t t') (@lem4853589 A t' x)). Qed.
Lemma lem4853593 {A : Type'} (t : type686 A) (x : A) : (term122 A t x) = (term123 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4853590 A t t' x)). Qed.
Lemma lem4853594 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4853595 {A : Type'} (t : type686 A) (x : A) : (term118 A t x) = (term124 A t x).
Proof. exact (MK_COMB (@lem4853594 A) (@lem4853593 A t x)). Qed.
Lemma lem4853600 {A : Type'} (t : type686 A) (x : A) : (term117 A x t) = (term124 A t x).
Proof. exact (TRANS (@lem4853573 A t x) (@lem4853595 A t x)). Qed.
Lemma lem4853601 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term129 A u x t) = (term130 A u t x).
Proof. exact (MK_COMB (@lem4853569 A u x) (@lem4853600 A t x)). Qed.
Lemma lem4853604 {A : Type'} (u : A -> Prop) (t : type686 A) : (term131 A u t) = (term132 A u t).
Proof. exact (fun_ext (fun x : A => @lem4853601 A u t x)). Qed.
Lemma lem4853605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4853606 {A : Type'} (u : A -> Prop) (t : type686 A) : (term89 A u t) = (term133 A u t).
Proof. exact (MK_COMB (@lem4853605 A) (@lem4853604 A u t)). Qed.
Lemma lem4853611 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term92 A x u t) = (term134 A x u t).
Proof. exact (MK_COMB (@lem4853557 A u x) (@lem4853606 A u t)). Qed.
Lemma lem4853614 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term95 A B x u t) = (term135 A B x u t).
Proof. exact (MK_COMB (@lem4853549 A B u) (@lem4853611 A x u t)). Qed.
Lemma lem4853617 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term97 A B x t) = (term136 A B x t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4853614 A B x u t)). Qed.
Lemma lem4853618 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4853619 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term99 A B x t) = (term137 A B x t).
Proof. exact (MK_COMB (@lem4853618 A) (@lem4853617 A B x t)). Qed.
Lemma lem4853624 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term102 A B x t) = (term138 A B x t).
Proof. exact (MK_COMB (@lem4853537 A t x) (@lem4853619 A B x t)). Qed.
Lemma lem4853627 {A : Type'} (B : type686 A) (t : type686 A) : (term104 A B t) = (term139 A B t).
Proof. exact (fun_ext (fun x : A => @lem4853624 A B x t)). Qed.
Lemma lem4853628 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4853629 {A : Type'} (B : type686 A) (t : type686 A) : (term105 A B t) = (term140 A B t).
Proof. exact (MK_COMB (@lem4853628 A) (@lem4853627 A B t)). Qed.
Lemma lem4853634 {A : Type'} (B : type686 A) (t : type686 A) : (term106 A B t) = (term141 A B t).
Proof. exact (MK_COMB (@lem4853498 A t B) (@lem4853629 A B t)). Qed.
Lemma lem4853637 {A : Type'} (B : type686 A) : (term107 A B) = (term142 A B).
Proof. exact (fun_ext (fun t : type686 A => @lem4853634 A B t)). Qed.
Lemma lem4853638 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4853639 {A : Type'} (B : type686 A) : (term108 A B) = (term143 A B).
Proof. exact (MK_COMB (@lem4853638 A) (@lem4853637 A B)). Qed.
Lemma lem4853644 {A : Type'} (B : type686 A) : (term143 A B) = (term108 A B).
Proof. exact (SYM (@lem4853639 A B)). Qed.
Lemma lem4853646 (p : Prop) : p = (term144 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4853647 {A : Type'} (B : type686 A) : (term143 A B) = (term145 A B).
Proof. exact (@lem4853646 (term143 A B)). Qed.
Lemma lem4853648 {A : Type'} (B : type686 A) : (term145 A B) = (term143 A B).
Proof. exact (SYM (@lem4853647 A B)). Qed.
Lemma lem4853649 {A : Type'} (B : type686 A) (h1 : term146 A B) : term146 A B.
Proof. exact (h1). Qed.
Lemma lem4853652 {A : Type'} (B : type686 A) (h1 : term145 A B) : term145 A B.
Proof. exact (h1). Qed.
Lemma lem4853653 {A : Type'} (B : type686 A) : term147 A B.
Proof. exact (fun h0 : term145 A B => @lem4853652 A B h0). Qed.
Lemma lem4853654 {A : Type'} (B : type686 A) (h1 : term147 A B) : term147 A B.
Proof. exact (h1). Qed.
Lemma lem4853655 {A : Type'} (B : type686 A) (h1 : term145 A B) : term145 A B.
Proof. exact (h1). Qed.
Lemma lem4853656 {A : Type'} (B : type686 A) (h1 : term145 A B) (h2 : term147 A B) : term145 A B.
Proof. exact (@lem4853654 A B h2 (@lem4853655 A B h1)). Qed.
Lemma lem4853657 {A : Type'} (B : type686 A) (h1 : term145 A B) : term148 A B.
Proof. exact (fun h0 : term147 A B => @lem4853656 A B h1 h0). Qed.
Lemma lem4853658 {A : Type'} (B : type686 A) (h1 : term147 A B) : term147 A B.
Proof. exact (h1). Qed.
Lemma lem4853659 {A : Type'} (B : type686 A) (h1 : term145 A B) (h2 : term147 A B) : term145 A B.
Proof. exact (@lem4853657 A B h1 (@lem4853658 A B h2)). Qed.
Lemma lem4853660 {A : Type'} (B : type686 A) (h1 : term147 A B) : term147 A B.
Proof. exact (fun h0 : term145 A B => @lem4853659 A B h0 h1). Qed.
Lemma lem4853661 {A : Type'} (B : type686 A) : term149 A B.
Proof. exact (fun h0 : term147 A B => @lem4853660 A B h0). Qed.
Lemma lem4853664 {A : Type'} (B : type686 A) : term147 A B.
Proof. exact (@lem4853661 A B (@lem4853653 A B)). Qed.
Lemma lem4853665 {A : Type'} (B : type686 A) : term147 A B.
Proof. exact (@lem4853664 A B). Qed.
Lemma lem4853671 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4853672 {A : Type'} (B : type686 A) : (term145 A B) = (term150 A B).
Proof. exact (@lem4853671 (term146 A B)). Qed.
Lemma lem4853674 (t : Prop) : (term151 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4853675 {A : Type'} (B : type686 A) : (term150 A B) = (term143 A B).
Proof. exact (@lem4853674 (term143 A B)). Qed.
Lemma lem4853680 {A : Type'} (B : type686 A) : (term145 A B) = (term143 A B).
Proof. exact (TRANS (@lem4853672 A B) (@lem4853675 A B)). Qed.
Lemma lem4853793 {A : Type'} : (term152 A) = (term153 A).
Proof. exact (fun_ext (fun B : type686 A => @lem4853680 A B)). Qed.
Lemma lem4853794 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4853803 {A : Type'} : (term154 A) = (term155 A).
Proof. exact (MK_COMB (@lem4853794 A) (@lem4853793 A)). Qed.
Lemma lem4853808 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term121 A t t' x) = (term121 A t t' x).
Proof. exact (eq_refl (term121 A t t' x)). Qed.
Lemma lem4853809 {A : Type'} (t : type686 A) (x : A) : (term123 A t x) = (term123 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4853808 A t t' x)). Qed.
Lemma lem4853810 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4853811 {A : Type'} (t : type686 A) (x : A) : (term124 A t x) = (term124 A t x).
Proof. exact (MK_COMB (@lem4853810 A) (@lem4853809 A t x)). Qed.
Lemma lem4853814 {A : Type'} (u : A -> Prop) (x : A) : (term128 A u x) = (term128 A u x).
Proof. exact (eq_refl (term128 A u x)). Qed.
Lemma lem4853815 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term130 A u t x) = (term130 A u t x).
Proof. exact (MK_COMB (@lem4853814 A u x) (@lem4853811 A t x)). Qed.
Lemma lem4853816 {A : Type'} (u : A -> Prop) (t : type686 A) : (term132 A u t) = (term132 A u t).
Proof. exact (fun_ext (fun x : A => @lem4853815 A u t x)). Qed.
Lemma lem4853817 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4853818 {A : Type'} (u : A -> Prop) (t : type686 A) : (term133 A u t) = (term133 A u t).
Proof. exact (MK_COMB (@lem4853817 A) (@lem4853816 A u t)). Qed.
Lemma lem4853821 {A : Type'} (u : A -> Prop) (x : A) : (term126 A u x) = (term126 A u x).
Proof. exact (eq_refl (term126 A u x)). Qed.
Lemma lem4853822 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term134 A x u t) = (term134 A x u t).
Proof. exact (MK_COMB (@lem4853821 A u x) (@lem4853818 A u t)). Qed.
Lemma lem4853825 {A : Type'} (B : type686 A) (u : A -> Prop) : (term119 A B u) = (term119 A B u).
Proof. exact (eq_refl (term119 A B u)). Qed.
Lemma lem4853826 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term135 A B x u t) = (term135 A B x u t).
Proof. exact (MK_COMB (@lem4853825 A B u) (@lem4853822 A x u t)). Qed.
Lemma lem4853827 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term136 A B x t) = (term136 A B x t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4853826 A B x u t)). Qed.
Lemma lem4853828 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4853829 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term137 A B x t) = (term137 A B x t).
Proof. exact (MK_COMB (@lem4853828 A) (@lem4853827 A B x t)). Qed.
Lemma lem4853834 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term121 A t t' x) = (term121 A t t' x).
Proof. exact (eq_refl (term121 A t t' x)). Qed.
Lemma lem4853835 {A : Type'} (t : type686 A) (x : A) : (term123 A t x) = (term123 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4853834 A t t' x)). Qed.
Lemma lem4853836 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4853837 {A : Type'} (t : type686 A) (x : A) : (term124 A t x) = (term124 A t x).
Proof. exact (MK_COMB (@lem4853836 A) (@lem4853835 A t x)). Qed.
Lemma lem4853838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4853839 {A : Type'} (t : type686 A) (x : A) : (term125 A t x) = (term125 A t x).
Proof. exact (MK_COMB (@lem4853838) (@lem4853837 A t x)). Qed.
Lemma lem4853840 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term138 A B x t) = (term138 A B x t).
Proof. exact (MK_COMB (@lem4853839 A t x) (@lem4853829 A B x t)). Qed.
Lemma lem4853841 {A : Type'} (B : type686 A) (t : type686 A) : (term139 A B t) = (term139 A B t).
Proof. exact (fun_ext (fun x : A => @lem4853840 A B x t)). Qed.
Lemma lem4853842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4853843 {A : Type'} (B : type686 A) (t : type686 A) : (term140 A B t) = (term140 A B t).
Proof. exact (MK_COMB (@lem4853842 A) (@lem4853841 A B t)). Qed.
Lemma lem4853848 {A : Type'} (t : type686 A) (B : type686 A) (c : A -> Prop) : (term112 A t B c) = (term112 A t B c).
Proof. exact (eq_refl (term112 A t B c)). Qed.
Lemma lem4853849 {A : Type'} (t : type686 A) (B : type686 A) : (term114 A t B) = (term114 A t B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4853848 A t B c)). Qed.
Lemma lem4853850 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853851 {A : Type'} (t : type686 A) (B : type686 A) : (term115 A t B) = (term115 A t B).
Proof. exact (MK_COMB (@lem4853850 A) (@lem4853849 A t B)). Qed.
Lemma lem4853852 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4853853 {A : Type'} (t : type686 A) (B : type686 A) : (term116 A t B) = (term116 A t B).
Proof. exact (MK_COMB (@lem4853852) (@lem4853851 A t B)). Qed.
Lemma lem4853854 {A : Type'} (B : type686 A) (t : type686 A) : (term141 A B t) = (term141 A B t).
Proof. exact (MK_COMB (@lem4853853 A t B) (@lem4853843 A B t)). Qed.
Lemma lem4853855 {A : Type'} (B : type686 A) : (term142 A B) = (term142 A B).
Proof. exact (fun_ext (fun t : type686 A => @lem4853854 A B t)). Qed.
Lemma lem4853856 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4853857 {A : Type'} (B : type686 A) : (term143 A B) = (term143 A B).
Proof. exact (MK_COMB (@lem4853856 A) (@lem4853855 A B)). Qed.
Lemma lem4853858 {A : Type'} : (term153 A) = (term153 A).
Proof. exact (fun_ext (fun B : type686 A => @lem4853857 A B)). Qed.
Lemma lem4853859 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4853860 {A : Type'} : (term155 A) = (term155 A).
Proof. exact (MK_COMB (@lem4853859 A) (@lem4853858 A)). Qed.
Lemma lem4853927 {A : Type'} : (term154 A) = (term155 A).
Proof. exact (TRANS (@lem4853803 A) (@lem4853860 A)). Qed.
Lemma lem4853928 {A : Type'} : (term155 A) = (term154 A).
Proof. exact (SYM (@lem4853927 A)). Qed.
Lemma lem4853929 {A : Type'} (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term115 A t B.
Proof. exact (h1). Qed.
Lemma lem4853930 {A : Type'} (t : type686 A) (x : A) (h1 : term124 A t x) : term124 A t x.
Proof. exact (h1). Qed.
Lemma lem4853932 (p : Prop) : p = (term144 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4853933 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term137 A B x t) = (term156 A B x t).
Proof. exact (@lem4853932 (term137 A B x t)). Qed.
Lemma lem4853934 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term156 A B x t) = (term137 A B x t).
Proof. exact (SYM (@lem4853933 A B x t)). Qed.
Lemma lem4853935 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (h1 : term157 A B x t) : term157 A B x t.
Proof. exact (h1). Qed.
Lemma lem4853942 {A : Type'} (t : type686 A) (B : type686 A) (c : A -> Prop) : (term112 A t B c) = (term158 A t B c).
Proof. exact (@lem17265 (t c) (B c)). Qed.
Lemma lem4853943 {A : Type'} (t : type686 A) (B : type686 A) : (term114 A t B) = (term159 A t B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4853942 A t B c)). Qed.
Lemma lem4853944 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4853981 {A : Type'} (t : type686 A) (B : type686 A) : (term115 A t B) = (term160 A t B).
Proof. exact (MK_COMB (@lem4853944 A) (@lem4853943 A t B)). Qed.
Lemma lem4853982 {A : Type'} (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term160 A t B.
Proof. exact (EQ_MP (@lem4853981 A t B) (@lem4853929 A t B h1)). Qed.
Lemma lem4853987 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term121 A t t' x) = (term121 A t t' x).
Proof. exact (eq_refl (term121 A t t' x)). Qed.
Lemma lem4853988 {A : Type'} (t : type686 A) (x : A) : (term123 A t x) = (term123 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4853987 A t t' x)). Qed.
Lemma lem4853989 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4854022 {A : Type'} (t : type686 A) (x : A) : (term124 A t x) = (term124 A t x).
Proof. exact (MK_COMB (@lem4853989 A) (@lem4853988 A t x)). Qed.
Lemma lem4854023 {A : Type'} (t : type686 A) (x : A) (h1 : term124 A t x) : term124 A t x.
Proof. exact (EQ_MP (@lem4854022 A t x) (@lem4853930 A t x h1)). Qed.
Lemma lem4854033 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term161 A t t' x) = (term162 A t t' x).
Proof. exact (@lem17045 (t t') (t' x)). Qed.
Lemma lem4854034 {A : Type'} (P : type686 A) : (term163 A P) = (term164 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4854035 {A : Type'} (t : type686 A) (x : A) : (term165 A t x) = (term166 A t x).
Proof. exact (@lem4854034 A (term123 A t x)). Qed.
Lemma lem4854036 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term167 A t x t') = (term121 A t t' x).
Proof. exact (eq_refl (term167 A t x t')). Qed.
Lemma lem4854037 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854038 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term168 A t x t') = (term161 A t t' x).
Proof. exact (MK_COMB (@lem4854037) (@lem4854036 A t t' x)). Qed.
Lemma lem4854039 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term168 A t x t') = (term162 A t t' x).
Proof. exact (TRANS (@lem4854038 A t t' x) (@lem4854033 A t t' x)). Qed.
Lemma lem4854040 {A : Type'} (t : type686 A) (x : A) : (term169 A t x) = (term170 A t x).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854039 A t t' x)). Qed.
Lemma lem4854041 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854042 {A : Type'} (t : type686 A) (x : A) : (term166 A t x) = (term171 A t x).
Proof. exact (MK_COMB (@lem4854041 A) (@lem4854040 A t x)). Qed.
Lemma lem4854043 {A : Type'} (t : type686 A) (x : A) : (term165 A t x) = (term171 A t x).
Proof. exact (TRANS (@lem4854035 A t x) (@lem4854042 A t x)). Qed.
Lemma lem4854045 {A : Type'} (u : A -> Prop) (x : A) : (term126 A u x) = (term126 A u x).
Proof. exact (eq_refl (term126 A u x)). Qed.
Lemma lem4854046 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term172 A u t x) = (term173 A u t x).
Proof. exact (MK_COMB (@lem4854045 A u x) (@lem4854043 A t x)). Qed.
Lemma lem4854047 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term174 A u t x) = (term172 A u t x).
Proof. exact (@lem17362 (u x) (term124 A t x)). Qed.
Lemma lem4854048 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term174 A u t x) = (term173 A u t x).
Proof. exact (TRANS (@lem4854047 A u t x) (@lem4854046 A u t x)). Qed.
Lemma lem4854049 {A : Type'} (P : A -> Prop) : (term175 A P) = (term176 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4854050 {A : Type'} (u : A -> Prop) (t : type686 A) : (term177 A u t) = (term178 A u t).
Proof. exact (@lem4854049 A (term132 A u t)). Qed.
Lemma lem4854051 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term179 A u t x) = (term130 A u t x).
Proof. exact (eq_refl (term179 A u t x)). Qed.
Lemma lem4854052 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854053 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term180 A u t x) = (term174 A u t x).
Proof. exact (MK_COMB (@lem4854052) (@lem4854051 A u t x)). Qed.
Lemma lem4854054 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term180 A u t x) = (term173 A u t x).
Proof. exact (TRANS (@lem4854053 A u t x) (@lem4854048 A u t x)). Qed.
Lemma lem4854055 {A : Type'} (u : A -> Prop) (t : type686 A) : (term181 A u t) = (term182 A u t).
Proof. exact (fun_ext (fun x : A => @lem4854054 A u t x)). Qed.
Lemma lem4854056 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4854057 {A : Type'} (u : A -> Prop) (t : type686 A) : (term178 A u t) = (term183 A u t).
Proof. exact (MK_COMB (@lem4854056 A) (@lem4854055 A u t)). Qed.
Lemma lem4854058 {A : Type'} (u : A -> Prop) (t : type686 A) : (term177 A u t) = (term183 A u t).
Proof. exact (TRANS (@lem4854050 A u t) (@lem4854057 A u t)). Qed.
Lemma lem4854060 {A : Type'} (u : A -> Prop) (x : A) : (term184 A u x) = (term184 A u x).
Proof. exact (eq_refl (term184 A u x)). Qed.
Lemma lem4854061 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term185 A x u t) = (term186 A x u t).
Proof. exact (MK_COMB (@lem4854060 A u x) (@lem4854058 A u t)). Qed.
Lemma lem4854062 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term187 A x u t) = (term185 A x u t).
Proof. exact (@lem17045 (u x) (term133 A u t)). Qed.
Lemma lem4854063 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term187 A x u t) = (term186 A x u t).
Proof. exact (TRANS (@lem4854062 A x u t) (@lem4854061 A x u t)). Qed.
Lemma lem4854065 {A : Type'} (B : type686 A) (u : A -> Prop) : (term188 A B u) = (term188 A B u).
Proof. exact (eq_refl (term188 A B u)). Qed.
Lemma lem4854066 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term189 A B x u t) = (term190 A B x u t).
Proof. exact (MK_COMB (@lem4854065 A B u) (@lem4854063 A x u t)). Qed.
Lemma lem4854067 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term191 A B x u t) = (term189 A B x u t).
Proof. exact (@lem17045 (B u) (term134 A x u t)). Qed.
Lemma lem4854068 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term191 A B x u t) = (term190 A B x u t).
Proof. exact (TRANS (@lem4854067 A B x u t) (@lem4854066 A B x u t)). Qed.
Lemma lem4854069 {A : Type'} (P : type686 A) : (term163 A P) = (term164 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4854070 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term157 A B x t) = (term192 A B x t).
Proof. exact (@lem4854069 A (term136 A B x t)). Qed.
Lemma lem4854071 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term193 A B x t u) = (term135 A B x u t).
Proof. exact (eq_refl (term193 A B x t u)). Qed.
Lemma lem4854072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854073 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term194 A B x t u) = (term191 A B x u t).
Proof. exact (MK_COMB (@lem4854072) (@lem4854071 A B x u t)). Qed.
Lemma lem4854074 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term194 A B x t u) = (term190 A B x u t).
Proof. exact (TRANS (@lem4854073 A B x u t) (@lem4854068 A B x u t)). Qed.
Lemma lem4854075 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term195 A B x t) = (term196 A B x t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4854074 A B x u t)). Qed.
Lemma lem4854076 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854077 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term192 A B x t) = (term197 A B x t).
Proof. exact (MK_COMB (@lem4854076 A) (@lem4854075 A B x t)). Qed.
Lemma lem4854078 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term157 A B x t) = (term197 A B x t).
Proof. exact (TRANS (@lem4854070 A B x t) (@lem4854077 A B x t)). Qed.
Lemma lem4854205 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4854206 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (@lem4854205 A P Q). Qed.
Lemma lem4854207 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term200 A x u t) = (term201 A x u t).
Proof. exact (@lem4854206 A (term202 A u x) (term182 A u t)). Qed.
Lemma lem4854208 {A : Type'} (u : A -> Prop) (t : type686 A) (x : A) : (term203 A u t x) = (term173 A u t x).
Proof. exact (eq_refl (term203 A u t x)). Qed.
Lemma lem4854209 {A : Type'} (u : A -> Prop) (t : type686 A) : (term204 A u t) = (term182 A u t).
Proof. exact (fun_ext (fun x : A => @lem4854208 A u t x)). Qed.
Lemma lem4854210 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4854211 {A : Type'} (u : A -> Prop) (t : type686 A) : (term205 A u t) = (term183 A u t).
Proof. exact (MK_COMB (@lem4854210 A) (@lem4854209 A u t)). Qed.
Lemma lem4854212 {A : Type'} (u : A -> Prop) (x : A) : (term184 A u x) = (term184 A u x).
Proof. exact (eq_refl (term184 A u x)). Qed.
Lemma lem4854213 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term200 A x u t) = (term186 A x u t).
Proof. exact (MK_COMB (@lem4854212 A u x) (@lem4854211 A u t)). Qed.
Lemma lem4854214 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854215 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term206 A x u t) = (term207 A x u t).
Proof. exact (MK_COMB (@lem4854214) (@lem4854213 A x u t)). Qed.
Lemma lem4854216 {A : Type'} (u : A -> Prop) (t : type686 A) (x' : A) : (term203 A u t x') = (term173 A u t x').
Proof. exact (eq_refl (term203 A u t x')). Qed.
Lemma lem4854217 {A : Type'} (u : A -> Prop) (x : A) : (term184 A u x) = (term184 A u x).
Proof. exact (eq_refl (term184 A u x)). Qed.
Lemma lem4854218 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) (x' : A) : (term208 A x u t x') = (term209 A x u t x').
Proof. exact (MK_COMB (@lem4854217 A u x) (@lem4854216 A u t x')). Qed.
Lemma lem4854219 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term210 A x u t) = (term211 A x u t).
Proof. exact (fun_ext (fun x' : A => @lem4854218 A x u t x')). Qed.
Lemma lem4854220 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4854221 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term201 A x u t) = (term212 A x u t).
Proof. exact (MK_COMB (@lem4854220 A) (@lem4854219 A x u t)). Qed.
Lemma lem4854222 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : ((term200 A x u t) = (term201 A x u t)) = ((term186 A x u t) = (term212 A x u t)).
Proof. exact (MK_COMB (@lem4854215 A x u t) (@lem4854221 A x u t)). Qed.
Lemma lem4854223 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term186 A x u t) = (term212 A x u t).
Proof. exact (EQ_MP (@lem4854222 A x u t) (@lem4854207 A x u t)). Qed.
Lemma lem4854224 {A : Type'} (B : type686 A) (u : A -> Prop) : (term188 A B u) = (term188 A B u).
Proof. exact (eq_refl (term188 A B u)). Qed.
Lemma lem4854225 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term190 A B x u t) = (term213 A B x u t).
Proof. exact (MK_COMB (@lem4854224 A B u) (@lem4854223 A x u t)). Qed.
Lemma lem4854227 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4854228 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (@lem4854227 A P Q). Qed.
Lemma lem4854229 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term214 A B x u t) = (term215 A B x u t).
Proof. exact (@lem4854228 A (term216 A B u) (term211 A x u t)). Qed.
Lemma lem4854230 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) (x' : A) : (term217 A x u t x') = (term209 A x u t x').
Proof. exact (eq_refl (term217 A x u t x')). Qed.
Lemma lem4854231 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term218 A x u t) = (term211 A x u t).
Proof. exact (fun_ext (fun x' : A => @lem4854230 A x u t x')). Qed.
Lemma lem4854232 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4854233 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) : (term219 A x u t) = (term212 A x u t).
Proof. exact (MK_COMB (@lem4854232 A) (@lem4854231 A x u t)). Qed.
Lemma lem4854234 {A : Type'} (B : type686 A) (u : A -> Prop) : (term188 A B u) = (term188 A B u).
Proof. exact (eq_refl (term188 A B u)). Qed.
Lemma lem4854235 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term214 A B x u t) = (term213 A B x u t).
Proof. exact (MK_COMB (@lem4854234 A B u) (@lem4854233 A x u t)). Qed.
Lemma lem4854236 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854237 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term220 A B x u t) = (term221 A B x u t).
Proof. exact (MK_COMB (@lem4854236) (@lem4854235 A B x u t)). Qed.
Lemma lem4854238 {A : Type'} (x : A) (u : A -> Prop) (t : type686 A) (x' : A) : (term217 A x u t x') = (term209 A x u t x').
Proof. exact (eq_refl (term217 A x u t x')). Qed.
Lemma lem4854239 {A : Type'} (B : type686 A) (u : A -> Prop) : (term188 A B u) = (term188 A B u).
Proof. exact (eq_refl (term188 A B u)). Qed.
Lemma lem4854240 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) (x' : A) : (term222 A B x u t x') = (term223 A B x u t x').
Proof. exact (MK_COMB (@lem4854239 A B u) (@lem4854238 A x u t x')). Qed.
Lemma lem4854241 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term224 A B x u t) = (term225 A B x u t).
Proof. exact (fun_ext (fun x' : A => @lem4854240 A B x u t x')). Qed.
Lemma lem4854242 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4854243 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term215 A B x u t) = (term226 A B x u t).
Proof. exact (MK_COMB (@lem4854242 A) (@lem4854241 A B x u t)). Qed.
Lemma lem4854244 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : ((term214 A B x u t) = (term215 A B x u t)) = ((term213 A B x u t) = (term226 A B x u t)).
Proof. exact (MK_COMB (@lem4854237 A B x u t) (@lem4854243 A B x u t)). Qed.
Lemma lem4854245 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term213 A B x u t) = (term226 A B x u t).
Proof. exact (EQ_MP (@lem4854244 A B x u t) (@lem4854229 A B x u t)). Qed.
Lemma lem4854246 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term190 A B x u t) = (term226 A B x u t).
Proof. exact (TRANS (@lem4854225 A B x u t) (@lem4854245 A B x u t)). Qed.
Lemma lem4854247 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term196 A B x t) = (term227 A B x t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4854246 A B x u t)). Qed.
Lemma lem4854248 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854249 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term197 A B x t) = (term228 A B x t).
Proof. exact (MK_COMB (@lem4854248 A) (@lem4854247 A B x t)). Qed.
Lemma lem4854251 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4854252 {A : Type'} (P : type672 A) : (term231 A P) = (term232 A P).
Proof. exact (@lem4854251 (A -> Prop) A P). Qed.
Lemma lem4854253 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term233 A B x t) = (term234 A B x t).
Proof. exact (@lem4854252 A (term235 A B x t)). Qed.
Lemma lem4854254 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term236 A B x t u) = (term225 A B x u t).
Proof. exact (eq_refl (term236 A B x t u)). Qed.
Lemma lem4854255 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4854256 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) (x' : A) : (term237 A B x t u x') = (term238 A B x u t x').
Proof. exact (MK_COMB (@lem4854254 A B x u t) (@lem4854255 A x')). Qed.
Lemma lem4854257 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) (x' : A) : (term238 A B x u t x') = (term223 A B x u t x').
Proof. exact (eq_refl (term238 A B x u t x')). Qed.
Lemma lem4854258 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) (x' : A) : (term237 A B x t u x') = (term223 A B x u t x').
Proof. exact (TRANS (@lem4854256 A B x u t x') (@lem4854257 A B x u t x')). Qed.
Lemma lem4854259 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term239 A B x t u) = (term225 A B x u t).
Proof. exact (fun_ext (fun x' : A => @lem4854258 A B x u t x')). Qed.
Lemma lem4854260 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4854261 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term240 A B x t u) = (term226 A B x u t).
Proof. exact (MK_COMB (@lem4854260 A) (@lem4854259 A B x u t)). Qed.
Lemma lem4854262 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term241 A B x t) = (term227 A B x t).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4854261 A B x u t)). Qed.
Lemma lem4854263 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854264 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term233 A B x t) = (term228 A B x t).
Proof. exact (MK_COMB (@lem4854263 A) (@lem4854262 A B x t)). Qed.
Lemma lem4854265 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854266 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term242 A B x t) = (term243 A B x t).
Proof. exact (MK_COMB (@lem4854265) (@lem4854264 A B x t)). Qed.
Lemma lem4854267 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (t : type686 A) : (term236 A B x t u) = (term225 A B x u t).
Proof. exact (eq_refl (term236 A B x t u)). Qed.
Lemma lem4854268 {A : Type'} (x' : type684 A) (u : A -> Prop) : (x' u) = (x' u).
Proof. exact (eq_refl (x' u)). Qed.
Lemma lem4854269 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term244 A B x t x' u) = (term245 A B x t x' u).
Proof. exact (MK_COMB (@lem4854267 A B x u t) (@lem4854268 A x' u)). Qed.
Lemma lem4854270 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term245 A B x t x' u) = (term246 A B x t x' u).
Proof. exact (eq_refl (term245 A B x t x' u)). Qed.
Lemma lem4854271 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term244 A B x t x' u) = (term246 A B x t x' u).
Proof. exact (TRANS (@lem4854269 A B x t x' u) (@lem4854270 A B x t x' u)). Qed.
Lemma lem4854272 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term247 A B x t x') = (term248 A B x t x').
Proof. exact (fun_ext (fun u : A -> Prop => @lem4854271 A B x t x' u)). Qed.
Lemma lem4854273 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854274 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term249 A B x t x') = (term250 A B x t x').
Proof. exact (MK_COMB (@lem4854273 A) (@lem4854272 A B x t x')). Qed.
Lemma lem4854275 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term251 A B x t) = (term252 A B x t).
Proof. exact (fun_ext (fun x' : type684 A => @lem4854274 A B x t x')). Qed.
Lemma lem4854276 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4854277 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term234 A B x t) = (term253 A B x t).
Proof. exact (MK_COMB (@lem4854276 A) (@lem4854275 A B x t)). Qed.
Lemma lem4854278 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : ((term233 A B x t) = (term234 A B x t)) = ((term228 A B x t) = (term253 A B x t)).
Proof. exact (MK_COMB (@lem4854266 A B x t) (@lem4854277 A B x t)). Qed.
Lemma lem4854279 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term228 A B x t) = (term253 A B x t).
Proof. exact (EQ_MP (@lem4854278 A B x t) (@lem4854253 A B x t)). Qed.
Lemma lem4854281 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term197 A B x t) = (term253 A B x t).
Proof. exact (TRANS (@lem4854249 A B x t) (@lem4854279 A B x t)). Qed.
Lemma lem4854282 {A : Type'} (B : type686 A) (x : A) (t : type686 A) : (term157 A B x t) = (term253 A B x t).
Proof. exact (TRANS (@lem4854078 A B x t) (@lem4854281 A B x t)). Qed.
Lemma lem4854283 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (h1 : term157 A B x t) : term253 A B x t.
Proof. exact (EQ_MP (@lem4854282 A B x t) (@lem4853935 A B x t h1)). Qed.
Lemma lem4854284 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term250 A B x t x'.
Proof. exact (h1). Qed.
Lemma lem4854285 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : term121 A t t' x.
Proof. exact (h1). Qed.
Lemma lem4854290 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854291 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4854290 (A -> Prop) Prop f x). Qed.
Lemma lem4854293 {A : Type'} (B : type686 A) (c : A -> Prop) : (B c) = (@I ((A -> Prop) -> Prop) B c).
Proof. exact (@lem4854291 A B c). Qed.
Lemma lem4854294 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854299 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854300 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4854299 (A -> Prop) Prop f x). Qed.
Lemma lem4854302 {A : Type'} (t : type686 A) (c : A -> Prop) : (t c) = (@I ((A -> Prop) -> Prop) t c).
Proof. exact (@lem4854300 A t c). Qed.
Lemma lem4854303 {A : Type'} (t : type686 A) (c : A -> Prop) : (term216 A t c) = (term254 A t c).
Proof. exact (MK_COMB (@lem4854294) (@lem4854302 A t c)). Qed.
Lemma lem4854304 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4854305 {A : Type'} (t : type686 A) (c : A -> Prop) : (term188 A t c) = (term255 A t c).
Proof. exact (MK_COMB (@lem4854304) (@lem4854303 A t c)). Qed.
Lemma lem4854306 {A : Type'} (t : type686 A) (B : type686 A) (c : A -> Prop) : (term158 A t B c) = (term256 A t B c).
Proof. exact (MK_COMB (@lem4854305 A t c) (@lem4854293 A B c)). Qed.
Lemma lem4854307 {A : Type'} (t : type686 A) (B : type686 A) : (term159 A t B) = (term257 A t B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4854306 A t B c)). Qed.
Lemma lem4854308 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854309 {A : Type'} (t : type686 A) (B : type686 A) : (term160 A t B) = (term258 A t B).
Proof. exact (MK_COMB (@lem4854308 A) (@lem4854307 A t B)). Qed.
Lemma lem4854310 {A : Type'} (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term258 A t B.
Proof. exact (EQ_MP (@lem4854309 A t B) (@lem4853982 A t B h1)). Qed.
Lemma lem4854311 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854312 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4854317 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854318 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4854317 (A -> Prop) A f x). Qed.
Lemma lem4854320 {A : Type'} (x' : type684 A) (u : A -> Prop) : (x' u) = (@I ((A -> Prop) -> A) x' u).
Proof. exact (@lem4854318 A x' u). Qed.
Lemma lem4854321 {A : Type'} (t : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term259 A t x' u) = (term260 A t x' u).
Proof. exact (MK_COMB (@lem4854312 A t) (@lem4854320 A x' u)). Qed.
Lemma lem4854323 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854324 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4854323 A Prop f x). Qed.
Lemma lem4854325 {A : Type'} (t : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term260 A t x' u) = (term261 A t x' u).
Proof. exact (@lem4854324 A t (@I ((A -> Prop) -> A) x' u)). Qed.
Lemma lem4854326 {A : Type'} (t : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term259 A t x' u) = (term261 A t x' u).
Proof. exact (TRANS (@lem4854321 A t x' u) (@lem4854325 A t x' u)). Qed.
Lemma lem4854327 {A : Type'} (t : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term262 A t x' u) = (term263 A t x' u).
Proof. exact (MK_COMB (@lem4854311) (@lem4854326 A t x' u)). Qed.
Lemma lem4854328 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854333 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854334 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4854333 (A -> Prop) Prop f x). Qed.
Lemma lem4854336 {A : Type'} (t : type686 A) (t' : A -> Prop) : (t t') = (@I ((A -> Prop) -> Prop) t t').
Proof. exact (@lem4854334 A t t'). Qed.
Lemma lem4854337 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term216 A t t') = (term254 A t t').
Proof. exact (MK_COMB (@lem4854328) (@lem4854336 A t t')). Qed.
Lemma lem4854338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4854339 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term188 A t t') = (term255 A t t').
Proof. exact (MK_COMB (@lem4854338) (@lem4854337 A t t')). Qed.
Lemma lem4854340 {A : Type'} (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term264 A t t' x' u) = (term265 A t t' x' u).
Proof. exact (MK_COMB (@lem4854339 A t t') (@lem4854327 A t' x' u)). Qed.
Lemma lem4854341 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term266 A t x' u) = (term267 A t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854340 A t t' x' u)). Qed.
Lemma lem4854342 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854343 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term268 A t x' u) = (term269 A t x' u).
Proof. exact (MK_COMB (@lem4854342 A) (@lem4854341 A t x' u)). Qed.
Lemma lem4854344 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4854349 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854350 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4854349 (A -> Prop) A f x). Qed.
Lemma lem4854352 {A : Type'} (x' : type684 A) (u : A -> Prop) : (x' u) = (@I ((A -> Prop) -> A) x' u).
Proof. exact (@lem4854350 A x' u). Qed.
Lemma lem4854353 {A : Type'} (x' : type684 A) (u : A -> Prop) : (term270 A x' u) = (term271 A x' u).
Proof. exact (MK_COMB (@lem4854344 A u) (@lem4854352 A x' u)). Qed.
Lemma lem4854355 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854356 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4854355 A Prop f x). Qed.
Lemma lem4854357 {A : Type'} (x' : type684 A) (u : A -> Prop) : (term271 A x' u) = (term272 A x' u).
Proof. exact (@lem4854356 A u (@I ((A -> Prop) -> A) x' u)). Qed.
Lemma lem4854358 {A : Type'} (x' : type684 A) (u : A -> Prop) : (term270 A x' u) = (term272 A x' u).
Proof. exact (TRANS (@lem4854353 A x' u) (@lem4854357 A x' u)). Qed.
Lemma lem4854359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4854360 {A : Type'} (x' : type684 A) (u : A -> Prop) : (term273 A x' u) = (term274 A x' u).
Proof. exact (MK_COMB (@lem4854359) (@lem4854358 A x' u)). Qed.
Lemma lem4854361 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term275 A t x' u) = (term276 A t x' u).
Proof. exact (MK_COMB (@lem4854360 A x' u) (@lem4854343 A t x' u)). Qed.
Lemma lem4854362 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854367 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854368 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4854367 A Prop f x). Qed.
Lemma lem4854370 {A : Type'} (u : A -> Prop) (x : A) : (u x) = (@I (A -> Prop) u x).
Proof. exact (@lem4854368 A u x). Qed.
Lemma lem4854371 {A : Type'} (u : A -> Prop) (x : A) : (term202 A u x) = (term277 A u x).
Proof. exact (MK_COMB (@lem4854362) (@lem4854370 A u x)). Qed.
Lemma lem4854372 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4854373 {A : Type'} (u : A -> Prop) (x : A) : (term184 A u x) = (term278 A u x).
Proof. exact (MK_COMB (@lem4854372) (@lem4854371 A u x)). Qed.
Lemma lem4854374 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term279 A x t x' u) = (term280 A x t x' u).
Proof. exact (MK_COMB (@lem4854373 A u x) (@lem4854361 A t x' u)). Qed.
Lemma lem4854375 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4854380 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854381 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4854380 (A -> Prop) Prop f x). Qed.
Lemma lem4854383 {A : Type'} (B : type686 A) (u : A -> Prop) : (B u) = (@I ((A -> Prop) -> Prop) B u).
Proof. exact (@lem4854381 A B u). Qed.
Lemma lem4854384 {A : Type'} (B : type686 A) (u : A -> Prop) : (term216 A B u) = (term254 A B u).
Proof. exact (MK_COMB (@lem4854375) (@lem4854383 A B u)). Qed.
Lemma lem4854385 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4854386 {A : Type'} (B : type686 A) (u : A -> Prop) : (term188 A B u) = (term255 A B u).
Proof. exact (MK_COMB (@lem4854385) (@lem4854384 A B u)). Qed.
Lemma lem4854387 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term246 A B x t x' u) = (term281 A B x t x' u).
Proof. exact (MK_COMB (@lem4854386 A B u) (@lem4854374 A x t x' u)). Qed.
Lemma lem4854388 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term248 A B x t x') = (term282 A B x t x').
Proof. exact (fun_ext (fun u : A -> Prop => @lem4854387 A B x t x' u)). Qed.
Lemma lem4854389 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854390 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term250 A B x t x') = (term283 A B x t x').
Proof. exact (MK_COMB (@lem4854389 A) (@lem4854388 A B x t x')). Qed.
Lemma lem4854391 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term283 A B x t x'.
Proof. exact (EQ_MP (@lem4854390 A B x t x') (@lem4854284 A B x t x' h1)). Qed.
Lemma lem4854396 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854397 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4854396 A Prop f x). Qed.
Lemma lem4854399 {A : Type'} (t' : A -> Prop) (x : A) : (t' x) = (@I (A -> Prop) t' x).
Proof. exact (@lem4854397 A t' x). Qed.
Lemma lem4854404 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4854405 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4854404 (A -> Prop) Prop f x). Qed.
Lemma lem4854407 {A : Type'} (t : type686 A) (t' : A -> Prop) : (t t') = (@I ((A -> Prop) -> Prop) t t').
Proof. exact (@lem4854405 A t t'). Qed.
Lemma lem4854408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4854409 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term119 A t t') = (term284 A t t').
Proof. exact (MK_COMB (@lem4854408) (@lem4854407 A t t')). Qed.
Lemma lem4854410 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) : (term121 A t t' x) = (term285 A t t' x).
Proof. exact (MK_COMB (@lem4854409 A t t') (@lem4854399 A t' x)). Qed.
Lemma lem4854411 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : term285 A t t' x.
Proof. exact (EQ_MP (@lem4854410 A t t' x) (@lem4854285 A t t' x h1)). Qed.
Lemma lem4854421 {A : Type'} (t : type686 A) (B : type686 A) (c : A -> Prop) : (term256 A t B c) = (term256 A t B c).
Proof. exact (eq_refl (term256 A t B c)). Qed.
Lemma lem4854422 {A : Type'} (t : type686 A) (B : type686 A) : (term257 A t B) = (term257 A t B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4854421 A t B c)). Qed.
Lemma lem4854423 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854425 {A : Type'} (t : type686 A) (B : type686 A) : (term258 A t B) = (term258 A t B).
Proof. exact (MK_COMB (@lem4854423 A) (@lem4854422 A t B)). Qed.
Lemma lem4854426 {A : Type'} (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term258 A t B.
Proof. exact (EQ_MP (@lem4854425 A t B) (@lem4854310 A t B h1)). Qed.
Lemma lem4854428 {A : Type'} (P : Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4854429 {A : Type'} (P : Prop) (Q : type686 A) : (term288 A P Q) = (term289 A P Q).
Proof. exact (@lem4854428 (A -> Prop) P Q). Qed.
Lemma lem4854430 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term290 A t x' u) = (term291 A t x' u).
Proof. exact (@lem4854429 A (term272 A x' u) (term267 A t x' u)). Qed.
Lemma lem4854431 {A : Type'} (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term292 A t x' u t') = (term265 A t t' x' u).
Proof. exact (eq_refl (term292 A t x' u t')). Qed.
Lemma lem4854432 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term293 A t x' u) = (term267 A t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854431 A t t' x' u)). Qed.
Lemma lem4854433 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854434 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term294 A t x' u) = (term269 A t x' u).
Proof. exact (MK_COMB (@lem4854433 A) (@lem4854432 A t x' u)). Qed.
Lemma lem4854435 {A : Type'} (x' : type684 A) (u : A -> Prop) : (term274 A x' u) = (term274 A x' u).
Proof. exact (eq_refl (term274 A x' u)). Qed.
Lemma lem4854436 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term290 A t x' u) = (term276 A t x' u).
Proof. exact (MK_COMB (@lem4854435 A x' u) (@lem4854434 A t x' u)). Qed.
Lemma lem4854437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854438 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term295 A t x' u) = (term296 A t x' u).
Proof. exact (MK_COMB (@lem4854437) (@lem4854436 A t x' u)). Qed.
Lemma lem4854439 {A : Type'} (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term292 A t x' u t') = (term265 A t t' x' u).
Proof. exact (eq_refl (term292 A t x' u t')). Qed.
Lemma lem4854440 {A : Type'} (x' : type684 A) (u : A -> Prop) : (term274 A x' u) = (term274 A x' u).
Proof. exact (eq_refl (term274 A x' u)). Qed.
Lemma lem4854441 {A : Type'} (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term297 A t x' u t') = (term298 A t t' x' u).
Proof. exact (MK_COMB (@lem4854440 A x' u) (@lem4854439 A t t' x' u)). Qed.
Lemma lem4854442 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term299 A t x' u) = (term300 A t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854441 A t t' x' u)). Qed.
Lemma lem4854443 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854444 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term291 A t x' u) = (term301 A t x' u).
Proof. exact (MK_COMB (@lem4854443 A) (@lem4854442 A t x' u)). Qed.
Lemma lem4854445 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : ((term290 A t x' u) = (term291 A t x' u)) = ((term276 A t x' u) = (term301 A t x' u)).
Proof. exact (MK_COMB (@lem4854438 A t x' u) (@lem4854444 A t x' u)). Qed.
Lemma lem4854446 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term276 A t x' u) = (term301 A t x' u).
Proof. exact (EQ_MP (@lem4854445 A t x' u) (@lem4854430 A t x' u)). Qed.
Lemma lem4854447 {A : Type'} (u : A -> Prop) (x : A) : (term278 A u x) = (term278 A u x).
Proof. exact (eq_refl (term278 A u x)). Qed.
Lemma lem4854448 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term280 A x t x' u) = (term302 A x t x' u).
Proof. exact (MK_COMB (@lem4854447 A u x) (@lem4854446 A t x' u)). Qed.
Lemma lem4854450 {A : Type'} (P : Prop) (Q : A -> Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4854451 {A : Type'} (P : Prop) (Q : type686 A) : (term305 A P Q) = (term306 A P Q).
Proof. exact (@lem4854450 (A -> Prop) P Q). Qed.
Lemma lem4854452 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term307 A x t x' u) = (term308 A x t x' u).
Proof. exact (@lem4854451 A (term277 A u x) (term300 A t x' u)). Qed.
Lemma lem4854453 {A : Type'} (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term309 A t x' u t') = (term298 A t t' x' u).
Proof. exact (eq_refl (term309 A t x' u t')). Qed.
Lemma lem4854454 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term310 A t x' u) = (term300 A t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854453 A t t' x' u)). Qed.
Lemma lem4854455 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854456 {A : Type'} (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term311 A t x' u) = (term301 A t x' u).
Proof. exact (MK_COMB (@lem4854455 A) (@lem4854454 A t x' u)). Qed.
Lemma lem4854457 {A : Type'} (u : A -> Prop) (x : A) : (term278 A u x) = (term278 A u x).
Proof. exact (eq_refl (term278 A u x)). Qed.
Lemma lem4854458 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term307 A x t x' u) = (term302 A x t x' u).
Proof. exact (MK_COMB (@lem4854457 A u x) (@lem4854456 A t x' u)). Qed.
Lemma lem4854459 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854460 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term312 A x t x' u) = (term313 A x t x' u).
Proof. exact (MK_COMB (@lem4854459) (@lem4854458 A x t x' u)). Qed.
Lemma lem4854461 {A : Type'} (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term309 A t x' u t') = (term298 A t t' x' u).
Proof. exact (eq_refl (term309 A t x' u t')). Qed.
Lemma lem4854462 {A : Type'} (u : A -> Prop) (x : A) : (term278 A u x) = (term278 A u x).
Proof. exact (eq_refl (term278 A u x)). Qed.
Lemma lem4854463 {A : Type'} (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term314 A x t x' u t') = (term315 A x t t' x' u).
Proof. exact (MK_COMB (@lem4854462 A u x) (@lem4854461 A t t' x' u)). Qed.
Lemma lem4854464 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term316 A x t x' u) = (term317 A x t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854463 A x t t' x' u)). Qed.
Lemma lem4854465 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854466 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term308 A x t x' u) = (term318 A x t x' u).
Proof. exact (MK_COMB (@lem4854465 A) (@lem4854464 A x t x' u)). Qed.
Lemma lem4854467 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : ((term307 A x t x' u) = (term308 A x t x' u)) = ((term302 A x t x' u) = (term318 A x t x' u)).
Proof. exact (MK_COMB (@lem4854460 A x t x' u) (@lem4854466 A x t x' u)). Qed.
Lemma lem4854468 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term302 A x t x' u) = (term318 A x t x' u).
Proof. exact (EQ_MP (@lem4854467 A x t x' u) (@lem4854452 A x t x' u)). Qed.
Lemma lem4854469 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term280 A x t x' u) = (term318 A x t x' u).
Proof. exact (TRANS (@lem4854448 A x t x' u) (@lem4854468 A x t x' u)). Qed.
Lemma lem4854470 {A : Type'} (B : type686 A) (u : A -> Prop) : (term255 A B u) = (term255 A B u).
Proof. exact (eq_refl (term255 A B u)). Qed.
Lemma lem4854471 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term281 A B x t x' u) = (term319 A B x t x' u).
Proof. exact (MK_COMB (@lem4854470 A B u) (@lem4854469 A x t x' u)). Qed.
Lemma lem4854473 {A : Type'} (P : Prop) (Q : A -> Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4854474 {A : Type'} (P : Prop) (Q : type686 A) : (term305 A P Q) = (term306 A P Q).
Proof. exact (@lem4854473 (A -> Prop) P Q). Qed.
Lemma lem4854475 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term320 A B x t x' u) = (term321 A B x t x' u).
Proof. exact (@lem4854474 A (term254 A B u) (term317 A x t x' u)). Qed.
Lemma lem4854476 {A : Type'} (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term322 A x t x' u t') = (term315 A x t t' x' u).
Proof. exact (eq_refl (term322 A x t x' u t')). Qed.
Lemma lem4854477 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term323 A x t x' u) = (term317 A x t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854476 A x t t' x' u)). Qed.
Lemma lem4854478 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854479 {A : Type'} (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term324 A x t x' u) = (term318 A x t x' u).
Proof. exact (MK_COMB (@lem4854478 A) (@lem4854477 A x t x' u)). Qed.
Lemma lem4854480 {A : Type'} (B : type686 A) (u : A -> Prop) : (term255 A B u) = (term255 A B u).
Proof. exact (eq_refl (term255 A B u)). Qed.
Lemma lem4854481 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term320 A B x t x' u) = (term319 A B x t x' u).
Proof. exact (MK_COMB (@lem4854480 A B u) (@lem4854479 A x t x' u)). Qed.
Lemma lem4854482 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854483 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term325 A B x t x' u) = (term326 A B x t x' u).
Proof. exact (MK_COMB (@lem4854482) (@lem4854481 A B x t x' u)). Qed.
Lemma lem4854484 {A : Type'} (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term322 A x t x' u t') = (term315 A x t t' x' u).
Proof. exact (eq_refl (term322 A x t x' u t')). Qed.
Lemma lem4854485 {A : Type'} (B : type686 A) (u : A -> Prop) : (term255 A B u) = (term255 A B u).
Proof. exact (eq_refl (term255 A B u)). Qed.
Lemma lem4854486 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term327 A B x t x' u t') = (term328 A B x t t' x' u).
Proof. exact (MK_COMB (@lem4854485 A B u) (@lem4854484 A x t t' x' u)). Qed.
Lemma lem4854487 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term329 A B x t x' u) = (term330 A B x t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854486 A B x t t' x' u)). Qed.
Lemma lem4854488 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854489 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term321 A B x t x' u) = (term331 A B x t x' u).
Proof. exact (MK_COMB (@lem4854488 A) (@lem4854487 A B x t x' u)). Qed.
Lemma lem4854490 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : ((term320 A B x t x' u) = (term321 A B x t x' u)) = ((term319 A B x t x' u) = (term331 A B x t x' u)).
Proof. exact (MK_COMB (@lem4854483 A B x t x' u) (@lem4854489 A B x t x' u)). Qed.
Lemma lem4854491 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term319 A B x t x' u) = (term331 A B x t x' u).
Proof. exact (EQ_MP (@lem4854490 A B x t x' u) (@lem4854475 A B x t x' u)). Qed.
Lemma lem4854492 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term281 A B x t x' u) = (term331 A B x t x' u).
Proof. exact (TRANS (@lem4854471 A B x t x' u) (@lem4854491 A B x t x' u)). Qed.
Lemma lem4854493 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term282 A B x t x') = (term332 A B x t x').
Proof. exact (fun_ext (fun u : A -> Prop => @lem4854492 A B x t x' u)). Qed.
Lemma lem4854494 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854495 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term283 A B x t x') = (term333 A B x t x').
Proof. exact (MK_COMB (@lem4854494 A) (@lem4854493 A B x t x')). Qed.
Lemma lem4854518 {A : Type'} (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term315 A x t t' x' u) = (term334 A x t t' x' u).
Proof. exact (@lem19490 (term272 A x' u) (term277 A u x) (term265 A t t' x' u)). Qed.
Lemma lem4854521 {A : Type'} (B : type686 A) (u : A -> Prop) : (term255 A B u) = (term255 A B u).
Proof. exact (eq_refl (term255 A B u)). Qed.
Lemma lem4854522 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term328 A B x t t' x' u) = (term335 A B x t t' x' u).
Proof. exact (MK_COMB (@lem4854521 A B u) (@lem4854518 A x t t' x' u)). Qed.
Lemma lem4854529 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term335 A B x t t' x' u) = (term336 A B x t t' x' u).
Proof. exact (@lem19490 (term337 A x x' u) (term254 A B u) (term338 A x t t' x' u)). Qed.
Lemma lem4854530 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (t' : A -> Prop) (x' : type684 A) (u : A -> Prop) : (term328 A B x t t' x' u) = (term336 A B x t t' x' u).
Proof. exact (TRANS (@lem4854522 A B x t t' x' u) (@lem4854529 A B x t t' x' u)). Qed.
Lemma lem4854531 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term330 A B x t x' u) = (term339 A B x t x' u).
Proof. exact (fun_ext (fun t' : A -> Prop => @lem4854530 A B x t t' x' u)). Qed.
Lemma lem4854532 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854533 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (u : A -> Prop) : (term331 A B x t x' u) = (term340 A B x t x' u).
Proof. exact (MK_COMB (@lem4854532 A) (@lem4854531 A B x t x' u)). Qed.
Lemma lem4854534 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term332 A B x t x') = (term341 A B x t x').
Proof. exact (fun_ext (fun u : A -> Prop => @lem4854533 A B x t x' u)). Qed.
Lemma lem4854535 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4854536 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term333 A B x t x') = (term342 A B x t x').
Proof. exact (MK_COMB (@lem4854535 A) (@lem4854534 A B x t x')). Qed.
Lemma lem4854537 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) : (term283 A B x t x') = (term342 A B x t x').
Proof. exact (TRANS (@lem4854495 A B x t x') (@lem4854536 A B x t x')). Qed.
Lemma lem4854538 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term342 A B x t x'.
Proof. exact (EQ_MP (@lem4854537 A B x t x') (@lem4854391 A B x t x' h1)). Qed.
Lemma lem4854547 {A : Type'} (_60189 : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term343 A t B _60189.
Proof. exact (@lem4854426 A t B h1 _60189). Qed.
Lemma lem4854548 {A : Type'} (t : type686 A) (B : type686 A) (_60189 : A -> Prop) : (term343 A t B _60189) = (term256 A t B _60189).
Proof. exact (eq_refl (term343 A t B _60189)). Qed.
Lemma lem4854550 {A : Type'} (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term344 A B x t x' _60190.
Proof. exact (@lem4854538 A B x t x' h1 _60190). Qed.
Lemma lem4854551 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (_60190 : A -> Prop) : (term344 A B x t x' _60190) = (term340 A B x t x' _60190).
Proof. exact (eq_refl (term344 A B x t x' _60190)). Qed.
Lemma lem4854552 {A : Type'} (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term340 A B x t x' _60190.
Proof. exact (EQ_MP (@lem4854551 A B x t x' _60190) (@lem4854550 A _60190 B x t x' h1)). Qed.
Lemma lem4854553 {A : Type'} (_60190 : A -> Prop) (_60191 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term345 A B x t x' _60190 _60191.
Proof. exact (@lem4854552 A _60190 B x t x' h1 _60191). Qed.
Lemma lem4854554 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term345 A B x t x' _60190 _60191) = (term336 A B x t _60191 x' _60190).
Proof. exact (eq_refl (term345 A B x t x' _60190 _60191)). Qed.
Lemma lem4854555 {A : Type'} (_60191 : A -> Prop) (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term336 A B x t _60191 x' _60190.
Proof. exact (EQ_MP (@lem4854554 A B x t _60191 x' _60190) (@lem4854553 A _60190 _60191 B x t x' h1)). Qed.
Lemma lem4854563 {A : Type'} (_60189 : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term256 A t B _60189.
Proof. exact (EQ_MP (@lem4854548 A t B _60189) (@lem4854547 A _60189 t B h1)). Qed.
Lemma lem4854577 {A : Type'} (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term346 A B x x' _60190.
Proof. exact (proj1 (@lem4854555 A (@el (A -> Prop)) _60190 B x t x' h1)). Qed.
Lemma lem4854591 {A : Type'} (_60191 : A -> Prop) (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term347 A B x t _60191 x' _60190.
Proof. exact (proj2 (@lem4854555 A _60191 _60190 B x t x' h1)). Qed.
Lemma lem4854593 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (proj1 (@lem4854411 A t t' x h1)). Qed.
Lemma lem4854594 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : term348 A t t'.
Proof. exact (fun h0 : term254 A t t' => @lem4854593 A t t' x h1). Qed.
Lemma lem4854596 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854597 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term348 A t t') = (@I ((A -> Prop) -> Prop) t t').
Proof. exact (@lem4854596 (@I ((A -> Prop) -> Prop) t t')). Qed.
Lemma lem4854598 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem4854597 A t t') (@lem4854594 A t t' x h1)). Qed.
Lemma lem4854604 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4854605 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : (term256 A t B _60189) = (term350 A B t _60189).
Proof. exact (@lem4854604 (@I ((A -> Prop) -> Prop) B _60189) (term254 A t _60189)). Qed.
Lemma lem4854611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854612 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : (term351 A t B _60189) = (term352 A B t _60189).
Proof. exact (MK_COMB (@lem4854611) (@lem4854605 A B t _60189)). Qed.
Lemma lem4854618 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : (term350 A B t _60189) = (term350 A B t _60189).
Proof. exact (eq_refl (term350 A B t _60189)). Qed.
Lemma lem4854619 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : ((term256 A t B _60189) = (term350 A B t _60189)) = ((term350 A B t _60189) = (term350 A B t _60189)).
Proof. exact (MK_COMB (@lem4854612 A B t _60189) (@lem4854618 A B t _60189)). Qed.
Lemma lem4854621 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4854622 (x : Prop) : (x = x) = True.
Proof. exact (@lem4854621 Prop x). Qed.
Lemma lem4854623 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : ((term350 A B t _60189) = (term350 A B t _60189)) = True.
Proof. exact (@lem4854622 (term350 A B t _60189)). Qed.
Lemma lem4854624 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : ((term256 A t B _60189) = (term350 A B t _60189)) = True.
Proof. exact (TRANS (@lem4854619 A B t _60189) (@lem4854623 A B t _60189)). Qed.
Lemma lem4854625 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : True = ((term256 A t B _60189) = (term350 A B t _60189)).
Proof. exact (SYM (@lem4854624 A B t _60189)). Qed.
Lemma lem4854626 {A : Type'} (B : type686 A) (t : type686 A) (_60189 : A -> Prop) : (term256 A t B _60189) = (term350 A B t _60189).
Proof. exact (EQ_MP (@lem4854625 A B t _60189) (@lem0)). Qed.
Lemma lem4854627 {A : Type'} (_60189 : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term350 A B t _60189.
Proof. exact (EQ_MP (@lem4854626 A B t _60189) (@lem4854563 A _60189 t B h1)). Qed.
Lemma lem4854629 (b : Prop) (a : Prop) : (a \/ b) = (term353 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4854630 {A : Type'} (t : type686 A) (B : type686 A) (_60189 : A -> Prop) : (term350 A B t _60189) = (term354 A t B _60189).
Proof. exact (@lem4854629 (term254 A t _60189) (@I ((A -> Prop) -> Prop) B _60189)). Qed.
Lemma lem4854632 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4854633 {A : Type'} (t : type686 A) (_60189 : A -> Prop) : (term355 A t _60189) = (@I ((A -> Prop) -> Prop) t _60189).
Proof. exact (@lem4854632 (@I ((A -> Prop) -> Prop) t _60189)). Qed.
Lemma lem4854634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4854635 {A : Type'} (t : type686 A) (_60189 : A -> Prop) : (term356 A t _60189) = (term357 A t _60189).
Proof. exact (MK_COMB (@lem4854634) (@lem4854633 A t _60189)). Qed.
Lemma lem4854636 {A : Type'} (B : type686 A) (_60189 : A -> Prop) : (@I ((A -> Prop) -> Prop) B _60189) = (@I ((A -> Prop) -> Prop) B _60189).
Proof. exact (eq_refl (@I ((A -> Prop) -> Prop) B _60189)). Qed.
Lemma lem4854637 {A : Type'} (t : type686 A) (B : type686 A) (_60189 : A -> Prop) : (term354 A t B _60189) = (term358 A t B _60189).
Proof. exact (MK_COMB (@lem4854635 A t _60189) (@lem4854636 A B _60189)). Qed.
Lemma lem4854638 {A : Type'} (t : type686 A) (B : type686 A) (_60189 : A -> Prop) : (term350 A B t _60189) = (term358 A t B _60189).
Proof. exact (TRANS (@lem4854630 A t B _60189) (@lem4854637 A t B _60189)). Qed.
Lemma lem4854641 {A : Type'} (_60189 : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term358 A t B _60189.
Proof. exact (EQ_MP (@lem4854638 A t B _60189) (@lem4854627 A _60189 t B h1)). Qed.
Lemma lem4854642 {A : Type'} (_60189 : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term358 A t B _60189.
Proof. exact (@lem4854641 A _60189 t B h1). Qed.
Lemma lem4854643 {A : Type'} (t' : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term358 A t B t'.
Proof. exact (@lem4854642 A t' t B h1). Qed.
Lemma lem4854646 {A : Type'} (B : type686 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term121 A t t' x) : @I ((A -> Prop) -> Prop) B t'.
Proof. exact (@lem4854643 A t' t B h1 (@lem4854598 A t t' x h2)). Qed.
Lemma lem4854647 {A : Type'} (B : type686 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term121 A t t' x) : term348 A B t'.
Proof. exact (fun h0 : term254 A B t' => @lem4854646 A B t t' x h1 h2). Qed.
Lemma lem4854649 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854650 {A : Type'} (B : type686 A) (t' : A -> Prop) : (term348 A B t') = (@I ((A -> Prop) -> Prop) B t').
Proof. exact (@lem4854649 (@I ((A -> Prop) -> Prop) B t')). Qed.
Lemma lem4854651 {A : Type'} (B : type686 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term121 A t t' x) : @I ((A -> Prop) -> Prop) B t'.
Proof. exact (EQ_MP (@lem4854650 A B t') (@lem4854647 A B t t' x h1 h2)). Qed.
Lemma lem4854653 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I (A -> Prop) t' x.
Proof. exact (proj2 (@lem4854411 A t t' x h1)). Qed.
Lemma lem4854654 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : term359 A t' x.
Proof. exact (fun h0 : term277 A t' x => @lem4854653 A t t' x h1). Qed.
Lemma lem4854656 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854657 {A : Type'} (t' : A -> Prop) (x : A) : (term359 A t' x) = (@I (A -> Prop) t' x).
Proof. exact (@lem4854656 (@I (A -> Prop) t' x)). Qed.
Lemma lem4854658 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I (A -> Prop) t' x.
Proof. exact (EQ_MP (@lem4854657 A t' x) (@lem4854654 A t t' x h1)). Qed.
Lemma lem4854660 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (proj1 (@lem4854411 A t t' x h1)). Qed.
Lemma lem4854661 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : term348 A t t'.
Proof. exact (fun h0 : term254 A t t' => @lem4854660 A t t' x h1). Qed.
Lemma lem4854663 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854664 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term348 A t t') = (@I ((A -> Prop) -> Prop) t t').
Proof. exact (@lem4854663 (@I ((A -> Prop) -> Prop) t t')). Qed.
Lemma lem4854665 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem4854664 A t t') (@lem4854661 A t t' x h1)). Qed.
Lemma lem4854667 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (proj1 (@lem4854411 A t t' x h1)). Qed.
Lemma lem4854668 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : term348 A t t'.
Proof. exact (fun h0 : term254 A t t' => @lem4854667 A t t' x h1). Qed.
Lemma lem4854670 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854671 {A : Type'} (t : type686 A) (t' : A -> Prop) : (term348 A t t') = (@I ((A -> Prop) -> Prop) t t').
Proof. exact (@lem4854670 (@I ((A -> Prop) -> Prop) t t')). Qed.
Lemma lem4854672 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I ((A -> Prop) -> Prop) t t'.
Proof. exact (EQ_MP (@lem4854671 A t t') (@lem4854668 A t t' x h1)). Qed.
Lemma lem4854674 {A : Type'} (_60189 : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term358 A t B _60189.
Proof. exact (EQ_MP (@lem4854638 A t B _60189) (@lem4854627 A _60189 t B h1)). Qed.
Lemma lem4854675 {A : Type'} (_60189 : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term358 A t B _60189.
Proof. exact (@lem4854674 A _60189 t B h1). Qed.
Lemma lem4854676 {A : Type'} (t' : A -> Prop) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term358 A t B t'.
Proof. exact (@lem4854675 A t' t B h1). Qed.
Lemma lem4854679 {A : Type'} (B : type686 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term121 A t t' x) : @I ((A -> Prop) -> Prop) B t'.
Proof. exact (@lem4854676 A t' t B h1 (@lem4854672 A t t' x h2)). Qed.
Lemma lem4854680 {A : Type'} (B : type686 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term121 A t t' x) : term348 A B t'.
Proof. exact (fun h0 : term254 A B t' => @lem4854679 A B t t' x h1 h2). Qed.
Lemma lem4854682 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854683 {A : Type'} (B : type686 A) (t' : A -> Prop) : (term348 A B t') = (@I ((A -> Prop) -> Prop) B t').
Proof. exact (@lem4854682 (@I ((A -> Prop) -> Prop) B t')). Qed.
Lemma lem4854684 {A : Type'} (B : type686 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term121 A t t' x) : @I ((A -> Prop) -> Prop) B t'.
Proof. exact (EQ_MP (@lem4854683 A B t') (@lem4854680 A B t t' x h1 h2)). Qed.
Lemma lem4854686 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I (A -> Prop) t' x.
Proof. exact (proj2 (@lem4854411 A t t' x h1)). Qed.
Lemma lem4854687 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : term359 A t' x.
Proof. exact (fun h0 : term277 A t' x => @lem4854686 A t t' x h1). Qed.
Lemma lem4854689 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854690 {A : Type'} (t' : A -> Prop) (x : A) : (term359 A t' x) = (@I (A -> Prop) t' x).
Proof. exact (@lem4854689 (@I (A -> Prop) t' x)). Qed.
Lemma lem4854691 {A : Type'} (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term121 A t t' x) : @I (A -> Prop) t' x.
Proof. exact (EQ_MP (@lem4854690 A t' x) (@lem4854687 A t t' x h1)). Qed.
Lemma lem4854697 (q : Prop) (p : Prop) (r : Prop) : (term360 p q r) = (term360 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4854698 {A : Type'} (x : A) (B : type686 A) (x' : type684 A) (_60190 : A -> Prop) : (term346 A B x x' _60190) = (term361 A x B x' _60190).
Proof. exact (@lem4854697 (term277 A _60190 x) (term254 A B _60190) (term272 A x' _60190)). Qed.
Lemma lem4854712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4854713 {A : Type'} (x' : type684 A) (B : type686 A) (_60190 : A -> Prop) : (term362 A B x' _60190) = (term363 A x' B _60190).
Proof. exact (@lem4854712 (term272 A x' _60190) (term254 A B _60190)). Qed.
Lemma lem4854719 {A : Type'} (_60190 : A -> Prop) (x : A) : (term278 A _60190 x) = (term278 A _60190 x).
Proof. exact (eq_refl (term278 A _60190 x)). Qed.
Lemma lem4854720 {A : Type'} (x : A) (x' : type684 A) (B : type686 A) (_60190 : A -> Prop) : (term361 A x B x' _60190) = (term364 A x x' B _60190).
Proof. exact (MK_COMB (@lem4854719 A _60190 x) (@lem4854713 A x' B _60190)). Qed.
Lemma lem4854724 (q : Prop) (p : Prop) (r : Prop) : (term360 p q r) = (term360 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4854725 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60190 : A -> Prop) : (term364 A x x' B _60190) = (term365 A x' x B _60190).
Proof. exact (@lem4854724 (term272 A x' _60190) (term277 A _60190 x) (term254 A B _60190)). Qed.
Lemma lem4854741 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60190 : A -> Prop) : (term361 A x B x' _60190) = (term365 A x' x B _60190).
Proof. exact (TRANS (@lem4854720 A x x' B _60190) (@lem4854725 A x' x B _60190)). Qed.
Lemma lem4854742 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60190 : A -> Prop) : (term346 A B x x' _60190) = (term365 A x' x B _60190).
Proof. exact (TRANS (@lem4854698 A x B x' _60190) (@lem4854741 A x' x B _60190)). Qed.
Lemma lem4854743 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854744 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60190 : A -> Prop) : (term366 A B x x' _60190) = (term367 A x' x B _60190).
Proof. exact (MK_COMB (@lem4854743) (@lem4854742 A x' x B _60190)). Qed.
Lemma lem4854758 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4854759 {A : Type'} (x : A) (B : type686 A) (_60190 : A -> Prop) : (term368 A B _60190 x) = (term369 A x B _60190).
Proof. exact (@lem4854758 (term277 A _60190 x) (term254 A B _60190)). Qed.
Lemma lem4854765 {A : Type'} (x' : type684 A) (_60190 : A -> Prop) : (term370 A x' _60190) = (term370 A x' _60190).
Proof. exact (eq_refl (term370 A x' _60190)). Qed.
Lemma lem4854766 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60190 : A -> Prop) : (term371 A x' B _60190 x) = (term365 A x' x B _60190).
Proof. exact (MK_COMB (@lem4854765 A x' _60190) (@lem4854759 A x B _60190)). Qed.
Lemma lem4854777 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60190 : A -> Prop) : ((term346 A B x x' _60190) = (term371 A x' B _60190 x)) = ((term365 A x' x B _60190) = (term365 A x' x B _60190)).
Proof. exact (MK_COMB (@lem4854744 A x' x B _60190) (@lem4854766 A x' x B _60190)). Qed.
Lemma lem4854779 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4854780 (x : Prop) : (x = x) = True.
Proof. exact (@lem4854779 Prop x). Qed.
Lemma lem4854781 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60190 : A -> Prop) : ((term365 A x' x B _60190) = (term365 A x' x B _60190)) = True.
Proof. exact (@lem4854780 (term365 A x' x B _60190)). Qed.
Lemma lem4854782 {A : Type'} (x' : type684 A) (B : type686 A) (_60190 : A -> Prop) (x : A) : ((term346 A B x x' _60190) = (term371 A x' B _60190 x)) = True.
Proof. exact (TRANS (@lem4854777 A x' x B _60190) (@lem4854781 A x' x B _60190)). Qed.
Lemma lem4854783 {A : Type'} (x' : type684 A) (B : type686 A) (_60190 : A -> Prop) (x : A) : True = ((term346 A B x x' _60190) = (term371 A x' B _60190 x)).
Proof. exact (SYM (@lem4854782 A x' B _60190 x)). Qed.
Lemma lem4854784 {A : Type'} (x' : type684 A) (B : type686 A) (_60190 : A -> Prop) (x : A) : (term346 A B x x' _60190) = (term371 A x' B _60190 x).
Proof. exact (EQ_MP (@lem4854783 A x' B _60190 x) (@lem0)). Qed.
Lemma lem4854785 {A : Type'} (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term371 A x' B _60190 x.
Proof. exact (EQ_MP (@lem4854784 A x' B _60190 x) (@lem4854577 A _60190 B x t x' h1)). Qed.
Lemma lem4854787 (b : Prop) (a : Prop) : (a \/ b) = (term353 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4854788 {A : Type'} (B : type686 A) (x : A) (x' : type684 A) (_60190 : A -> Prop) : (term371 A x' B _60190 x) = (term372 A B x x' _60190).
Proof. exact (@lem4854787 (term368 A B _60190 x) (term272 A x' _60190)). Qed.
Lemma lem4854790 (a : Prop) (b : Prop) : (term373 a b) = (term374 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4854791 {A : Type'} (B : type686 A) (_60190 : A -> Prop) (x : A) : (term375 A B _60190 x) = (term376 A B _60190 x).
Proof. exact (@lem4854790 (term254 A B _60190) (term277 A _60190 x)). Qed.
Lemma lem4854793 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4854794 {A : Type'} (B : type686 A) (_60190 : A -> Prop) : (term355 A B _60190) = (@I ((A -> Prop) -> Prop) B _60190).
Proof. exact (@lem4854793 (@I ((A -> Prop) -> Prop) B _60190)). Qed.
Lemma lem4854795 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4854796 {A : Type'} (B : type686 A) (_60190 : A -> Prop) : (term377 A B _60190) = (term284 A B _60190).
Proof. exact (MK_COMB (@lem4854795) (@lem4854794 A B _60190)). Qed.
Lemma lem4854798 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4854799 {A : Type'} (_60190 : A -> Prop) (x : A) : (term378 A _60190 x) = (@I (A -> Prop) _60190 x).
Proof. exact (@lem4854798 (@I (A -> Prop) _60190 x)). Qed.
Lemma lem4854800 {A : Type'} (B : type686 A) (_60190 : A -> Prop) (x : A) : (term376 A B _60190 x) = (term285 A B _60190 x).
Proof. exact (MK_COMB (@lem4854796 A B _60190) (@lem4854799 A _60190 x)). Qed.
Lemma lem4854801 {A : Type'} (B : type686 A) (_60190 : A -> Prop) (x : A) : (term375 A B _60190 x) = (term285 A B _60190 x).
Proof. exact (TRANS (@lem4854791 A B _60190 x) (@lem4854800 A B _60190 x)). Qed.
Lemma lem4854802 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4854803 {A : Type'} (B : type686 A) (_60190 : A -> Prop) (x : A) : (term379 A B _60190 x) = (term380 A B _60190 x).
Proof. exact (MK_COMB (@lem4854802) (@lem4854801 A B _60190 x)). Qed.
Lemma lem4854804 {A : Type'} (x' : type684 A) (_60190 : A -> Prop) : (term272 A x' _60190) = (term272 A x' _60190).
Proof. exact (eq_refl (term272 A x' _60190)). Qed.
Lemma lem4854805 {A : Type'} (B : type686 A) (x : A) (x' : type684 A) (_60190 : A -> Prop) : (term372 A B x x' _60190) = (term381 A B x x' _60190).
Proof. exact (MK_COMB (@lem4854803 A B _60190 x) (@lem4854804 A x' _60190)). Qed.
Lemma lem4854806 {A : Type'} (B : type686 A) (x : A) (x' : type684 A) (_60190 : A -> Prop) : (term371 A x' B _60190 x) = (term381 A B x x' _60190).
Proof. exact (TRANS (@lem4854788 A B x x' _60190) (@lem4854805 A B x x' _60190)). Qed.
Lemma lem4854808 {A : Type'} (B : type686 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term121 A t t' x) : term285 A B t' x.
Proof. exact (conj (@lem4854684 A B t t' x h1 h2) (@lem4854691 A t t' x h2)). Qed.
Lemma lem4854810 {A : Type'} (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term381 A B x x' _60190.
Proof. exact (EQ_MP (@lem4854806 A B x x' _60190) (@lem4854785 A _60190 B x t x' h1)). Qed.
Lemma lem4854811 {A : Type'} (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term381 A B x x' _60190.
Proof. exact (@lem4854810 A _60190 B x t x' h1). Qed.
Lemma lem4854812 {A : Type'} (t' : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term381 A B x x' t'.
Proof. exact (@lem4854811 A t' B x t x' h1). Qed.
Lemma lem4854815 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : term272 A x' t'.
Proof. exact (@lem4854812 A t' B x t x' h2 (@lem4854808 A B t t' x h1 h3)). Qed.
Lemma lem4854816 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : term382 A x' t'.
Proof. exact (fun h0 : term383 A x' t' => @lem4854815 A B x' t t' x h1 h2 h3). Qed.
Lemma lem4854818 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854819 {A : Type'} (x' : type684 A) (t' : A -> Prop) : (term382 A x' t') = (term272 A x' t').
Proof. exact (@lem4854818 (term272 A x' t')). Qed.
Lemma lem4854820 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : term272 A x' t'.
Proof. exact (EQ_MP (@lem4854819 A x' t') (@lem4854816 A B x' t t' x h1 h2 h3)). Qed.
Lemma lem4854822 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4854823 {A : Type'} (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term265 A t _60191 x' _60190) = (term386 A t _60191 x' _60190).
Proof. exact (@lem4854822 (@I ((A -> Prop) -> Prop) t _60191) (term261 A _60191 x' _60190)). Qed.
Lemma lem4854824 {A : Type'} (_60190 : A -> Prop) (x : A) : (term278 A _60190 x) = (term278 A _60190 x).
Proof. exact (eq_refl (term278 A _60190 x)). Qed.
Lemma lem4854825 {A : Type'} (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term338 A x t _60191 x' _60190) = (term387 A x t _60191 x' _60190).
Proof. exact (MK_COMB (@lem4854824 A _60190 x) (@lem4854823 A t _60191 x' _60190)). Qed.
Lemma lem4854827 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4854828 {A : Type'} (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term387 A x t _60191 x' _60190) = (term388 A x t _60191 x' _60190).
Proof. exact (@lem4854827 (@I (A -> Prop) _60190 x) (term389 A t _60191 x' _60190)). Qed.
Lemma lem4854829 {A : Type'} (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term338 A x t _60191 x' _60190) = (term388 A x t _60191 x' _60190).
Proof. exact (TRANS (@lem4854825 A x t _60191 x' _60190) (@lem4854828 A x t _60191 x' _60190)). Qed.
Lemma lem4854830 {A : Type'} (B : type686 A) (_60190 : A -> Prop) : (term255 A B _60190) = (term255 A B _60190).
Proof. exact (eq_refl (term255 A B _60190)). Qed.
Lemma lem4854831 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term347 A B x t _60191 x' _60190) = (term390 A B x t _60191 x' _60190).
Proof. exact (MK_COMB (@lem4854830 A B _60190) (@lem4854829 A x t _60191 x' _60190)). Qed.
Lemma lem4854833 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4854834 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term390 A B x t _60191 x' _60190) = (term391 A B x t _60191 x' _60190).
Proof. exact (@lem4854833 (@I ((A -> Prop) -> Prop) B _60190) (term392 A x t _60191 x' _60190)). Qed.
Lemma lem4854835 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term347 A B x t _60191 x' _60190) = (term391 A B x t _60191 x' _60190).
Proof. exact (TRANS (@lem4854831 A B x t _60191 x' _60190) (@lem4854834 A B x t _60191 x' _60190)). Qed.
Lemma lem4854837 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4854838 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term391 A B x t _60191 x' _60190) = (term393 A B x t _60191 x' _60190).
Proof. exact (@lem4854837 (term394 A B x t _60191 x' _60190)). Qed.
Lemma lem4854839 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (_60191 : A -> Prop) (x' : type684 A) (_60190 : A -> Prop) : (term347 A B x t _60191 x' _60190) = (term393 A B x t _60191 x' _60190).
Proof. exact (TRANS (@lem4854835 A B x t _60191 x' _60190) (@lem4854838 A B x t _60191 x' _60190)). Qed.
Lemma lem4854841 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : term395 A t x' t'.
Proof. exact (conj (@lem4854665 A t t' x h3) (@lem4854820 A B x' t t' x h1 h2 h3)). Qed.
Lemma lem4854842 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : term396 A x t x' t'.
Proof. exact (conj (@lem4854658 A t t' x h3) (@lem4854841 A B x' t t' x h1 h2 h3)). Qed.
Lemma lem4854843 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : term397 A B x t x' t'.
Proof. exact (conj (@lem4854651 A B t t' x h1 h3) (@lem4854842 A B x' t t' x h1 h2 h3)). Qed.
Lemma lem4854845 {A : Type'} (_60191 : A -> Prop) (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term393 A B x t _60191 x' _60190.
Proof. exact (EQ_MP (@lem4854839 A B x t _60191 x' _60190) (@lem4854591 A _60191 _60190 B x t x' h1)). Qed.
Lemma lem4854846 {A : Type'} (_60191 : A -> Prop) (_60190 : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term393 A B x t _60191 x' _60190.
Proof. exact (@lem4854845 A _60191 _60190 B x t x' h1). Qed.
Lemma lem4854847 {A : Type'} (t' : A -> Prop) (B : type686 A) (x : A) (t : type686 A) (x' : type684 A) (h1 : term250 A B x t x') : term398 A B x t x' t'.
Proof. exact (@lem4854846 A t' t' B x t x' h1). Qed.
Lemma lem4854850 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : False.
Proof. exact (@lem4854847 A t' B x t x' h2 (@lem4854843 A B x' t t' x h1 h2 h3)). Qed.
Lemma lem4854851 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : term399.
Proof. exact (fun h0 : ~ False => @lem4854850 A B x' t t' x h1 h2 h3). Qed.
Lemma lem4854853 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4854854 : term399 = False.
Proof. exact (@lem4854853 False). Qed.
Lemma lem4854855 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (t' : A -> Prop) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term121 A t t' x) : False.
Proof. exact (EQ_MP (@lem4854854) (@lem4854851 A B x' t t' x h1 h2 h3)). Qed.
Lemma lem4854856 {A : Type'} (B : type686 A) (x' : type684 A) (t : type686 A) (x : A) (h1 : term115 A t B) (h2 : term250 A B x t x') (h3 : term124 A t x) : False.
Proof. exact (ex_elim (@lem4854023 A t x h3) (fun t' : A -> Prop => fun h0 : term123 A t x t' => @lem4854855 A B x' t t' x h1 h2 h0)). Qed.
Lemma lem4854857 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (h1 : term115 A t B) (h2 : term124 A t x) (h3 : term157 A B x t) : False.
Proof. exact (ex_elim (@lem4854283 A B x t h3) (fun x' : type684 A => fun h0 : term252 A B x t x' => @lem4854856 A B x' t x h1 h0 h2)). Qed.
Lemma lem4854858 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (h1 : term115 A t B) (h2 : term124 A t x) (h3 : term157 A B x t) : (term124 A t x) = False.
Proof. exact (prop_ext (fun h4 : term124 A t x => @lem4854857 A B x t h1 h2 h3) (fun h4 : False => @lem4854023 A t x h2)). Qed.
Lemma lem4854859 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (h1 : term115 A t B) (h2 : term124 A t x) (h3 : term157 A B x t) : False.
Proof. exact (EQ_MP (@lem4854858 A B x t h1 h2 h3) (@lem4854023 A t x h2)). Qed.
Lemma lem4854860 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (h1 : term115 A t B) (h2 : term124 A t x) (h3 : term157 A B x t) : (term157 A B x t) = False.
Proof. exact (prop_ext (fun h4 : term157 A B x t => @lem4854859 A B x t h1 h2 h3) (fun h4 : False => @lem4853935 A B x t h3)). Qed.
Lemma lem4854861 {A : Type'} (B : type686 A) (x : A) (t : type686 A) (h1 : term115 A t B) (h2 : term124 A t x) (h3 : term157 A B x t) : False.
Proof. exact (EQ_MP (@lem4854860 A B x t h1 h2 h3) (@lem4853935 A B x t h3)). Qed.
Lemma lem4854862 {A : Type'} (B : type686 A) (t : type686 A) (x : A) (h1 : term115 A t B) (h2 : term124 A t x) : term156 A B x t.
Proof. exact (fun h0 : term157 A B x t => @lem4854861 A B x t h1 h2 h0). Qed.
Lemma lem4854863 {A : Type'} (B : type686 A) (t : type686 A) (x : A) (h1 : term115 A t B) (h2 : term124 A t x) : term137 A B x t.
Proof. exact (EQ_MP (@lem4853934 A B x t) (@lem4854862 A B t x h1 h2)). Qed.
Lemma lem4854864 {A : Type'} (x : A) (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term138 A B x t.
Proof. exact (fun h0 : term124 A t x => @lem4854863 A B t x h1 h0). Qed.
Lemma lem4854869 {A : Type'} (t : type686 A) (B : type686 A) (h1 : term115 A t B) : term140 A B t.
Proof. exact (fun x : A => @lem4854864 A x t B h1). Qed.
Lemma lem4854870 {A : Type'} (B : type686 A) (t : type686 A) : term141 A B t.
Proof. exact (fun h0 : term115 A t B => @lem4854869 A t B h0). Qed.
Lemma lem4854875 {A : Type'} (B : type686 A) : term143 A B.
Proof. exact (fun t : type686 A => @lem4854870 A B t). Qed.
Lemma lem4854880 {A : Type'} : term155 A.
Proof. exact (fun B : type686 A => @lem4854875 A B). Qed.
Lemma lem4854881 {A : Type'} : term154 A.
Proof. exact (EQ_MP (@lem4853928 A) (@lem4854880 A)). Qed.
Lemma lem4854882 {A : Type'} (B : type686 A) : term400 A B.
Proof. exact (@lem4854881 A B). Qed.
Lemma lem4854883 {A : Type'} (B : type686 A) : (term400 A B) = (term145 A B).
Proof. exact (eq_refl (term400 A B)). Qed.
Lemma lem4854884 {A : Type'} (B : type686 A) : term145 A B.
Proof. exact (EQ_MP (@lem4854883 A B) (@lem4854882 A B)). Qed.
Lemma lem4854886 {A : Type'} (B : type686 A) : term145 A B.
Proof. exact (@lem4853665 A B (@lem4854884 A B)). Qed.
Lemma lem4854887 {A : Type'} (B : type686 A) (h1 : term146 A B) : False.
Proof. exact (@lem4854886 A B (@lem4853649 A B h1)). Qed.
Lemma lem4854888 {A : Type'} (B : type686 A) (h1 : term146 A B) : (term146 A B) = False.
Proof. exact (prop_ext (fun h2 : term146 A B => @lem4854887 A B h1) (fun h2 : False => @lem4853649 A B h1)). Qed.
Lemma lem4854889 {A : Type'} (B : type686 A) (h1 : term146 A B) : False.
Proof. exact (EQ_MP (@lem4854888 A B h1) (@lem4853649 A B h1)). Qed.
Lemma lem4854890 {A : Type'} (B : type686 A) : term145 A B.
Proof. exact (fun h0 : term146 A B => @lem4854889 A B h0). Qed.
Lemma lem4854891 {A : Type'} (B : type686 A) : term143 A B.
Proof. exact (EQ_MP (@lem4853648 A B) (@lem4854890 A B)). Qed.
Lemma lem4854892 {A : Type'} (B : type686 A) : term108 A B.
Proof. exact (EQ_MP (@lem4853644 A B) (@lem4854891 A B)). Qed.
Lemma lem4854893 {A : Type'} (B : type686 A) : term84 A B.
Proof. exact (EQ_MP (@lem4853467 A B) (@lem4854892 A B)). Qed.
Lemma lem4854894 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term27 A B s) : term27 A B s.
Proof. exact (h1). Qed.
Lemma lem4854896 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4853024 A P Q) (@lem4853023 A P Q)). Qed.
Lemma lem4854897 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4854896 A P Q). Qed.
Lemma lem4854898 {A : Type'} (B : type686 A) : (@UNION_OF A (@ARBITRARY A) B) = (term401 A B).
Proof. exact (@lem4854897 A (@ARBITRARY A) B). Qed.
Lemma lem4854906 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4853027 A s) (@lem4853026 A s)). Qed.
Lemma lem4854907 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4854906 A s). Qed.
Lemma lem4854908 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = True.
Proof. exact (@lem4854907 A u). Qed.
Lemma lem4854909 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4854910 {A : Type'} (u : type686 A) : (term77 A u) = (and True).
Proof. exact (MK_COMB (@lem4854909) (@lem4854908 A u)). Qed.
Lemma lem4854921 {A : Type'} (B : type686 A) (u : type686 A) (s : A -> Prop) : (term402 A B u s) = (term402 A B u s).
Proof. exact (eq_refl (term402 A B u s)). Qed.
Lemma lem4854922 {A : Type'} (B : type686 A) (u : type686 A) (s : A -> Prop) : (term403 A B u s) = (term404 A B u s).
Proof. exact (MK_COMB (@lem4854910 A u) (@lem4854921 A B u s)). Qed.
Lemma lem4854924 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4854925 {A : Type'} (B : type686 A) (u : type686 A) (s : A -> Prop) : (term404 A B u s) = (term402 A B u s).
Proof. exact (@lem4854924 (term402 A B u s)). Qed.
Lemma lem4854936 {A : Type'} (B : type686 A) (u : type686 A) (s : A -> Prop) : (term403 A B u s) = (term402 A B u s).
Proof. exact (TRANS (@lem4854922 A B u s) (@lem4854925 A B u s)). Qed.
Lemma lem4854937 {A : Type'} (B : type686 A) (s : A -> Prop) : (term405 A B s) = (term406 A B s).
Proof. exact (fun_ext (fun u : type686 A => @lem4854936 A B u s)). Qed.
Lemma lem4854938 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem4854939 {A : Type'} (B : type686 A) (s : A -> Prop) : (term407 A B s) = (term408 A B s).
Proof. exact (MK_COMB (@lem4854938 A) (@lem4854937 A B s)). Qed.
Lemma lem4854944 {A : Type'} (B : type686 A) : (term401 A B) = (term409 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4854939 A B s)). Qed.
Lemma lem4854945 {A : Type'} (B : type686 A) : (@UNION_OF A (@ARBITRARY A) B) = (term409 A B).
Proof. exact (TRANS (@lem4854898 A B) (@lem4854944 A B)). Qed.
Lemma lem4854946 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4854947 {A : Type'} (B : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) B s) = (term410 A B s).
Proof. exact (MK_COMB (@lem4854945 A B) (@lem4854946 A s)). Qed.
Lemma lem4854949 {A B : Type'} (f : A -> B) (y : A) : (term411 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4854950 {A : Type'} (f : type686 A) (y : A -> Prop) : (term412 A f y) = (f y).
Proof. exact (@lem4854949 (A -> Prop) Prop f y). Qed.
Lemma lem4854951 {A : Type'} (B : type686 A) (s : A -> Prop) : (term413 A B s) = (term410 A B s).
Proof. exact (@lem4854950 A (term409 A B) s). Qed.
Lemma lem4854952 {A : Type'} (B : type686 A) (s : A -> Prop) : (term410 A B s) = (term408 A B s).
Proof. exact (eq_refl (term410 A B s)). Qed.
Lemma lem4854953 {A : Type'} (B : type686 A) : (term414 A B) = (term409 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4854952 A B s)). Qed.
Lemma lem4854954 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4854955 {A : Type'} (B : type686 A) (s : A -> Prop) : (term413 A B s) = (term410 A B s).
Proof. exact (MK_COMB (@lem4854953 A B) (@lem4854954 A s)). Qed.
Lemma lem4854956 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4854957 {A : Type'} (B : type686 A) (s : A -> Prop) : (term415 A B s) = (term416 A B s).
Proof. exact (MK_COMB (@lem4854956) (@lem4854955 A B s)). Qed.
Lemma lem4854958 {A : Type'} (B : type686 A) (s : A -> Prop) : (term410 A B s) = (term408 A B s).
Proof. exact (eq_refl (term410 A B s)). Qed.
Lemma lem4854959 {A : Type'} (B : type686 A) (s : A -> Prop) : ((term413 A B s) = (term410 A B s)) = ((term410 A B s) = (term408 A B s)).
Proof. exact (MK_COMB (@lem4854957 A B s) (@lem4854958 A B s)). Qed.
Lemma lem4854960 {A : Type'} (B : type686 A) (s : A -> Prop) : (term410 A B s) = (term408 A B s).
Proof. exact (EQ_MP (@lem4854959 A B s) (@lem4854951 A B s)). Qed.
Lemma lem4854975 {A : Type'} (B : type686 A) (s : A -> Prop) : (@UNION_OF A (@ARBITRARY A) B s) = (term408 A B s).
Proof. exact (TRANS (@lem4854947 A B s) (@lem4854960 A B s)). Qed.
Lemma lem4854976 {A : Type'} (B : type686 A) (s : A -> Prop) : (term408 A B s) = (@UNION_OF A (@ARBITRARY A) B s).
Proof. exact (SYM (@lem4854975 A B s)). Qed.
Lemma lem4854977 (t1 : Prop) : term417 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4854978 (t1 : Prop) : (term417 t1) = (term418 t1).
Proof. exact (eq_refl (term417 t1)). Qed.
Lemma lem4854979 (t1 : Prop) : term418 t1.
Proof. exact (EQ_MP (@lem4854978 t1) (@lem4854977 t1)). Qed.
Lemma lem4854980 (t1 : Prop) (t2 : Prop) : term419 t1 t2.
Proof. exact (@lem4854979 t1 t2). Qed.
Lemma lem4854981 (t1 : Prop) (t2 : Prop) : (term419 t1 t2) = (term420 t1 t2).
Proof. exact (eq_refl (term419 t1 t2)). Qed.
Lemma lem4854982 (t1 : Prop) (t2 : Prop) : term420 t1 t2.
Proof. exact (EQ_MP (@lem4854981 t1 t2) (@lem4854980 t1 t2)). Qed.
Lemma lem4854983 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term421 t1 t2 t3.
Proof. exact (@lem4854982 t1 t2 t3). Qed.
Lemma lem4854984 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term421 t1 t2 t3) = ((term360 t1 t2 t3) = (term422 t1 t2 t3)).
Proof. exact (eq_refl (term421 t1 t2 t3)). Qed.
Lemma lem4854985 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term360 t1 t2 t3) = (term422 t1 t2 t3).
Proof. exact (EQ_MP (@lem4854984 t1 t2 t3) (@lem4854983 t1 t2 t3)). Qed.
Lemma lem4854986 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term422 t1 t2 t3) = (term360 t1 t2 t3).
Proof. exact (SYM (@lem4854985 t1 t2 t3)). Qed.
Lemma lem4855004 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4855005 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (@lem4855004 A s t). Qed.
Lemma lem4855006 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (@SUBSET A u s) = (term87 A u s).
Proof. exact (@lem4855005 A u s). Qed.
Lemma lem4855013 {A : Type'} (x : A) (u : A -> Prop) : (term90 A x u) = (term90 A x u).
Proof. exact (eq_refl (term90 A x u)). Qed.
Lemma lem4855014 {A : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) : (term423 A x u s) = (term424 A x u s).
Proof. exact (MK_COMB (@lem4855013 A x u) (@lem4855006 A u s)). Qed.
Lemma lem4855017 {A : Type'} (u : A -> Prop) (B : type686 A) : (term93 A u B) = (term93 A u B).
Proof. exact (eq_refl (term93 A u B)). Qed.
Lemma lem4855018 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term425 A B x u s) = (term426 A B x u s).
Proof. exact (MK_COMB (@lem4855017 A u B) (@lem4855014 A x u s)). Qed.
Lemma lem4855021 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term427 A B x s) = (term428 A B x s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855018 A B x u s)). Qed.
Lemma lem4855022 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855023 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term429 A B x s) = (term430 A B x s).
Proof. exact (MK_COMB (@lem4855022 A) (@lem4855021 A B x s)). Qed.
Lemma lem4855028 {A : Type'} (x : A) (s : A -> Prop) : (term127 A x s) = (term127 A x s).
Proof. exact (eq_refl (term127 A x s)). Qed.
Lemma lem4855029 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term431 A B x s) = (term432 A B x s).
Proof. exact (MK_COMB (@lem4855028 A x s) (@lem4855023 A B x s)). Qed.
Lemma lem4855032 {A : Type'} (B : type686 A) (s : A -> Prop) : (term433 A B s) = (term434 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855029 A B x s)). Qed.
Lemma lem4855033 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855034 {A : Type'} (B : type686 A) (s : A -> Prop) : (term27 A B s) = (term435 A B s).
Proof. exact (MK_COMB (@lem4855033 A) (@lem4855032 A B s)). Qed.
Lemma lem4855039 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855040 {A : Type'} (B : type686 A) (s : A -> Prop) : (term436 A B s) = (term437 A B s).
Proof. exact (MK_COMB (@lem4855039) (@lem4855034 A B s)). Qed.
Lemma lem4855056 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4855057 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (@lem4855056 A s t). Qed.
Lemma lem4855058 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (@SUBSET A u s) = (term87 A u s).
Proof. exact (@lem4855057 A u s). Qed.
Lemma lem4855065 {A : Type'} (u : A -> Prop) (B : type686 A) : (term93 A u B) = (term93 A u B).
Proof. exact (eq_refl (term93 A u B)). Qed.
Lemma lem4855066 {A : Type'} (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term438 A B u s) = (term439 A B u s).
Proof. exact (MK_COMB (@lem4855065 A u B) (@lem4855058 A u s)). Qed.
Lemma lem4855069 {A : Type'} (GEN_PVAR_210 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_210) = (@SETSPEC (A -> Prop) GEN_PVAR_210).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_210)). Qed.
Lemma lem4855070 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term440 A GEN_PVAR_210 B u s) = (term441 A GEN_PVAR_210 B u s).
Proof. exact (MK_COMB (@lem4855069 A GEN_PVAR_210) (@lem4855066 A B u s)). Qed.
Lemma lem4855071 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4855072 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) (u : A -> Prop) : (term442 A GEN_PVAR_210 B s u) = (term443 A GEN_PVAR_210 B s u).
Proof. exact (MK_COMB (@lem4855070 A GEN_PVAR_210 B u s) (@lem4855071 A u)). Qed.
Lemma lem4855073 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term444 A GEN_PVAR_210 B s) = (term445 A GEN_PVAR_210 B s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855072 A GEN_PVAR_210 B s u)). Qed.
Lemma lem4855074 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855075 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term446 A GEN_PVAR_210 B s) = (term447 A GEN_PVAR_210 B s).
Proof. exact (MK_COMB (@lem4855074 A) (@lem4855073 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855080 {A : Type'} (B : type686 A) (s : A -> Prop) : (term448 A B s) = (term449 A B s).
Proof. exact (fun_ext (fun GEN_PVAR_210 : A -> Prop => @lem4855075 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855081 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4855082 {A : Type'} (B : type686 A) (s : A -> Prop) : (term450 A B s) = (term451 A B s).
Proof. exact (MK_COMB (@lem4855081 A) (@lem4855080 A B s)). Qed.
Lemma lem4855083 {A : Type'} (c : A -> Prop) : (@IN (A -> Prop) c) = (@IN (A -> Prop) c).
Proof. exact (eq_refl (@IN (A -> Prop) c)). Qed.
Lemma lem4855084 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term452 A c B s) = (term453 A c B s).
Proof. exact (MK_COMB (@lem4855083 A c) (@lem4855082 A B s)). Qed.
Lemma lem4855085 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855086 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term454 A c B s) = (term455 A c B s).
Proof. exact (MK_COMB (@lem4855085) (@lem4855084 A c B s)). Qed.
Lemma lem4855087 {A : Type'} (B : type686 A) (c : A -> Prop) : (B c) = (B c).
Proof. exact (eq_refl (B c)). Qed.
Lemma lem4855088 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term456 A s B c) = (term457 A s B c).
Proof. exact (MK_COMB (@lem4855086 A c B s) (@lem4855087 A B c)). Qed.
Lemma lem4855091 {A : Type'} (s : A -> Prop) (B : type686 A) : (term458 A s B) = (term459 A s B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4855088 A s B c)). Qed.
Lemma lem4855092 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4855093 {A : Type'} (s : A -> Prop) (B : type686 A) : (term460 A s B) = (term461 A s B).
Proof. exact (MK_COMB (@lem4855092 A) (@lem4855091 A s B)). Qed.
Lemma lem4855098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855099 {A : Type'} (s : A -> Prop) (B : type686 A) : (term462 A s B) = (term463 A s B).
Proof. exact (MK_COMB (@lem4855098) (@lem4855093 A s B)). Qed.
Lemma lem4855103 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term464 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4855104 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term464 A s t).
Proof. exact (@lem4855103 A s t). Qed.
Lemma lem4855105 {A : Type'} (B : type686 A) (s : A -> Prop) : ((term465 A B s) = s) = (term466 A B s).
Proof. exact (@lem4855104 A (term465 A B s) s). Qed.
Lemma lem4855121 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem4855122 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term87 A s t).
Proof. exact (@lem4855121 A s t). Qed.
Lemma lem4855123 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (@SUBSET A u s) = (term87 A u s).
Proof. exact (@lem4855122 A u s). Qed.
Lemma lem4855130 {A : Type'} (u : A -> Prop) (B : type686 A) : (term93 A u B) = (term93 A u B).
Proof. exact (eq_refl (term93 A u B)). Qed.
Lemma lem4855131 {A : Type'} (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term438 A B u s) = (term439 A B u s).
Proof. exact (MK_COMB (@lem4855130 A u B) (@lem4855123 A u s)). Qed.
Lemma lem4855134 {A : Type'} (GEN_PVAR_210 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_210) = (@SETSPEC (A -> Prop) GEN_PVAR_210).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_210)). Qed.
Lemma lem4855135 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term440 A GEN_PVAR_210 B u s) = (term441 A GEN_PVAR_210 B u s).
Proof. exact (MK_COMB (@lem4855134 A GEN_PVAR_210) (@lem4855131 A B u s)). Qed.
Lemma lem4855136 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4855137 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) (u : A -> Prop) : (term442 A GEN_PVAR_210 B s u) = (term443 A GEN_PVAR_210 B s u).
Proof. exact (MK_COMB (@lem4855135 A GEN_PVAR_210 B u s) (@lem4855136 A u)). Qed.
Lemma lem4855138 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term444 A GEN_PVAR_210 B s) = (term445 A GEN_PVAR_210 B s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855137 A GEN_PVAR_210 B s u)). Qed.
Lemma lem4855139 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855140 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term446 A GEN_PVAR_210 B s) = (term447 A GEN_PVAR_210 B s).
Proof. exact (MK_COMB (@lem4855139 A) (@lem4855138 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855145 {A : Type'} (B : type686 A) (s : A -> Prop) : (term448 A B s) = (term449 A B s).
Proof. exact (fun_ext (fun GEN_PVAR_210 : A -> Prop => @lem4855140 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855146 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4855147 {A : Type'} (B : type686 A) (s : A -> Prop) : (term450 A B s) = (term451 A B s).
Proof. exact (MK_COMB (@lem4855146 A) (@lem4855145 A B s)). Qed.
Lemma lem4855148 {A : Type'} : (@UNIONS A) = (@UNIONS A).
Proof. exact (eq_refl (@UNIONS A)). Qed.
Lemma lem4855149 {A : Type'} (B : type686 A) (s : A -> Prop) : (term465 A B s) = (term467 A B s).
Proof. exact (MK_COMB (@lem4855148 A) (@lem4855147 A B s)). Qed.
Lemma lem4855150 {A : Type'} (x : A) : (@IN A x) = (@IN A x).
Proof. exact (eq_refl (@IN A x)). Qed.
Lemma lem4855151 {A : Type'} (x : A) (B : type686 A) (s : A -> Prop) : (term468 A x B s) = (term469 A x B s).
Proof. exact (MK_COMB (@lem4855150 A x) (@lem4855149 A B s)). Qed.
Lemma lem4855152 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4855153 {A : Type'} (x : A) (B : type686 A) (s : A -> Prop) : (term470 A x B s) = (term471 A x B s).
Proof. exact (MK_COMB (@lem4855152) (@lem4855151 A x B s)). Qed.
Lemma lem4855154 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4855155 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : ((term468 A x B s) = (@IN A x s)) = ((term469 A x B s) = (@IN A x s)).
Proof. exact (MK_COMB (@lem4855153 A x B s) (@lem4855154 A x s)). Qed.
Lemma lem4855160 {A : Type'} (B : type686 A) (s : A -> Prop) : (term472 A B s) = (term473 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855155 A B x s)). Qed.
Lemma lem4855161 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855162 {A : Type'} (B : type686 A) (s : A -> Prop) : (term466 A B s) = (term474 A B s).
Proof. exact (MK_COMB (@lem4855161 A) (@lem4855160 A B s)). Qed.
Lemma lem4855167 {A : Type'} (B : type686 A) (s : A -> Prop) : ((term465 A B s) = s) = (term474 A B s).
Proof. exact (TRANS (@lem4855105 A B s) (@lem4855162 A B s)). Qed.
Lemma lem4855168 {A : Type'} (B : type686 A) (s : A -> Prop) : (term475 A B s) = (term476 A B s).
Proof. exact (MK_COMB (@lem4855099 A s B) (@lem4855167 A B s)). Qed.
Lemma lem4855171 {A : Type'} (B : type686 A) (s : A -> Prop) : (term477 A B s) = (term478 A B s).
Proof. exact (MK_COMB (@lem4855040 A B s) (@lem4855168 A B s)). Qed.
Lemma lem4855174 {A : Type'} (B : type686 A) (s : A -> Prop) : (term478 A B s) = (term477 A B s).
Proof. exact (SYM (@lem4855171 A B s)). Qed.
Lemma lem4855184 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855185 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855184 A P x). Qed.
Lemma lem4855186 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4855185 A s x). Qed.
Lemma lem4855187 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855188 {A : Type'} (s : A -> Prop) (x : A) : (term127 A x s) = (term128 A s x).
Proof. exact (MK_COMB (@lem4855187) (@lem4855186 A s x)). Qed.
Lemma lem4855196 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855197 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4855196 (A -> Prop) P x). Qed.
Lemma lem4855198 {A : Type'} (B : type686 A) (u : A -> Prop) : (@IN (A -> Prop) u B) = (B u).
Proof. exact (@lem4855197 A B u). Qed.
Lemma lem4855199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855200 {A : Type'} (B : type686 A) (u : A -> Prop) : (term93 A u B) = (term119 A B u).
Proof. exact (MK_COMB (@lem4855199) (@lem4855198 A B u)). Qed.
Lemma lem4855204 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855205 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855204 A P x). Qed.
Lemma lem4855206 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem4855205 A u x). Qed.
Lemma lem4855207 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855208 {A : Type'} (u : A -> Prop) (x : A) : (term90 A x u) = (term126 A u x).
Proof. exact (MK_COMB (@lem4855207) (@lem4855206 A u x)). Qed.
Lemma lem4855216 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855217 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855216 A P x). Qed.
Lemma lem4855218 {A : Type'} (u : A -> Prop) (x : A) : (@IN A x u) = (u x).
Proof. exact (@lem4855217 A u x). Qed.
Lemma lem4855219 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855220 {A : Type'} (u : A -> Prop) (x : A) : (term127 A x u) = (term128 A u x).
Proof. exact (MK_COMB (@lem4855219) (@lem4855218 A u x)). Qed.
Lemma lem4855222 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855223 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855222 A P x). Qed.
Lemma lem4855224 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4855223 A s x). Qed.
Lemma lem4855225 {A : Type'} (u : A -> Prop) (s : A -> Prop) (x : A) : (term479 A u x s) = (term480 A u s x).
Proof. exact (MK_COMB (@lem4855220 A u x) (@lem4855224 A s x)). Qed.
Lemma lem4855228 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term481 A u s) = (term482 A u s).
Proof. exact (fun_ext (fun x : A => @lem4855225 A u s x)). Qed.
Lemma lem4855229 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855230 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term87 A u s) = (term483 A u s).
Proof. exact (MK_COMB (@lem4855229 A) (@lem4855228 A u s)). Qed.
Lemma lem4855235 {A : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) : (term424 A x u s) = (term484 A x u s).
Proof. exact (MK_COMB (@lem4855208 A u x) (@lem4855230 A u s)). Qed.
Lemma lem4855238 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term426 A B x u s) = (term485 A B x u s).
Proof. exact (MK_COMB (@lem4855200 A B u) (@lem4855235 A x u s)). Qed.
Lemma lem4855241 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term428 A B x s) = (term486 A B x s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855238 A B x u s)). Qed.
Lemma lem4855242 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855243 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term430 A B x s) = (term487 A B x s).
Proof. exact (MK_COMB (@lem4855242 A) (@lem4855241 A B x s)). Qed.
Lemma lem4855248 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term432 A B x s) = (term488 A B x s).
Proof. exact (MK_COMB (@lem4855188 A s x) (@lem4855243 A B x s)). Qed.
Lemma lem4855251 {A : Type'} (B : type686 A) (s : A -> Prop) : (term434 A B s) = (term489 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855248 A B x s)). Qed.
Lemma lem4855252 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855253 {A : Type'} (B : type686 A) (s : A -> Prop) : (term435 A B s) = (term490 A B s).
Proof. exact (MK_COMB (@lem4855252 A) (@lem4855251 A B s)). Qed.
Lemma lem4855258 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855259 {A : Type'} (B : type686 A) (s : A -> Prop) : (term437 A B s) = (term491 A B s).
Proof. exact (MK_COMB (@lem4855258) (@lem4855253 A B s)). Qed.
Lemma lem4855269 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term492 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4855270 {A : Type'} (p : type686 A) (x : A -> Prop) : (term493 A x p) = (p x).
Proof. exact (@lem4855269 (A -> Prop) p x). Qed.
Lemma lem4855271 {A : Type'} (B : type686 A) (s : A -> Prop) (c : A -> Prop) : (term494 A c B s) = (term495 A B s c).
Proof. exact (@lem4855270 A (term496 A B s) c). Qed.
Lemma lem4855272 {A : Type'} (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term495 A B s u) = (term439 A B u s).
Proof. exact (eq_refl (term495 A B s u)). Qed.
Lemma lem4855273 {A : Type'} (GEN_PVAR_210 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_210) = (@SETSPEC (A -> Prop) GEN_PVAR_210).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_210)). Qed.
Lemma lem4855274 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term497 A GEN_PVAR_210 B s u) = (term441 A GEN_PVAR_210 B u s).
Proof. exact (MK_COMB (@lem4855273 A GEN_PVAR_210) (@lem4855272 A B u s)). Qed.
Lemma lem4855275 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4855276 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) (u : A -> Prop) : (term498 A GEN_PVAR_210 B s u) = (term443 A GEN_PVAR_210 B s u).
Proof. exact (MK_COMB (@lem4855274 A GEN_PVAR_210 B u s) (@lem4855275 A u)). Qed.
Lemma lem4855277 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term499 A GEN_PVAR_210 B s) = (term445 A GEN_PVAR_210 B s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855276 A GEN_PVAR_210 B s u)). Qed.
Lemma lem4855278 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855279 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term500 A GEN_PVAR_210 B s) = (term447 A GEN_PVAR_210 B s).
Proof. exact (MK_COMB (@lem4855278 A) (@lem4855277 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855280 {A : Type'} (B : type686 A) (s : A -> Prop) : (term501 A B s) = (term449 A B s).
Proof. exact (fun_ext (fun GEN_PVAR_210 : A -> Prop => @lem4855279 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855281 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4855282 {A : Type'} (B : type686 A) (s : A -> Prop) : (term502 A B s) = (term451 A B s).
Proof. exact (MK_COMB (@lem4855281 A) (@lem4855280 A B s)). Qed.
Lemma lem4855283 {A : Type'} (c : A -> Prop) : (@IN (A -> Prop) c) = (@IN (A -> Prop) c).
Proof. exact (eq_refl (@IN (A -> Prop) c)). Qed.
Lemma lem4855284 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term494 A c B s) = (term453 A c B s).
Proof. exact (MK_COMB (@lem4855283 A c) (@lem4855282 A B s)). Qed.
Lemma lem4855285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4855286 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term503 A c B s) = (term504 A c B s).
Proof. exact (MK_COMB (@lem4855285) (@lem4855284 A c B s)). Qed.
Lemma lem4855287 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term495 A B s c) = (term439 A B c s).
Proof. exact (eq_refl (term495 A B s c)). Qed.
Lemma lem4855288 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : ((term494 A c B s) = (term495 A B s c)) = ((term453 A c B s) = (term439 A B c s)).
Proof. exact (MK_COMB (@lem4855286 A c B s) (@lem4855287 A B c s)). Qed.
Lemma lem4855289 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term453 A c B s) = (term439 A B c s).
Proof. exact (EQ_MP (@lem4855288 A B c s) (@lem4855271 A B s c)). Qed.
Lemma lem4855293 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855294 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4855293 (A -> Prop) P x). Qed.
Lemma lem4855295 {A : Type'} (B : type686 A) (c : A -> Prop) : (@IN (A -> Prop) c B) = (B c).
Proof. exact (@lem4855294 A B c). Qed.
Lemma lem4855296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855297 {A : Type'} (B : type686 A) (c : A -> Prop) : (term93 A c B) = (term119 A B c).
Proof. exact (MK_COMB (@lem4855296) (@lem4855295 A B c)). Qed.
Lemma lem4855305 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855306 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855305 A P x). Qed.
Lemma lem4855307 {A : Type'} (c : A -> Prop) (x : A) : (@IN A x c) = (c x).
Proof. exact (@lem4855306 A c x). Qed.
Lemma lem4855308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855309 {A : Type'} (c : A -> Prop) (x : A) : (term127 A x c) = (term128 A c x).
Proof. exact (MK_COMB (@lem4855308) (@lem4855307 A c x)). Qed.
Lemma lem4855311 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855312 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855311 A P x). Qed.
Lemma lem4855313 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4855312 A s x). Qed.
Lemma lem4855314 {A : Type'} (c : A -> Prop) (s : A -> Prop) (x : A) : (term479 A c x s) = (term480 A c s x).
Proof. exact (MK_COMB (@lem4855309 A c x) (@lem4855313 A s x)). Qed.
Lemma lem4855317 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term481 A c s) = (term482 A c s).
Proof. exact (fun_ext (fun x : A => @lem4855314 A c s x)). Qed.
Lemma lem4855318 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855319 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term87 A c s) = (term483 A c s).
Proof. exact (MK_COMB (@lem4855318 A) (@lem4855317 A c s)). Qed.
Lemma lem4855324 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term439 A B c s) = (term505 A B c s).
Proof. exact (MK_COMB (@lem4855297 A B c) (@lem4855319 A c s)). Qed.
Lemma lem4855327 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term453 A c B s) = (term505 A B c s).
Proof. exact (TRANS (@lem4855289 A B c s) (@lem4855324 A B c s)). Qed.
Lemma lem4855328 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855329 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term455 A c B s) = (term506 A B c s).
Proof. exact (MK_COMB (@lem4855328) (@lem4855327 A B c s)). Qed.
Lemma lem4855330 {A : Type'} (B : type686 A) (c : A -> Prop) : (B c) = (B c).
Proof. exact (eq_refl (B c)). Qed.
Lemma lem4855331 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term457 A s B c) = (term507 A s B c).
Proof. exact (MK_COMB (@lem4855329 A B c s) (@lem4855330 A B c)). Qed.
Lemma lem4855334 {A : Type'} (s : A -> Prop) (B : type686 A) : (term459 A s B) = (term508 A s B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4855331 A s B c)). Qed.
Lemma lem4855335 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4855336 {A : Type'} (s : A -> Prop) (B : type686 A) : (term461 A s B) = (term509 A s B).
Proof. exact (MK_COMB (@lem4855335 A) (@lem4855334 A s B)). Qed.
Lemma lem4855341 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855342 {A : Type'} (s : A -> Prop) (B : type686 A) : (term463 A s B) = (term510 A s B).
Proof. exact (MK_COMB (@lem4855341) (@lem4855336 A s B)). Qed.
Lemma lem4855350 {A : Type'} (s : type686 A) (x : A) : (term117 A x s) = (term118 A s x).
Proof. exact (EQ_MP (@lem3211663 A s x) (@lem3211662 A s x)). Qed.
Lemma lem4855351 {A : Type'} (s : type686 A) (x : A) : (term117 A x s) = (term118 A s x).
Proof. exact (@lem4855350 A s x). Qed.
Lemma lem4855352 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term469 A x B s) = (term511 A B s x).
Proof. exact (@lem4855351 A (term451 A B s) x). Qed.
Lemma lem4855360 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term492 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3211641 _83095 p x) (@lem3211640 _83095 p x)). Qed.
Lemma lem4855361 {A : Type'} (p : type686 A) (x : A -> Prop) : (term493 A x p) = (p x).
Proof. exact (@lem4855360 (A -> Prop) p x). Qed.
Lemma lem4855362 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) : (term494 A t B s) = (term495 A B s t).
Proof. exact (@lem4855361 A (term496 A B s) t). Qed.
Lemma lem4855363 {A : Type'} (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term495 A B s u) = (term439 A B u s).
Proof. exact (eq_refl (term495 A B s u)). Qed.
Lemma lem4855364 {A : Type'} (GEN_PVAR_210 : A -> Prop) : (@SETSPEC (A -> Prop) GEN_PVAR_210) = (@SETSPEC (A -> Prop) GEN_PVAR_210).
Proof. exact (eq_refl (@SETSPEC (A -> Prop) GEN_PVAR_210)). Qed.
Lemma lem4855365 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (u : A -> Prop) (s : A -> Prop) : (term497 A GEN_PVAR_210 B s u) = (term441 A GEN_PVAR_210 B u s).
Proof. exact (MK_COMB (@lem4855364 A GEN_PVAR_210) (@lem4855363 A B u s)). Qed.
Lemma lem4855366 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4855367 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) (u : A -> Prop) : (term498 A GEN_PVAR_210 B s u) = (term443 A GEN_PVAR_210 B s u).
Proof. exact (MK_COMB (@lem4855365 A GEN_PVAR_210 B u s) (@lem4855366 A u)). Qed.
Lemma lem4855368 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term499 A GEN_PVAR_210 B s) = (term445 A GEN_PVAR_210 B s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855367 A GEN_PVAR_210 B s u)). Qed.
Lemma lem4855369 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855370 {A : Type'} (GEN_PVAR_210 : A -> Prop) (B : type686 A) (s : A -> Prop) : (term500 A GEN_PVAR_210 B s) = (term447 A GEN_PVAR_210 B s).
Proof. exact (MK_COMB (@lem4855369 A) (@lem4855368 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855371 {A : Type'} (B : type686 A) (s : A -> Prop) : (term501 A B s) = (term449 A B s).
Proof. exact (fun_ext (fun GEN_PVAR_210 : A -> Prop => @lem4855370 A GEN_PVAR_210 B s)). Qed.
Lemma lem4855372 {A : Type'} : (@GSPEC (A -> Prop)) = (@GSPEC (A -> Prop)).
Proof. exact (eq_refl (@GSPEC (A -> Prop))). Qed.
Lemma lem4855373 {A : Type'} (B : type686 A) (s : A -> Prop) : (term502 A B s) = (term451 A B s).
Proof. exact (MK_COMB (@lem4855372 A) (@lem4855371 A B s)). Qed.
Lemma lem4855374 {A : Type'} (t : A -> Prop) : (@IN (A -> Prop) t) = (@IN (A -> Prop) t).
Proof. exact (eq_refl (@IN (A -> Prop) t)). Qed.
Lemma lem4855375 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) : (term494 A t B s) = (term453 A t B s).
Proof. exact (MK_COMB (@lem4855374 A t) (@lem4855373 A B s)). Qed.
Lemma lem4855376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4855377 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) : (term503 A t B s) = (term504 A t B s).
Proof. exact (MK_COMB (@lem4855376) (@lem4855375 A t B s)). Qed.
Lemma lem4855378 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term495 A B s t) = (term439 A B t s).
Proof. exact (eq_refl (term495 A B s t)). Qed.
Lemma lem4855379 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : ((term494 A t B s) = (term495 A B s t)) = ((term453 A t B s) = (term439 A B t s)).
Proof. exact (MK_COMB (@lem4855377 A t B s) (@lem4855378 A B t s)). Qed.
Lemma lem4855380 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term453 A t B s) = (term439 A B t s).
Proof. exact (EQ_MP (@lem4855379 A B t s) (@lem4855362 A B s t)). Qed.
Lemma lem4855384 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855385 {A : Type'} (P : type686 A) (x : A -> Prop) : (@IN (A -> Prop) x P) = (P x).
Proof. exact (@lem4855384 (A -> Prop) P x). Qed.
Lemma lem4855386 {A : Type'} (B : type686 A) (t : A -> Prop) : (@IN (A -> Prop) t B) = (B t).
Proof. exact (@lem4855385 A B t). Qed.
Lemma lem4855387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855388 {A : Type'} (B : type686 A) (t : A -> Prop) : (term93 A t B) = (term119 A B t).
Proof. exact (MK_COMB (@lem4855387) (@lem4855386 A B t)). Qed.
Lemma lem4855396 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855397 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855396 A P x). Qed.
Lemma lem4855398 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4855397 A t x). Qed.
Lemma lem4855399 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855400 {A : Type'} (t : A -> Prop) (x : A) : (term127 A x t) = (term128 A t x).
Proof. exact (MK_COMB (@lem4855399) (@lem4855398 A t x)). Qed.
Lemma lem4855402 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855403 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855402 A P x). Qed.
Lemma lem4855404 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4855403 A s x). Qed.
Lemma lem4855405 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term479 A t x s) = (term480 A t s x).
Proof. exact (MK_COMB (@lem4855400 A t x) (@lem4855404 A s x)). Qed.
Lemma lem4855408 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term481 A t s) = (term482 A t s).
Proof. exact (fun_ext (fun x : A => @lem4855405 A t s x)). Qed.
Lemma lem4855409 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855410 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term87 A t s) = (term483 A t s).
Proof. exact (MK_COMB (@lem4855409 A) (@lem4855408 A t s)). Qed.
Lemma lem4855415 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term439 A B t s) = (term505 A B t s).
Proof. exact (MK_COMB (@lem4855388 A B t) (@lem4855410 A t s)). Qed.
Lemma lem4855418 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term453 A t B s) = (term505 A B t s).
Proof. exact (TRANS (@lem4855380 A B t s) (@lem4855415 A B t s)). Qed.
Lemma lem4855419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855420 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term512 A t B s) = (term513 A B t s).
Proof. exact (MK_COMB (@lem4855419) (@lem4855418 A B t s)). Qed.
Lemma lem4855422 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855423 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855422 A P x). Qed.
Lemma lem4855424 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem4855423 A t x). Qed.
Lemma lem4855425 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term514 A B s x t) = (term515 A B s t x).
Proof. exact (MK_COMB (@lem4855420 A B t s) (@lem4855424 A t x)). Qed.
Lemma lem4855428 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term516 A B s x) = (term517 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4855425 A B s t x)). Qed.
Lemma lem4855429 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855430 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term511 A B s x) = (term518 A B s x).
Proof. exact (MK_COMB (@lem4855429 A) (@lem4855428 A B s x)). Qed.
Lemma lem4855435 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term469 A x B s) = (term518 A B s x).
Proof. exact (TRANS (@lem4855352 A B s x) (@lem4855430 A B s x)). Qed.
Lemma lem4855436 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4855437 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term471 A x B s) = (term519 A B s x).
Proof. exact (MK_COMB (@lem4855436) (@lem4855435 A B s x)). Qed.
Lemma lem4855439 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4855440 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4855439 A P x). Qed.
Lemma lem4855441 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem4855440 A s x). Qed.
Lemma lem4855442 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : ((term469 A x B s) = (@IN A x s)) = ((term518 A B s x) = (s x)).
Proof. exact (MK_COMB (@lem4855437 A B s x) (@lem4855441 A s x)). Qed.
Lemma lem4855445 {A : Type'} (B : type686 A) (s : A -> Prop) : (term473 A B s) = (term520 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855442 A B s x)). Qed.
Lemma lem4855446 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855447 {A : Type'} (B : type686 A) (s : A -> Prop) : (term474 A B s) = (term521 A B s).
Proof. exact (MK_COMB (@lem4855446 A) (@lem4855445 A B s)). Qed.
Lemma lem4855452 {A : Type'} (B : type686 A) (s : A -> Prop) : (term476 A B s) = (term522 A B s).
Proof. exact (MK_COMB (@lem4855342 A s B) (@lem4855447 A B s)). Qed.
Lemma lem4855455 {A : Type'} (B : type686 A) (s : A -> Prop) : (term478 A B s) = (term523 A B s).
Proof. exact (MK_COMB (@lem4855259 A B s) (@lem4855452 A B s)). Qed.
Lemma lem4855458 {A : Type'} (B : type686 A) (s : A -> Prop) : (term523 A B s) = (term478 A B s).
Proof. exact (SYM (@lem4855455 A B s)). Qed.
Lemma lem4855460 (p : Prop) : p = (term144 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4855461 {A : Type'} (B : type686 A) (s : A -> Prop) : (term523 A B s) = (term524 A B s).
Proof. exact (@lem4855460 (term523 A B s)). Qed.
Lemma lem4855462 {A : Type'} (B : type686 A) (s : A -> Prop) : (term524 A B s) = (term523 A B s).
Proof. exact (SYM (@lem4855461 A B s)). Qed.
Lemma lem4855463 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term525 A B s) : term525 A B s.
Proof. exact (h1). Qed.
Lemma lem4855466 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term524 A B s) : term524 A B s.
Proof. exact (h1). Qed.
Lemma lem4855467 {A : Type'} (B : type686 A) (s : A -> Prop) : term526 A B s.
Proof. exact (fun h0 : term524 A B s => @lem4855466 A B s h0). Qed.
Lemma lem4855468 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term526 A B s) : term526 A B s.
Proof. exact (h1). Qed.
Lemma lem4855469 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term524 A B s) : term524 A B s.
Proof. exact (h1). Qed.
Lemma lem4855470 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term524 A B s) (h2 : term526 A B s) : term524 A B s.
Proof. exact (@lem4855468 A B s h2 (@lem4855469 A B s h1)). Qed.
Lemma lem4855471 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term524 A B s) : term527 A B s.
Proof. exact (fun h0 : term526 A B s => @lem4855470 A B s h1 h0). Qed.
Lemma lem4855472 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term526 A B s) : term526 A B s.
Proof. exact (h1). Qed.
Lemma lem4855473 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term524 A B s) (h2 : term526 A B s) : term524 A B s.
Proof. exact (@lem4855471 A B s h1 (@lem4855472 A B s h2)). Qed.
Lemma lem4855474 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term526 A B s) : term526 A B s.
Proof. exact (fun h0 : term524 A B s => @lem4855473 A B s h0 h1). Qed.
Lemma lem4855475 {A : Type'} (B : type686 A) (s : A -> Prop) : term528 A B s.
Proof. exact (fun h0 : term526 A B s => @lem4855474 A B s h0). Qed.
Lemma lem4855478 {A : Type'} (B : type686 A) (s : A -> Prop) : term526 A B s.
Proof. exact (@lem4855475 A B s (@lem4855467 A B s)). Qed.
Lemma lem4855479 {A : Type'} (B : type686 A) (s : A -> Prop) : term526 A B s.
Proof. exact (@lem4855478 A B s). Qed.
Lemma lem4855489 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4855490 {A : Type'} (B : type686 A) (s : A -> Prop) : (term524 A B s) = (term529 A B s).
Proof. exact (@lem4855489 (term525 A B s)). Qed.
Lemma lem4855492 (t : Prop) : (term151 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4855493 {A : Type'} (B : type686 A) (s : A -> Prop) : (term529 A B s) = (term523 A B s).
Proof. exact (@lem4855492 (term523 A B s)). Qed.
Lemma lem4855496 {A : Type'} (B : type686 A) (s : A -> Prop) : (term524 A B s) = (term523 A B s).
Proof. exact (TRANS (@lem4855490 A B s) (@lem4855493 A B s)). Qed.
Lemma lem4855619 {A : Type'} (s : A -> Prop) : (term530 A s) = (term531 A s).
Proof. exact (fun_ext (fun B : type686 A => @lem4855496 A B s)). Qed.
Lemma lem4855620 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4855621 {A : Type'} (s : A -> Prop) : (term532 A s) = (term533 A s).
Proof. exact (MK_COMB (@lem4855620 A) (@lem4855619 A s)). Qed.
Lemma lem4855626 {A : Type'} : (term534 A) = (term535 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4855621 A s)). Qed.
Lemma lem4855627 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4855636 {A : Type'} : (term536 A) = (term537 A).
Proof. exact (MK_COMB (@lem4855627 A) (@lem4855626 A)). Qed.
Lemma lem4855637 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4855638 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4855643 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term480 A t s x) = (term480 A t s x).
Proof. exact (eq_refl (term480 A t s x)). Qed.
Lemma lem4855644 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term482 A t s) = (term482 A t s).
Proof. exact (fun_ext (fun x : A => @lem4855643 A t s x)). Qed.
Lemma lem4855645 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855646 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term483 A t s) = (term483 A t s).
Proof. exact (MK_COMB (@lem4855645 A) (@lem4855644 A t s)). Qed.
Lemma lem4855649 {A : Type'} (B : type686 A) (t : A -> Prop) : (term119 A B t) = (term119 A B t).
Proof. exact (eq_refl (term119 A B t)). Qed.
Lemma lem4855650 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term505 A B t s) = (term505 A B t s).
Proof. exact (MK_COMB (@lem4855649 A B t) (@lem4855646 A t s)). Qed.
Lemma lem4855651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855652 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term513 A B t s) = (term513 A B t s).
Proof. exact (MK_COMB (@lem4855651) (@lem4855650 A B t s)). Qed.
Lemma lem4855653 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term515 A B s t x) = (term515 A B s t x).
Proof. exact (MK_COMB (@lem4855652 A B t s) (@lem4855638 A t x)). Qed.
Lemma lem4855654 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term517 A B s x) = (term517 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4855653 A B s t x)). Qed.
Lemma lem4855655 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855656 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term518 A B s x) = (term518 A B s x).
Proof. exact (MK_COMB (@lem4855655 A) (@lem4855654 A B s x)). Qed.
Lemma lem4855657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4855658 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term519 A B s x) = (term519 A B s x).
Proof. exact (MK_COMB (@lem4855657) (@lem4855656 A B s x)). Qed.
Lemma lem4855659 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : ((term518 A B s x) = (s x)) = ((term518 A B s x) = (s x)).
Proof. exact (MK_COMB (@lem4855658 A B s x) (@lem4855637 A s x)). Qed.
Lemma lem4855660 {A : Type'} (B : type686 A) (s : A -> Prop) : (term520 A B s) = (term520 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855659 A B s x)). Qed.
Lemma lem4855661 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855662 {A : Type'} (B : type686 A) (s : A -> Prop) : (term521 A B s) = (term521 A B s).
Proof. exact (MK_COMB (@lem4855661 A) (@lem4855660 A B s)). Qed.
Lemma lem4855663 {A : Type'} (B : type686 A) (c : A -> Prop) : (B c) = (B c).
Proof. exact (eq_refl (B c)). Qed.
Lemma lem4855668 {A : Type'} (c : A -> Prop) (s : A -> Prop) (x : A) : (term480 A c s x) = (term480 A c s x).
Proof. exact (eq_refl (term480 A c s x)). Qed.
Lemma lem4855669 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term482 A c s) = (term482 A c s).
Proof. exact (fun_ext (fun x : A => @lem4855668 A c s x)). Qed.
Lemma lem4855670 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855671 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term483 A c s) = (term483 A c s).
Proof. exact (MK_COMB (@lem4855670 A) (@lem4855669 A c s)). Qed.
Lemma lem4855674 {A : Type'} (B : type686 A) (c : A -> Prop) : (term119 A B c) = (term119 A B c).
Proof. exact (eq_refl (term119 A B c)). Qed.
Lemma lem4855675 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term505 A B c s) = (term505 A B c s).
Proof. exact (MK_COMB (@lem4855674 A B c) (@lem4855671 A c s)). Qed.
Lemma lem4855676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855677 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term506 A B c s) = (term506 A B c s).
Proof. exact (MK_COMB (@lem4855676) (@lem4855675 A B c s)). Qed.
Lemma lem4855678 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term507 A s B c) = (term507 A s B c).
Proof. exact (MK_COMB (@lem4855677 A B c s) (@lem4855663 A B c)). Qed.
Lemma lem4855679 {A : Type'} (s : A -> Prop) (B : type686 A) : (term508 A s B) = (term508 A s B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4855678 A s B c)). Qed.
Lemma lem4855680 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4855681 {A : Type'} (s : A -> Prop) (B : type686 A) : (term509 A s B) = (term509 A s B).
Proof. exact (MK_COMB (@lem4855680 A) (@lem4855679 A s B)). Qed.
Lemma lem4855682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4855683 {A : Type'} (s : A -> Prop) (B : type686 A) : (term510 A s B) = (term510 A s B).
Proof. exact (MK_COMB (@lem4855682) (@lem4855681 A s B)). Qed.
Lemma lem4855684 {A : Type'} (B : type686 A) (s : A -> Prop) : (term522 A B s) = (term522 A B s).
Proof. exact (MK_COMB (@lem4855683 A s B) (@lem4855662 A B s)). Qed.
Lemma lem4855689 {A : Type'} (u : A -> Prop) (s : A -> Prop) (x : A) : (term480 A u s x) = (term480 A u s x).
Proof. exact (eq_refl (term480 A u s x)). Qed.
Lemma lem4855690 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term482 A u s) = (term482 A u s).
Proof. exact (fun_ext (fun x : A => @lem4855689 A u s x)). Qed.
Lemma lem4855691 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855692 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term483 A u s) = (term483 A u s).
Proof. exact (MK_COMB (@lem4855691 A) (@lem4855690 A u s)). Qed.
Lemma lem4855695 {A : Type'} (u : A -> Prop) (x : A) : (term126 A u x) = (term126 A u x).
Proof. exact (eq_refl (term126 A u x)). Qed.
Lemma lem4855696 {A : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) : (term484 A x u s) = (term484 A x u s).
Proof. exact (MK_COMB (@lem4855695 A u x) (@lem4855692 A u s)). Qed.
Lemma lem4855699 {A : Type'} (B : type686 A) (u : A -> Prop) : (term119 A B u) = (term119 A B u).
Proof. exact (eq_refl (term119 A B u)). Qed.
Lemma lem4855700 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term485 A B x u s) = (term485 A B x u s).
Proof. exact (MK_COMB (@lem4855699 A B u) (@lem4855696 A x u s)). Qed.
Lemma lem4855701 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term486 A B x s) = (term486 A B x s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855700 A B x u s)). Qed.
Lemma lem4855702 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855703 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term487 A B x s) = (term487 A B x s).
Proof. exact (MK_COMB (@lem4855702 A) (@lem4855701 A B x s)). Qed.
Lemma lem4855706 {A : Type'} (s : A -> Prop) (x : A) : (term128 A s x) = (term128 A s x).
Proof. exact (eq_refl (term128 A s x)). Qed.
Lemma lem4855707 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term488 A B x s) = (term488 A B x s).
Proof. exact (MK_COMB (@lem4855706 A s x) (@lem4855703 A B x s)). Qed.
Lemma lem4855708 {A : Type'} (B : type686 A) (s : A -> Prop) : (term489 A B s) = (term489 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855707 A B x s)). Qed.
Lemma lem4855709 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855710 {A : Type'} (B : type686 A) (s : A -> Prop) : (term490 A B s) = (term490 A B s).
Proof. exact (MK_COMB (@lem4855709 A) (@lem4855708 A B s)). Qed.
Lemma lem4855711 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4855712 {A : Type'} (B : type686 A) (s : A -> Prop) : (term491 A B s) = (term491 A B s).
Proof. exact (MK_COMB (@lem4855711) (@lem4855710 A B s)). Qed.
Lemma lem4855713 {A : Type'} (B : type686 A) (s : A -> Prop) : (term523 A B s) = (term523 A B s).
Proof. exact (MK_COMB (@lem4855712 A B s) (@lem4855684 A B s)). Qed.
Lemma lem4855714 {A : Type'} (s : A -> Prop) : (term531 A s) = (term531 A s).
Proof. exact (fun_ext (fun B : type686 A => @lem4855713 A B s)). Qed.
Lemma lem4855715 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4855716 {A : Type'} (s : A -> Prop) : (term533 A s) = (term533 A s).
Proof. exact (MK_COMB (@lem4855715 A) (@lem4855714 A s)). Qed.
Lemma lem4855717 {A : Type'} : (term535 A) = (term535 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4855716 A s)). Qed.
Lemma lem4855718 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4855719 {A : Type'} : (term537 A) = (term537 A).
Proof. exact (MK_COMB (@lem4855718 A) (@lem4855717 A)). Qed.
Lemma lem4855806 {A : Type'} : (term536 A) = (term537 A).
Proof. exact (TRANS (@lem4855636 A) (@lem4855719 A)). Qed.
Lemma lem4855807 {A : Type'} : (term537 A) = (term536 A).
Proof. exact (SYM (@lem4855806 A)). Qed.
Lemma lem4855808 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) : term490 A B s.
Proof. exact (h1). Qed.
Lemma lem4855810 (p : Prop) : p = (term144 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4855811 {A : Type'} (B : type686 A) (s : A -> Prop) : (term522 A B s) = (term538 A B s).
Proof. exact (@lem4855810 (term522 A B s)). Qed.
Lemma lem4855812 {A : Type'} (B : type686 A) (s : A -> Prop) : (term538 A B s) = (term522 A B s).
Proof. exact (SYM (@lem4855811 A B s)). Qed.
Lemma lem4855813 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term539 A B s) : term539 A B s.
Proof. exact (h1). Qed.
Lemma lem4855823 {A : Type'} (u : A -> Prop) (s : A -> Prop) (x : A) : (term480 A u s x) = (term540 A u s x).
Proof. exact (@lem17265 (u x) (s x)). Qed.
Lemma lem4855824 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term482 A u s) = (term541 A u s).
Proof. exact (fun_ext (fun x : A => @lem4855823 A u s x)). Qed.
Lemma lem4855825 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855826 {A : Type'} (u : A -> Prop) (s : A -> Prop) : (term483 A u s) = (term542 A u s).
Proof. exact (MK_COMB (@lem4855825 A) (@lem4855824 A u s)). Qed.
Lemma lem4855828 {A : Type'} (u : A -> Prop) (x : A) : (term126 A u x) = (term126 A u x).
Proof. exact (eq_refl (term126 A u x)). Qed.
Lemma lem4855829 {A : Type'} (x : A) (u : A -> Prop) (s : A -> Prop) : (term484 A x u s) = (term543 A x u s).
Proof. exact (MK_COMB (@lem4855828 A u x) (@lem4855826 A u s)). Qed.
Lemma lem4855831 {A : Type'} (B : type686 A) (u : A -> Prop) : (term119 A B u) = (term119 A B u).
Proof. exact (eq_refl (term119 A B u)). Qed.
Lemma lem4855832 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term485 A B x u s) = (term544 A B x u s).
Proof. exact (MK_COMB (@lem4855831 A B u) (@lem4855829 A x u s)). Qed.
Lemma lem4855833 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term486 A B x s) = (term545 A B x s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855832 A B x u s)). Qed.
Lemma lem4855834 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855835 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term487 A B x s) = (term546 A B x s).
Proof. exact (MK_COMB (@lem4855834 A) (@lem4855833 A B x s)). Qed.
Lemma lem4855837 {A : Type'} (s : A -> Prop) (x : A) : (term184 A s x) = (term184 A s x).
Proof. exact (eq_refl (term184 A s x)). Qed.
Lemma lem4855838 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term547 A B x s) = (term548 A B x s).
Proof. exact (MK_COMB (@lem4855837 A s x) (@lem4855835 A B x s)). Qed.
Lemma lem4855839 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term488 A B x s) = (term547 A B x s).
Proof. exact (@lem17265 (s x) (term487 A B x s)). Qed.
Lemma lem4855840 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term488 A B x s) = (term548 A B x s).
Proof. exact (TRANS (@lem4855839 A B x s) (@lem4855838 A B x s)). Qed.
Lemma lem4855841 {A : Type'} (B : type686 A) (s : A -> Prop) : (term489 A B s) = (term549 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855840 A B x s)). Qed.
Lemma lem4855842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855843 {A : Type'} (B : type686 A) (s : A -> Prop) : (term490 A B s) = (term550 A B s).
Proof. exact (MK_COMB (@lem4855842 A) (@lem4855841 A B s)). Qed.
Lemma lem4855954 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4855955 {A : Type'} (P : Prop) (Q : type686 A) : (term551 A P Q) = (term552 A P Q).
Proof. exact (@lem4855954 (A -> Prop) P Q). Qed.
Lemma lem4855956 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term553 A B x s) = (term554 A B x s).
Proof. exact (@lem4855955 A (term202 A s x) (term545 A B x s)). Qed.
Lemma lem4855957 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term555 A B x s u) = (term544 A B x u s).
Proof. exact (eq_refl (term555 A B x s u)). Qed.
Lemma lem4855958 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term556 A B x s) = (term545 A B x s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855957 A B x u s)). Qed.
Lemma lem4855959 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855960 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term557 A B x s) = (term546 A B x s).
Proof. exact (MK_COMB (@lem4855959 A) (@lem4855958 A B x s)). Qed.
Lemma lem4855961 {A : Type'} (s : A -> Prop) (x : A) : (term184 A s x) = (term184 A s x).
Proof. exact (eq_refl (term184 A s x)). Qed.
Lemma lem4855962 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term553 A B x s) = (term548 A B x s).
Proof. exact (MK_COMB (@lem4855961 A s x) (@lem4855960 A B x s)). Qed.
Lemma lem4855963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4855964 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term558 A B x s) = (term559 A B x s).
Proof. exact (MK_COMB (@lem4855963) (@lem4855962 A B x s)). Qed.
Lemma lem4855965 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term555 A B x s u) = (term544 A B x u s).
Proof. exact (eq_refl (term555 A B x s u)). Qed.
Lemma lem4855966 {A : Type'} (s : A -> Prop) (x : A) : (term184 A s x) = (term184 A s x).
Proof. exact (eq_refl (term184 A s x)). Qed.
Lemma lem4855967 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term560 A B x s u) = (term561 A B x u s).
Proof. exact (MK_COMB (@lem4855966 A s x) (@lem4855965 A B x u s)). Qed.
Lemma lem4855968 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term562 A B x s) = (term563 A B x s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855967 A B x u s)). Qed.
Lemma lem4855969 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855970 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term554 A B x s) = (term564 A B x s).
Proof. exact (MK_COMB (@lem4855969 A) (@lem4855968 A B x s)). Qed.
Lemma lem4855971 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : ((term553 A B x s) = (term554 A B x s)) = ((term548 A B x s) = (term564 A B x s)).
Proof. exact (MK_COMB (@lem4855964 A B x s) (@lem4855970 A B x s)). Qed.
Lemma lem4855972 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term548 A B x s) = (term564 A B x s).
Proof. exact (EQ_MP (@lem4855971 A B x s) (@lem4855956 A B x s)). Qed.
Lemma lem4855973 {A : Type'} (B : type686 A) (s : A -> Prop) : (term549 A B s) = (term565 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855972 A B x s)). Qed.
Lemma lem4855974 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855975 {A : Type'} (B : type686 A) (s : A -> Prop) : (term550 A B s) = (term566 A B s).
Proof. exact (MK_COMB (@lem4855974 A) (@lem4855973 A B s)). Qed.
Lemma lem4855977 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4855978 {A : Type'} (P : type1364 A) : (term567 A P) = (term568 A P).
Proof. exact (@lem4855977 A (A -> Prop) P). Qed.
Lemma lem4855979 {A : Type'} (B : type686 A) (s : A -> Prop) : (term569 A B s) = (term570 A B s).
Proof. exact (@lem4855978 A (term571 A B s)). Qed.
Lemma lem4855980 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term572 A B s x) = (term563 A B x s).
Proof. exact (eq_refl (term572 A B s x)). Qed.
Lemma lem4855981 {A : Type'} (u : A -> Prop) : u = u.
Proof. exact (eq_refl u). Qed.
Lemma lem4855982 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) (u : A -> Prop) : (term573 A B s x u) = (term574 A B x s u).
Proof. exact (MK_COMB (@lem4855980 A B x s) (@lem4855981 A u)). Qed.
Lemma lem4855983 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term574 A B x s u) = (term561 A B x u s).
Proof. exact (eq_refl (term574 A B x s u)). Qed.
Lemma lem4855984 {A : Type'} (B : type686 A) (x : A) (u : A -> Prop) (s : A -> Prop) : (term573 A B s x u) = (term561 A B x u s).
Proof. exact (TRANS (@lem4855982 A B x s u) (@lem4855983 A B x u s)). Qed.
Lemma lem4855985 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term575 A B s x) = (term563 A B x s).
Proof. exact (fun_ext (fun u : A -> Prop => @lem4855984 A B x u s)). Qed.
Lemma lem4855986 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4855987 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term576 A B s x) = (term564 A B x s).
Proof. exact (MK_COMB (@lem4855986 A) (@lem4855985 A B x s)). Qed.
Lemma lem4855988 {A : Type'} (B : type686 A) (s : A -> Prop) : (term577 A B s) = (term565 A B s).
Proof. exact (fun_ext (fun x : A => @lem4855987 A B x s)). Qed.
Lemma lem4855989 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4855990 {A : Type'} (B : type686 A) (s : A -> Prop) : (term569 A B s) = (term566 A B s).
Proof. exact (MK_COMB (@lem4855989 A) (@lem4855988 A B s)). Qed.
Lemma lem4855991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4855992 {A : Type'} (B : type686 A) (s : A -> Prop) : (term578 A B s) = (term579 A B s).
Proof. exact (MK_COMB (@lem4855991) (@lem4855990 A B s)). Qed.
Lemma lem4855993 {A : Type'} (B : type686 A) (x : A) (s : A -> Prop) : (term572 A B s x) = (term563 A B x s).
Proof. exact (eq_refl (term572 A B s x)). Qed.
Lemma lem4855994 {A : Type'} (u : type1402 A) (x : A) : (u x) = (u x).
Proof. exact (eq_refl (u x)). Qed.
Lemma lem4855995 {A : Type'} (B : type686 A) (s : A -> Prop) (u : type1402 A) (x : A) : (term580 A B s u x) = (term581 A B s u x).
Proof. exact (MK_COMB (@lem4855993 A B x s) (@lem4855994 A u x)). Qed.
Lemma lem4855996 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term581 A B s u x) = (term582 A B u x s).
Proof. exact (eq_refl (term581 A B s u x)). Qed.
Lemma lem4855997 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term580 A B s u x) = (term582 A B u x s).
Proof. exact (TRANS (@lem4855995 A B s u x) (@lem4855996 A B u x s)). Qed.
Lemma lem4855998 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term583 A B s u) = (term584 A B u s).
Proof. exact (fun_ext (fun x : A => @lem4855997 A B u x s)). Qed.
Lemma lem4855999 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4856000 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term585 A B s u) = (term586 A B u s).
Proof. exact (MK_COMB (@lem4855999 A) (@lem4855998 A B u s)). Qed.
Lemma lem4856001 {A : Type'} (B : type686 A) (s : A -> Prop) : (term587 A B s) = (term588 A B s).
Proof. exact (fun_ext (fun u : type1402 A => @lem4856000 A B u s)). Qed.
Lemma lem4856002 {A : Type'} : (@ex (A -> A -> Prop)) = (@ex (A -> A -> Prop)).
Proof. exact (eq_refl (@ex (A -> A -> Prop))). Qed.
Lemma lem4856003 {A : Type'} (B : type686 A) (s : A -> Prop) : (term570 A B s) = (term589 A B s).
Proof. exact (MK_COMB (@lem4856002 A) (@lem4856001 A B s)). Qed.
Lemma lem4856004 {A : Type'} (B : type686 A) (s : A -> Prop) : ((term569 A B s) = (term570 A B s)) = ((term566 A B s) = (term589 A B s)).
Proof. exact (MK_COMB (@lem4855992 A B s) (@lem4856003 A B s)). Qed.
Lemma lem4856005 {A : Type'} (B : type686 A) (s : A -> Prop) : (term566 A B s) = (term589 A B s).
Proof. exact (EQ_MP (@lem4856004 A B s) (@lem4855979 A B s)). Qed.
Lemma lem4856007 {A : Type'} (B : type686 A) (s : A -> Prop) : (term550 A B s) = (term589 A B s).
Proof. exact (TRANS (@lem4855975 A B s) (@lem4856005 A B s)). Qed.
Lemma lem4856008 {A : Type'} (B : type686 A) (s : A -> Prop) : (term490 A B s) = (term589 A B s).
Proof. exact (TRANS (@lem4855843 A B s) (@lem4856007 A B s)). Qed.
Lemma lem4856009 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) : term589 A B s.
Proof. exact (EQ_MP (@lem4856008 A B s) (@lem4855808 A B s h1)). Qed.
Lemma lem4856017 {A : Type'} (c : A -> Prop) (s : A -> Prop) (x : A) : (term480 A c s x) = (term540 A c s x).
Proof. exact (@lem17265 (c x) (s x)). Qed.
Lemma lem4856018 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term482 A c s) = (term541 A c s).
Proof. exact (fun_ext (fun x : A => @lem4856017 A c s x)). Qed.
Lemma lem4856019 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4856020 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term483 A c s) = (term542 A c s).
Proof. exact (MK_COMB (@lem4856019 A) (@lem4856018 A c s)). Qed.
Lemma lem4856022 {A : Type'} (B : type686 A) (c : A -> Prop) : (term119 A B c) = (term119 A B c).
Proof. exact (eq_refl (term119 A B c)). Qed.
Lemma lem4856023 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term505 A B c s) = (term590 A B c s).
Proof. exact (MK_COMB (@lem4856022 A B c) (@lem4856020 A c s)). Qed.
Lemma lem4856024 {A : Type'} (B : type686 A) (c : A -> Prop) : (term216 A B c) = (term216 A B c).
Proof. exact (eq_refl (term216 A B c)). Qed.
Lemma lem4856025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856026 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term513 A B c s) = (term591 A B c s).
Proof. exact (MK_COMB (@lem4856025) (@lem4856023 A B c s)). Qed.
Lemma lem4856027 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term592 A s B c) = (term593 A s B c).
Proof. exact (MK_COMB (@lem4856026 A B c s) (@lem4856024 A B c)). Qed.
Lemma lem4856028 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term594 A s B c) = (term592 A s B c).
Proof. exact (@lem17362 (term505 A B c s) (B c)). Qed.
Lemma lem4856029 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term594 A s B c) = (term593 A s B c).
Proof. exact (TRANS (@lem4856028 A s B c) (@lem4856027 A s B c)). Qed.
Lemma lem4856030 {A : Type'} (P : type686 A) : (term595 A P) = (term596 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem4856031 {A : Type'} (s : A -> Prop) (B : type686 A) : (term597 A s B) = (term598 A s B).
Proof. exact (@lem4856030 A (term508 A s B)). Qed.
Lemma lem4856032 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term599 A s B c) = (term507 A s B c).
Proof. exact (eq_refl (term599 A s B c)). Qed.
Lemma lem4856033 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856034 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term600 A s B c) = (term594 A s B c).
Proof. exact (MK_COMB (@lem4856033) (@lem4856032 A s B c)). Qed.
Lemma lem4856035 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term600 A s B c) = (term593 A s B c).
Proof. exact (TRANS (@lem4856034 A s B c) (@lem4856029 A s B c)). Qed.
Lemma lem4856036 {A : Type'} (s : A -> Prop) (B : type686 A) : (term601 A s B) = (term602 A s B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4856035 A s B c)). Qed.
Lemma lem4856037 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856038 {A : Type'} (s : A -> Prop) (B : type686 A) : (term598 A s B) = (term603 A s B).
Proof. exact (MK_COMB (@lem4856037 A) (@lem4856036 A s B)). Qed.
Lemma lem4856039 {A : Type'} (s : A -> Prop) (B : type686 A) : (term597 A s B) = (term603 A s B).
Proof. exact (TRANS (@lem4856031 A s B) (@lem4856038 A s B)). Qed.
Lemma lem4856050 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term604 A t s x) = (term605 A t s x).
Proof. exact (@lem17362 (t x) (s x)). Qed.
Lemma lem4856055 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term480 A t s x) = (term540 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem4856056 {A : Type'} (P : A -> Prop) : (term175 A P) = (term176 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4856057 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term606 A t s) = (term607 A t s).
Proof. exact (@lem4856056 A (term482 A t s)). Qed.
Lemma lem4856058 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term608 A t s x) = (term480 A t s x).
Proof. exact (eq_refl (term608 A t s x)). Qed.
Lemma lem4856059 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856060 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term609 A t s x) = (term604 A t s x).
Proof. exact (MK_COMB (@lem4856059) (@lem4856058 A t s x)). Qed.
Lemma lem4856061 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term609 A t s x) = (term605 A t s x).
Proof. exact (TRANS (@lem4856060 A t s x) (@lem4856050 A t s x)). Qed.
Lemma lem4856062 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term610 A t s) = (term611 A t s).
Proof. exact (fun_ext (fun x : A => @lem4856061 A t s x)). Qed.
Lemma lem4856063 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856064 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term607 A t s) = (term612 A t s).
Proof. exact (MK_COMB (@lem4856063 A) (@lem4856062 A t s)). Qed.
Lemma lem4856065 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term606 A t s) = (term612 A t s).
Proof. exact (TRANS (@lem4856057 A t s) (@lem4856064 A t s)). Qed.
Lemma lem4856066 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term482 A t s) = (term541 A t s).
Proof. exact (fun_ext (fun x : A => @lem4856055 A t s x)). Qed.
Lemma lem4856067 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4856068 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term483 A t s) = (term542 A t s).
Proof. exact (MK_COMB (@lem4856067 A) (@lem4856066 A t s)). Qed.
Lemma lem4856070 {A : Type'} (B : type686 A) (t : A -> Prop) : (term188 A B t) = (term188 A B t).
Proof. exact (eq_refl (term188 A B t)). Qed.
Lemma lem4856071 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term613 A B t s) = (term614 A B t s).
Proof. exact (MK_COMB (@lem4856070 A B t) (@lem4856065 A t s)). Qed.
Lemma lem4856072 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term615 A B t s) = (term613 A B t s).
Proof. exact (@lem17045 (B t) (term483 A t s)). Qed.
Lemma lem4856073 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term615 A B t s) = (term614 A B t s).
Proof. exact (TRANS (@lem4856072 A B t s) (@lem4856071 A B t s)). Qed.
Lemma lem4856075 {A : Type'} (B : type686 A) (t : A -> Prop) : (term119 A B t) = (term119 A B t).
Proof. exact (eq_refl (term119 A B t)). Qed.
Lemma lem4856076 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term505 A B t s) = (term590 A B t s).
Proof. exact (MK_COMB (@lem4856075 A B t) (@lem4856068 A t s)). Qed.
Lemma lem4856077 {A : Type'} (t : A -> Prop) (x : A) : (term202 A t x) = (term202 A t x).
Proof. exact (eq_refl (term202 A t x)). Qed.
Lemma lem4856078 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem4856079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856080 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term616 A B t s) = (term617 A B t s).
Proof. exact (MK_COMB (@lem4856079) (@lem4856073 A B t s)). Qed.
Lemma lem4856081 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term618 A B s t x) = (term619 A B s t x).
Proof. exact (MK_COMB (@lem4856080 A B t s) (@lem4856077 A t x)). Qed.
Lemma lem4856082 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term620 A B s t x) = (term618 A B s t x).
Proof. exact (@lem17045 (term505 A B t s) (t x)). Qed.
Lemma lem4856083 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term620 A B s t x) = (term619 A B s t x).
Proof. exact (TRANS (@lem4856082 A B s t x) (@lem4856081 A B s t x)). Qed.
Lemma lem4856084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856085 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term513 A B t s) = (term591 A B t s).
Proof. exact (MK_COMB (@lem4856084) (@lem4856076 A B t s)). Qed.
Lemma lem4856086 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term515 A B s t x) = (term621 A B s t x).
Proof. exact (MK_COMB (@lem4856085 A B t s) (@lem4856078 A t x)). Qed.
Lemma lem4856087 {A : Type'} (P : type686 A) : (term163 A P) = (term164 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem4856088 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term622 A B s x) = (term623 A B s x).
Proof. exact (@lem4856087 A (term517 A B s x)). Qed.
Lemma lem4856089 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term624 A B s x t) = (term515 A B s t x).
Proof. exact (eq_refl (term624 A B s x t)). Qed.
Lemma lem4856090 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856091 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term625 A B s x t) = (term620 A B s t x).
Proof. exact (MK_COMB (@lem4856090) (@lem4856089 A B s t x)). Qed.
Lemma lem4856092 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term625 A B s x t) = (term619 A B s t x).
Proof. exact (TRANS (@lem4856091 A B s t x) (@lem4856083 A B s t x)). Qed.
Lemma lem4856093 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term626 A B s x) = (term627 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856092 A B s t x)). Qed.
Lemma lem4856094 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4856095 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term623 A B s x) = (term628 A B s x).
Proof. exact (MK_COMB (@lem4856094 A) (@lem4856093 A B s x)). Qed.
Lemma lem4856096 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term622 A B s x) = (term628 A B s x).
Proof. exact (TRANS (@lem4856088 A B s x) (@lem4856095 A B s x)). Qed.
Lemma lem4856097 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term517 A B s x) = (term629 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856086 A B s t x)). Qed.
Lemma lem4856098 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856099 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term518 A B s x) = (term630 A B s x).
Proof. exact (MK_COMB (@lem4856098 A) (@lem4856097 A B s x)). Qed.
Lemma lem4856100 {A : Type'} (s : A -> Prop) (x : A) : (term202 A s x) = (term202 A s x).
Proof. exact (eq_refl (term202 A s x)). Qed.
Lemma lem4856101 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4856102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856103 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term631 A B s x) = (term632 A B s x).
Proof. exact (MK_COMB (@lem4856102) (@lem4856096 A B s x)). Qed.
Lemma lem4856104 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term633 A B s x) = (term634 A B s x).
Proof. exact (MK_COMB (@lem4856103 A B s x) (@lem4856101 A s x)). Qed.
Lemma lem4856105 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856106 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term635 A B s x) = (term636 A B s x).
Proof. exact (MK_COMB (@lem4856105) (@lem4856099 A B s x)). Qed.
Lemma lem4856107 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term637 A B s x) = (term638 A B s x).
Proof. exact (MK_COMB (@lem4856106 A B s x) (@lem4856100 A s x)). Qed.
Lemma lem4856108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856109 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term639 A B s x) = (term640 A B s x).
Proof. exact (MK_COMB (@lem4856108) (@lem4856107 A B s x)). Qed.
Lemma lem4856110 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term641 A B s x) = (term642 A B s x).
Proof. exact (MK_COMB (@lem4856109 A B s x) (@lem4856104 A B s x)). Qed.
Lemma lem4856111 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term643 A B s x) = (term641 A B s x).
Proof. exact (@lem17646 (term518 A B s x) (s x)). Qed.
Lemma lem4856112 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term643 A B s x) = (term642 A B s x).
Proof. exact (TRANS (@lem4856111 A B s x) (@lem4856110 A B s x)). Qed.
Lemma lem4856113 {A : Type'} (P : A -> Prop) : (term175 A P) = (term176 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4856114 {A : Type'} (B : type686 A) (s : A -> Prop) : (term644 A B s) = (term645 A B s).
Proof. exact (@lem4856113 A (term520 A B s)). Qed.
Lemma lem4856115 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term646 A B s x) = ((term518 A B s x) = (s x)).
Proof. exact (eq_refl (term646 A B s x)). Qed.
Lemma lem4856116 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856117 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term647 A B s x) = (term643 A B s x).
Proof. exact (MK_COMB (@lem4856116) (@lem4856115 A B s x)). Qed.
Lemma lem4856118 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term647 A B s x) = (term642 A B s x).
Proof. exact (TRANS (@lem4856117 A B s x) (@lem4856112 A B s x)). Qed.
Lemma lem4856119 {A : Type'} (B : type686 A) (s : A -> Prop) : (term648 A B s) = (term649 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856118 A B s x)). Qed.
Lemma lem4856120 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856121 {A : Type'} (B : type686 A) (s : A -> Prop) : (term645 A B s) = (term650 A B s).
Proof. exact (MK_COMB (@lem4856120 A) (@lem4856119 A B s)). Qed.
Lemma lem4856122 {A : Type'} (B : type686 A) (s : A -> Prop) : (term644 A B s) = (term650 A B s).
Proof. exact (TRANS (@lem4856114 A B s) (@lem4856121 A B s)). Qed.
Lemma lem4856123 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856124 {A : Type'} (s : A -> Prop) (B : type686 A) : (term651 A s B) = (term652 A s B).
Proof. exact (MK_COMB (@lem4856123) (@lem4856039 A s B)). Qed.
Lemma lem4856125 {A : Type'} (B : type686 A) (s : A -> Prop) : (term653 A B s) = (term654 A B s).
Proof. exact (MK_COMB (@lem4856124 A s B) (@lem4856122 A B s)). Qed.
Lemma lem4856126 {A : Type'} (B : type686 A) (s : A -> Prop) : (term539 A B s) = (term653 A B s).
Proof. exact (@lem17045 (term509 A s B) (term521 A B s)). Qed.
Lemma lem4856127 {A : Type'} (B : type686 A) (s : A -> Prop) : (term539 A B s) = (term654 A B s).
Proof. exact (TRANS (@lem4856126 A B s) (@lem4856125 A B s)). Qed.
Lemma lem4856209 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term655 A P Q) = (term656 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4856210 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term655 A P Q) = (term656 A P Q).
Proof. exact (@lem4856209 A P Q). Qed.
Lemma lem4856211 {A : Type'} (B : type686 A) (s : A -> Prop) : (term657 A B s) = (term658 A B s).
Proof. exact (@lem4856210 A (term659 A B s) (term660 A B s)). Qed.
Lemma lem4856212 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term661 A B s x) = (term638 A B s x).
Proof. exact (eq_refl (term661 A B s x)). Qed.
Lemma lem4856213 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856214 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term662 A B s x) = (term640 A B s x).
Proof. exact (MK_COMB (@lem4856213) (@lem4856212 A B s x)). Qed.
Lemma lem4856215 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term663 A B s x) = (term634 A B s x).
Proof. exact (eq_refl (term663 A B s x)). Qed.
Lemma lem4856216 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term664 A B s x) = (term642 A B s x).
Proof. exact (MK_COMB (@lem4856214 A B s x) (@lem4856215 A B s x)). Qed.
Lemma lem4856217 {A : Type'} (B : type686 A) (s : A -> Prop) : (term665 A B s) = (term649 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856216 A B s x)). Qed.
Lemma lem4856218 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856219 {A : Type'} (B : type686 A) (s : A -> Prop) : (term657 A B s) = (term650 A B s).
Proof. exact (MK_COMB (@lem4856218 A) (@lem4856217 A B s)). Qed.
Lemma lem4856220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856221 {A : Type'} (B : type686 A) (s : A -> Prop) : (term666 A B s) = (term667 A B s).
Proof. exact (MK_COMB (@lem4856220) (@lem4856219 A B s)). Qed.
Lemma lem4856222 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term661 A B s x) = (term638 A B s x).
Proof. exact (eq_refl (term661 A B s x)). Qed.
Lemma lem4856223 {A : Type'} (B : type686 A) (s : A -> Prop) : (term668 A B s) = (term659 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856222 A B s x)). Qed.
Lemma lem4856224 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856225 {A : Type'} (B : type686 A) (s : A -> Prop) : (term669 A B s) = (term670 A B s).
Proof. exact (MK_COMB (@lem4856224 A) (@lem4856223 A B s)). Qed.
Lemma lem4856226 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856227 {A : Type'} (B : type686 A) (s : A -> Prop) : (term671 A B s) = (term672 A B s).
Proof. exact (MK_COMB (@lem4856226) (@lem4856225 A B s)). Qed.
Lemma lem4856228 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term663 A B s x) = (term634 A B s x).
Proof. exact (eq_refl (term663 A B s x)). Qed.
Lemma lem4856229 {A : Type'} (B : type686 A) (s : A -> Prop) : (term673 A B s) = (term660 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856228 A B s x)). Qed.
Lemma lem4856230 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856231 {A : Type'} (B : type686 A) (s : A -> Prop) : (term674 A B s) = (term675 A B s).
Proof. exact (MK_COMB (@lem4856230 A) (@lem4856229 A B s)). Qed.
Lemma lem4856232 {A : Type'} (B : type686 A) (s : A -> Prop) : (term658 A B s) = (term676 A B s).
Proof. exact (MK_COMB (@lem4856227 A B s) (@lem4856231 A B s)). Qed.
Lemma lem4856233 {A : Type'} (B : type686 A) (s : A -> Prop) : ((term657 A B s) = (term658 A B s)) = ((term650 A B s) = (term676 A B s)).
Proof. exact (MK_COMB (@lem4856221 A B s) (@lem4856232 A B s)). Qed.
Lemma lem4856234 {A : Type'} (B : type686 A) (s : A -> Prop) : (term650 A B s) = (term676 A B s).
Proof. exact (EQ_MP (@lem4856233 A B s) (@lem4856211 A B s)). Qed.
Lemma lem4856471 {A : Type'} (s : A -> Prop) (B : type686 A) : (term652 A s B) = (term652 A s B).
Proof. exact (eq_refl (term652 A s B)). Qed.
Lemma lem4856472 {A : Type'} (B : type686 A) (s : A -> Prop) : (term654 A B s) = (term677 A B s).
Proof. exact (MK_COMB (@lem4856471 A s B) (@lem4856234 A B s)). Qed.
Lemma lem4856474 {A : Type'} (P : A -> Prop) (Q : Prop) : (term678 A P Q) = (term679 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4856475 {A : Type'} (P : type686 A) (Q : Prop) : (term680 A P Q) = (term681 A P Q).
Proof. exact (@lem4856474 (A -> Prop) P Q). Qed.
Lemma lem4856476 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term682 A B s x) = (term683 A B s x).
Proof. exact (@lem4856475 A (term629 A B s x) (term202 A s x)). Qed.
Lemma lem4856477 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term684 A B s x t) = (term621 A B s t x).
Proof. exact (eq_refl (term684 A B s x t)). Qed.
Lemma lem4856478 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term685 A B s x) = (term629 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856477 A B s t x)). Qed.
Lemma lem4856479 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856480 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term686 A B s x) = (term630 A B s x).
Proof. exact (MK_COMB (@lem4856479 A) (@lem4856478 A B s x)). Qed.
Lemma lem4856481 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856482 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term687 A B s x) = (term636 A B s x).
Proof. exact (MK_COMB (@lem4856481) (@lem4856480 A B s x)). Qed.
Lemma lem4856483 {A : Type'} (s : A -> Prop) (x : A) : (term202 A s x) = (term202 A s x).
Proof. exact (eq_refl (term202 A s x)). Qed.
Lemma lem4856484 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term682 A B s x) = (term638 A B s x).
Proof. exact (MK_COMB (@lem4856482 A B s x) (@lem4856483 A s x)). Qed.
Lemma lem4856485 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856486 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term688 A B s x) = (term689 A B s x).
Proof. exact (MK_COMB (@lem4856485) (@lem4856484 A B s x)). Qed.
Lemma lem4856487 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term684 A B s x t) = (term621 A B s t x).
Proof. exact (eq_refl (term684 A B s x t)). Qed.
Lemma lem4856488 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856489 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term690 A B s x t) = (term691 A B s t x).
Proof. exact (MK_COMB (@lem4856488) (@lem4856487 A B s t x)). Qed.
Lemma lem4856490 {A : Type'} (s : A -> Prop) (x : A) : (term202 A s x) = (term202 A s x).
Proof. exact (eq_refl (term202 A s x)). Qed.
Lemma lem4856491 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term692 A B t s x) = (term693 A B t s x).
Proof. exact (MK_COMB (@lem4856489 A B s t x) (@lem4856490 A s x)). Qed.
Lemma lem4856492 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term694 A B s x) = (term695 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856491 A B t s x)). Qed.
Lemma lem4856493 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856494 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term683 A B s x) = (term696 A B s x).
Proof. exact (MK_COMB (@lem4856493 A) (@lem4856492 A B s x)). Qed.
Lemma lem4856495 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : ((term682 A B s x) = (term683 A B s x)) = ((term638 A B s x) = (term696 A B s x)).
Proof. exact (MK_COMB (@lem4856486 A B s x) (@lem4856494 A B s x)). Qed.
Lemma lem4856496 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term638 A B s x) = (term696 A B s x).
Proof. exact (EQ_MP (@lem4856495 A B s x) (@lem4856476 A B s x)). Qed.
Lemma lem4856497 {A : Type'} (B : type686 A) (s : A -> Prop) : (term659 A B s) = (term697 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856496 A B s x)). Qed.
Lemma lem4856498 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856499 {A : Type'} (B : type686 A) (s : A -> Prop) : (term670 A B s) = (term698 A B s).
Proof. exact (MK_COMB (@lem4856498 A) (@lem4856497 A B s)). Qed.
Lemma lem4856500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856501 {A : Type'} (B : type686 A) (s : A -> Prop) : (term672 A B s) = (term699 A B s).
Proof. exact (MK_COMB (@lem4856500) (@lem4856499 A B s)). Qed.
Lemma lem4856503 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4856504 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (@lem4856503 A P Q). Qed.
Lemma lem4856505 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term700 A B t s) = (term701 A B t s).
Proof. exact (@lem4856504 A (term216 A B t) (term611 A t s)). Qed.
Lemma lem4856506 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term702 A t s x) = (term605 A t s x).
Proof. exact (eq_refl (term702 A t s x)). Qed.
Lemma lem4856507 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term703 A t s) = (term611 A t s).
Proof. exact (fun_ext (fun x : A => @lem4856506 A t s x)). Qed.
Lemma lem4856508 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856509 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term704 A t s) = (term612 A t s).
Proof. exact (MK_COMB (@lem4856508 A) (@lem4856507 A t s)). Qed.
Lemma lem4856510 {A : Type'} (B : type686 A) (t : A -> Prop) : (term188 A B t) = (term188 A B t).
Proof. exact (eq_refl (term188 A B t)). Qed.
Lemma lem4856511 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term700 A B t s) = (term614 A B t s).
Proof. exact (MK_COMB (@lem4856510 A B t) (@lem4856509 A t s)). Qed.
Lemma lem4856512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856513 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term705 A B t s) = (term706 A B t s).
Proof. exact (MK_COMB (@lem4856512) (@lem4856511 A B t s)). Qed.
Lemma lem4856514 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term702 A t s x) = (term605 A t s x).
Proof. exact (eq_refl (term702 A t s x)). Qed.
Lemma lem4856515 {A : Type'} (B : type686 A) (t : A -> Prop) : (term188 A B t) = (term188 A B t).
Proof. exact (eq_refl (term188 A B t)). Qed.
Lemma lem4856516 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term707 A B t s x) = (term708 A B t s x).
Proof. exact (MK_COMB (@lem4856515 A B t) (@lem4856514 A t s x)). Qed.
Lemma lem4856517 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term709 A B t s) = (term710 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4856516 A B t s x)). Qed.
Lemma lem4856518 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856519 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term701 A B t s) = (term711 A B t s).
Proof. exact (MK_COMB (@lem4856518 A) (@lem4856517 A B t s)). Qed.
Lemma lem4856520 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : ((term700 A B t s) = (term701 A B t s)) = ((term614 A B t s) = (term711 A B t s)).
Proof. exact (MK_COMB (@lem4856513 A B t s) (@lem4856519 A B t s)). Qed.
Lemma lem4856521 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term614 A B t s) = (term711 A B t s).
Proof. exact (EQ_MP (@lem4856520 A B t s) (@lem4856505 A B t s)). Qed.
Lemma lem4856522 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856523 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term617 A B t s) = (term712 A B t s).
Proof. exact (MK_COMB (@lem4856522) (@lem4856521 A B t s)). Qed.
Lemma lem4856524 {A : Type'} (t : A -> Prop) (x : A) : (term202 A t x) = (term202 A t x).
Proof. exact (eq_refl (term202 A t x)). Qed.
Lemma lem4856525 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term619 A B s t x) = (term713 A B s t x).
Proof. exact (MK_COMB (@lem4856523 A B t s) (@lem4856524 A t x)). Qed.
Lemma lem4856527 {A : Type'} (P : A -> Prop) (Q : Prop) : (term714 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4856528 {A : Type'} (P : A -> Prop) (Q : Prop) : (term714 A P Q) = (term715 A P Q).
Proof. exact (@lem4856527 A P Q). Qed.
Lemma lem4856529 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term716 A B s t x) = (term717 A B s t x).
Proof. exact (@lem4856528 A (term710 A B t s) (term202 A t x)). Qed.
Lemma lem4856530 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term718 A B t s x) = (term708 A B t s x).
Proof. exact (eq_refl (term718 A B t s x)). Qed.
Lemma lem4856531 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term719 A B t s) = (term710 A B t s).
Proof. exact (fun_ext (fun x : A => @lem4856530 A B t s x)). Qed.
Lemma lem4856532 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856533 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term720 A B t s) = (term711 A B t s).
Proof. exact (MK_COMB (@lem4856532 A) (@lem4856531 A B t s)). Qed.
Lemma lem4856534 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856535 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term721 A B t s) = (term712 A B t s).
Proof. exact (MK_COMB (@lem4856534) (@lem4856533 A B t s)). Qed.
Lemma lem4856536 {A : Type'} (t : A -> Prop) (x : A) : (term202 A t x) = (term202 A t x).
Proof. exact (eq_refl (term202 A t x)). Qed.
Lemma lem4856537 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term716 A B s t x) = (term713 A B s t x).
Proof. exact (MK_COMB (@lem4856535 A B t s) (@lem4856536 A t x)). Qed.
Lemma lem4856538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856539 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term722 A B s t x) = (term723 A B s t x).
Proof. exact (MK_COMB (@lem4856538) (@lem4856537 A B s t x)). Qed.
Lemma lem4856540 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term718 A B t s x') = (term708 A B t s x').
Proof. exact (eq_refl (term718 A B t s x')). Qed.
Lemma lem4856541 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856542 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x' : A) : (term724 A B t s x') = (term725 A B t s x').
Proof. exact (MK_COMB (@lem4856541) (@lem4856540 A B t s x')). Qed.
Lemma lem4856543 {A : Type'} (t : A -> Prop) (x : A) : (term202 A t x) = (term202 A t x).
Proof. exact (eq_refl (term202 A t x)). Qed.
Lemma lem4856544 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term726 A B s x' t x) = (term727 A B s x' t x).
Proof. exact (MK_COMB (@lem4856542 A B t s x') (@lem4856543 A t x)). Qed.
Lemma lem4856545 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term728 A B s t x) = (term729 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4856544 A B s x' t x)). Qed.
Lemma lem4856546 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856547 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term717 A B s t x) = (term730 A B s t x).
Proof. exact (MK_COMB (@lem4856546 A) (@lem4856545 A B s t x)). Qed.
Lemma lem4856548 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : ((term716 A B s t x) = (term717 A B s t x)) = ((term713 A B s t x) = (term730 A B s t x)).
Proof. exact (MK_COMB (@lem4856539 A B s t x) (@lem4856547 A B s t x)). Qed.
Lemma lem4856549 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term713 A B s t x) = (term730 A B s t x).
Proof. exact (EQ_MP (@lem4856548 A B s t x) (@lem4856529 A B s t x)). Qed.
Lemma lem4856550 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term619 A B s t x) = (term730 A B s t x).
Proof. exact (TRANS (@lem4856525 A B s t x) (@lem4856549 A B s t x)). Qed.
Lemma lem4856551 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term627 A B s x) = (term731 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856550 A B s t x)). Qed.
Lemma lem4856552 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4856553 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term628 A B s x) = (term732 A B s x).
Proof. exact (MK_COMB (@lem4856552 A) (@lem4856551 A B s x)). Qed.
Lemma lem4856555 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem4856556 {A : Type'} (P : type672 A) : (term231 A P) = (term232 A P).
Proof. exact (@lem4856555 (A -> Prop) A P). Qed.
Lemma lem4856557 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term733 A B s x) = (term734 A B s x).
Proof. exact (@lem4856556 A (term735 A B s x)). Qed.
Lemma lem4856558 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term736 A B s x t) = (term729 A B s t x).
Proof. exact (eq_refl (term736 A B s x t)). Qed.
Lemma lem4856559 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4856560 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) (x' : A) : (term737 A B s x t x') = (term738 A B s t x x').
Proof. exact (MK_COMB (@lem4856558 A B s t x) (@lem4856559 A x')). Qed.
Lemma lem4856561 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term738 A B s t x x') = (term727 A B s x' t x).
Proof. exact (eq_refl (term738 A B s t x x')). Qed.
Lemma lem4856562 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) : (term737 A B s x t x') = (term727 A B s x' t x).
Proof. exact (TRANS (@lem4856560 A B s t x x') (@lem4856561 A B s x' t x)). Qed.
Lemma lem4856563 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term739 A B s x t) = (term729 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4856562 A B s x' t x)). Qed.
Lemma lem4856564 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856565 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term740 A B s x t) = (term730 A B s t x).
Proof. exact (MK_COMB (@lem4856564 A) (@lem4856563 A B s t x)). Qed.
Lemma lem4856566 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term741 A B s x) = (term731 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856565 A B s t x)). Qed.
Lemma lem4856567 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4856568 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term733 A B s x) = (term732 A B s x).
Proof. exact (MK_COMB (@lem4856567 A) (@lem4856566 A B s x)). Qed.
Lemma lem4856569 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856570 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term742 A B s x) = (term743 A B s x).
Proof. exact (MK_COMB (@lem4856569) (@lem4856568 A B s x)). Qed.
Lemma lem4856571 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term736 A B s x t) = (term729 A B s t x).
Proof. exact (eq_refl (term736 A B s x t)). Qed.
Lemma lem4856572 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (x' t).
Proof. exact (eq_refl (x' t)). Qed.
Lemma lem4856573 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) (x' : type684 A) (t : A -> Prop) : (term744 A B s x x' t) = (term745 A B s x x' t).
Proof. exact (MK_COMB (@lem4856571 A B s t x) (@lem4856572 A x' t)). Qed.
Lemma lem4856574 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term745 A B s x x' t) = (term746 A B s x' t x).
Proof. exact (eq_refl (term745 A B s x x' t)). Qed.
Lemma lem4856575 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term744 A B s x x' t) = (term746 A B s x' t x).
Proof. exact (TRANS (@lem4856573 A B s x x' t) (@lem4856574 A B s x' t x)). Qed.
Lemma lem4856576 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term747 A B s x x') = (term748 A B s x' x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856575 A B s x' t x)). Qed.
Lemma lem4856577 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4856578 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term749 A B s x x') = (term750 A B s x' x).
Proof. exact (MK_COMB (@lem4856577 A) (@lem4856576 A B s x' x)). Qed.
Lemma lem4856579 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term751 A B s x) = (term752 A B s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem4856578 A B s x' x)). Qed.
Lemma lem4856580 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4856581 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term734 A B s x) = (term753 A B s x).
Proof. exact (MK_COMB (@lem4856580 A) (@lem4856579 A B s x)). Qed.
Lemma lem4856582 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : ((term733 A B s x) = (term734 A B s x)) = ((term732 A B s x) = (term753 A B s x)).
Proof. exact (MK_COMB (@lem4856570 A B s x) (@lem4856581 A B s x)). Qed.
Lemma lem4856583 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term732 A B s x) = (term753 A B s x).
Proof. exact (EQ_MP (@lem4856582 A B s x) (@lem4856557 A B s x)). Qed.
Lemma lem4856584 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term628 A B s x) = (term753 A B s x).
Proof. exact (TRANS (@lem4856553 A B s x) (@lem4856583 A B s x)). Qed.
Lemma lem4856585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856586 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term632 A B s x) = (term754 A B s x).
Proof. exact (MK_COMB (@lem4856585) (@lem4856584 A B s x)). Qed.
Lemma lem4856587 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4856588 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term634 A B s x) = (term755 A B s x).
Proof. exact (MK_COMB (@lem4856586 A B s x) (@lem4856587 A s x)). Qed.
Lemma lem4856590 {A : Type'} (P : A -> Prop) (Q : Prop) : (term678 A P Q) = (term679 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4856591 {A : Type'} (P : type162 A) (Q : Prop) : (term756 A P Q) = (term757 A P Q).
Proof. exact (@lem4856590 (type684 A) P Q). Qed.
Lemma lem4856592 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term758 A B s x) = (term759 A B s x).
Proof. exact (@lem4856591 A (term752 A B s x) (s x)). Qed.
Lemma lem4856593 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term760 A B s x x') = (term750 A B s x' x).
Proof. exact (eq_refl (term760 A B s x x')). Qed.
Lemma lem4856594 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term761 A B s x) = (term752 A B s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem4856593 A B s x' x)). Qed.
Lemma lem4856595 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4856596 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term762 A B s x) = (term753 A B s x).
Proof. exact (MK_COMB (@lem4856595 A) (@lem4856594 A B s x)). Qed.
Lemma lem4856597 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856598 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term763 A B s x) = (term754 A B s x).
Proof. exact (MK_COMB (@lem4856597) (@lem4856596 A B s x)). Qed.
Lemma lem4856599 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4856600 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term758 A B s x) = (term755 A B s x).
Proof. exact (MK_COMB (@lem4856598 A B s x) (@lem4856599 A s x)). Qed.
Lemma lem4856601 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856602 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term764 A B s x) = (term765 A B s x).
Proof. exact (MK_COMB (@lem4856601) (@lem4856600 A B s x)). Qed.
Lemma lem4856603 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term760 A B s x x') = (term750 A B s x' x).
Proof. exact (eq_refl (term760 A B s x x')). Qed.
Lemma lem4856604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856605 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term766 A B s x x') = (term767 A B s x' x).
Proof. exact (MK_COMB (@lem4856604) (@lem4856603 A B s x' x)). Qed.
Lemma lem4856606 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem4856607 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term768 A B x' s x) = (term769 A B x' s x).
Proof. exact (MK_COMB (@lem4856605 A B s x' x) (@lem4856606 A s x)). Qed.
Lemma lem4856608 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term770 A B s x) = (term771 A B s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem4856607 A B x' s x)). Qed.
Lemma lem4856609 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4856610 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term759 A B s x) = (term772 A B s x).
Proof. exact (MK_COMB (@lem4856609 A) (@lem4856608 A B s x)). Qed.
Lemma lem4856611 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : ((term758 A B s x) = (term759 A B s x)) = ((term755 A B s x) = (term772 A B s x)).
Proof. exact (MK_COMB (@lem4856602 A B s x) (@lem4856610 A B s x)). Qed.
Lemma lem4856612 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term755 A B s x) = (term772 A B s x).
Proof. exact (EQ_MP (@lem4856611 A B s x) (@lem4856592 A B s x)). Qed.
Lemma lem4856613 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term634 A B s x) = (term772 A B s x).
Proof. exact (TRANS (@lem4856588 A B s x) (@lem4856612 A B s x)). Qed.
Lemma lem4856614 {A : Type'} (B : type686 A) (s : A -> Prop) : (term660 A B s) = (term773 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856613 A B s x)). Qed.
Lemma lem4856615 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856616 {A : Type'} (B : type686 A) (s : A -> Prop) : (term675 A B s) = (term774 A B s).
Proof. exact (MK_COMB (@lem4856615 A) (@lem4856614 A B s)). Qed.
Lemma lem4856617 {A : Type'} (B : type686 A) (s : A -> Prop) : (term676 A B s) = (term775 A B s).
Proof. exact (MK_COMB (@lem4856501 A B s) (@lem4856616 A B s)). Qed.
Lemma lem4856619 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term656 A P Q) = (term655 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4856620 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term656 A P Q) = (term655 A P Q).
Proof. exact (@lem4856619 A P Q). Qed.
Lemma lem4856621 {A : Type'} (B : type686 A) (s : A -> Prop) : (term776 A B s) = (term777 A B s).
Proof. exact (@lem4856620 A (term697 A B s) (term773 A B s)). Qed.
Lemma lem4856622 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term778 A B s x) = (term696 A B s x).
Proof. exact (eq_refl (term778 A B s x)). Qed.
Lemma lem4856623 {A : Type'} (B : type686 A) (s : A -> Prop) : (term779 A B s) = (term697 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856622 A B s x)). Qed.
Lemma lem4856624 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856625 {A : Type'} (B : type686 A) (s : A -> Prop) : (term780 A B s) = (term698 A B s).
Proof. exact (MK_COMB (@lem4856624 A) (@lem4856623 A B s)). Qed.
Lemma lem4856626 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856627 {A : Type'} (B : type686 A) (s : A -> Prop) : (term781 A B s) = (term699 A B s).
Proof. exact (MK_COMB (@lem4856626) (@lem4856625 A B s)). Qed.
Lemma lem4856628 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term782 A B s x) = (term772 A B s x).
Proof. exact (eq_refl (term782 A B s x)). Qed.
Lemma lem4856629 {A : Type'} (B : type686 A) (s : A -> Prop) : (term783 A B s) = (term773 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856628 A B s x)). Qed.
Lemma lem4856630 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856631 {A : Type'} (B : type686 A) (s : A -> Prop) : (term784 A B s) = (term774 A B s).
Proof. exact (MK_COMB (@lem4856630 A) (@lem4856629 A B s)). Qed.
Lemma lem4856632 {A : Type'} (B : type686 A) (s : A -> Prop) : (term776 A B s) = (term775 A B s).
Proof. exact (MK_COMB (@lem4856627 A B s) (@lem4856631 A B s)). Qed.
Lemma lem4856633 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856634 {A : Type'} (B : type686 A) (s : A -> Prop) : (term785 A B s) = (term786 A B s).
Proof. exact (MK_COMB (@lem4856633) (@lem4856632 A B s)). Qed.
Lemma lem4856635 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term778 A B s x) = (term696 A B s x).
Proof. exact (eq_refl (term778 A B s x)). Qed.
Lemma lem4856636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856637 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term787 A B s x) = (term788 A B s x).
Proof. exact (MK_COMB (@lem4856636) (@lem4856635 A B s x)). Qed.
Lemma lem4856638 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term782 A B s x) = (term772 A B s x).
Proof. exact (eq_refl (term782 A B s x)). Qed.
Lemma lem4856639 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term789 A B s x) = (term790 A B s x).
Proof. exact (MK_COMB (@lem4856637 A B s x) (@lem4856638 A B s x)). Qed.
Lemma lem4856640 {A : Type'} (B : type686 A) (s : A -> Prop) : (term791 A B s) = (term792 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856639 A B s x)). Qed.
Lemma lem4856641 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856642 {A : Type'} (B : type686 A) (s : A -> Prop) : (term777 A B s) = (term793 A B s).
Proof. exact (MK_COMB (@lem4856641 A) (@lem4856640 A B s)). Qed.
Lemma lem4856643 {A : Type'} (B : type686 A) (s : A -> Prop) : ((term776 A B s) = (term777 A B s)) = ((term775 A B s) = (term793 A B s)).
Proof. exact (MK_COMB (@lem4856634 A B s) (@lem4856642 A B s)). Qed.
Lemma lem4856644 {A : Type'} (B : type686 A) (s : A -> Prop) : (term775 A B s) = (term793 A B s).
Proof. exact (EQ_MP (@lem4856643 A B s) (@lem4856621 A B s)). Qed.
Lemma lem4856648 {A : Type'} (P : A -> Prop) (Q : Prop) : (term714 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4856649 {A : Type'} (P : type686 A) (Q : Prop) : (term794 A P Q) = (term795 A P Q).
Proof. exact (@lem4856648 (A -> Prop) P Q). Qed.
Lemma lem4856650 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term796 A B s x) = (term797 A B s x).
Proof. exact (@lem4856649 A (term695 A B s x) (term772 A B s x)). Qed.
Lemma lem4856651 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term798 A B s x t) = (term693 A B t s x).
Proof. exact (eq_refl (term798 A B s x t)). Qed.
Lemma lem4856652 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term799 A B s x) = (term695 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856651 A B t s x)). Qed.
Lemma lem4856653 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856654 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term800 A B s x) = (term696 A B s x).
Proof. exact (MK_COMB (@lem4856653 A) (@lem4856652 A B s x)). Qed.
Lemma lem4856655 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856656 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term801 A B s x) = (term788 A B s x).
Proof. exact (MK_COMB (@lem4856655) (@lem4856654 A B s x)). Qed.
Lemma lem4856657 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term772 A B s x) = (term772 A B s x).
Proof. exact (eq_refl (term772 A B s x)). Qed.
Lemma lem4856658 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term796 A B s x) = (term790 A B s x).
Proof. exact (MK_COMB (@lem4856656 A B s x) (@lem4856657 A B s x)). Qed.
Lemma lem4856659 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856660 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term802 A B s x) = (term803 A B s x).
Proof. exact (MK_COMB (@lem4856659) (@lem4856658 A B s x)). Qed.
Lemma lem4856661 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term798 A B s x t) = (term693 A B t s x).
Proof. exact (eq_refl (term798 A B s x t)). Qed.
Lemma lem4856662 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856663 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term804 A B s x t) = (term805 A B t s x).
Proof. exact (MK_COMB (@lem4856662) (@lem4856661 A B t s x)). Qed.
Lemma lem4856664 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term772 A B s x) = (term772 A B s x).
Proof. exact (eq_refl (term772 A B s x)). Qed.
Lemma lem4856665 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term806 A t B s x) = (term807 A t B s x).
Proof. exact (MK_COMB (@lem4856663 A B t s x) (@lem4856664 A B s x)). Qed.
Lemma lem4856666 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term808 A B s x) = (term809 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856665 A t B s x)). Qed.
Lemma lem4856667 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856668 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term797 A B s x) = (term810 A B s x).
Proof. exact (MK_COMB (@lem4856667 A) (@lem4856666 A B s x)). Qed.
Lemma lem4856669 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : ((term796 A B s x) = (term797 A B s x)) = ((term790 A B s x) = (term810 A B s x)).
Proof. exact (MK_COMB (@lem4856660 A B s x) (@lem4856668 A B s x)). Qed.
Lemma lem4856670 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term790 A B s x) = (term810 A B s x).
Proof. exact (EQ_MP (@lem4856669 A B s x) (@lem4856650 A B s x)). Qed.
Lemma lem4856672 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4856673 {A : Type'} (P : Prop) (Q : type162 A) : (term811 A P Q) = (term812 A P Q).
Proof. exact (@lem4856672 (type684 A) P Q). Qed.
Lemma lem4856674 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term813 A t B s x) = (term814 A t B s x).
Proof. exact (@lem4856673 A (term693 A B t s x) (term771 A B s x)). Qed.
Lemma lem4856675 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term815 A B s x x') = (term769 A B x' s x).
Proof. exact (eq_refl (term815 A B s x x')). Qed.
Lemma lem4856676 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term816 A B s x) = (term771 A B s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem4856675 A B x' s x)). Qed.
Lemma lem4856677 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4856678 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term817 A B s x) = (term772 A B s x).
Proof. exact (MK_COMB (@lem4856677 A) (@lem4856676 A B s x)). Qed.
Lemma lem4856679 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term805 A B t s x) = (term805 A B t s x).
Proof. exact (eq_refl (term805 A B t s x)). Qed.
Lemma lem4856680 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term813 A t B s x) = (term807 A t B s x).
Proof. exact (MK_COMB (@lem4856679 A B t s x) (@lem4856678 A B s x)). Qed.
Lemma lem4856681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856682 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term818 A t B s x) = (term819 A t B s x).
Proof. exact (MK_COMB (@lem4856681) (@lem4856680 A t B s x)). Qed.
Lemma lem4856683 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term815 A B s x x') = (term769 A B x' s x).
Proof. exact (eq_refl (term815 A B s x x')). Qed.
Lemma lem4856684 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term805 A B t s x) = (term805 A B t s x).
Proof. exact (eq_refl (term805 A B t s x)). Qed.
Lemma lem4856685 {A : Type'} (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term820 A t B s x x') = (term821 A t B x' s x).
Proof. exact (MK_COMB (@lem4856684 A B t s x) (@lem4856683 A B x' s x)). Qed.
Lemma lem4856686 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term822 A t B s x) = (term823 A t B s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem4856685 A t B x' s x)). Qed.
Lemma lem4856687 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4856688 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term814 A t B s x) = (term824 A t B s x).
Proof. exact (MK_COMB (@lem4856687 A) (@lem4856686 A t B s x)). Qed.
Lemma lem4856689 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : ((term813 A t B s x) = (term814 A t B s x)) = ((term807 A t B s x) = (term824 A t B s x)).
Proof. exact (MK_COMB (@lem4856682 A t B s x) (@lem4856688 A t B s x)). Qed.
Lemma lem4856690 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term807 A t B s x) = (term824 A t B s x).
Proof. exact (EQ_MP (@lem4856689 A t B s x) (@lem4856674 A t B s x)). Qed.
Lemma lem4856691 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term809 A B s x) = (term825 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856690 A t B s x)). Qed.
Lemma lem4856692 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856693 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term810 A B s x) = (term826 A B s x).
Proof. exact (MK_COMB (@lem4856692 A) (@lem4856691 A B s x)). Qed.
Lemma lem4856694 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term790 A B s x) = (term826 A B s x).
Proof. exact (TRANS (@lem4856670 A B s x) (@lem4856693 A B s x)). Qed.
Lemma lem4856695 {A : Type'} (B : type686 A) (s : A -> Prop) : (term792 A B s) = (term827 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856694 A B s x)). Qed.
Lemma lem4856696 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856697 {A : Type'} (B : type686 A) (s : A -> Prop) : (term793 A B s) = (term828 A B s).
Proof. exact (MK_COMB (@lem4856696 A) (@lem4856695 A B s)). Qed.
Lemma lem4856698 {A : Type'} (B : type686 A) (s : A -> Prop) : (term775 A B s) = (term828 A B s).
Proof. exact (TRANS (@lem4856644 A B s) (@lem4856697 A B s)). Qed.
Lemma lem4856699 {A : Type'} (B : type686 A) (s : A -> Prop) : (term676 A B s) = (term828 A B s).
Proof. exact (TRANS (@lem4856617 A B s) (@lem4856698 A B s)). Qed.
Lemma lem4856700 {A : Type'} (s : A -> Prop) (B : type686 A) : (term652 A s B) = (term652 A s B).
Proof. exact (eq_refl (term652 A s B)). Qed.
Lemma lem4856701 {A : Type'} (B : type686 A) (s : A -> Prop) : (term677 A B s) = (term829 A B s).
Proof. exact (MK_COMB (@lem4856700 A s B) (@lem4856699 A B s)). Qed.
Lemma lem4856705 {A : Type'} (P : A -> Prop) (Q : Prop) : (term714 A P Q) = (term715 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4856706 {A : Type'} (P : type686 A) (Q : Prop) : (term794 A P Q) = (term795 A P Q).
Proof. exact (@lem4856705 (A -> Prop) P Q). Qed.
Lemma lem4856707 {A : Type'} (B : type686 A) (s : A -> Prop) : (term830 A B s) = (term831 A B s).
Proof. exact (@lem4856706 A (term602 A s B) (term828 A B s)). Qed.
Lemma lem4856708 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term832 A s B c) = (term593 A s B c).
Proof. exact (eq_refl (term832 A s B c)). Qed.
Lemma lem4856709 {A : Type'} (s : A -> Prop) (B : type686 A) : (term833 A s B) = (term602 A s B).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4856708 A s B c)). Qed.
Lemma lem4856710 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856711 {A : Type'} (s : A -> Prop) (B : type686 A) : (term834 A s B) = (term603 A s B).
Proof. exact (MK_COMB (@lem4856710 A) (@lem4856709 A s B)). Qed.
Lemma lem4856712 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856713 {A : Type'} (s : A -> Prop) (B : type686 A) : (term835 A s B) = (term652 A s B).
Proof. exact (MK_COMB (@lem4856712) (@lem4856711 A s B)). Qed.
Lemma lem4856714 {A : Type'} (B : type686 A) (s : A -> Prop) : (term828 A B s) = (term828 A B s).
Proof. exact (eq_refl (term828 A B s)). Qed.
Lemma lem4856715 {A : Type'} (B : type686 A) (s : A -> Prop) : (term830 A B s) = (term829 A B s).
Proof. exact (MK_COMB (@lem4856713 A s B) (@lem4856714 A B s)). Qed.
Lemma lem4856716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856717 {A : Type'} (B : type686 A) (s : A -> Prop) : (term836 A B s) = (term837 A B s).
Proof. exact (MK_COMB (@lem4856716) (@lem4856715 A B s)). Qed.
Lemma lem4856718 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term832 A s B c) = (term593 A s B c).
Proof. exact (eq_refl (term832 A s B c)). Qed.
Lemma lem4856719 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856720 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term838 A s B c) = (term839 A s B c).
Proof. exact (MK_COMB (@lem4856719) (@lem4856718 A s B c)). Qed.
Lemma lem4856721 {A : Type'} (B : type686 A) (s : A -> Prop) : (term828 A B s) = (term828 A B s).
Proof. exact (eq_refl (term828 A B s)). Qed.
Lemma lem4856722 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term840 A c B s) = (term841 A c B s).
Proof. exact (MK_COMB (@lem4856720 A s B c) (@lem4856721 A B s)). Qed.
Lemma lem4856723 {A : Type'} (B : type686 A) (s : A -> Prop) : (term842 A B s) = (term843 A B s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4856722 A c B s)). Qed.
Lemma lem4856724 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856725 {A : Type'} (B : type686 A) (s : A -> Prop) : (term831 A B s) = (term844 A B s).
Proof. exact (MK_COMB (@lem4856724 A) (@lem4856723 A B s)). Qed.
Lemma lem4856726 {A : Type'} (B : type686 A) (s : A -> Prop) : ((term830 A B s) = (term831 A B s)) = ((term829 A B s) = (term844 A B s)).
Proof. exact (MK_COMB (@lem4856717 A B s) (@lem4856725 A B s)). Qed.
Lemma lem4856727 {A : Type'} (B : type686 A) (s : A -> Prop) : (term829 A B s) = (term844 A B s).
Proof. exact (EQ_MP (@lem4856726 A B s) (@lem4856707 A B s)). Qed.
Lemma lem4856729 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4856730 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (@lem4856729 A P Q). Qed.
Lemma lem4856731 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term845 A c B s) = (term846 A c B s).
Proof. exact (@lem4856730 A (term593 A s B c) (term827 A B s)). Qed.
Lemma lem4856732 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term847 A B s x) = (term826 A B s x).
Proof. exact (eq_refl (term847 A B s x)). Qed.
Lemma lem4856733 {A : Type'} (B : type686 A) (s : A -> Prop) : (term848 A B s) = (term827 A B s).
Proof. exact (fun_ext (fun x : A => @lem4856732 A B s x)). Qed.
Lemma lem4856734 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856735 {A : Type'} (B : type686 A) (s : A -> Prop) : (term849 A B s) = (term828 A B s).
Proof. exact (MK_COMB (@lem4856734 A) (@lem4856733 A B s)). Qed.
Lemma lem4856736 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term839 A s B c) = (term839 A s B c).
Proof. exact (eq_refl (term839 A s B c)). Qed.
Lemma lem4856737 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term845 A c B s) = (term841 A c B s).
Proof. exact (MK_COMB (@lem4856736 A s B c) (@lem4856735 A B s)). Qed.
Lemma lem4856738 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856739 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term850 A c B s) = (term851 A c B s).
Proof. exact (MK_COMB (@lem4856738) (@lem4856737 A c B s)). Qed.
Lemma lem4856740 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term847 A B s x) = (term826 A B s x).
Proof. exact (eq_refl (term847 A B s x)). Qed.
Lemma lem4856741 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term839 A s B c) = (term839 A s B c).
Proof. exact (eq_refl (term839 A s B c)). Qed.
Lemma lem4856742 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term852 A c B s x) = (term853 A c B s x).
Proof. exact (MK_COMB (@lem4856741 A s B c) (@lem4856740 A B s x)). Qed.
Lemma lem4856743 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term854 A c B s) = (term855 A c B s).
Proof. exact (fun_ext (fun x : A => @lem4856742 A c B s x)). Qed.
Lemma lem4856744 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856745 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term846 A c B s) = (term856 A c B s).
Proof. exact (MK_COMB (@lem4856744 A) (@lem4856743 A c B s)). Qed.
Lemma lem4856746 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : ((term845 A c B s) = (term846 A c B s)) = ((term841 A c B s) = (term856 A c B s)).
Proof. exact (MK_COMB (@lem4856739 A c B s) (@lem4856745 A c B s)). Qed.
Lemma lem4856747 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term841 A c B s) = (term856 A c B s).
Proof. exact (EQ_MP (@lem4856746 A c B s) (@lem4856731 A c B s)). Qed.
Lemma lem4856749 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4856750 {A : Type'} (P : Prop) (Q : type686 A) : (term551 A P Q) = (term552 A P Q).
Proof. exact (@lem4856749 (A -> Prop) P Q). Qed.
Lemma lem4856751 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term857 A c B s x) = (term858 A c B s x).
Proof. exact (@lem4856750 A (term593 A s B c) (term825 A B s x)). Qed.
Lemma lem4856752 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term859 A B s x t) = (term824 A t B s x).
Proof. exact (eq_refl (term859 A B s x t)). Qed.
Lemma lem4856753 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term860 A B s x) = (term825 A B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856752 A t B s x)). Qed.
Lemma lem4856754 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856755 {A : Type'} (B : type686 A) (s : A -> Prop) (x : A) : (term861 A B s x) = (term826 A B s x).
Proof. exact (MK_COMB (@lem4856754 A) (@lem4856753 A B s x)). Qed.
Lemma lem4856756 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term839 A s B c) = (term839 A s B c).
Proof. exact (eq_refl (term839 A s B c)). Qed.
Lemma lem4856757 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term857 A c B s x) = (term853 A c B s x).
Proof. exact (MK_COMB (@lem4856756 A s B c) (@lem4856755 A B s x)). Qed.
Lemma lem4856758 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856759 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term862 A c B s x) = (term863 A c B s x).
Proof. exact (MK_COMB (@lem4856758) (@lem4856757 A c B s x)). Qed.
Lemma lem4856760 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term859 A B s x t) = (term824 A t B s x).
Proof. exact (eq_refl (term859 A B s x t)). Qed.
Lemma lem4856761 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term839 A s B c) = (term839 A s B c).
Proof. exact (eq_refl (term839 A s B c)). Qed.
Lemma lem4856762 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term864 A c B s x t) = (term865 A c t B s x).
Proof. exact (MK_COMB (@lem4856761 A s B c) (@lem4856760 A t B s x)). Qed.
Lemma lem4856763 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term866 A c B s x) = (term867 A c B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856762 A c t B s x)). Qed.
Lemma lem4856764 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856765 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term858 A c B s x) = (term868 A c B s x).
Proof. exact (MK_COMB (@lem4856764 A) (@lem4856763 A c B s x)). Qed.
Lemma lem4856766 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : ((term857 A c B s x) = (term858 A c B s x)) = ((term853 A c B s x) = (term868 A c B s x)).
Proof. exact (MK_COMB (@lem4856759 A c B s x) (@lem4856765 A c B s x)). Qed.
Lemma lem4856767 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term853 A c B s x) = (term868 A c B s x).
Proof. exact (EQ_MP (@lem4856766 A c B s x) (@lem4856751 A c B s x)). Qed.
Lemma lem4856769 {A : Type'} (P : Prop) (Q : A -> Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4856770 {A : Type'} (P : Prop) (Q : type162 A) : (term811 A P Q) = (term812 A P Q).
Proof. exact (@lem4856769 (type684 A) P Q). Qed.
Lemma lem4856771 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term869 A c t B s x) = (term870 A c t B s x).
Proof. exact (@lem4856770 A (term593 A s B c) (term823 A t B s x)). Qed.
Lemma lem4856772 {A : Type'} (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term871 A t B s x x') = (term821 A t B x' s x).
Proof. exact (eq_refl (term871 A t B s x x')). Qed.
Lemma lem4856773 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term872 A t B s x) = (term823 A t B s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem4856772 A t B x' s x)). Qed.
Lemma lem4856774 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4856775 {A : Type'} (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term873 A t B s x) = (term824 A t B s x).
Proof. exact (MK_COMB (@lem4856774 A) (@lem4856773 A t B s x)). Qed.
Lemma lem4856776 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term839 A s B c) = (term839 A s B c).
Proof. exact (eq_refl (term839 A s B c)). Qed.
Lemma lem4856777 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term869 A c t B s x) = (term865 A c t B s x).
Proof. exact (MK_COMB (@lem4856776 A s B c) (@lem4856775 A t B s x)). Qed.
Lemma lem4856778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4856779 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term874 A c t B s x) = (term875 A c t B s x).
Proof. exact (MK_COMB (@lem4856778) (@lem4856777 A c t B s x)). Qed.
Lemma lem4856780 {A : Type'} (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term871 A t B s x x') = (term821 A t B x' s x).
Proof. exact (eq_refl (term871 A t B s x x')). Qed.
Lemma lem4856781 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term839 A s B c) = (term839 A s B c).
Proof. exact (eq_refl (term839 A s B c)). Qed.
Lemma lem4856782 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term876 A c t B s x x') = (term877 A c t B x' s x).
Proof. exact (MK_COMB (@lem4856781 A s B c) (@lem4856780 A t B x' s x)). Qed.
Lemma lem4856783 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term878 A c t B s x) = (term879 A c t B s x).
Proof. exact (fun_ext (fun x' : type684 A => @lem4856782 A c t B x' s x)). Qed.
Lemma lem4856784 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem4856785 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term870 A c t B s x) = (term880 A c t B s x).
Proof. exact (MK_COMB (@lem4856784 A) (@lem4856783 A c t B s x)). Qed.
Lemma lem4856786 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : ((term869 A c t B s x) = (term870 A c t B s x)) = ((term865 A c t B s x) = (term880 A c t B s x)).
Proof. exact (MK_COMB (@lem4856779 A c t B s x) (@lem4856785 A c t B s x)). Qed.
Lemma lem4856787 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term865 A c t B s x) = (term880 A c t B s x).
Proof. exact (EQ_MP (@lem4856786 A c t B s x) (@lem4856771 A c t B s x)). Qed.
Lemma lem4856788 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term867 A c B s x) = (term881 A c B s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856787 A c t B s x)). Qed.
Lemma lem4856789 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856790 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term868 A c B s x) = (term882 A c B s x).
Proof. exact (MK_COMB (@lem4856789 A) (@lem4856788 A c B s x)). Qed.
Lemma lem4856791 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) : (term853 A c B s x) = (term882 A c B s x).
Proof. exact (TRANS (@lem4856767 A c B s x) (@lem4856790 A c B s x)). Qed.
Lemma lem4856792 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term855 A c B s) = (term883 A c B s).
Proof. exact (fun_ext (fun x : A => @lem4856791 A c B s x)). Qed.
Lemma lem4856793 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4856794 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term856 A c B s) = (term884 A c B s).
Proof. exact (MK_COMB (@lem4856793 A) (@lem4856792 A c B s)). Qed.
Lemma lem4856795 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) : (term841 A c B s) = (term884 A c B s).
Proof. exact (TRANS (@lem4856747 A c B s) (@lem4856794 A c B s)). Qed.
Lemma lem4856796 {A : Type'} (B : type686 A) (s : A -> Prop) : (term843 A B s) = (term885 A B s).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4856795 A c B s)). Qed.
Lemma lem4856797 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem4856798 {A : Type'} (B : type686 A) (s : A -> Prop) : (term844 A B s) = (term886 A B s).
Proof. exact (MK_COMB (@lem4856797 A) (@lem4856796 A B s)). Qed.
Lemma lem4856799 {A : Type'} (B : type686 A) (s : A -> Prop) : (term829 A B s) = (term886 A B s).
Proof. exact (TRANS (@lem4856727 A B s) (@lem4856798 A B s)). Qed.
Lemma lem4856800 {A : Type'} (B : type686 A) (s : A -> Prop) : (term677 A B s) = (term886 A B s).
Proof. exact (TRANS (@lem4856701 A B s) (@lem4856799 A B s)). Qed.
Lemma lem4856801 {A : Type'} (B : type686 A) (s : A -> Prop) : (term654 A B s) = (term886 A B s).
Proof. exact (TRANS (@lem4856472 A B s) (@lem4856800 A B s)). Qed.
Lemma lem4856802 {A : Type'} (B : type686 A) (s : A -> Prop) : (term539 A B s) = (term886 A B s).
Proof. exact (TRANS (@lem4856127 A B s) (@lem4856801 A B s)). Qed.
Lemma lem4856803 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term539 A B s) : term886 A B s.
Proof. exact (EQ_MP (@lem4856802 A B s) (@lem4855813 A B s h1)). Qed.
Lemma lem4856804 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (h1 : term884 A c B s) : term884 A c B s.
Proof. exact (h1). Qed.
Lemma lem4856805 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) (h1 : term882 A c B s x) : term882 A c B s x.
Proof. exact (h1). Qed.
Lemma lem4856806 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) (h1 : term880 A c t B s x) : term880 A c t B s x.
Proof. exact (h1). Qed.
Lemma lem4856807 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term877 A c t B x' s x) : term877 A c t B x' s x.
Proof. exact (h1). Qed.
Lemma lem4856808 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term586 A B u s.
Proof. exact (h1). Qed.
Lemma lem4856813 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856814 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856813 A Prop f x). Qed.
Lemma lem4856816 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4856814 A s x). Qed.
Lemma lem4856817 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856822 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856823 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856822 A Prop f x). Qed.
Lemma lem4856825 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4856823 A t x). Qed.
Lemma lem4856826 {A : Type'} (t : A -> Prop) (x : A) : (term202 A t x) = (term277 A t x).
Proof. exact (MK_COMB (@lem4856817) (@lem4856825 A t x)). Qed.
Lemma lem4856827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856828 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4856833 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856834 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4856833 (A -> Prop) A f x). Qed.
Lemma lem4856836 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem4856834 A x' t). Qed.
Lemma lem4856837 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term259 A s x' t) = (term260 A s x' t).
Proof. exact (MK_COMB (@lem4856828 A s) (@lem4856836 A x' t)). Qed.
Lemma lem4856839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856840 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856839 A Prop f x). Qed.
Lemma lem4856841 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term260 A s x' t) = (term261 A s x' t).
Proof. exact (@lem4856840 A s (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem4856842 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term259 A s x' t) = (term261 A s x' t).
Proof. exact (TRANS (@lem4856837 A s x' t) (@lem4856841 A s x' t)). Qed.
Lemma lem4856843 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term262 A s x' t) = (term263 A s x' t).
Proof. exact (MK_COMB (@lem4856827) (@lem4856842 A s x' t)). Qed.
Lemma lem4856844 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem4856849 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856850 {A : Type'} (f : type684 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A) f x).
Proof. exact (@lem4856849 (A -> Prop) A f x). Qed.
Lemma lem4856852 {A : Type'} (x' : type684 A) (t : A -> Prop) : (x' t) = (@I ((A -> Prop) -> A) x' t).
Proof. exact (@lem4856850 A x' t). Qed.
Lemma lem4856853 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term270 A x' t) = (term271 A x' t).
Proof. exact (MK_COMB (@lem4856844 A t) (@lem4856852 A x' t)). Qed.
Lemma lem4856855 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856856 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856855 A Prop f x). Qed.
Lemma lem4856857 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term271 A x' t) = (term272 A x' t).
Proof. exact (@lem4856856 A t (@I ((A -> Prop) -> A) x' t)). Qed.
Lemma lem4856858 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term270 A x' t) = (term272 A x' t).
Proof. exact (TRANS (@lem4856853 A x' t) (@lem4856857 A x' t)). Qed.
Lemma lem4856859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856860 {A : Type'} (x' : type684 A) (t : A -> Prop) : (term273 A x' t) = (term274 A x' t).
Proof. exact (MK_COMB (@lem4856859) (@lem4856858 A x' t)). Qed.
Lemma lem4856861 {A : Type'} (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term887 A s x' t) = (term888 A s x' t).
Proof. exact (MK_COMB (@lem4856860 A x' t) (@lem4856843 A s x' t)). Qed.
Lemma lem4856862 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856867 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856868 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4856867 (A -> Prop) Prop f x). Qed.
Lemma lem4856870 {A : Type'} (B : type686 A) (t : A -> Prop) : (B t) = (@I ((A -> Prop) -> Prop) B t).
Proof. exact (@lem4856868 A B t). Qed.
Lemma lem4856871 {A : Type'} (B : type686 A) (t : A -> Prop) : (term216 A B t) = (term254 A B t).
Proof. exact (MK_COMB (@lem4856862) (@lem4856870 A B t)). Qed.
Lemma lem4856872 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856873 {A : Type'} (B : type686 A) (t : A -> Prop) : (term188 A B t) = (term255 A B t).
Proof. exact (MK_COMB (@lem4856872) (@lem4856871 A B t)). Qed.
Lemma lem4856874 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term889 A B s x' t) = (term890 A B s x' t).
Proof. exact (MK_COMB (@lem4856873 A B t) (@lem4856861 A s x' t)). Qed.
Lemma lem4856875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856876 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term891 A B s x' t) = (term892 A B s x' t).
Proof. exact (MK_COMB (@lem4856875) (@lem4856874 A B s x' t)). Qed.
Lemma lem4856877 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term746 A B s x' t x) = (term893 A B s x' t x).
Proof. exact (MK_COMB (@lem4856876 A B s x' t) (@lem4856826 A t x)). Qed.
Lemma lem4856878 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term748 A B s x' x) = (term894 A B s x' x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4856877 A B s x' t x)). Qed.
Lemma lem4856879 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4856880 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term750 A B s x' x) = (term895 A B s x' x).
Proof. exact (MK_COMB (@lem4856879 A) (@lem4856878 A B s x' x)). Qed.
Lemma lem4856881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856882 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term767 A B s x' x) = (term896 A B s x' x).
Proof. exact (MK_COMB (@lem4856881) (@lem4856880 A B s x' x)). Qed.
Lemma lem4856883 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term769 A B x' s x) = (term897 A B x' s x).
Proof. exact (MK_COMB (@lem4856882 A B s x' x) (@lem4856816 A s x)). Qed.
Lemma lem4856884 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856889 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856890 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856889 A Prop f x). Qed.
Lemma lem4856892 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4856890 A s x). Qed.
Lemma lem4856893 {A : Type'} (s : A -> Prop) (x : A) : (term202 A s x) = (term277 A s x).
Proof. exact (MK_COMB (@lem4856884) (@lem4856892 A s x)). Qed.
Lemma lem4856898 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856899 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856898 A Prop f x). Qed.
Lemma lem4856901 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4856899 A t x). Qed.
Lemma lem4856906 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856907 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856906 A Prop f x). Qed.
Lemma lem4856909 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4856907 A s x). Qed.
Lemma lem4856910 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856915 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856916 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856915 A Prop f x). Qed.
Lemma lem4856918 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4856916 A t x). Qed.
Lemma lem4856919 {A : Type'} (t : A -> Prop) (x : A) : (term202 A t x) = (term277 A t x).
Proof. exact (MK_COMB (@lem4856910) (@lem4856918 A t x)). Qed.
Lemma lem4856920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856921 {A : Type'} (t : A -> Prop) (x : A) : (term184 A t x) = (term278 A t x).
Proof. exact (MK_COMB (@lem4856920) (@lem4856919 A t x)). Qed.
Lemma lem4856922 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term540 A t s x) = (term898 A t s x).
Proof. exact (MK_COMB (@lem4856921 A t x) (@lem4856909 A s x)). Qed.
Lemma lem4856923 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term541 A t s) = (term899 A t s).
Proof. exact (fun_ext (fun x : A => @lem4856922 A t s x)). Qed.
Lemma lem4856924 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4856925 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term542 A t s) = (term900 A t s).
Proof. exact (MK_COMB (@lem4856924 A) (@lem4856923 A t s)). Qed.
Lemma lem4856930 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856931 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4856930 (A -> Prop) Prop f x). Qed.
Lemma lem4856933 {A : Type'} (B : type686 A) (t : A -> Prop) : (B t) = (@I ((A -> Prop) -> Prop) B t).
Proof. exact (@lem4856931 A B t). Qed.
Lemma lem4856934 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856935 {A : Type'} (B : type686 A) (t : A -> Prop) : (term119 A B t) = (term284 A B t).
Proof. exact (MK_COMB (@lem4856934) (@lem4856933 A B t)). Qed.
Lemma lem4856936 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term590 A B t s) = (term901 A B t s).
Proof. exact (MK_COMB (@lem4856935 A B t) (@lem4856925 A t s)). Qed.
Lemma lem4856937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856938 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) : (term591 A B t s) = (term902 A B t s).
Proof. exact (MK_COMB (@lem4856937) (@lem4856936 A B t s)). Qed.
Lemma lem4856939 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term621 A B s t x) = (term903 A B s t x).
Proof. exact (MK_COMB (@lem4856938 A B t s) (@lem4856901 A t x)). Qed.
Lemma lem4856940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856941 {A : Type'} (B : type686 A) (s : A -> Prop) (t : A -> Prop) (x : A) : (term691 A B s t x) = (term904 A B s t x).
Proof. exact (MK_COMB (@lem4856940) (@lem4856939 A B s t x)). Qed.
Lemma lem4856942 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term693 A B t s x) = (term905 A B t s x).
Proof. exact (MK_COMB (@lem4856941 A B s t x) (@lem4856893 A s x)). Qed.
Lemma lem4856943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856944 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) : (term805 A B t s x) = (term906 A B t s x).
Proof. exact (MK_COMB (@lem4856943) (@lem4856942 A B t s x)). Qed.
Lemma lem4856945 {A : Type'} (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term821 A t B x' s x) = (term907 A t B x' s x).
Proof. exact (MK_COMB (@lem4856944 A B t s x) (@lem4856883 A B x' s x)). Qed.
Lemma lem4856946 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856951 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856952 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4856951 (A -> Prop) Prop f x). Qed.
Lemma lem4856954 {A : Type'} (B : type686 A) (c : A -> Prop) : (B c) = (@I ((A -> Prop) -> Prop) B c).
Proof. exact (@lem4856952 A B c). Qed.
Lemma lem4856955 {A : Type'} (B : type686 A) (c : A -> Prop) : (term216 A B c) = (term254 A B c).
Proof. exact (MK_COMB (@lem4856946) (@lem4856954 A B c)). Qed.
Lemma lem4856960 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856961 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856960 A Prop f x). Qed.
Lemma lem4856963 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4856961 A s x). Qed.
Lemma lem4856964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4856969 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856970 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4856969 A Prop f x). Qed.
Lemma lem4856972 {A : Type'} (c : A -> Prop) (x : A) : (c x) = (@I (A -> Prop) c x).
Proof. exact (@lem4856970 A c x). Qed.
Lemma lem4856973 {A : Type'} (c : A -> Prop) (x : A) : (term202 A c x) = (term277 A c x).
Proof. exact (MK_COMB (@lem4856964) (@lem4856972 A c x)). Qed.
Lemma lem4856974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856975 {A : Type'} (c : A -> Prop) (x : A) : (term184 A c x) = (term278 A c x).
Proof. exact (MK_COMB (@lem4856974) (@lem4856973 A c x)). Qed.
Lemma lem4856976 {A : Type'} (c : A -> Prop) (s : A -> Prop) (x : A) : (term540 A c s x) = (term898 A c s x).
Proof. exact (MK_COMB (@lem4856975 A c x) (@lem4856963 A s x)). Qed.
Lemma lem4856977 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term541 A c s) = (term899 A c s).
Proof. exact (fun_ext (fun x : A => @lem4856976 A c s x)). Qed.
Lemma lem4856978 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4856979 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term542 A c s) = (term900 A c s).
Proof. exact (MK_COMB (@lem4856978 A) (@lem4856977 A c s)). Qed.
Lemma lem4856984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4856985 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4856984 (A -> Prop) Prop f x). Qed.
Lemma lem4856987 {A : Type'} (B : type686 A) (c : A -> Prop) : (B c) = (@I ((A -> Prop) -> Prop) B c).
Proof. exact (@lem4856985 A B c). Qed.
Lemma lem4856988 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856989 {A : Type'} (B : type686 A) (c : A -> Prop) : (term119 A B c) = (term284 A B c).
Proof. exact (MK_COMB (@lem4856988) (@lem4856987 A B c)). Qed.
Lemma lem4856990 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term590 A B c s) = (term901 A B c s).
Proof. exact (MK_COMB (@lem4856989 A B c) (@lem4856979 A c s)). Qed.
Lemma lem4856991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4856992 {A : Type'} (B : type686 A) (c : A -> Prop) (s : A -> Prop) : (term591 A B c s) = (term902 A B c s).
Proof. exact (MK_COMB (@lem4856991) (@lem4856990 A B c s)). Qed.
Lemma lem4856993 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term593 A s B c) = (term908 A s B c).
Proof. exact (MK_COMB (@lem4856992 A B c s) (@lem4856955 A B c)). Qed.
Lemma lem4856994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4856995 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) : (term839 A s B c) = (term909 A s B c).
Proof. exact (MK_COMB (@lem4856994) (@lem4856993 A s B c)). Qed.
Lemma lem4856996 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) : (term877 A c t B x' s x) = (term910 A c t B x' s x).
Proof. exact (MK_COMB (@lem4856995 A s B c) (@lem4856945 A t B x' s x)). Qed.
Lemma lem4856997 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term877 A c t B x' s x) : term910 A c t B x' s x.
Proof. exact (EQ_MP (@lem4856996 A c t B x' s x) (@lem4856807 A c t B x' s x h1)). Qed.
Lemma lem4857002 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857003 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4857002 A Prop f x). Qed.
Lemma lem4857005 {A : Type'} (s : A -> Prop) (x' : A) : (s x') = (@I (A -> Prop) s x').
Proof. exact (@lem4857003 A s x'). Qed.
Lemma lem4857006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4857013 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857014 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4857013 A (A -> Prop) f x). Qed.
Lemma lem4857015 {A : Type'} (u : type1402 A) (x : A) : (u x) = (@I (A -> A -> Prop) u x).
Proof. exact (@lem4857014 A u x). Qed.
Lemma lem4857016 {A : Type'} (x' : A) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem4857017 {A : Type'} (u : type1402 A) (x : A) (x' : A) : (u x x') = (@I (A -> A -> Prop) u x x').
Proof. exact (MK_COMB (@lem4857015 A u x) (@lem4857016 A x')). Qed.
Lemma lem4857019 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857020 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4857019 A Prop f x). Qed.
Lemma lem4857021 {A : Type'} (u : type1402 A) (x : A) (x' : A) : (@I (A -> A -> Prop) u x x') = (term911 A u x x').
Proof. exact (@lem4857020 A (@I (A -> A -> Prop) u x) x'). Qed.
Lemma lem4857023 {A : Type'} (u : type1402 A) (x : A) (x' : A) : (u x x') = (term911 A u x x').
Proof. exact (TRANS (@lem4857017 A u x x') (@lem4857021 A u x x')). Qed.
Lemma lem4857024 {A : Type'} (u : type1402 A) (x : A) (x' : A) : (term912 A u x x') = (term913 A u x x').
Proof. exact (MK_COMB (@lem4857006) (@lem4857023 A u x x')). Qed.
Lemma lem4857025 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4857026 {A : Type'} (u : type1402 A) (x : A) (x' : A) : (term914 A u x x') = (term915 A u x x').
Proof. exact (MK_COMB (@lem4857025) (@lem4857024 A u x x')). Qed.
Lemma lem4857027 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term916 A u x s x') = (term917 A u x s x').
Proof. exact (MK_COMB (@lem4857026 A u x x') (@lem4857005 A s x')). Qed.
Lemma lem4857028 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term918 A u x s) = (term919 A u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857027 A u x s x')). Qed.
Lemma lem4857029 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857030 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term920 A u x s) = (term921 A u x s).
Proof. exact (MK_COMB (@lem4857029 A) (@lem4857028 A u x s)). Qed.
Lemma lem4857037 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857038 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4857037 A (A -> Prop) f x). Qed.
Lemma lem4857039 {A : Type'} (u : type1402 A) (x : A) : (u x) = (@I (A -> A -> Prop) u x).
Proof. exact (@lem4857038 A u x). Qed.
Lemma lem4857040 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4857041 {A : Type'} (u : type1402 A) (x : A) : (u x x) = (@I (A -> A -> Prop) u x x).
Proof. exact (MK_COMB (@lem4857039 A u x) (@lem4857040 A x)). Qed.
Lemma lem4857043 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857044 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4857043 A Prop f x). Qed.
Lemma lem4857045 {A : Type'} (u : type1402 A) (x : A) : (@I (A -> A -> Prop) u x x) = (term922 A u x).
Proof. exact (@lem4857044 A (@I (A -> A -> Prop) u x) x). Qed.
Lemma lem4857047 {A : Type'} (u : type1402 A) (x : A) : (u x x) = (term922 A u x).
Proof. exact (TRANS (@lem4857041 A u x) (@lem4857045 A u x)). Qed.
Lemma lem4857048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4857049 {A : Type'} (u : type1402 A) (x : A) : (term923 A u x) = (term924 A u x).
Proof. exact (MK_COMB (@lem4857048) (@lem4857047 A u x)). Qed.
Lemma lem4857050 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term925 A u x s) = (term926 A u x s).
Proof. exact (MK_COMB (@lem4857049 A u x) (@lem4857030 A u x s)). Qed.
Lemma lem4857051 {A : Type'} (B : type686 A) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem4857056 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857057 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem4857056 A (A -> Prop) f x). Qed.
Lemma lem4857059 {A : Type'} (u : type1402 A) (x : A) : (u x) = (@I (A -> A -> Prop) u x).
Proof. exact (@lem4857057 A u x). Qed.
Lemma lem4857060 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term927 A B u x) = (term928 A B u x).
Proof. exact (MK_COMB (@lem4857051 A B) (@lem4857059 A u x)). Qed.
Lemma lem4857062 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857063 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem4857062 (A -> Prop) Prop f x). Qed.
Lemma lem4857064 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term928 A B u x) = (term929 A B u x).
Proof. exact (@lem4857063 A B (@I (A -> A -> Prop) u x)). Qed.
Lemma lem4857065 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term927 A B u x) = (term929 A B u x).
Proof. exact (TRANS (@lem4857060 A B u x) (@lem4857064 A B u x)). Qed.
Lemma lem4857066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4857067 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term930 A B u x) = (term931 A B u x).
Proof. exact (MK_COMB (@lem4857066) (@lem4857065 A B u x)). Qed.
Lemma lem4857068 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term932 A B u x s) = (term933 A B u x s).
Proof. exact (MK_COMB (@lem4857067 A B u x) (@lem4857050 A u x s)). Qed.
Lemma lem4857069 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4857074 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4857075 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem4857074 A Prop f x). Qed.
Lemma lem4857077 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4857075 A s x). Qed.
Lemma lem4857078 {A : Type'} (s : A -> Prop) (x : A) : (term202 A s x) = (term277 A s x).
Proof. exact (MK_COMB (@lem4857069) (@lem4857077 A s x)). Qed.
Lemma lem4857079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4857080 {A : Type'} (s : A -> Prop) (x : A) : (term184 A s x) = (term278 A s x).
Proof. exact (MK_COMB (@lem4857079) (@lem4857078 A s x)). Qed.
Lemma lem4857081 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term582 A B u x s) = (term934 A B u x s).
Proof. exact (MK_COMB (@lem4857080 A s x) (@lem4857068 A B u x s)). Qed.
Lemma lem4857082 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term584 A B u s) = (term935 A B u s).
Proof. exact (fun_ext (fun x : A => @lem4857081 A B u x s)). Qed.
Lemma lem4857083 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857084 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term586 A B u s) = (term936 A B u s).
Proof. exact (MK_COMB (@lem4857083 A) (@lem4857082 A B u s)). Qed.
Lemma lem4857085 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term936 A B u s.
Proof. exact (EQ_MP (@lem4857084 A B u s) (@lem4856808 A B u s h1)). Qed.
Lemma lem4857086 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : term908 A s B c.
Proof. exact (h1). Qed.
Lemma lem4857087 {A : Type'} (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term907 A t B x' s x) : term907 A t B x' s x.
Proof. exact (h1). Qed.
Lemma lem4857089 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : term901 A B c s.
Proof. exact (proj1 (@lem4857086 A s B c h1)). Qed.
Lemma lem4857092 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term905 A B t s x.
Proof. exact (h1). Qed.
Lemma lem4857093 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term897 A B x' s x.
Proof. exact (h1). Qed.
Lemma lem4857095 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term903 A B s t x.
Proof. exact (proj1 (@lem4857092 A B t s x h1)). Qed.
Lemma lem4857097 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term901 A B t s.
Proof. exact (proj1 (@lem4857095 A B t s x h1)). Qed.
Lemma lem4857098 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term900 A t s.
Proof. exact (proj2 (@lem4857097 A B t s x h1)). Qed.
Lemma lem4857101 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term895 A B s x' x.
Proof. exact (proj1 (@lem4857093 A B x' s x h1)). Qed.
Lemma lem4857362 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term898 A t s x) = (term898 A t s x).
Proof. exact (eq_refl (term898 A t s x)). Qed.
Lemma lem4857363 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term899 A t s) = (term899 A t s).
Proof. exact (fun_ext (fun x : A => @lem4857362 A t s x)). Qed.
Lemma lem4857364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857366 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term900 A t s) = (term900 A t s).
Proof. exact (MK_COMB (@lem4857364 A) (@lem4857363 A t s)). Qed.
Lemma lem4857367 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term900 A t s.
Proof. exact (EQ_MP (@lem4857366 A t s) (@lem4857098 A B t s x h1)). Qed.
Lemma lem4857369 {A : Type'} (P : Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4857370 {A : Type'} (P : Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (@lem4857369 A P Q). Qed.
Lemma lem4857371 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term937 A u x s) = (term938 A u x s).
Proof. exact (@lem4857370 A (term922 A u x) (term919 A u x s)). Qed.
Lemma lem4857372 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term939 A u x s x') = (term917 A u x s x').
Proof. exact (eq_refl (term939 A u x s x')). Qed.
Lemma lem4857373 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term940 A u x s) = (term919 A u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857372 A u x s x')). Qed.
Lemma lem4857374 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857375 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term941 A u x s) = (term921 A u x s).
Proof. exact (MK_COMB (@lem4857374 A) (@lem4857373 A u x s)). Qed.
Lemma lem4857376 {A : Type'} (u : type1402 A) (x : A) : (term924 A u x) = (term924 A u x).
Proof. exact (eq_refl (term924 A u x)). Qed.
Lemma lem4857377 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term937 A u x s) = (term926 A u x s).
Proof. exact (MK_COMB (@lem4857376 A u x) (@lem4857375 A u x s)). Qed.
Lemma lem4857378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4857379 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term942 A u x s) = (term943 A u x s).
Proof. exact (MK_COMB (@lem4857378) (@lem4857377 A u x s)). Qed.
Lemma lem4857380 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term939 A u x s x') = (term917 A u x s x').
Proof. exact (eq_refl (term939 A u x s x')). Qed.
Lemma lem4857381 {A : Type'} (u : type1402 A) (x : A) : (term924 A u x) = (term924 A u x).
Proof. exact (eq_refl (term924 A u x)). Qed.
Lemma lem4857382 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term944 A u x s x') = (term945 A u x s x').
Proof. exact (MK_COMB (@lem4857381 A u x) (@lem4857380 A u x s x')). Qed.
Lemma lem4857383 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term946 A u x s) = (term947 A u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857382 A u x s x')). Qed.
Lemma lem4857384 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857385 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term938 A u x s) = (term948 A u x s).
Proof. exact (MK_COMB (@lem4857384 A) (@lem4857383 A u x s)). Qed.
Lemma lem4857386 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : ((term937 A u x s) = (term938 A u x s)) = ((term926 A u x s) = (term948 A u x s)).
Proof. exact (MK_COMB (@lem4857379 A u x s) (@lem4857385 A u x s)). Qed.
Lemma lem4857387 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term926 A u x s) = (term948 A u x s).
Proof. exact (EQ_MP (@lem4857386 A u x s) (@lem4857371 A u x s)). Qed.
Lemma lem4857388 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term931 A B u x) = (term931 A B u x).
Proof. exact (eq_refl (term931 A B u x)). Qed.
Lemma lem4857389 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term933 A B u x s) = (term949 A B u x s).
Proof. exact (MK_COMB (@lem4857388 A B u x) (@lem4857387 A u x s)). Qed.
Lemma lem4857391 {A : Type'} (P : Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem4857392 {A : Type'} (P : Prop) (Q : A -> Prop) : (term286 A P Q) = (term287 A P Q).
Proof. exact (@lem4857391 A P Q). Qed.
Lemma lem4857393 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term950 A B u x s) = (term951 A B u x s).
Proof. exact (@lem4857392 A (term929 A B u x) (term947 A u x s)). Qed.
Lemma lem4857394 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term952 A u x s x') = (term945 A u x s x').
Proof. exact (eq_refl (term952 A u x s x')). Qed.
Lemma lem4857395 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term953 A u x s) = (term947 A u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857394 A u x s x')). Qed.
Lemma lem4857396 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857397 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) : (term954 A u x s) = (term948 A u x s).
Proof. exact (MK_COMB (@lem4857396 A) (@lem4857395 A u x s)). Qed.
Lemma lem4857398 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term931 A B u x) = (term931 A B u x).
Proof. exact (eq_refl (term931 A B u x)). Qed.
Lemma lem4857399 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term950 A B u x s) = (term949 A B u x s).
Proof. exact (MK_COMB (@lem4857398 A B u x) (@lem4857397 A u x s)). Qed.
Lemma lem4857400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4857401 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term955 A B u x s) = (term956 A B u x s).
Proof. exact (MK_COMB (@lem4857400) (@lem4857399 A B u x s)). Qed.
Lemma lem4857402 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term952 A u x s x') = (term945 A u x s x').
Proof. exact (eq_refl (term952 A u x s x')). Qed.
Lemma lem4857403 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term931 A B u x) = (term931 A B u x).
Proof. exact (eq_refl (term931 A B u x)). Qed.
Lemma lem4857404 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term957 A B u x s x') = (term958 A B u x s x').
Proof. exact (MK_COMB (@lem4857403 A B u x) (@lem4857402 A u x s x')). Qed.
Lemma lem4857405 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term959 A B u x s) = (term960 A B u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857404 A B u x s x')). Qed.
Lemma lem4857406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857407 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term951 A B u x s) = (term961 A B u x s).
Proof. exact (MK_COMB (@lem4857406 A) (@lem4857405 A B u x s)). Qed.
Lemma lem4857408 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : ((term950 A B u x s) = (term951 A B u x s)) = ((term949 A B u x s) = (term961 A B u x s)).
Proof. exact (MK_COMB (@lem4857401 A B u x s) (@lem4857407 A B u x s)). Qed.
Lemma lem4857409 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term949 A B u x s) = (term961 A B u x s).
Proof. exact (EQ_MP (@lem4857408 A B u x s) (@lem4857393 A B u x s)). Qed.
Lemma lem4857410 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term933 A B u x s) = (term961 A B u x s).
Proof. exact (TRANS (@lem4857389 A B u x s) (@lem4857409 A B u x s)). Qed.
Lemma lem4857411 {A : Type'} (s : A -> Prop) (x : A) : (term278 A s x) = (term278 A s x).
Proof. exact (eq_refl (term278 A s x)). Qed.
Lemma lem4857412 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term934 A B u x s) = (term962 A B u x s).
Proof. exact (MK_COMB (@lem4857411 A s x) (@lem4857410 A B u x s)). Qed.
Lemma lem4857414 {A : Type'} (P : Prop) (Q : A -> Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem4857415 {A : Type'} (P : Prop) (Q : A -> Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (@lem4857414 A P Q). Qed.
Lemma lem4857416 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term963 A B u x s) = (term964 A B u x s).
Proof. exact (@lem4857415 A (term277 A s x) (term960 A B u x s)). Qed.
Lemma lem4857417 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term965 A B u x s x') = (term958 A B u x s x').
Proof. exact (eq_refl (term965 A B u x s x')). Qed.
Lemma lem4857418 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term966 A B u x s) = (term960 A B u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857417 A B u x s x')). Qed.
Lemma lem4857419 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857420 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term967 A B u x s) = (term961 A B u x s).
Proof. exact (MK_COMB (@lem4857419 A) (@lem4857418 A B u x s)). Qed.
Lemma lem4857421 {A : Type'} (s : A -> Prop) (x : A) : (term278 A s x) = (term278 A s x).
Proof. exact (eq_refl (term278 A s x)). Qed.
Lemma lem4857422 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term963 A B u x s) = (term962 A B u x s).
Proof. exact (MK_COMB (@lem4857421 A s x) (@lem4857420 A B u x s)). Qed.
Lemma lem4857423 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4857424 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term968 A B u x s) = (term969 A B u x s).
Proof. exact (MK_COMB (@lem4857423) (@lem4857422 A B u x s)). Qed.
Lemma lem4857425 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term965 A B u x s x') = (term958 A B u x s x').
Proof. exact (eq_refl (term965 A B u x s x')). Qed.
Lemma lem4857426 {A : Type'} (s : A -> Prop) (x : A) : (term278 A s x) = (term278 A s x).
Proof. exact (eq_refl (term278 A s x)). Qed.
Lemma lem4857427 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term970 A B u x s x') = (term971 A B u x s x').
Proof. exact (MK_COMB (@lem4857426 A s x) (@lem4857425 A B u x s x')). Qed.
Lemma lem4857428 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term972 A B u x s) = (term973 A B u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857427 A B u x s x')). Qed.
Lemma lem4857429 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857430 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term964 A B u x s) = (term974 A B u x s).
Proof. exact (MK_COMB (@lem4857429 A) (@lem4857428 A B u x s)). Qed.
Lemma lem4857431 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : ((term963 A B u x s) = (term964 A B u x s)) = ((term962 A B u x s) = (term974 A B u x s)).
Proof. exact (MK_COMB (@lem4857424 A B u x s) (@lem4857430 A B u x s)). Qed.
Lemma lem4857432 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term962 A B u x s) = (term974 A B u x s).
Proof. exact (EQ_MP (@lem4857431 A B u x s) (@lem4857416 A B u x s)). Qed.
Lemma lem4857433 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term934 A B u x s) = (term974 A B u x s).
Proof. exact (TRANS (@lem4857412 A B u x s) (@lem4857432 A B u x s)). Qed.
Lemma lem4857434 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term935 A B u s) = (term975 A B u s).
Proof. exact (fun_ext (fun x : A => @lem4857433 A B u x s)). Qed.
Lemma lem4857435 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857436 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term936 A B u s) = (term976 A B u s).
Proof. exact (MK_COMB (@lem4857435 A) (@lem4857434 A B u s)). Qed.
Lemma lem4857456 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term971 A B u x s x') = (term977 A B u x s x').
Proof. exact (@lem19490 (term929 A B u x) (term277 A s x) (term945 A u x s x')). Qed.
Lemma lem4857463 {A : Type'} (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term978 A u x s x') = (term979 A u x s x').
Proof. exact (@lem19490 (term922 A u x) (term277 A s x) (term917 A u x s x')). Qed.
Lemma lem4857466 {A : Type'} (s : A -> Prop) (B : type686 A) (u : type1402 A) (x : A) : (term980 A s B u x) = (term980 A s B u x).
Proof. exact (eq_refl (term980 A s B u x)). Qed.
Lemma lem4857467 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term977 A B u x s x') = (term981 A B u x s x').
Proof. exact (MK_COMB (@lem4857466 A s B u x) (@lem4857463 A u x s x')). Qed.
Lemma lem4857469 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) (x' : A) : (term971 A B u x s x') = (term981 A B u x s x').
Proof. exact (TRANS (@lem4857456 A B u x s x') (@lem4857467 A B u x s x')). Qed.
Lemma lem4857470 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term973 A B u x s) = (term982 A B u x s).
Proof. exact (fun_ext (fun x' : A => @lem4857469 A B u x s x')). Qed.
Lemma lem4857471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857472 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) (s : A -> Prop) : (term974 A B u x s) = (term983 A B u x s).
Proof. exact (MK_COMB (@lem4857471 A) (@lem4857470 A B u x s)). Qed.
Lemma lem4857473 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term975 A B u s) = (term984 A B u s).
Proof. exact (fun_ext (fun x : A => @lem4857472 A B u x s)). Qed.
Lemma lem4857474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4857475 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term976 A B u s) = (term985 A B u s).
Proof. exact (MK_COMB (@lem4857474 A) (@lem4857473 A B u s)). Qed.
Lemma lem4857476 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) : (term936 A B u s) = (term985 A B u s).
Proof. exact (TRANS (@lem4857436 A B u s) (@lem4857475 A B u s)). Qed.
Lemma lem4857477 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term985 A B u s.
Proof. exact (EQ_MP (@lem4857476 A B u s) (@lem4857085 A B u s h1)). Qed.
Lemma lem4857479 {A : Type'} (t : A -> Prop) (x : A) : (term277 A t x) = (term277 A t x).
Proof. exact (eq_refl (term277 A t x)). Qed.
Lemma lem4857496 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term890 A B s x' t) = (term986 A B s x' t).
Proof. exact (@lem19490 (term272 A x' t) (term254 A B t) (term263 A s x' t)). Qed.
Lemma lem4857497 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4857498 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) : (term892 A B s x' t) = (term987 A B s x' t).
Proof. exact (MK_COMB (@lem4857497) (@lem4857496 A B s x' t)). Qed.
Lemma lem4857499 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term893 A B s x' t x) = (term988 A B s x' t x).
Proof. exact (MK_COMB (@lem4857498 A B s x' t) (@lem4857479 A t x)). Qed.
Lemma lem4857506 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term988 A B s x' t x) = (term989 A B s x' t x).
Proof. exact (@lem19699 (term362 A B x' t) (term990 A B s x' t) (term277 A t x)). Qed.
Lemma lem4857507 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (t : A -> Prop) (x : A) : (term893 A B s x' t x) = (term989 A B s x' t x).
Proof. exact (TRANS (@lem4857499 A B s x' t x) (@lem4857506 A B s x' t x)). Qed.
Lemma lem4857508 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term894 A B s x' x) = (term991 A B s x' x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem4857507 A B s x' t x)). Qed.
Lemma lem4857509 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4857511 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (x : A) : (term895 A B s x' x) = (term992 A B s x' x).
Proof. exact (MK_COMB (@lem4857509 A) (@lem4857508 A B s x' x)). Qed.
Lemma lem4857512 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term992 A B s x' x.
Proof. exact (EQ_MP (@lem4857511 A B s x' x) (@lem4857101 A B x' s x h1)). Qed.
Lemma lem4857532 {A : Type'} (_60197 : A) (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term993 A t s _60197.
Proof. exact (@lem4857367 A B t s x h1 _60197). Qed.
Lemma lem4857533 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_60197 : A) : (term993 A t s _60197) = (term898 A t s _60197).
Proof. exact (eq_refl (term993 A t s _60197)). Qed.
Lemma lem4857535 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term994 A B u s _60198.
Proof. exact (@lem4857477 A B u s h1 _60198). Qed.
Lemma lem4857536 {A : Type'} (B : type686 A) (u : type1402 A) (_60198 : A) (s : A -> Prop) : (term994 A B u s _60198) = (term983 A B u _60198 s).
Proof. exact (eq_refl (term994 A B u s _60198)). Qed.
Lemma lem4857537 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term983 A B u _60198 s.
Proof. exact (EQ_MP (@lem4857536 A B u _60198 s) (@lem4857535 A _60198 B u s h1)). Qed.
Lemma lem4857538 {A : Type'} (_60198 : A) (_60199 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term995 A B u _60198 s _60199.
Proof. exact (@lem4857537 A _60198 B u s h1 _60199). Qed.
Lemma lem4857539 {A : Type'} (B : type686 A) (u : type1402 A) (_60198 : A) (s : A -> Prop) (_60199 : A) : (term995 A B u _60198 s _60199) = (term981 A B u _60198 s _60199).
Proof. exact (eq_refl (term995 A B u _60198 s _60199)). Qed.
Lemma lem4857540 {A : Type'} (_60198 : A) (_60199 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term981 A B u _60198 s _60199.
Proof. exact (EQ_MP (@lem4857539 A B u _60198 s _60199) (@lem4857538 A _60198 _60199 B u s h1)). Qed.
Lemma lem4857541 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term996 A B s x' x _60200.
Proof. exact (@lem4857512 A B x' s x h1 _60200). Qed.
Lemma lem4857542 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term996 A B s x' x _60200) = (term989 A B s x' _60200 x).
Proof. exact (eq_refl (term996 A B s x' x _60200)). Qed.
Lemma lem4857543 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term989 A B s x' _60200 x.
Proof. exact (EQ_MP (@lem4857542 A B s x' _60200 x) (@lem4857541 A _60200 B x' s x h1)). Qed.
Lemma lem4857552 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term997 A B s x' _60200 x.
Proof. exact (proj2 (@lem4857543 A _60200 B x' s x h1)). Qed.
Lemma lem4857553 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term998 A B x' _60200 x.
Proof. exact (proj1 (@lem4857543 A _60200 B x' s x h1)). Qed.
Lemma lem4857554 {A : Type'} (_60198 : A) (_60199 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term979 A u _60198 s _60199.
Proof. exact (proj2 (@lem4857540 A _60198 _60199 B u s h1)). Qed.
Lemma lem4857559 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : term254 A B c.
Proof. exact (proj2 (@lem4857086 A s B c h1)). Qed.
Lemma lem4857591 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term277 A s x.
Proof. exact (proj2 (@lem4857092 A B t s x h1)). Qed.
Lemma lem4857601 {A : Type'} (_60197 : A) (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term898 A t s _60197.
Proof. exact (EQ_MP (@lem4857533 A t s _60197) (@lem4857532 A _60197 B t s x h1)). Qed.
Lemma lem4857636 {A : Type'} (B : type686 A) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term998 A B x' _60200 x) = (term999 A B x' _60200 x).
Proof. exact (@lem4854986 (term254 A B _60200) (term272 A x' _60200) (term277 A _60200 x)). Qed.
Lemma lem4857637 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term999 A B x' _60200 x.
Proof. exact (EQ_MP (@lem4857636 A B x' _60200 x) (@lem4857553 A _60200 B x' s x h1)). Qed.
Lemma lem4857648 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term997 A B s x' _60200 x) = (term1000 A B s x' _60200 x).
Proof. exact (@lem4854986 (term254 A B _60200) (term263 A s x' _60200) (term277 A _60200 x)). Qed.
Lemma lem4857649 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term1000 A B s x' _60200 x.
Proof. exact (EQ_MP (@lem4857648 A B s x' _60200 x) (@lem4857552 A _60200 B x' s x h1)). Qed.
Lemma lem4857655 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1001 A s B u _60198.
Proof. exact (proj1 (@lem4857540 A _60198 (@el A) B u s h1)). Qed.
Lemma lem4857661 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1002 A s u _60198.
Proof. exact (proj1 (@lem4857554 A _60198 (@el A) B u s h1)). Qed.
Lemma lem4857671 {A : Type'} (_60198 : A) (_60199 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1003 A u _60198 s _60199.
Proof. exact (proj2 (@lem4857554 A _60198 _60199 B u s h1)). Qed.
Lemma lem4857673 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : @I ((A -> Prop) -> Prop) B c.
Proof. exact (proj1 (@lem4857089 A s B c h1)). Qed.
Lemma lem4857674 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : term348 A B c.
Proof. exact (fun h0 : term254 A B c => @lem4857673 A s B c h1). Qed.
Lemma lem4857676 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857677 {A : Type'} (B : type686 A) (c : A -> Prop) : (term348 A B c) = (@I ((A -> Prop) -> Prop) B c).
Proof. exact (@lem4857676 (@I ((A -> Prop) -> Prop) B c)). Qed.
Lemma lem4857678 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : @I ((A -> Prop) -> Prop) B c.
Proof. exact (EQ_MP (@lem4857677 A B c) (@lem4857674 A s B c h1)). Qed.
Lemma lem4857681 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4857683 {A : Type'} (B : type686 A) (c : A -> Prop) : (term254 A B c) = (term1004 A B c).
Proof. exact (@lem4857681 (@I ((A -> Prop) -> Prop) B c)). Qed.
Lemma lem4857686 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : term1004 A B c.
Proof. exact (EQ_MP (@lem4857683 A B c) (@lem4857559 A s B c h1)). Qed.
Lemma lem4857689 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : False.
Proof. exact (@lem4857686 A s B c h1 (@lem4857678 A s B c h1)). Qed.
Lemma lem4857690 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : term399.
Proof. exact (fun h0 : ~ False => @lem4857689 A s B c h1). Qed.
Lemma lem4857692 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857693 : term399 = False.
Proof. exact (@lem4857692 False). Qed.
Lemma lem4857694 {A : Type'} (s : A -> Prop) (B : type686 A) (c : A -> Prop) (h1 : term908 A s B c) : False.
Proof. exact (EQ_MP (@lem4857693) (@lem4857690 A s B c h1)). Qed.
Lemma lem4857696 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : @I (A -> Prop) t x.
Proof. exact (proj2 (@lem4857095 A B t s x h1)). Qed.
Lemma lem4857697 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term359 A t x.
Proof. exact (fun h0 : term277 A t x => @lem4857696 A B t s x h1). Qed.
Lemma lem4857699 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857700 {A : Type'} (t : A -> Prop) (x : A) : (term359 A t x) = (@I (A -> Prop) t x).
Proof. exact (@lem4857699 (@I (A -> Prop) t x)). Qed.
Lemma lem4857701 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : @I (A -> Prop) t x.
Proof. exact (EQ_MP (@lem4857700 A t x) (@lem4857697 A B t s x h1)). Qed.
Lemma lem4857707 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4857708 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : (term898 A t s _60197) = (term1005 A s t _60197).
Proof. exact (@lem4857707 (@I (A -> Prop) s _60197) (term277 A t _60197)). Qed.
Lemma lem4857714 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4857715 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : (term1006 A t s _60197) = (term1007 A s t _60197).
Proof. exact (MK_COMB (@lem4857714) (@lem4857708 A s t _60197)). Qed.
Lemma lem4857721 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : (term1005 A s t _60197) = (term1005 A s t _60197).
Proof. exact (eq_refl (term1005 A s t _60197)). Qed.
Lemma lem4857722 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : ((term898 A t s _60197) = (term1005 A s t _60197)) = ((term1005 A s t _60197) = (term1005 A s t _60197)).
Proof. exact (MK_COMB (@lem4857715 A s t _60197) (@lem4857721 A s t _60197)). Qed.
Lemma lem4857724 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4857725 (x : Prop) : (x = x) = True.
Proof. exact (@lem4857724 Prop x). Qed.
Lemma lem4857726 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : ((term1005 A s t _60197) = (term1005 A s t _60197)) = True.
Proof. exact (@lem4857725 (term1005 A s t _60197)). Qed.
Lemma lem4857727 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : ((term898 A t s _60197) = (term1005 A s t _60197)) = True.
Proof. exact (TRANS (@lem4857722 A s t _60197) (@lem4857726 A s t _60197)). Qed.
Lemma lem4857728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : True = ((term898 A t s _60197) = (term1005 A s t _60197)).
Proof. exact (SYM (@lem4857727 A s t _60197)). Qed.
Lemma lem4857729 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_60197 : A) : (term898 A t s _60197) = (term1005 A s t _60197).
Proof. exact (EQ_MP (@lem4857728 A s t _60197) (@lem0)). Qed.
Lemma lem4857730 {A : Type'} (_60197 : A) (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term1005 A s t _60197.
Proof. exact (EQ_MP (@lem4857729 A s t _60197) (@lem4857601 A _60197 B t s x h1)). Qed.
Lemma lem4857732 (b : Prop) (a : Prop) : (a \/ b) = (term353 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4857733 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_60197 : A) : (term1005 A s t _60197) = (term1008 A t s _60197).
Proof. exact (@lem4857732 (term277 A t _60197) (@I (A -> Prop) s _60197)). Qed.
Lemma lem4857735 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4857736 {A : Type'} (t : A -> Prop) (_60197 : A) : (term378 A t _60197) = (@I (A -> Prop) t _60197).
Proof. exact (@lem4857735 (@I (A -> Prop) t _60197)). Qed.
Lemma lem4857737 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4857738 {A : Type'} (t : A -> Prop) (_60197 : A) : (term1009 A t _60197) = (term1010 A t _60197).
Proof. exact (MK_COMB (@lem4857737) (@lem4857736 A t _60197)). Qed.
Lemma lem4857739 {A : Type'} (s : A -> Prop) (_60197 : A) : (@I (A -> Prop) s _60197) = (@I (A -> Prop) s _60197).
Proof. exact (eq_refl (@I (A -> Prop) s _60197)). Qed.
Lemma lem4857740 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_60197 : A) : (term1008 A t s _60197) = (term1011 A t s _60197).
Proof. exact (MK_COMB (@lem4857738 A t _60197) (@lem4857739 A s _60197)). Qed.
Lemma lem4857741 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_60197 : A) : (term1005 A s t _60197) = (term1011 A t s _60197).
Proof. exact (TRANS (@lem4857733 A t s _60197) (@lem4857740 A t s _60197)). Qed.
Lemma lem4857744 {A : Type'} (_60197 : A) (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term1011 A t s _60197.
Proof. exact (EQ_MP (@lem4857741 A t s _60197) (@lem4857730 A _60197 B t s x h1)). Qed.
Lemma lem4857745 {A : Type'} (_60197 : A) (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term1011 A t s _60197.
Proof. exact (@lem4857744 A _60197 B t s x h1). Qed.
Lemma lem4857746 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term1011 A t s x.
Proof. exact (@lem4857745 A x B t s x h1). Qed.
Lemma lem4857749 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : @I (A -> Prop) s x.
Proof. exact (@lem4857746 A B t s x h1 (@lem4857701 A B t s x h1)). Qed.
Lemma lem4857750 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term359 A s x.
Proof. exact (fun h0 : term277 A s x => @lem4857749 A B t s x h1). Qed.
Lemma lem4857752 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857753 {A : Type'} (s : A -> Prop) (x : A) : (term359 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4857752 (@I (A -> Prop) s x)). Qed.
Lemma lem4857754 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4857753 A s x) (@lem4857750 A B t s x h1)). Qed.
Lemma lem4857757 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4857759 {A : Type'} (s : A -> Prop) (x : A) : (term277 A s x) = (term1012 A s x).
Proof. exact (@lem4857757 (@I (A -> Prop) s x)). Qed.
Lemma lem4857762 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term1012 A s x.
Proof. exact (EQ_MP (@lem4857759 A s x) (@lem4857591 A B t s x h1)). Qed.
Lemma lem4857765 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : False.
Proof. exact (@lem4857762 A B t s x h1 (@lem4857754 A B t s x h1)). Qed.
Lemma lem4857766 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : term399.
Proof. exact (fun h0 : ~ False => @lem4857765 A B t s x h1). Qed.
Lemma lem4857768 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857769 : term399 = False.
Proof. exact (@lem4857768 False). Qed.
Lemma lem4857770 {A : Type'} (B : type686 A) (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term905 A B t s x) : False.
Proof. exact (EQ_MP (@lem4857769) (@lem4857766 A B t s x h1)). Qed.
Lemma lem4857772 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4857093 A B x' s x h1)). Qed.
Lemma lem4857773 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term359 A s x.
Proof. exact (fun h0 : term277 A s x => @lem4857772 A B x' s x h1). Qed.
Lemma lem4857775 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857776 {A : Type'} (s : A -> Prop) (x : A) : (term359 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4857775 (@I (A -> Prop) s x)). Qed.
Lemma lem4857777 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4857776 A s x) (@lem4857773 A B x' s x h1)). Qed.
Lemma lem4857783 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4857784 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1001 A s B u _60198) = (term1013 A B u s _60198).
Proof. exact (@lem4857783 (term929 A B u _60198) (term277 A s _60198)). Qed.
Lemma lem4857790 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4857791 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1014 A s B u _60198) = (term1015 A B u s _60198).
Proof. exact (MK_COMB (@lem4857790) (@lem4857784 A B u s _60198)). Qed.
Lemma lem4857797 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1013 A B u s _60198) = (term1013 A B u s _60198).
Proof. exact (eq_refl (term1013 A B u s _60198)). Qed.
Lemma lem4857798 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : ((term1001 A s B u _60198) = (term1013 A B u s _60198)) = ((term1013 A B u s _60198) = (term1013 A B u s _60198)).
Proof. exact (MK_COMB (@lem4857791 A B u s _60198) (@lem4857797 A B u s _60198)). Qed.
Lemma lem4857800 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4857801 (x : Prop) : (x = x) = True.
Proof. exact (@lem4857800 Prop x). Qed.
Lemma lem4857802 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : ((term1013 A B u s _60198) = (term1013 A B u s _60198)) = True.
Proof. exact (@lem4857801 (term1013 A B u s _60198)). Qed.
Lemma lem4857803 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : ((term1001 A s B u _60198) = (term1013 A B u s _60198)) = True.
Proof. exact (TRANS (@lem4857798 A B u s _60198) (@lem4857802 A B u s _60198)). Qed.
Lemma lem4857804 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : True = ((term1001 A s B u _60198) = (term1013 A B u s _60198)).
Proof. exact (SYM (@lem4857803 A B u s _60198)). Qed.
Lemma lem4857805 {A : Type'} (B : type686 A) (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1001 A s B u _60198) = (term1013 A B u s _60198).
Proof. exact (EQ_MP (@lem4857804 A B u s _60198) (@lem0)). Qed.
Lemma lem4857806 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1013 A B u s _60198.
Proof. exact (EQ_MP (@lem4857805 A B u s _60198) (@lem4857655 A _60198 B u s h1)). Qed.
Lemma lem4857808 (b : Prop) (a : Prop) : (a \/ b) = (term353 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4857809 {A : Type'} (s : A -> Prop) (B : type686 A) (u : type1402 A) (_60198 : A) : (term1013 A B u s _60198) = (term1016 A s B u _60198).
Proof. exact (@lem4857808 (term277 A s _60198) (term929 A B u _60198)). Qed.
Lemma lem4857811 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4857812 {A : Type'} (s : A -> Prop) (_60198 : A) : (term378 A s _60198) = (@I (A -> Prop) s _60198).
Proof. exact (@lem4857811 (@I (A -> Prop) s _60198)). Qed.
Lemma lem4857813 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4857814 {A : Type'} (s : A -> Prop) (_60198 : A) : (term1009 A s _60198) = (term1010 A s _60198).
Proof. exact (MK_COMB (@lem4857813) (@lem4857812 A s _60198)). Qed.
Lemma lem4857815 {A : Type'} (B : type686 A) (u : type1402 A) (_60198 : A) : (term929 A B u _60198) = (term929 A B u _60198).
Proof. exact (eq_refl (term929 A B u _60198)). Qed.
Lemma lem4857816 {A : Type'} (s : A -> Prop) (B : type686 A) (u : type1402 A) (_60198 : A) : (term1016 A s B u _60198) = (term1017 A s B u _60198).
Proof. exact (MK_COMB (@lem4857814 A s _60198) (@lem4857815 A B u _60198)). Qed.
Lemma lem4857817 {A : Type'} (s : A -> Prop) (B : type686 A) (u : type1402 A) (_60198 : A) : (term1013 A B u s _60198) = (term1017 A s B u _60198).
Proof. exact (TRANS (@lem4857809 A s B u _60198) (@lem4857816 A s B u _60198)). Qed.
Lemma lem4857820 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1017 A s B u _60198.
Proof. exact (EQ_MP (@lem4857817 A s B u _60198) (@lem4857806 A _60198 B u s h1)). Qed.
Lemma lem4857821 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1017 A s B u _60198.
Proof. exact (@lem4857820 A _60198 B u s h1). Qed.
Lemma lem4857822 {A : Type'} (x : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1017 A s B u x.
Proof. exact (@lem4857821 A x B u s h1). Qed.
Lemma lem4857825 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term929 A B u x.
Proof. exact (@lem4857822 A x B u s h1 (@lem4857777 A B x' s x h2)). Qed.
Lemma lem4857826 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1018 A B u x.
Proof. exact (fun h0 : term1019 A B u x => @lem4857825 A u B x' s x h1 h2). Qed.
Lemma lem4857828 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857829 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term1018 A B u x) = (term929 A B u x).
Proof. exact (@lem4857828 (term929 A B u x)). Qed.
Lemma lem4857830 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term929 A B u x.
Proof. exact (EQ_MP (@lem4857829 A B u x) (@lem4857826 A u B x' s x h1 h2)). Qed.
Lemma lem4857832 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4857093 A B x' s x h1)). Qed.
Lemma lem4857833 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term359 A s x.
Proof. exact (fun h0 : term277 A s x => @lem4857832 A B x' s x h1). Qed.
Lemma lem4857835 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857836 {A : Type'} (s : A -> Prop) (x : A) : (term359 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4857835 (@I (A -> Prop) s x)). Qed.
Lemma lem4857837 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4857836 A s x) (@lem4857833 A B x' s x h1)). Qed.
Lemma lem4857839 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4857093 A B x' s x h1)). Qed.
Lemma lem4857840 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term359 A s x.
Proof. exact (fun h0 : term277 A s x => @lem4857839 A B x' s x h1). Qed.
Lemma lem4857842 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857843 {A : Type'} (s : A -> Prop) (x : A) : (term359 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4857842 (@I (A -> Prop) s x)). Qed.
Lemma lem4857844 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4857843 A s x) (@lem4857840 A B x' s x h1)). Qed.
Lemma lem4857846 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1017 A s B u _60198.
Proof. exact (EQ_MP (@lem4857817 A s B u _60198) (@lem4857806 A _60198 B u s h1)). Qed.
Lemma lem4857847 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1017 A s B u _60198.
Proof. exact (@lem4857846 A _60198 B u s h1). Qed.
Lemma lem4857848 {A : Type'} (x : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1017 A s B u x.
Proof. exact (@lem4857847 A x B u s h1). Qed.
Lemma lem4857851 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term929 A B u x.
Proof. exact (@lem4857848 A x B u s h1 (@lem4857844 A B x' s x h2)). Qed.
Lemma lem4857852 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1018 A B u x.
Proof. exact (fun h0 : term1019 A B u x => @lem4857851 A u B x' s x h1 h2). Qed.
Lemma lem4857854 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857855 {A : Type'} (B : type686 A) (u : type1402 A) (x : A) : (term1018 A B u x) = (term929 A B u x).
Proof. exact (@lem4857854 (term929 A B u x)). Qed.
Lemma lem4857856 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term929 A B u x.
Proof. exact (EQ_MP (@lem4857855 A B u x) (@lem4857852 A u B x' s x h1 h2)). Qed.
Lemma lem4857858 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4857093 A B x' s x h1)). Qed.
Lemma lem4857859 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term359 A s x.
Proof. exact (fun h0 : term277 A s x => @lem4857858 A B x' s x h1). Qed.
Lemma lem4857861 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857862 {A : Type'} (s : A -> Prop) (x : A) : (term359 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4857861 (@I (A -> Prop) s x)). Qed.
Lemma lem4857863 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4857862 A s x) (@lem4857859 A B x' s x h1)). Qed.
Lemma lem4857869 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4857870 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1002 A s u _60198) = (term1020 A u s _60198).
Proof. exact (@lem4857869 (term922 A u _60198) (term277 A s _60198)). Qed.
Lemma lem4857876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4857877 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1021 A s u _60198) = (term1022 A u s _60198).
Proof. exact (MK_COMB (@lem4857876) (@lem4857870 A u s _60198)). Qed.
Lemma lem4857883 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1020 A u s _60198) = (term1020 A u s _60198).
Proof. exact (eq_refl (term1020 A u s _60198)). Qed.
Lemma lem4857884 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : ((term1002 A s u _60198) = (term1020 A u s _60198)) = ((term1020 A u s _60198) = (term1020 A u s _60198)).
Proof. exact (MK_COMB (@lem4857877 A u s _60198) (@lem4857883 A u s _60198)). Qed.
Lemma lem4857886 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4857887 (x : Prop) : (x = x) = True.
Proof. exact (@lem4857886 Prop x). Qed.
Lemma lem4857888 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : ((term1020 A u s _60198) = (term1020 A u s _60198)) = True.
Proof. exact (@lem4857887 (term1020 A u s _60198)). Qed.
Lemma lem4857889 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : ((term1002 A s u _60198) = (term1020 A u s _60198)) = True.
Proof. exact (TRANS (@lem4857884 A u s _60198) (@lem4857888 A u s _60198)). Qed.
Lemma lem4857890 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : True = ((term1002 A s u _60198) = (term1020 A u s _60198)).
Proof. exact (SYM (@lem4857889 A u s _60198)). Qed.
Lemma lem4857891 {A : Type'} (u : type1402 A) (s : A -> Prop) (_60198 : A) : (term1002 A s u _60198) = (term1020 A u s _60198).
Proof. exact (EQ_MP (@lem4857890 A u s _60198) (@lem0)). Qed.
Lemma lem4857892 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1020 A u s _60198.
Proof. exact (EQ_MP (@lem4857891 A u s _60198) (@lem4857661 A _60198 B u s h1)). Qed.
Lemma lem4857894 (b : Prop) (a : Prop) : (a \/ b) = (term353 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4857895 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) : (term1020 A u s _60198) = (term1023 A s u _60198).
Proof. exact (@lem4857894 (term277 A s _60198) (term922 A u _60198)). Qed.
Lemma lem4857897 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4857898 {A : Type'} (s : A -> Prop) (_60198 : A) : (term378 A s _60198) = (@I (A -> Prop) s _60198).
Proof. exact (@lem4857897 (@I (A -> Prop) s _60198)). Qed.
Lemma lem4857899 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4857900 {A : Type'} (s : A -> Prop) (_60198 : A) : (term1009 A s _60198) = (term1010 A s _60198).
Proof. exact (MK_COMB (@lem4857899) (@lem4857898 A s _60198)). Qed.
Lemma lem4857901 {A : Type'} (u : type1402 A) (_60198 : A) : (term922 A u _60198) = (term922 A u _60198).
Proof. exact (eq_refl (term922 A u _60198)). Qed.
Lemma lem4857902 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) : (term1023 A s u _60198) = (term1024 A s u _60198).
Proof. exact (MK_COMB (@lem4857900 A s _60198) (@lem4857901 A u _60198)). Qed.
Lemma lem4857903 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) : (term1020 A u s _60198) = (term1024 A s u _60198).
Proof. exact (TRANS (@lem4857895 A s u _60198) (@lem4857902 A s u _60198)). Qed.
Lemma lem4857906 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1024 A s u _60198.
Proof. exact (EQ_MP (@lem4857903 A s u _60198) (@lem4857892 A _60198 B u s h1)). Qed.
Lemma lem4857907 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1024 A s u _60198.
Proof. exact (@lem4857906 A _60198 B u s h1). Qed.
Lemma lem4857908 {A : Type'} (x : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1024 A s u x.
Proof. exact (@lem4857907 A x B u s h1). Qed.
Lemma lem4857911 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term922 A u x.
Proof. exact (@lem4857908 A x B u s h1 (@lem4857863 A B x' s x h2)). Qed.
Lemma lem4857912 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1025 A u x.
Proof. exact (fun h0 : term1026 A u x => @lem4857911 A u B x' s x h1 h2). Qed.
Lemma lem4857914 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4857915 {A : Type'} (u : type1402 A) (x : A) : (term1025 A u x) = (term922 A u x).
Proof. exact (@lem4857914 (term922 A u x)). Qed.
Lemma lem4857916 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term922 A u x.
Proof. exact (EQ_MP (@lem4857915 A u x) (@lem4857912 A u B x' s x h1 h2)). Qed.
Lemma lem4857922 (q : Prop) (p : Prop) (r : Prop) : (term360 p q r) = (term360 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4857923 {A : Type'} (x' : type684 A) (B : type686 A) (_60200 : A -> Prop) (x : A) : (term999 A B x' _60200 x) = (term371 A x' B _60200 x).
Proof. exact (@lem4857922 (term272 A x' _60200) (term254 A B _60200) (term277 A _60200 x)). Qed.
Lemma lem4857937 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4857938 {A : Type'} (x : A) (B : type686 A) (_60200 : A -> Prop) : (term368 A B _60200 x) = (term369 A x B _60200).
Proof. exact (@lem4857937 (term277 A _60200 x) (term254 A B _60200)). Qed.
Lemma lem4857944 {A : Type'} (x' : type684 A) (_60200 : A -> Prop) : (term370 A x' _60200) = (term370 A x' _60200).
Proof. exact (eq_refl (term370 A x' _60200)). Qed.
Lemma lem4857945 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60200 : A -> Prop) : (term371 A x' B _60200 x) = (term365 A x' x B _60200).
Proof. exact (MK_COMB (@lem4857944 A x' _60200) (@lem4857938 A x B _60200)). Qed.
Lemma lem4857956 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60200 : A -> Prop) : (term999 A B x' _60200 x) = (term365 A x' x B _60200).
Proof. exact (TRANS (@lem4857923 A x' B _60200 x) (@lem4857945 A x' x B _60200)). Qed.
Lemma lem4857957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4857958 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60200 : A -> Prop) : (term1027 A B x' _60200 x) = (term367 A x' x B _60200).
Proof. exact (MK_COMB (@lem4857957) (@lem4857956 A x' x B _60200)). Qed.
Lemma lem4857972 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4857973 {A : Type'} (x : A) (B : type686 A) (_60200 : A -> Prop) : (term368 A B _60200 x) = (term369 A x B _60200).
Proof. exact (@lem4857972 (term277 A _60200 x) (term254 A B _60200)). Qed.
Lemma lem4857979 {A : Type'} (x' : type684 A) (_60200 : A -> Prop) : (term370 A x' _60200) = (term370 A x' _60200).
Proof. exact (eq_refl (term370 A x' _60200)). Qed.
Lemma lem4857980 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60200 : A -> Prop) : (term371 A x' B _60200 x) = (term365 A x' x B _60200).
Proof. exact (MK_COMB (@lem4857979 A x' _60200) (@lem4857973 A x B _60200)). Qed.
Lemma lem4857991 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60200 : A -> Prop) : ((term999 A B x' _60200 x) = (term371 A x' B _60200 x)) = ((term365 A x' x B _60200) = (term365 A x' x B _60200)).
Proof. exact (MK_COMB (@lem4857958 A x' x B _60200) (@lem4857980 A x' x B _60200)). Qed.
Lemma lem4857993 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4857994 (x : Prop) : (x = x) = True.
Proof. exact (@lem4857993 Prop x). Qed.
Lemma lem4857995 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (_60200 : A -> Prop) : ((term365 A x' x B _60200) = (term365 A x' x B _60200)) = True.
Proof. exact (@lem4857994 (term365 A x' x B _60200)). Qed.
Lemma lem4857996 {A : Type'} (x' : type684 A) (B : type686 A) (_60200 : A -> Prop) (x : A) : ((term999 A B x' _60200 x) = (term371 A x' B _60200 x)) = True.
Proof. exact (TRANS (@lem4857991 A x' x B _60200) (@lem4857995 A x' x B _60200)). Qed.
Lemma lem4857997 {A : Type'} (x' : type684 A) (B : type686 A) (_60200 : A -> Prop) (x : A) : True = ((term999 A B x' _60200 x) = (term371 A x' B _60200 x)).
Proof. exact (SYM (@lem4857996 A x' B _60200 x)). Qed.
Lemma lem4857998 {A : Type'} (x' : type684 A) (B : type686 A) (_60200 : A -> Prop) (x : A) : (term999 A B x' _60200 x) = (term371 A x' B _60200 x).
Proof. exact (EQ_MP (@lem4857997 A x' B _60200 x) (@lem0)). Qed.
Lemma lem4857999 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term371 A x' B _60200 x.
Proof. exact (EQ_MP (@lem4857998 A x' B _60200 x) (@lem4857637 A _60200 B x' s x h1)). Qed.
Lemma lem4858001 (b : Prop) (a : Prop) : (a \/ b) = (term353 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4858002 {A : Type'} (B : type686 A) (x : A) (x' : type684 A) (_60200 : A -> Prop) : (term371 A x' B _60200 x) = (term372 A B x x' _60200).
Proof. exact (@lem4858001 (term368 A B _60200 x) (term272 A x' _60200)). Qed.
Lemma lem4858004 (a : Prop) (b : Prop) : (term373 a b) = (term374 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4858005 {A : Type'} (B : type686 A) (_60200 : A -> Prop) (x : A) : (term375 A B _60200 x) = (term376 A B _60200 x).
Proof. exact (@lem4858004 (term254 A B _60200) (term277 A _60200 x)). Qed.
Lemma lem4858007 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4858008 {A : Type'} (B : type686 A) (_60200 : A -> Prop) : (term355 A B _60200) = (@I ((A -> Prop) -> Prop) B _60200).
Proof. exact (@lem4858007 (@I ((A -> Prop) -> Prop) B _60200)). Qed.
Lemma lem4858009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4858010 {A : Type'} (B : type686 A) (_60200 : A -> Prop) : (term377 A B _60200) = (term284 A B _60200).
Proof. exact (MK_COMB (@lem4858009) (@lem4858008 A B _60200)). Qed.
Lemma lem4858012 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4858013 {A : Type'} (_60200 : A -> Prop) (x : A) : (term378 A _60200 x) = (@I (A -> Prop) _60200 x).
Proof. exact (@lem4858012 (@I (A -> Prop) _60200 x)). Qed.
Lemma lem4858014 {A : Type'} (B : type686 A) (_60200 : A -> Prop) (x : A) : (term376 A B _60200 x) = (term285 A B _60200 x).
Proof. exact (MK_COMB (@lem4858010 A B _60200) (@lem4858013 A _60200 x)). Qed.
Lemma lem4858015 {A : Type'} (B : type686 A) (_60200 : A -> Prop) (x : A) : (term375 A B _60200 x) = (term285 A B _60200 x).
Proof. exact (TRANS (@lem4858005 A B _60200 x) (@lem4858014 A B _60200 x)). Qed.
Lemma lem4858016 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4858017 {A : Type'} (B : type686 A) (_60200 : A -> Prop) (x : A) : (term379 A B _60200 x) = (term380 A B _60200 x).
Proof. exact (MK_COMB (@lem4858016) (@lem4858015 A B _60200 x)). Qed.
Lemma lem4858018 {A : Type'} (x' : type684 A) (_60200 : A -> Prop) : (term272 A x' _60200) = (term272 A x' _60200).
Proof. exact (eq_refl (term272 A x' _60200)). Qed.
Lemma lem4858019 {A : Type'} (B : type686 A) (x : A) (x' : type684 A) (_60200 : A -> Prop) : (term372 A B x x' _60200) = (term381 A B x x' _60200).
Proof. exact (MK_COMB (@lem4858017 A B _60200 x) (@lem4858018 A x' _60200)). Qed.
Lemma lem4858020 {A : Type'} (B : type686 A) (x : A) (x' : type684 A) (_60200 : A -> Prop) : (term371 A x' B _60200 x) = (term381 A B x x' _60200).
Proof. exact (TRANS (@lem4858002 A B x x' _60200) (@lem4858019 A B x x' _60200)). Qed.
Lemma lem4858022 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1028 A B u x.
Proof. exact (conj (@lem4857856 A u B x' s x h1 h2) (@lem4857916 A u B x' s x h1 h2)). Qed.
Lemma lem4858024 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term381 A B x x' _60200.
Proof. exact (EQ_MP (@lem4858020 A B x x' _60200) (@lem4857999 A _60200 B x' s x h1)). Qed.
Lemma lem4858025 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term381 A B x x' _60200.
Proof. exact (@lem4858024 A _60200 B x' s x h1). Qed.
Lemma lem4858026 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term1029 A B x' u x.
Proof. exact (@lem4858025 A (@I (A -> A -> Prop) u x) B x' s x h1). Qed.
Lemma lem4858029 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1030 A x' u x.
Proof. exact (@lem4858026 A u B x' s x h2 (@lem4858022 A u B x' s x h1 h2)). Qed.
Lemma lem4858030 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1031 A x' u x.
Proof. exact (fun h0 : term1032 A x' u x => @lem4858029 A u B x' s x h1 h2). Qed.
Lemma lem4858032 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4858033 {A : Type'} (x' : type684 A) (u : type1402 A) (x : A) : (term1031 A x' u x) = (term1030 A x' u x).
Proof. exact (@lem4858032 (term1030 A x' u x)). Qed.
Lemma lem4858034 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1030 A x' u x.
Proof. exact (EQ_MP (@lem4858033 A x' u x) (@lem4858030 A u B x' s x h1 h2)). Qed.
Lemma lem4858050 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4858051 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term917 A u _60198 s _60199) = (term1033 A s u _60198 _60199).
Proof. exact (@lem4858050 (@I (A -> Prop) s _60199) (term913 A u _60198 _60199)). Qed.
Lemma lem4858057 {A : Type'} (s : A -> Prop) (_60198 : A) : (term278 A s _60198) = (term278 A s _60198).
Proof. exact (eq_refl (term278 A s _60198)). Qed.
Lemma lem4858058 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1003 A u _60198 s _60199) = (term1034 A s u _60198 _60199).
Proof. exact (MK_COMB (@lem4858057 A s _60198) (@lem4858051 A s u _60198 _60199)). Qed.
Lemma lem4858062 (q : Prop) (p : Prop) (r : Prop) : (term360 p q r) = (term360 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4858063 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1034 A s u _60198 _60199) = (term1035 A s u _60198 _60199).
Proof. exact (@lem4858062 (@I (A -> Prop) s _60199) (term277 A s _60198) (term913 A u _60198 _60199)). Qed.
Lemma lem4858079 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1003 A u _60198 s _60199) = (term1035 A s u _60198 _60199).
Proof. exact (TRANS (@lem4858058 A s u _60198 _60199) (@lem4858063 A s u _60198 _60199)). Qed.
Lemma lem4858080 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4858081 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1036 A u _60198 s _60199) = (term1037 A s u _60198 _60199).
Proof. exact (MK_COMB (@lem4858080) (@lem4858079 A s u _60198 _60199)). Qed.
Lemma lem4858097 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1035 A s u _60198 _60199) = (term1035 A s u _60198 _60199).
Proof. exact (eq_refl (term1035 A s u _60198 _60199)). Qed.
Lemma lem4858098 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : ((term1003 A u _60198 s _60199) = (term1035 A s u _60198 _60199)) = ((term1035 A s u _60198 _60199) = (term1035 A s u _60198 _60199)).
Proof. exact (MK_COMB (@lem4858081 A s u _60198 _60199) (@lem4858097 A s u _60198 _60199)). Qed.
Lemma lem4858100 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4858101 (x : Prop) : (x = x) = True.
Proof. exact (@lem4858100 Prop x). Qed.
Lemma lem4858102 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : ((term1035 A s u _60198 _60199) = (term1035 A s u _60198 _60199)) = True.
Proof. exact (@lem4858101 (term1035 A s u _60198 _60199)). Qed.
Lemma lem4858103 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : ((term1003 A u _60198 s _60199) = (term1035 A s u _60198 _60199)) = True.
Proof. exact (TRANS (@lem4858098 A s u _60198 _60199) (@lem4858102 A s u _60198 _60199)). Qed.
Lemma lem4858104 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : True = ((term1003 A u _60198 s _60199) = (term1035 A s u _60198 _60199)).
Proof. exact (SYM (@lem4858103 A s u _60198 _60199)). Qed.
Lemma lem4858105 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1003 A u _60198 s _60199) = (term1035 A s u _60198 _60199).
Proof. exact (EQ_MP (@lem4858104 A s u _60198 _60199) (@lem0)). Qed.
Lemma lem4858106 {A : Type'} (_60198 : A) (_60199 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1035 A s u _60198 _60199.
Proof. exact (EQ_MP (@lem4858105 A s u _60198 _60199) (@lem4857671 A _60198 _60199 B u s h1)). Qed.
Lemma lem4858108 (b : Prop) (a : Prop) : (a \/ b) = (term353 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4858109 {A : Type'} (u : type1402 A) (_60198 : A) (s : A -> Prop) (_60199 : A) : (term1035 A s u _60198 _60199) = (term1038 A u _60198 s _60199).
Proof. exact (@lem4858108 (term1039 A s u _60198 _60199) (@I (A -> Prop) s _60199)). Qed.
Lemma lem4858111 (a : Prop) (b : Prop) : (term373 a b) = (term374 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4858112 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1040 A s u _60198 _60199) = (term1041 A s u _60198 _60199).
Proof. exact (@lem4858111 (term277 A s _60198) (term913 A u _60198 _60199)). Qed.
Lemma lem4858114 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4858115 {A : Type'} (s : A -> Prop) (_60198 : A) : (term378 A s _60198) = (@I (A -> Prop) s _60198).
Proof. exact (@lem4858114 (@I (A -> Prop) s _60198)). Qed.
Lemma lem4858116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4858117 {A : Type'} (s : A -> Prop) (_60198 : A) : (term1042 A s _60198) = (term1043 A s _60198).
Proof. exact (MK_COMB (@lem4858116) (@lem4858115 A s _60198)). Qed.
Lemma lem4858119 (a : Prop) : (term151 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4858120 {A : Type'} (u : type1402 A) (_60198 : A) (_60199 : A) : (term1044 A u _60198 _60199) = (term911 A u _60198 _60199).
Proof. exact (@lem4858119 (term911 A u _60198 _60199)). Qed.
Lemma lem4858121 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1041 A s u _60198 _60199) = (term1045 A s u _60198 _60199).
Proof. exact (MK_COMB (@lem4858117 A s _60198) (@lem4858120 A u _60198 _60199)). Qed.
Lemma lem4858122 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1040 A s u _60198 _60199) = (term1045 A s u _60198 _60199).
Proof. exact (TRANS (@lem4858112 A s u _60198 _60199) (@lem4858121 A s u _60198 _60199)). Qed.
Lemma lem4858123 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4858124 {A : Type'} (s : A -> Prop) (u : type1402 A) (_60198 : A) (_60199 : A) : (term1046 A s u _60198 _60199) = (term1047 A s u _60198 _60199).
Proof. exact (MK_COMB (@lem4858123) (@lem4858122 A s u _60198 _60199)). Qed.
Lemma lem4858125 {A : Type'} (s : A -> Prop) (_60199 : A) : (@I (A -> Prop) s _60199) = (@I (A -> Prop) s _60199).
Proof. exact (eq_refl (@I (A -> Prop) s _60199)). Qed.
Lemma lem4858126 {A : Type'} (u : type1402 A) (_60198 : A) (s : A -> Prop) (_60199 : A) : (term1038 A u _60198 s _60199) = (term1048 A u _60198 s _60199).
Proof. exact (MK_COMB (@lem4858124 A s u _60198 _60199) (@lem4858125 A s _60199)). Qed.
Lemma lem4858127 {A : Type'} (u : type1402 A) (_60198 : A) (s : A -> Prop) (_60199 : A) : (term1035 A s u _60198 _60199) = (term1048 A u _60198 s _60199).
Proof. exact (TRANS (@lem4858109 A u _60198 s _60199) (@lem4858126 A u _60198 s _60199)). Qed.
Lemma lem4858129 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1049 A s x' u x.
Proof. exact (conj (@lem4857837 A B x' s x h2) (@lem4858034 A u B x' s x h1 h2)). Qed.
Lemma lem4858131 {A : Type'} (_60198 : A) (_60199 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1048 A u _60198 s _60199.
Proof. exact (EQ_MP (@lem4858127 A u _60198 s _60199) (@lem4858106 A _60198 _60199 B u s h1)). Qed.
Lemma lem4858132 {A : Type'} (_60198 : A) (_60199 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1048 A u _60198 s _60199.
Proof. exact (@lem4858131 A _60198 _60199 B u s h1). Qed.
Lemma lem4858133 {A : Type'} (x' : type684 A) (x : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1050 A s x' u x.
Proof. exact (@lem4858132 A x (term1051 A x' u x) B u s h1). Qed.
Lemma lem4858136 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1052 A s x' u x.
Proof. exact (@lem4858133 A x' x B u s h1 (@lem4858129 A u B x' s x h1 h2)). Qed.
Lemma lem4858137 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1053 A s x' u x.
Proof. exact (fun h0 : term1054 A s x' u x => @lem4858136 A u B x' s x h1 h2). Qed.
Lemma lem4858139 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4858140 {A : Type'} (s : A -> Prop) (x' : type684 A) (u : type1402 A) (x : A) : (term1053 A s x' u x) = (term1052 A s x' u x).
Proof. exact (@lem4858139 (term1052 A s x' u x)). Qed.
Lemma lem4858141 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1052 A s x' u x.
Proof. exact (EQ_MP (@lem4858140 A s x' u x) (@lem4858137 A u B x' s x h1 h2)). Qed.
Lemma lem4858143 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (proj2 (@lem4857093 A B x' s x h1)). Qed.
Lemma lem4858144 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term359 A s x.
Proof. exact (fun h0 : term277 A s x => @lem4858143 A B x' s x h1). Qed.
Lemma lem4858146 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4858147 {A : Type'} (s : A -> Prop) (x : A) : (term359 A s x) = (@I (A -> Prop) s x).
Proof. exact (@lem4858146 (@I (A -> Prop) s x)). Qed.
Lemma lem4858148 {A : Type'} (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : @I (A -> Prop) s x.
Proof. exact (EQ_MP (@lem4858147 A s x) (@lem4858144 A B x' s x h1)). Qed.
Lemma lem4858150 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1024 A s u _60198.
Proof. exact (EQ_MP (@lem4857903 A s u _60198) (@lem4857892 A _60198 B u s h1)). Qed.
Lemma lem4858151 {A : Type'} (_60198 : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1024 A s u _60198.
Proof. exact (@lem4858150 A _60198 B u s h1). Qed.
Lemma lem4858152 {A : Type'} (x : A) (B : type686 A) (u : type1402 A) (s : A -> Prop) (h1 : term586 A B u s) : term1024 A s u x.
Proof. exact (@lem4858151 A x B u s h1). Qed.
Lemma lem4858155 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term922 A u x.
Proof. exact (@lem4858152 A x B u s h1 (@lem4858148 A B x' s x h2)). Qed.
Lemma lem4858156 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1025 A u x.
Proof. exact (fun h0 : term1026 A u x => @lem4858155 A u B x' s x h1 h2). Qed.
Lemma lem4858158 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4858159 {A : Type'} (u : type1402 A) (x : A) : (term1025 A u x) = (term922 A u x).
Proof. exact (@lem4858158 (term922 A u x)). Qed.
Lemma lem4858160 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term922 A u x.
Proof. exact (EQ_MP (@lem4858159 A u x) (@lem4858156 A u B x' s x h1 h2)). Qed.
Lemma lem4858162 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4858163 {A : Type'} (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term1055 A s x' _60200 x) = (term1056 A s x' _60200 x).
Proof. exact (@lem4858162 (term261 A s x' _60200) (@I (A -> Prop) _60200 x)). Qed.
Lemma lem4858164 {A : Type'} (B : type686 A) (_60200 : A -> Prop) : (term255 A B _60200) = (term255 A B _60200).
Proof. exact (eq_refl (term255 A B _60200)). Qed.
Lemma lem4858165 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term1000 A B s x' _60200 x) = (term1057 A B s x' _60200 x).
Proof. exact (MK_COMB (@lem4858164 A B _60200) (@lem4858163 A s x' _60200 x)). Qed.
Lemma lem4858167 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4858168 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term1057 A B s x' _60200 x) = (term1058 A B s x' _60200 x).
Proof. exact (@lem4858167 (@I ((A -> Prop) -> Prop) B _60200) (term1059 A s x' _60200 x)). Qed.
Lemma lem4858169 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term1000 A B s x' _60200 x) = (term1058 A B s x' _60200 x).
Proof. exact (TRANS (@lem4858165 A B s x' _60200 x) (@lem4858168 A B s x' _60200 x)). Qed.
Lemma lem4858171 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4858172 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term1058 A B s x' _60200 x) = (term1060 A B s x' _60200 x).
Proof. exact (@lem4858171 (term1061 A B s x' _60200 x)). Qed.
Lemma lem4858173 {A : Type'} (B : type686 A) (s : A -> Prop) (x' : type684 A) (_60200 : A -> Prop) (x : A) : (term1000 A B s x' _60200 x) = (term1060 A B s x' _60200 x).
Proof. exact (TRANS (@lem4858169 A B s x' _60200 x) (@lem4858172 A B s x' _60200 x)). Qed.
Lemma lem4858175 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1062 A s x' u x.
Proof. exact (conj (@lem4858141 A u B x' s x h1 h2) (@lem4858160 A u B x' s x h1 h2)). Qed.
Lemma lem4858176 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term1063 A B s x' u x.
Proof. exact (conj (@lem4857830 A u B x' s x h1 h2) (@lem4858175 A u B x' s x h1 h2)). Qed.
Lemma lem4858178 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term1060 A B s x' _60200 x.
Proof. exact (EQ_MP (@lem4858173 A B s x' _60200 x) (@lem4857649 A _60200 B x' s x h1)). Qed.
Lemma lem4858179 {A : Type'} (_60200 : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term1060 A B s x' _60200 x.
Proof. exact (@lem4858178 A _60200 B x' s x h1). Qed.
Lemma lem4858180 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term897 A B x' s x) : term1064 A B s x' u x.
Proof. exact (@lem4858179 A (@I (A -> A -> Prop) u x) B x' s x h1). Qed.
Lemma lem4858183 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : False.
Proof. exact (@lem4858180 A u B x' s x h2 (@lem4858176 A u B x' s x h1 h2)). Qed.
Lemma lem4858184 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : term399.
Proof. exact (fun h0 : ~ False => @lem4858183 A u B x' s x h1 h2). Qed.
Lemma lem4858186 (p : Prop) : (term349 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4858187 : term399 = False.
Proof. exact (@lem4858186 False). Qed.
Lemma lem4858188 {A : Type'} (u : type1402 A) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term897 A B x' s x) : False.
Proof. exact (EQ_MP (@lem4858187) (@lem4858184 A u B x' s x h1 h2)). Qed.
Lemma lem4858189 {A : Type'} (u : type1402 A) (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term907 A t B x' s x) : False.
Proof. exact (or_elim (@lem4857087 A t B x' s x h2) (fun h0 : term905 A B t s x => @lem4857770 A B t s x h0) (fun h0 : term897 A B x' s x => @lem4858188 A u B x' s x h1 h0)). Qed.
Lemma lem4858190 {A : Type'} (u : type1402 A) (c : A -> Prop) (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term586 A B u s) (h2 : term877 A c t B x' s x) : False.
Proof. exact (or_elim (@lem4856997 A c t B x' s x h2) (fun h0 : term908 A s B c => @lem4857694 A s B c h0) (fun h0 : term907 A t B x' s x => @lem4858189 A u t B x' s x h1 h0)). Qed.
Lemma lem4858191 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (x' : type684 A) (s : A -> Prop) (x : A) (h1 : term490 A B s) (h2 : term877 A c t B x' s x) : False.
Proof. exact (ex_elim (@lem4856009 A B s h1) (fun u : type1402 A => fun h0 : term588 A B s u => @lem4858190 A u c t B x' s x h0 h2)). Qed.
Lemma lem4858192 {A : Type'} (c : A -> Prop) (t : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) (h1 : term490 A B s) (h2 : term880 A c t B s x) : False.
Proof. exact (ex_elim (@lem4856806 A c t B s x h2) (fun x' : type684 A => fun h0 : term879 A c t B s x x' => @lem4858191 A c t B x' s x h1 h0)). Qed.
Lemma lem4858193 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (x : A) (h1 : term490 A B s) (h2 : term882 A c B s x) : False.
Proof. exact (ex_elim (@lem4856805 A c B s x h2) (fun t : A -> Prop => fun h0 : term881 A c B s x t => @lem4858192 A c t B s x h1 h0)). Qed.
Lemma lem4858194 {A : Type'} (c : A -> Prop) (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) (h2 : term884 A c B s) : False.
Proof. exact (ex_elim (@lem4856804 A c B s h2) (fun x : A => fun h0 : term883 A c B s x => @lem4858193 A c B s x h1 h0)). Qed.
Lemma lem4858195 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) (h2 : term539 A B s) : False.
Proof. exact (ex_elim (@lem4856803 A B s h2) (fun c : A -> Prop => fun h0 : term885 A B s c => @lem4858194 A c B s h1 h0)). Qed.
Lemma lem4858196 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) (h2 : term539 A B s) : (term539 A B s) = False.
Proof. exact (prop_ext (fun h3 : term539 A B s => @lem4858195 A B s h1 h2) (fun h3 : False => @lem4855813 A B s h2)). Qed.
Lemma lem4858197 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) (h2 : term539 A B s) : False.
Proof. exact (EQ_MP (@lem4858196 A B s h1 h2) (@lem4855813 A B s h2)). Qed.
Lemma lem4858198 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) : term538 A B s.
Proof. exact (fun h0 : term539 A B s => @lem4858197 A B s h1 h0). Qed.
Lemma lem4858199 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term490 A B s) : term522 A B s.
Proof. exact (EQ_MP (@lem4855812 A B s) (@lem4858198 A B s h1)). Qed.
Lemma lem4858200 {A : Type'} (B : type686 A) (s : A -> Prop) : term523 A B s.
Proof. exact (fun h0 : term490 A B s => @lem4858199 A B s h0). Qed.
Lemma lem4858205 {A : Type'} (s : A -> Prop) : term533 A s.
Proof. exact (fun B : type686 A => @lem4858200 A B s). Qed.
Lemma lem4858210 {A : Type'} : term537 A.
Proof. exact (fun s : A -> Prop => @lem4858205 A s). Qed.
Lemma lem4858211 {A : Type'} : term536 A.
Proof. exact (EQ_MP (@lem4855807 A) (@lem4858210 A)). Qed.
Lemma lem4858212 {A : Type'} (s : A -> Prop) : term1065 A s.
Proof. exact (@lem4858211 A s). Qed.
Lemma lem4858213 {A : Type'} (s : A -> Prop) : (term1065 A s) = (term532 A s).
Proof. exact (eq_refl (term1065 A s)). Qed.
Lemma lem4858214 {A : Type'} (s : A -> Prop) : term532 A s.
Proof. exact (EQ_MP (@lem4858213 A s) (@lem4858212 A s)). Qed.
Lemma lem4858215 {A : Type'} (s : A -> Prop) (B : type686 A) : term1066 A s B.
Proof. exact (@lem4858214 A s B). Qed.
Lemma lem4858216 {A : Type'} (B : type686 A) (s : A -> Prop) : (term1066 A s B) = (term524 A B s).
Proof. exact (eq_refl (term1066 A s B)). Qed.
Lemma lem4858217 {A : Type'} (B : type686 A) (s : A -> Prop) : term524 A B s.
Proof. exact (EQ_MP (@lem4858216 A B s) (@lem4858215 A s B)). Qed.
Lemma lem4858219 {A : Type'} (B : type686 A) (s : A -> Prop) : term524 A B s.
Proof. exact (@lem4855479 A B s (@lem4858217 A B s)). Qed.
Lemma lem4858220 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term525 A B s) : False.
Proof. exact (@lem4858219 A B s (@lem4855463 A B s h1)). Qed.
Lemma lem4858221 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term525 A B s) : (term525 A B s) = False.
Proof. exact (prop_ext (fun h2 : term525 A B s => @lem4858220 A B s h1) (fun h2 : False => @lem4855463 A B s h1)). Qed.
Lemma lem4858222 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term525 A B s) : False.
Proof. exact (EQ_MP (@lem4858221 A B s h1) (@lem4855463 A B s h1)). Qed.
Lemma lem4858223 {A : Type'} (B : type686 A) (s : A -> Prop) : term524 A B s.
Proof. exact (fun h0 : term525 A B s => @lem4858222 A B s h0). Qed.
Lemma lem4858224 {A : Type'} (B : type686 A) (s : A -> Prop) : term523 A B s.
Proof. exact (EQ_MP (@lem4855462 A B s) (@lem4858223 A B s)). Qed.
Lemma lem4858225 {A : Type'} (B : type686 A) (s : A -> Prop) : term478 A B s.
Proof. exact (EQ_MP (@lem4855458 A B s) (@lem4858224 A B s)). Qed.
Lemma lem4858226 {A : Type'} (B : type686 A) (s : A -> Prop) : term477 A B s.
Proof. exact (EQ_MP (@lem4855174 A B s) (@lem4858225 A B s)). Qed.
Lemma lem4858227 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term27 A B s) : term475 A B s.
Proof. exact (@lem4858226 A B s (@lem4854894 A B s h1)). Qed.
Lemma lem4858228 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term27 A B s) : term408 A B s.
Proof. exact (ex_intro (term406 A B s) (term450 A B s) (@lem4858227 A B s h1)). Qed.
Lemma lem4858229 {A : Type'} (B : type686 A) (s : A -> Prop) (h1 : term27 A B s) : @UNION_OF A (@ARBITRARY A) B s.
Proof. exact (EQ_MP (@lem4854976 A B s) (@lem4858228 A B s h1)). Qed.
Lemma lem4858230 {A : Type'} (B : type686 A) (s : A -> Prop) : term44 A B s.
Proof. exact (fun h0 : term27 A B s => @lem4858229 A B s h0). Qed.
Lemma lem4858235 {A : Type'} (B : type686 A) : term56 A B.
Proof. exact (fun s : A -> Prop => @lem4858230 A B s). Qed.
Lemma lem4858236 {A : Type'} (B : type686 A) : term86 A B.
Proof. exact (conj (@lem4854893 A B) (@lem4858235 A B)). Qed.
Lemma lem4858237 {A : Type'} (B : type686 A) : term57 A B.
Proof. exact (EQ_MP (@lem4853393 A B) (@lem4858236 A B)). Qed.
Lemma lem4858238 {A : Type'} (B : type686 A) : term31 A B.
Proof. exact (EQ_MP (@lem4853284 A B) (@lem4858237 A B)). Qed.
Lemma lem4858243 {A : Type'} : term1067 A.
Proof. exact (fun B : type686 A => @lem4858238 A B). Qed.
