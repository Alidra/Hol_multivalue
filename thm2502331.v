Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2502331_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import BOOL_CASES_AX_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import INT_DIVMOD_UNIQ_spec.
Require Import INT_DIV_0_spec.
Require Import INT_REM_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1386578_spec.
Require Import thm1482679_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982729_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318514_spec.
Require Import thm2318515_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm82_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem2498023 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2498024 (m : int) (h1 : term0) : term1 m.
Proof. exact (@lem2498023 h1 m). Qed.
Lemma lem2498025 (m : int) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2498026 (m : int) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem2498025 m) (@lem2498024 m h1)). Qed.
Lemma lem2498027 (m : int) (n : int) (h1 : term0) : term3 m n.
Proof. exact (@lem2498026 m h1 n). Qed.
Lemma lem2498028 (m : int) (n : int) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2498029 (m : int) (n : int) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem2498028 m n) (@lem2498027 m n h1)). Qed.
Lemma lem2498030 (m : int) (n : int) (q : int) (h1 : term0) : term5 m n q.
Proof. exact (@lem2498029 m n h1 q). Qed.
Lemma lem2498031 (q : int) (m : int) (n : int) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem2498032 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (EQ_MP (@lem2498031 q m n) (@lem2498030 m n q h1)). Qed.
Lemma lem2498033 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term7 q m n r.
Proof. exact (@lem2498032 q m n h1 r). Qed.
Lemma lem2498034 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2498035 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (EQ_MP (@lem2498034 q m n r) (@lem2498033 q m n r h1)). Qed.
Lemma lem2498036 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem2498037 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2498035 q m n r h1 (@lem2498036 m q r n h2)). Qed.
Lemma lem2498038 (m : int) (q : int) (r : int) (n : int) (h1 : term9 m q r n) : term11 q m n r.
Proof. exact (fun h0 : term0 => @lem2498037 m q r n h0 h1). Qed.
Lemma lem2498039 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2498040 (m : int) (q : int) (r : int) (n : int) (h1 : term0) (h2 : term9 m q r n) : term10 q m n r.
Proof. exact (@lem2498038 m q r n h2 (@lem2498039 h1)). Qed.
Lemma lem2498041 (q : int) (m : int) (n : int) (r : int) (h1 : term0) : term8 q m n r.
Proof. exact (fun h0 : term9 m q r n => @lem2498040 m q r n h1 h0). Qed.
Lemma lem2498042 (q : int) (m : int) (n : int) (h1 : term0) : term6 q m n.
Proof. exact (fun r : int => @lem2498041 q m n r h1). Qed.
Lemma lem2498043 (q : int) (m : int) (h1 : term0) : term12 q m.
Proof. exact (fun n : int => @lem2498042 q m n h1). Qed.
Lemma lem2498044 (q : int) (h1 : term0) : term13 q.
Proof. exact (fun m : int => @lem2498043 q m h1). Qed.
Lemma lem2498045 (h1 : term0) : term14.
Proof. exact (fun q : int => @lem2498044 q h1). Qed.
Lemma lem2498046 : term15.
Proof. exact (fun h0 : term0 => @lem2498045 h0). Qed.
Lemma lem2498047 : term14.
Proof. exact (@lem2498046 (@lem2495588)). Qed.
Lemma lem2498048 (q : int) : term16 q.
Proof. exact (@lem2498047 q). Qed.
Lemma lem2498049 (q : int) : (term16 q) = (term13 q).
Proof. exact (eq_refl (term16 q)). Qed.
Lemma lem2498050 (q : int) : term13 q.
Proof. exact (EQ_MP (@lem2498049 q) (@lem2498048 q)). Qed.
Lemma lem2498051 (q : int) (m : int) : term17 q m.
Proof. exact (@lem2498050 q m). Qed.
Lemma lem2498052 (q : int) (m : int) : (term17 q m) = (term12 q m).
Proof. exact (eq_refl (term17 q m)). Qed.
Lemma lem2498053 (q : int) (m : int) : term12 q m.
Proof. exact (EQ_MP (@lem2498052 q m) (@lem2498051 q m)). Qed.
Lemma lem2498054 (q : int) (m : int) (n : int) : term18 q m n.
Proof. exact (@lem2498053 q m n). Qed.
Lemma lem2498055 (q : int) (m : int) (n : int) : (term18 q m n) = (term6 q m n).
Proof. exact (eq_refl (term18 q m n)). Qed.
Lemma lem2498056 (q : int) (m : int) (n : int) : term6 q m n.
Proof. exact (EQ_MP (@lem2498055 q m n) (@lem2498054 q m n)). Qed.
Lemma lem2498057 (q : int) (m : int) (n : int) (r : int) : term7 q m n r.
Proof. exact (@lem2498056 q m n r). Qed.
Lemma lem2498058 (q : int) (m : int) (n : int) (r : int) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem2498074 (p : Prop) : term19 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem2498075 (p : Prop) : (term19 p) = (term20 p).
Proof. exact (eq_refl (term19 p)). Qed.
Lemma lem2498076 (p : Prop) : term20 p.
Proof. exact (EQ_MP (@lem2498075 p) (@lem2498074 p)). Qed.
Lemma lem2498077 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem2498078 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem2498093 (q : Prop) (r : Prop) : (term21 q r) = (term21 q r).
Proof. exact (eq_refl (term21 q r)). Qed.
Lemma lem2498094 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term22 q r p) = (term23 q r).
Proof. exact (MK_COMB (@lem2498093 q r) (@lem2498077 p h1)). Qed.
Lemma lem2498095 (q : Prop) (r : Prop) : (term23 q r) = ((term24 q r) = (term25 q r)).
Proof. exact (eq_refl (term23 q r)). Qed.
Lemma lem2498096 (q : Prop) (r : Prop) (p : Prop) : (term26 q r p) = (term26 q r p).
Proof. exact (eq_refl (term26 q r p)). Qed.
Lemma lem2498097 (p : Prop) (q : Prop) (r : Prop) : ((term22 q r p) = (term23 q r)) = ((term22 q r p) = ((term24 q r) = (term25 q r))).
Proof. exact (MK_COMB (@lem2498096 q r p) (@lem2498095 q r)). Qed.
Lemma lem2498098 (p : Prop) (q : Prop) (r : Prop) : (term22 q r p) = ((term27 q p r) = (term28 p q r)).
Proof. exact (eq_refl (term22 q r p)). Qed.
Lemma lem2498099 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2498100 (p : Prop) (q : Prop) (r : Prop) : (term26 q r p) = (term29 p q r).
Proof. exact (MK_COMB (@lem2498099) (@lem2498098 p q r)). Qed.
Lemma lem2498101 (q : Prop) (r : Prop) : ((term24 q r) = (term25 q r)) = ((term24 q r) = (term25 q r)).
Proof. exact (eq_refl ((term24 q r) = (term25 q r))). Qed.
Lemma lem2498102 (p : Prop) (q : Prop) (r : Prop) : ((term22 q r p) = ((term24 q r) = (term25 q r))) = (((term27 q p r) = (term28 p q r)) = ((term24 q r) = (term25 q r))).
Proof. exact (MK_COMB (@lem2498100 p q r) (@lem2498101 q r)). Qed.
Lemma lem2498103 (p : Prop) (q : Prop) (r : Prop) : ((term22 q r p) = (term23 q r)) = (((term27 q p r) = (term28 p q r)) = ((term24 q r) = (term25 q r))).
Proof. exact (TRANS (@lem2498097 p q r) (@lem2498102 p q r)). Qed.
Lemma lem2498104 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term27 q p r) = (term28 p q r)) = ((term24 q r) = (term25 q r)).
Proof. exact (EQ_MP (@lem2498103 p q r) (@lem2498094 q r p h1)). Qed.
Lemma lem2498105 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : ((term24 q r) = (term25 q r)) = ((term27 q p r) = (term28 p q r)).
Proof. exact (SYM (@lem2498104 q r p h1)). Qed.
Lemma lem2498106 (q : Prop) (r : Prop) : (term21 q r) = (term21 q r).
Proof. exact (eq_refl (term21 q r)). Qed.
Lemma lem2498107 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term22 q r p) = (term30 q r).
Proof. exact (MK_COMB (@lem2498106 q r) (@lem2498078 p h1)). Qed.
Lemma lem2498108 (q : Prop) (r : Prop) : (term30 q r) = ((term31 q r) = (term32 q r)).
Proof. exact (eq_refl (term30 q r)). Qed.
Lemma lem2498109 (q : Prop) (r : Prop) (p : Prop) : (term26 q r p) = (term26 q r p).
Proof. exact (eq_refl (term26 q r p)). Qed.
Lemma lem2498110 (p : Prop) (q : Prop) (r : Prop) : ((term22 q r p) = (term30 q r)) = ((term22 q r p) = ((term31 q r) = (term32 q r))).
Proof. exact (MK_COMB (@lem2498109 q r p) (@lem2498108 q r)). Qed.
Lemma lem2498111 (p : Prop) (q : Prop) (r : Prop) : (term22 q r p) = ((term27 q p r) = (term28 p q r)).
Proof. exact (eq_refl (term22 q r p)). Qed.
Lemma lem2498112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2498113 (p : Prop) (q : Prop) (r : Prop) : (term26 q r p) = (term29 p q r).
Proof. exact (MK_COMB (@lem2498112) (@lem2498111 p q r)). Qed.
Lemma lem2498114 (q : Prop) (r : Prop) : ((term31 q r) = (term32 q r)) = ((term31 q r) = (term32 q r)).
Proof. exact (eq_refl ((term31 q r) = (term32 q r))). Qed.
Lemma lem2498115 (p : Prop) (q : Prop) (r : Prop) : ((term22 q r p) = ((term31 q r) = (term32 q r))) = (((term27 q p r) = (term28 p q r)) = ((term31 q r) = (term32 q r))).
Proof. exact (MK_COMB (@lem2498113 p q r) (@lem2498114 q r)). Qed.
Lemma lem2498116 (p : Prop) (q : Prop) (r : Prop) : ((term22 q r p) = (term30 q r)) = (((term27 q p r) = (term28 p q r)) = ((term31 q r) = (term32 q r))).
Proof. exact (TRANS (@lem2498110 p q r) (@lem2498115 p q r)). Qed.
Lemma lem2498117 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term27 q p r) = (term28 p q r)) = ((term31 q r) = (term32 q r)).
Proof. exact (EQ_MP (@lem2498116 p q r) (@lem2498107 q r p h1)). Qed.
Lemma lem2498118 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : ((term31 q r) = (term32 q r)) = ((term27 q p r) = (term28 p q r)).
Proof. exact (SYM (@lem2498117 q r p h1)). Qed.
Lemma lem2498124 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2498125 (q : Prop) : (True -> q) = q.
Proof. exact (@lem2498124 q). Qed.
Lemma lem2498126 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498127 (q : Prop) : (term33 q) = (and q).
Proof. exact (MK_COMB (@lem2498126) (@lem2498125 q)). Qed.
Lemma lem2498129 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2498130 (r : Prop) : (True -> r) = r.
Proof. exact (@lem2498129 r). Qed.
Lemma lem2498131 (q : Prop) (r : Prop) : (term24 q r) = (q /\ r).
Proof. exact (MK_COMB (@lem2498127 q) (@lem2498130 r)). Qed.
Lemma lem2498134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2498135 (q : Prop) (r : Prop) : (term34 q r) = (term35 q r).
Proof. exact (MK_COMB (@lem2498134) (@lem2498131 q r)). Qed.
Lemma lem2498137 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2498138 (q : Prop) (r : Prop) : (term25 q r) = (q /\ r).
Proof. exact (@lem2498137 (q /\ r)). Qed.
Lemma lem2498141 (q : Prop) (r : Prop) : ((term24 q r) = (term25 q r)) = ((q /\ r) = (q /\ r)).
Proof. exact (MK_COMB (@lem2498135 q r) (@lem2498138 q r)). Qed.
Lemma lem2498143 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2498144 (x : Prop) : (x = x) = True.
Proof. exact (@lem2498143 Prop x). Qed.
Lemma lem2498145 (q : Prop) (r : Prop) : ((q /\ r) = (q /\ r)) = True.
Proof. exact (@lem2498144 (q /\ r)). Qed.
Lemma lem2498146 (q : Prop) (r : Prop) : ((term24 q r) = (term25 q r)) = True.
Proof. exact (TRANS (@lem2498141 q r) (@lem2498145 q r)). Qed.
Lemma lem2498147 (q : Prop) (r : Prop) : True = ((term24 q r) = (term25 q r)).
Proof. exact (SYM (@lem2498146 q r)). Qed.
Lemma lem2498148 (q : Prop) (r : Prop) : (term24 q r) = (term25 q r).
Proof. exact (EQ_MP (@lem2498147 q r) (@lem0)). Qed.
Lemma lem2498154 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2498155 (q : Prop) : (False -> q) = True.
Proof. exact (@lem2498154 q). Qed.
Lemma lem2498156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498157 (q : Prop) : (term36 q) = (and True).
Proof. exact (MK_COMB (@lem2498156) (@lem2498155 q)). Qed.
Lemma lem2498159 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2498160 (r : Prop) : (False -> r) = True.
Proof. exact (@lem2498159 r). Qed.
Lemma lem2498161 (q : Prop) (r : Prop) : (term31 q r) = (True /\ True).
Proof. exact (MK_COMB (@lem2498157 q) (@lem2498160 r)). Qed.
Lemma lem2498163 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2498164 : (True /\ True) = True.
Proof. exact (@lem2498163 True). Qed.
Lemma lem2498165 (q : Prop) (r : Prop) : (term31 q r) = True.
Proof. exact (TRANS (@lem2498161 q r) (@lem2498164)). Qed.
Lemma lem2498166 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2498167 (q : Prop) (r : Prop) : (term37 q r) = (@eq Prop True).
Proof. exact (MK_COMB (@lem2498166) (@lem2498165 q r)). Qed.
Lemma lem2498169 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2498170 (q : Prop) (r : Prop) : (term32 q r) = True.
Proof. exact (@lem2498169 (q /\ r)). Qed.
Lemma lem2498171 (q : Prop) (r : Prop) : ((term31 q r) = (term32 q r)) = (True = True).
Proof. exact (MK_COMB (@lem2498167 q r) (@lem2498170 q r)). Qed.
Lemma lem2498173 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem2498174 : (True = True) = True.
Proof. exact (@lem2498173 True). Qed.
Lemma lem2498175 (q : Prop) (r : Prop) : ((term31 q r) = (term32 q r)) = True.
Proof. exact (TRANS (@lem2498171 q r) (@lem2498174)). Qed.
Lemma lem2498176 (q : Prop) (r : Prop) : True = ((term31 q r) = (term32 q r)).
Proof. exact (SYM (@lem2498175 q r)). Qed.
Lemma lem2498177 (q : Prop) (r : Prop) : (term31 q r) = (term32 q r).
Proof. exact (EQ_MP (@lem2498176 q r) (@lem0)). Qed.
Lemma lem2498178 (q : Prop) (r : Prop) (p : Prop) (h1 : p = False) : (term27 q p r) = (term28 p q r).
Proof. exact (EQ_MP (@lem2498118 q r p h1) (@lem2498177 q r)). Qed.
Lemma lem2498179 (q : Prop) (r : Prop) (p : Prop) (h1 : p = True) : (term27 q p r) = (term28 p q r).
Proof. exact (EQ_MP (@lem2498105 q r p h1) (@lem2498148 q r)). Qed.
Lemma lem2498183 (n : int) : term38 n.
Proof. exact (@lem9784 (n = term39)). Qed.
Lemma lem2498184 (n : int) : (term38 n) = (term40 n).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem2498185 (n : int) : term40 n.
Proof. exact (EQ_MP (@lem2498184 n) (@lem2498183 n)). Qed.
Lemma lem2498187 (n : int) (h1 : term41 n) : term41 n.
Proof. exact (h1). Qed.
Lemma lem2498188 {A : Type'} (P : A -> Prop) : term42 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem2498189 {A : Type'} (P : A -> Prop) : (term42 A P) = (term43 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem2498190 {A : Type'} (P : A -> Prop) : term43 A P.
Proof. exact (EQ_MP (@lem2498189 A P) (@lem2498188 A P)). Qed.
Lemma lem2498191 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term44 A P Q.
Proof. exact (@lem2498190 A P Q). Qed.
Lemma lem2498192 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term44 A P Q) = ((term45 A P Q) = (term46 A P Q)).
Proof. exact (eq_refl (term44 A P Q)). Qed.
Lemma lem2498195 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term45 A P Q) = (term46 A P Q).
Proof. exact (EQ_MP (@lem2498192 A P Q) (@lem2498191 A P Q)). Qed.
Lemma lem2498196 (P : int -> Prop) (Q : int -> Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem2498195 int P Q). Qed.
Lemma lem2498197 : term49 = term50.
Proof. exact (@lem2498196 term51 term52). Qed.
Lemma lem2498198 (m : int) : (term53 m) = (term54 m).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem2498199 : term55 = term51.
Proof. exact (fun_ext (fun m : int => @lem2498198 m)). Qed.
Lemma lem2498200 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2498201 : term56 = term57.
Proof. exact (MK_COMB (@lem2498200) (@lem2498199)). Qed.
Lemma lem2498202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498203 : term58 = term59.
Proof. exact (MK_COMB (@lem2498202) (@lem2498201)). Qed.
Lemma lem2498204 (m : int) : (term60 m) = (term61 m).
Proof. exact (eq_refl (term60 m)). Qed.
Lemma lem2498205 : term62 = term52.
Proof. exact (fun_ext (fun m : int => @lem2498204 m)). Qed.
Lemma lem2498206 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2498207 : term63 = term64.
Proof. exact (MK_COMB (@lem2498206) (@lem2498205)). Qed.
Lemma lem2498208 : term49 = term65.
Proof. exact (MK_COMB (@lem2498203) (@lem2498207)). Qed.
Lemma lem2498209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2498210 : term66 = term67.
Proof. exact (MK_COMB (@lem2498209) (@lem2498208)). Qed.
Lemma lem2498211 (m : int) : (term53 m) = (term54 m).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem2498212 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498213 (m : int) : (term68 m) = (term69 m).
Proof. exact (MK_COMB (@lem2498212) (@lem2498211 m)). Qed.
Lemma lem2498214 (m : int) : (term60 m) = (term61 m).
Proof. exact (eq_refl (term60 m)). Qed.
Lemma lem2498215 (m : int) : (term70 m) = (term71 m).
Proof. exact (MK_COMB (@lem2498213 m) (@lem2498214 m)). Qed.
Lemma lem2498216 : term72 = term73.
Proof. exact (fun_ext (fun m : int => @lem2498215 m)). Qed.
Lemma lem2498217 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2498218 : term50 = term74.
Proof. exact (MK_COMB (@lem2498217) (@lem2498216)). Qed.
Lemma lem2498219 : (term49 = term50) = (term65 = term74).
Proof. exact (MK_COMB (@lem2498210) (@lem2498218)). Qed.
Lemma lem2498220 : term65 = term74.
Proof. exact (EQ_MP (@lem2498219) (@lem2498197)). Qed.
Lemma lem2498226 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term45 A P Q) = (term46 A P Q).
Proof. exact (EQ_MP (@lem2498192 A P Q) (@lem2498191 A P Q)). Qed.
Lemma lem2498227 (P : int -> Prop) (Q : int -> Prop) : (term47 P Q) = (term48 P Q).
Proof. exact (@lem2498226 int P Q). Qed.
Lemma lem2498228 (m : int) : (term75 m) = (term76 m).
Proof. exact (@lem2498227 (term77 m) (term78 m)). Qed.
Lemma lem2498229 (m : int) (n : int) : (term79 m n) = (term80 m n).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem2498230 (m : int) : (term81 m) = (term77 m).
Proof. exact (fun_ext (fun n : int => @lem2498229 m n)). Qed.
Lemma lem2498231 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2498232 (m : int) : (term82 m) = (term54 m).
Proof. exact (MK_COMB (@lem2498231) (@lem2498230 m)). Qed.
Lemma lem2498233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498234 (m : int) : (term83 m) = (term69 m).
Proof. exact (MK_COMB (@lem2498233) (@lem2498232 m)). Qed.
Lemma lem2498235 (n : int) (m : int) : (term84 m n) = (term85 n m).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem2498236 (m : int) : (term86 m) = (term78 m).
Proof. exact (fun_ext (fun n : int => @lem2498235 n m)). Qed.
Lemma lem2498237 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2498238 (m : int) : (term87 m) = (term61 m).
Proof. exact (MK_COMB (@lem2498237) (@lem2498236 m)). Qed.
Lemma lem2498239 (m : int) : (term75 m) = (term71 m).
Proof. exact (MK_COMB (@lem2498234 m) (@lem2498238 m)). Qed.
Lemma lem2498240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2498241 (m : int) : (term88 m) = (term89 m).
Proof. exact (MK_COMB (@lem2498240) (@lem2498239 m)). Qed.
Lemma lem2498242 (m : int) (n : int) : (term79 m n) = (term80 m n).
Proof. exact (eq_refl (term79 m n)). Qed.
Lemma lem2498243 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498244 (m : int) (n : int) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem2498243) (@lem2498242 m n)). Qed.
Lemma lem2498245 (n : int) (m : int) : (term84 m n) = (term85 n m).
Proof. exact (eq_refl (term84 m n)). Qed.
Lemma lem2498246 (n : int) (m : int) : (term92 m n) = (term93 n m).
Proof. exact (MK_COMB (@lem2498244 m n) (@lem2498245 n m)). Qed.
Lemma lem2498247 (m : int) : (term94 m) = (term95 m).
Proof. exact (fun_ext (fun n : int => @lem2498246 n m)). Qed.
Lemma lem2498248 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2498249 (m : int) : (term76 m) = (term96 m).
Proof. exact (MK_COMB (@lem2498248) (@lem2498247 m)). Qed.
Lemma lem2498250 (m : int) : ((term75 m) = (term76 m)) = ((term71 m) = (term96 m)).
Proof. exact (MK_COMB (@lem2498241 m) (@lem2498249 m)). Qed.
Lemma lem2498251 (m : int) : (term71 m) = (term96 m).
Proof. exact (EQ_MP (@lem2498250 m) (@lem2498228 m)). Qed.
Lemma lem2498278 : term73 = term97.
Proof. exact (fun_ext (fun m : int => @lem2498251 m)). Qed.
Lemma lem2498279 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2498280 : term74 = term98.
Proof. exact (MK_COMB (@lem2498279) (@lem2498278)). Qed.
Lemma lem2498285 : term65 = term98.
Proof. exact (TRANS (@lem2498220) (@lem2498280)). Qed.
Lemma lem2498286 : term98 = term65.
Proof. exact (SYM (@lem2498285)). Qed.
Lemma lem2498287 (m : int) : term99 m.
Proof. exact (@lem2396893 m). Qed.
Lemma lem2498288 (m : int) : (term99 m) = ((term100 m) = m).
Proof. exact (eq_refl (term99 m)). Qed.
Lemma lem2498290 (m : int) : term101 m.
Proof. exact (@lem2395867 m). Qed.
Lemma lem2498291 (m : int) : (term101 m) = ((term102 m) = term39).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem2498304 (n : int) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem2498305 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2498306 (n : int) (h1 : n = term39) : (@eq int n) = term103.
Proof. exact (MK_COMB (@lem2498305) (@lem2498304 n h1)). Qed.
Lemma lem2498307 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem2498308 (n : int) (h1 : n = term39) : (n = term39) = (term39 = term39).
Proof. exact (MK_COMB (@lem2498306 n h1) (@lem2498307)). Qed.
Lemma lem2498310 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2498311 (x : int) : (x = x) = True.
Proof. exact (@lem2498310 int x). Qed.
Lemma lem2498312 : (term39 = term39) = True.
Proof. exact (@lem2498311 term39). Qed.
Lemma lem2498313 (n : int) (h1 : n = term39) : (n = term39) = True.
Proof. exact (TRANS (@lem2498308 n h1) (@lem2498312)). Qed.
Lemma lem2498314 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2498315 (n : int) (h1 : n = term39) : (term41 n) = (~ True).
Proof. exact (MK_COMB (@lem2498314) (@lem2498313 n h1)). Qed.
Lemma lem2498317 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem2498318 (n : int) (h1 : n = term39) : (term41 n) = False.
Proof. exact (TRANS (@lem2498315 n h1) (@lem2498317)). Qed.
Lemma lem2498319 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498320 (n : int) (h1 : n = term39) : (term104 n) = (imp False).
Proof. exact (MK_COMB (@lem2498319) (@lem2498318 n h1)). Qed.
Lemma lem2498321 (m : int) : (term105 m) = (term105 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem2498322 (m : int) (n : int) (h1 : n = term39) : (term106 n m) = (term107 m).
Proof. exact (MK_COMB (@lem2498320 n h1) (@lem2498321 m)). Qed.
Lemma lem2498324 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2498325 (m : int) : (term107 m) = True.
Proof. exact (@lem2498324 (term105 m)). Qed.
Lemma lem2498326 (m : int) (n : int) (h1 : n = term39) : (term106 n m) = True.
Proof. exact (TRANS (@lem2498322 m n h1) (@lem2498325 m)). Qed.
Lemma lem2498327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498328 (m : int) (n : int) (h1 : n = term39) : (term108 n m) = (and True).
Proof. exact (MK_COMB (@lem2498327) (@lem2498326 m n h1)). Qed.
Lemma lem2498330 (n : int) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem2498331 (m : int) : (int_lt m) = (int_lt m).
Proof. exact (eq_refl (int_lt m)). Qed.
Lemma lem2498332 (m : int) (n : int) (h1 : n = term39) : (int_lt m n) = (term109 m).
Proof. exact (MK_COMB (@lem2498331 m) (@lem2498330 n h1)). Qed.
Lemma lem2498333 (m : int) (n : int) (h1 : n = term39) : (term110 m n) = (term111 m).
Proof. exact (MK_COMB (@lem2498328 m n h1) (@lem2498332 m n h1)). Qed.
Lemma lem2498335 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2498336 (m : int) : (term111 m) = (term109 m).
Proof. exact (@lem2498335 (term109 m)). Qed.
Lemma lem2498337 (m : int) (n : int) (h1 : n = term39) : (term110 m n) = (term109 m).
Proof. exact (TRANS (@lem2498333 m n h1) (@lem2498336 m)). Qed.
Lemma lem2498338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498339 (m : int) (n : int) (h1 : n = term39) : (term112 m n) = (term113 m).
Proof. exact (MK_COMB (@lem2498338) (@lem2498337 m n h1)). Qed.
Lemma lem2498343 (n : int) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem2498344 (m : int) : (div m) = (div m).
Proof. exact (eq_refl (div m)). Qed.
Lemma lem2498345 (m : int) (n : int) (h1 : n = term39) : (div m n) = (term102 m).
Proof. exact (MK_COMB (@lem2498344 m) (@lem2498343 n h1)). Qed.
Lemma lem2498347 (m : int) : (term102 m) = term39.
Proof. exact (EQ_MP (@lem2498291 m) (@lem2498290 m)). Qed.
Lemma lem2498348 (m : int) (n : int) (h1 : n = term39) : (div m n) = term39.
Proof. exact (TRANS (@lem2498345 m n h1) (@lem2498347 m)). Qed.
Lemma lem2498349 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2498350 (m : int) (n : int) (h1 : n = term39) : (term114 m n) = term103.
Proof. exact (MK_COMB (@lem2498349) (@lem2498348 m n h1)). Qed.
Lemma lem2498351 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem2498352 (m : int) (n : int) (h1 : n = term39) : ((div m n) = term39) = (term39 = term39).
Proof. exact (MK_COMB (@lem2498350 m n h1) (@lem2498351)). Qed.
Lemma lem2498354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2498355 (x : int) : (x = x) = True.
Proof. exact (@lem2498354 int x). Qed.
Lemma lem2498356 : (term39 = term39) = True.
Proof. exact (@lem2498355 term39). Qed.
Lemma lem2498357 (m : int) (n : int) (h1 : n = term39) : ((div m n) = term39) = True.
Proof. exact (TRANS (@lem2498352 m n h1) (@lem2498356)). Qed.
Lemma lem2498358 (m : int) (n : int) (h1 : n = term39) : (term80 m n) = (term115 m).
Proof. exact (MK_COMB (@lem2498339 m n h1) (@lem2498357 m n h1)). Qed.
Lemma lem2498360 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem2498361 (m : int) : (term115 m) = True.
Proof. exact (@lem2498360 (term109 m)). Qed.
Lemma lem2498362 (m : int) (n : int) (h1 : n = term39) : (term80 m n) = True.
Proof. exact (TRANS (@lem2498358 m n h1) (@lem2498361 m)). Qed.
Lemma lem2498363 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498364 (m : int) (n : int) (h1 : n = term39) : (term91 m n) = (and True).
Proof. exact (MK_COMB (@lem2498363) (@lem2498362 m n h1)). Qed.
Lemma lem2498374 (n : int) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem2498375 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2498376 (n : int) (h1 : n = term39) : (@eq int n) = term103.
Proof. exact (MK_COMB (@lem2498375) (@lem2498374 n h1)). Qed.
Lemma lem2498377 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem2498378 (n : int) (h1 : n = term39) : (n = term39) = (term39 = term39).
Proof. exact (MK_COMB (@lem2498376 n h1) (@lem2498377)). Qed.
Lemma lem2498380 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2498381 (x : int) : (x = x) = True.
Proof. exact (@lem2498380 int x). Qed.
Lemma lem2498382 : (term39 = term39) = True.
Proof. exact (@lem2498381 term39). Qed.
Lemma lem2498383 (n : int) (h1 : n = term39) : (n = term39) = True.
Proof. exact (TRANS (@lem2498378 n h1) (@lem2498382)). Qed.
Lemma lem2498384 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2498385 (n : int) (h1 : n = term39) : (term41 n) = (~ True).
Proof. exact (MK_COMB (@lem2498384) (@lem2498383 n h1)). Qed.
Lemma lem2498387 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem2498388 (n : int) (h1 : n = term39) : (term41 n) = False.
Proof. exact (TRANS (@lem2498385 n h1) (@lem2498387)). Qed.
Lemma lem2498389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498390 (n : int) (h1 : n = term39) : (term104 n) = (imp False).
Proof. exact (MK_COMB (@lem2498389) (@lem2498388 n h1)). Qed.
Lemma lem2498391 (m : int) : (term105 m) = (term105 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem2498392 (m : int) (n : int) (h1 : n = term39) : (term106 n m) = (term107 m).
Proof. exact (MK_COMB (@lem2498390 n h1) (@lem2498391 m)). Qed.
Lemma lem2498394 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem2498395 (m : int) : (term107 m) = True.
Proof. exact (@lem2498394 (term105 m)). Qed.
Lemma lem2498396 (m : int) (n : int) (h1 : n = term39) : (term106 n m) = True.
Proof. exact (TRANS (@lem2498392 m n h1) (@lem2498395 m)). Qed.
Lemma lem2498397 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498398 (m : int) (n : int) (h1 : n = term39) : (term108 n m) = (and True).
Proof. exact (MK_COMB (@lem2498397) (@lem2498396 m n h1)). Qed.
Lemma lem2498400 (n : int) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem2498401 (m : int) : (int_lt m) = (int_lt m).
Proof. exact (eq_refl (int_lt m)). Qed.
Lemma lem2498402 (m : int) (n : int) (h1 : n = term39) : (int_lt m n) = (term109 m).
Proof. exact (MK_COMB (@lem2498401 m) (@lem2498400 n h1)). Qed.
Lemma lem2498403 (m : int) (n : int) (h1 : n = term39) : (term110 m n) = (term111 m).
Proof. exact (MK_COMB (@lem2498398 m n h1) (@lem2498402 m n h1)). Qed.
Lemma lem2498405 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2498406 (m : int) : (term111 m) = (term109 m).
Proof. exact (@lem2498405 (term109 m)). Qed.
Lemma lem2498407 (m : int) (n : int) (h1 : n = term39) : (term110 m n) = (term109 m).
Proof. exact (TRANS (@lem2498403 m n h1) (@lem2498406 m)). Qed.
Lemma lem2498408 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498409 (m : int) (n : int) (h1 : n = term39) : (term112 m n) = (term113 m).
Proof. exact (MK_COMB (@lem2498408) (@lem2498407 m n h1)). Qed.
Lemma lem2498413 (n : int) (h1 : n = term39) : n = term39.
Proof. exact (h1). Qed.
Lemma lem2498414 (m : int) : (rem m) = (rem m).
Proof. exact (eq_refl (rem m)). Qed.
Lemma lem2498415 (m : int) (n : int) (h1 : n = term39) : (rem m n) = (term100 m).
Proof. exact (MK_COMB (@lem2498414 m) (@lem2498413 n h1)). Qed.
Lemma lem2498417 (m : int) : (term100 m) = m.
Proof. exact (EQ_MP (@lem2498288 m) (@lem2498287 m)). Qed.
Lemma lem2498418 (m : int) (n : int) (h1 : n = term39) : (rem m n) = m.
Proof. exact (TRANS (@lem2498415 m n h1) (@lem2498417 m)). Qed.
Lemma lem2498419 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2498420 (m : int) (n : int) (h1 : n = term39) : (term116 m n) = (@eq int m).
Proof. exact (MK_COMB (@lem2498419) (@lem2498418 m n h1)). Qed.
Lemma lem2498421 (m : int) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem2498422 (m : int) (n : int) (h1 : n = term39) : ((rem m n) = m) = (m = m).
Proof. exact (MK_COMB (@lem2498420 m n h1) (@lem2498421 m)). Qed.
Lemma lem2498424 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2498425 (x : int) : (x = x) = True.
Proof. exact (@lem2498424 int x). Qed.
Lemma lem2498426 (m : int) : (m = m) = True.
Proof. exact (@lem2498425 m). Qed.
Lemma lem2498427 (m : int) (n : int) (h1 : n = term39) : ((rem m n) = m) = True.
Proof. exact (TRANS (@lem2498422 m n h1) (@lem2498426 m)). Qed.
Lemma lem2498428 (m : int) (n : int) (h1 : n = term39) : (term85 n m) = (term115 m).
Proof. exact (MK_COMB (@lem2498409 m n h1) (@lem2498427 m n h1)). Qed.
Lemma lem2498430 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem2498431 (m : int) : (term115 m) = True.
Proof. exact (@lem2498430 (term109 m)). Qed.
Lemma lem2498432 (m : int) (n : int) (h1 : n = term39) : (term85 n m) = True.
Proof. exact (TRANS (@lem2498428 m n h1) (@lem2498431 m)). Qed.
Lemma lem2498433 (m : int) (n : int) (h1 : n = term39) : (term93 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem2498364 m n h1) (@lem2498432 m n h1)). Qed.
Lemma lem2498435 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2498436 : (True /\ True) = True.
Proof. exact (@lem2498435 True). Qed.
Lemma lem2498437 (m : int) (n : int) (h1 : n = term39) : (term93 n m) = True.
Proof. exact (TRANS (@lem2498433 m n h1) (@lem2498436)). Qed.
Lemma lem2498438 (m : int) (n : int) (h1 : n = term39) : True = (term93 n m).
Proof. exact (SYM (@lem2498437 m n h1)). Qed.
Lemma lem2498439 (m : int) (n : int) (h1 : n = term39) : term93 n m.
Proof. exact (EQ_MP (@lem2498438 m n h1) (@lem0)). Qed.
Lemma lem2498446 (n : int) : term117 n.
Proof. exact (@lem82 (n = term39)). Qed.
Lemma lem2498468 (n : int) (h1 : term41 n) : (n = term39) = False.
Proof. exact (@lem2498446 n (@lem2498187 n h1)). Qed.
Lemma lem2498469 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2498470 (n : int) (h1 : term41 n) : (term41 n) = (~ False).
Proof. exact (MK_COMB (@lem2498469) (@lem2498468 n h1)). Qed.
Lemma lem2498472 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2498473 (n : int) (h1 : term41 n) : (term41 n) = True.
Proof. exact (TRANS (@lem2498470 n h1) (@lem2498472)). Qed.
Lemma lem2498474 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498475 (n : int) (h1 : term41 n) : (term104 n) = (imp True).
Proof. exact (MK_COMB (@lem2498474) (@lem2498473 n h1)). Qed.
Lemma lem2498476 (m : int) : (term105 m) = (term105 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem2498477 (m : int) (n : int) (h1 : term41 n) : (term106 n m) = (term118 m).
Proof. exact (MK_COMB (@lem2498475 n h1) (@lem2498476 m)). Qed.
Lemma lem2498479 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2498480 (m : int) : (term118 m) = (term105 m).
Proof. exact (@lem2498479 (term105 m)). Qed.
Lemma lem2498481 (m : int) (n : int) (h1 : term41 n) : (term106 n m) = (term105 m).
Proof. exact (TRANS (@lem2498477 m n h1) (@lem2498480 m)). Qed.
Lemma lem2498482 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498483 (m : int) (n : int) (h1 : term41 n) : (term108 n m) = (term119 m).
Proof. exact (MK_COMB (@lem2498482) (@lem2498481 m n h1)). Qed.
Lemma lem2498484 (m : int) (n : int) : (int_lt m n) = (int_lt m n).
Proof. exact (eq_refl (int_lt m n)). Qed.
Lemma lem2498485 (m : int) (n : int) (h1 : term41 n) : (term110 m n) = (term120 m n).
Proof. exact (MK_COMB (@lem2498483 m n h1) (@lem2498484 m n)). Qed.
Lemma lem2498488 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498489 (m : int) (n : int) (h1 : term41 n) : (term112 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2498488) (@lem2498485 m n h1)). Qed.
Lemma lem2498492 (m : int) (n : int) : ((div m n) = term39) = ((div m n) = term39).
Proof. exact (eq_refl ((div m n) = term39)). Qed.
Lemma lem2498493 (m : int) (n : int) (h1 : term41 n) : (term80 m n) = (term122 m n).
Proof. exact (MK_COMB (@lem2498489 m n h1) (@lem2498492 m n)). Qed.
Lemma lem2498496 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498497 (m : int) (n : int) (h1 : term41 n) : (term91 m n) = (term123 m n).
Proof. exact (MK_COMB (@lem2498496) (@lem2498493 m n h1)). Qed.
Lemma lem2498505 (n : int) (h1 : term41 n) : (n = term39) = False.
Proof. exact (@lem2498446 n (@lem2498187 n h1)). Qed.
Lemma lem2498506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2498507 (n : int) (h1 : term41 n) : (term41 n) = (~ False).
Proof. exact (MK_COMB (@lem2498506) (@lem2498505 n h1)). Qed.
Lemma lem2498509 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2498510 (n : int) (h1 : term41 n) : (term41 n) = True.
Proof. exact (TRANS (@lem2498507 n h1) (@lem2498509)). Qed.
Lemma lem2498511 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498512 (n : int) (h1 : term41 n) : (term104 n) = (imp True).
Proof. exact (MK_COMB (@lem2498511) (@lem2498510 n h1)). Qed.
Lemma lem2498513 (m : int) : (term105 m) = (term105 m).
Proof. exact (eq_refl (term105 m)). Qed.
Lemma lem2498514 (m : int) (n : int) (h1 : term41 n) : (term106 n m) = (term118 m).
Proof. exact (MK_COMB (@lem2498512 n h1) (@lem2498513 m)). Qed.
Lemma lem2498516 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem2498517 (m : int) : (term118 m) = (term105 m).
Proof. exact (@lem2498516 (term105 m)). Qed.
Lemma lem2498518 (m : int) (n : int) (h1 : term41 n) : (term106 n m) = (term105 m).
Proof. exact (TRANS (@lem2498514 m n h1) (@lem2498517 m)). Qed.
Lemma lem2498519 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498520 (m : int) (n : int) (h1 : term41 n) : (term108 n m) = (term119 m).
Proof. exact (MK_COMB (@lem2498519) (@lem2498518 m n h1)). Qed.
Lemma lem2498521 (m : int) (n : int) : (int_lt m n) = (int_lt m n).
Proof. exact (eq_refl (int_lt m n)). Qed.
Lemma lem2498522 (m : int) (n : int) (h1 : term41 n) : (term110 m n) = (term120 m n).
Proof. exact (MK_COMB (@lem2498520 m n h1) (@lem2498521 m n)). Qed.
Lemma lem2498525 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2498526 (m : int) (n : int) (h1 : term41 n) : (term112 m n) = (term121 m n).
Proof. exact (MK_COMB (@lem2498525) (@lem2498522 m n h1)). Qed.
Lemma lem2498529 (n : int) (m : int) : ((rem m n) = m) = ((rem m n) = m).
Proof. exact (eq_refl ((rem m n) = m)). Qed.
Lemma lem2498530 (m : int) (n : int) (h1 : term41 n) : (term85 n m) = (term124 n m).
Proof. exact (MK_COMB (@lem2498526 m n h1) (@lem2498529 n m)). Qed.
Lemma lem2498533 (m : int) (n : int) (h1 : term41 n) : (term93 n m) = (term125 n m).
Proof. exact (MK_COMB (@lem2498497 m n h1) (@lem2498530 m n h1)). Qed.
Lemma lem2498536 (m : int) (n : int) (h1 : term41 n) : (term125 n m) = (term93 n m).
Proof. exact (SYM (@lem2498533 m n h1)). Qed.
Lemma lem2498538 (p : Prop) (q : Prop) (r : Prop) : (term27 q p r) = (term28 p q r).
Proof. exact (or_elim (@lem2498076 p) (fun h0 : p = True => @lem2498179 q r p h0) (fun h0 : p = False => @lem2498178 q r p h0)). Qed.
Lemma lem2498539 (n : int) (m : int) : (term125 n m) = (term126 n m).
Proof. exact (@lem2498538 (term120 m n) ((div m n) = term39) ((rem m n) = m)). Qed.
Lemma lem2498550 (n : int) (m : int) : (term126 n m) = (term125 n m).
Proof. exact (SYM (@lem2498539 n m)). Qed.
Lemma lem2498551 (m : int) (n : int) (h1 : term120 m n) : term120 m n.
Proof. exact (h1). Qed.
Lemma lem2498552 (m : int) (n : int) (h1 : int_lt m n) : int_lt m n.
Proof. exact (h1). Qed.
Lemma lem2498553 (m : int) (h1 : term105 m) : term105 m.
Proof. exact (h1). Qed.
Lemma lem2498555 (q : int) (m : int) (n : int) (r : int) : term8 q m n r.
Proof. exact (EQ_MP (@lem2498058 q m n r) (@lem2498057 q m n r)). Qed.
Lemma lem2498556 (n : int) (m : int) : term127 n m.
Proof. exact (@lem2498555 term39 m n m). Qed.
Lemma lem2498557 (m : int) (n : int) : (term128 m n) = (term129 m n).
Proof. exact (@lem2318604 (term129 m n)). Qed.
Lemma lem2498583 (m : int) (n : int) : (term130 m n) = (term131 m n).
Proof. exact (@lem17045 (term105 m) (term132 m n)). Qed.
Lemma lem2498585 (n : int) (m : int) : (term133 n m) = (term133 n m).
Proof. exact (eq_refl (term133 n m)). Qed.
Lemma lem2498586 (m : int) (n : int) : (term134 m n) = (term135 m n).
Proof. exact (MK_COMB (@lem2498585 n m) (@lem2498583 m n)). Qed.
Lemma lem2498587 (m : int) (n : int) : (term136 m n) = (term134 m n).
Proof. exact (@lem17045 (m = (term137 n m)) (term138 m n)). Qed.
Lemma lem2498588 (m : int) (n : int) : (term136 m n) = (term135 m n).
Proof. exact (TRANS (@lem2498587 m n) (@lem2498586 m n)). Qed.
Lemma lem2498590 (m : int) (n : int) : (term139 m n) = (term139 m n).
Proof. exact (eq_refl (term139 m n)). Qed.
Lemma lem2498591 (m : int) (n : int) : (term140 m n) = (term141 m n).
Proof. exact (MK_COMB (@lem2498590 m n) (@lem2498588 m n)). Qed.
Lemma lem2498592 (m : int) (n : int) : (term142 m n) = (term140 m n).
Proof. exact (@lem17362 (int_lt m n) (term143 m n)). Qed.
Lemma lem2498593 (m : int) (n : int) : (term142 m n) = (term141 m n).
Proof. exact (TRANS (@lem2498592 m n) (@lem2498591 m n)). Qed.
Lemma lem2498595 (m : int) : (term119 m) = (term119 m).
Proof. exact (eq_refl (term119 m)). Qed.
Lemma lem2498596 (m : int) (n : int) : (term144 m n) = (term145 m n).
Proof. exact (MK_COMB (@lem2498595 m) (@lem2498593 m n)). Qed.
Lemma lem2498597 (m : int) (n : int) : (term146 m n) = (term144 m n).
Proof. exact (@lem17362 (term105 m) (term147 m n)). Qed.
Lemma lem2498598 (m : int) (n : int) : (term146 m n) = (term145 m n).
Proof. exact (TRANS (@lem2498597 m n) (@lem2498596 m n)). Qed.
Lemma lem2498600 (n : int) : (term148 n) = (term148 n).
Proof. exact (eq_refl (term148 n)). Qed.
Lemma lem2498601 (m : int) (n : int) : (term149 m n) = (term150 m n).
Proof. exact (MK_COMB (@lem2498600 n) (@lem2498598 m n)). Qed.
Lemma lem2498602 (m : int) (n : int) : (term151 m n) = (term149 m n).
Proof. exact (@lem17362 (term41 n) (term152 m n)). Qed.
Lemma lem2498634 (m : int) (n : int) : (term151 m n) = (term150 m n).
Proof. exact (TRANS (@lem2498602 m n) (@lem2498601 m n)). Qed.
Lemma lem2498636 (y : int) (x : int) : (term153 x y) = (term154 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2498637 (n : int) : (term41 n) = (term155 n).
Proof. exact (@lem2498636 term39 n). Qed.
Lemma lem2498639 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498640 (n : int) : (term157 n) = (term158 n).
Proof. exact (@lem2498639 (term159 n) term39). Qed.
Lemma lem2498642 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498643 (n : int) : (term162 n) = (term163 n).
Proof. exact (@lem2498642 n term164). Qed.
Lemma lem2498645 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498646 : term166 = term167.
Proof. exact (@lem2498645 term168). Qed.
Lemma lem2498647 (n : int) : (term169 n) = (term169 n).
Proof. exact (eq_refl (term169 n)). Qed.
Lemma lem2498648 (n : int) : (term163 n) = (term170 n).
Proof. exact (MK_COMB (@lem2498647 n) (@lem2498646)). Qed.
Lemma lem2498649 (n : int) : (term162 n) = (term170 n).
Proof. exact (TRANS (@lem2498643 n) (@lem2498648 n)). Qed.
Lemma lem2498650 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498651 (n : int) : (term171 n) = (term172 n).
Proof. exact (MK_COMB (@lem2498650) (@lem2498649 n)). Qed.
Lemma lem2498653 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498654 : term173 = term174.
Proof. exact (@lem2498653 (NUMERAL 0)). Qed.
Lemma lem2498655 (n : int) : (term158 n) = (term175 n).
Proof. exact (MK_COMB (@lem2498651 n) (@lem2498654)). Qed.
Lemma lem2498656 (n : int) : (term157 n) = (term175 n).
Proof. exact (TRANS (@lem2498640 n) (@lem2498655 n)). Qed.
Lemma lem2498657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2498658 (n : int) : (term176 n) = (term177 n).
Proof. exact (MK_COMB (@lem2498657) (@lem2498656 n)). Qed.
Lemma lem2498660 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498661 (n : int) : (term178 n) = (term179 n).
Proof. exact (@lem2498660 term180 n). Qed.
Lemma lem2498663 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498664 : term181 = term182.
Proof. exact (@lem2498663 term39 term164). Qed.
Lemma lem2498666 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498667 : term173 = term174.
Proof. exact (@lem2498666 (NUMERAL 0)). Qed.
Lemma lem2498668 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2498669 : term183 = term184.
Proof. exact (MK_COMB (@lem2498668) (@lem2498667)). Qed.
Lemma lem2498671 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498672 : term166 = term167.
Proof. exact (@lem2498671 term168). Qed.
Lemma lem2498673 : term182 = term185.
Proof. exact (MK_COMB (@lem2498669) (@lem2498672)). Qed.
Lemma lem2498674 : term181 = term185.
Proof. exact (TRANS (@lem2498664) (@lem2498673)). Qed.
Lemma lem2498675 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498676 : term186 = term187.
Proof. exact (MK_COMB (@lem2498675) (@lem2498674)). Qed.
Lemma lem2498677 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2498678 (n : int) : (term179 n) = (term188 n).
Proof. exact (MK_COMB (@lem2498676) (@lem2498677 n)). Qed.
Lemma lem2498679 (n : int) : (term178 n) = (term188 n).
Proof. exact (TRANS (@lem2498661 n) (@lem2498678 n)). Qed.
Lemma lem2498680 (n : int) : (term155 n) = (term189 n).
Proof. exact (MK_COMB (@lem2498658 n) (@lem2498679 n)). Qed.
Lemma lem2498681 (n : int) : (term41 n) = (term189 n).
Proof. exact (TRANS (@lem2498637 n) (@lem2498680 n)). Qed.
Lemma lem2498684 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498685 (m : int) : (term105 m) = (term190 m).
Proof. exact (@lem2498684 term39 m). Qed.
Lemma lem2498687 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498688 : term173 = term174.
Proof. exact (@lem2498687 (NUMERAL 0)). Qed.
Lemma lem2498689 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498690 : term191 = term192.
Proof. exact (MK_COMB (@lem2498689) (@lem2498688)). Qed.
Lemma lem2498691 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2498692 (m : int) : (term190 m) = (term193 m).
Proof. exact (MK_COMB (@lem2498690) (@lem2498691 m)). Qed.
Lemma lem2498694 (m : int) : (term105 m) = (term193 m).
Proof. exact (TRANS (@lem2498685 m) (@lem2498692 m)). Qed.
Lemma lem2498696 (x : int) (y : int) : (int_lt x y) = (term194 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2498697 (m : int) (n : int) : (int_lt m n) = (term194 m n).
Proof. exact (@lem2498696 m n). Qed.
Lemma lem2498699 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498700 (m : int) (n : int) : (term194 m n) = (term195 m n).
Proof. exact (@lem2498699 (term159 m) n). Qed.
Lemma lem2498702 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498703 (m : int) : (term162 m) = (term163 m).
Proof. exact (@lem2498702 m term164). Qed.
Lemma lem2498705 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498706 : term166 = term167.
Proof. exact (@lem2498705 term168). Qed.
Lemma lem2498707 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2498708 (m : int) : (term163 m) = (term170 m).
Proof. exact (MK_COMB (@lem2498707 m) (@lem2498706)). Qed.
Lemma lem2498709 (m : int) : (term162 m) = (term170 m).
Proof. exact (TRANS (@lem2498703 m) (@lem2498708 m)). Qed.
Lemma lem2498710 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498711 (m : int) : (term171 m) = (term172 m).
Proof. exact (MK_COMB (@lem2498710) (@lem2498709 m)). Qed.
Lemma lem2498712 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2498713 (m : int) (n : int) : (term195 m n) = (term196 m n).
Proof. exact (MK_COMB (@lem2498711 m) (@lem2498712 n)). Qed.
Lemma lem2498714 (m : int) (n : int) : (term194 m n) = (term196 m n).
Proof. exact (TRANS (@lem2498700 m n) (@lem2498713 m n)). Qed.
Lemma lem2498715 (m : int) (n : int) : (int_lt m n) = (term196 m n).
Proof. exact (TRANS (@lem2498697 m n) (@lem2498714 m n)). Qed.
Lemma lem2498717 (y : int) (x : int) : (term153 x y) = (term154 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2498718 (n : int) (m : int) : (term197 n m) = (term198 n m).
Proof. exact (@lem2498717 (term137 n m) m). Qed.
Lemma lem2498720 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498721 (n : int) (m : int) : (term199 n m) = (term200 n m).
Proof. exact (@lem2498720 (term159 m) (term137 n m)). Qed.
Lemma lem2498723 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498724 (m : int) : (term162 m) = (term163 m).
Proof. exact (@lem2498723 m term164). Qed.
Lemma lem2498726 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498727 : term166 = term167.
Proof. exact (@lem2498726 term168). Qed.
Lemma lem2498728 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2498729 (m : int) : (term163 m) = (term170 m).
Proof. exact (MK_COMB (@lem2498728 m) (@lem2498727)). Qed.
Lemma lem2498730 (m : int) : (term162 m) = (term170 m).
Proof. exact (TRANS (@lem2498724 m) (@lem2498729 m)). Qed.
Lemma lem2498731 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498732 (m : int) : (term171 m) = (term172 m).
Proof. exact (MK_COMB (@lem2498731) (@lem2498730 m)). Qed.
Lemma lem2498734 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498735 (n : int) (m : int) : (term201 n m) = (term202 n m).
Proof. exact (@lem2498734 (term203 n) m). Qed.
Lemma lem2498737 (x : int) (y : int) : (term204 x y) = (term205 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2498738 (n : int) : (term206 n) = (term207 n).
Proof. exact (@lem2498737 term39 n). Qed.
Lemma lem2498740 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498741 : term173 = term174.
Proof. exact (@lem2498740 (NUMERAL 0)). Qed.
Lemma lem2498742 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2498743 : term208 = term209.
Proof. exact (MK_COMB (@lem2498742) (@lem2498741)). Qed.
Lemma lem2498744 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2498745 (n : int) : (term207 n) = (term210 n).
Proof. exact (MK_COMB (@lem2498743) (@lem2498744 n)). Qed.
Lemma lem2498746 (n : int) : (term206 n) = (term210 n).
Proof. exact (TRANS (@lem2498738 n) (@lem2498745 n)). Qed.
Lemma lem2498747 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2498748 (n : int) : (term211 n) = (term212 n).
Proof. exact (MK_COMB (@lem2498747) (@lem2498746 n)). Qed.
Lemma lem2498749 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2498750 (n : int) (m : int) : (term202 n m) = (term213 n m).
Proof. exact (MK_COMB (@lem2498748 n) (@lem2498749 m)). Qed.
Lemma lem2498751 (n : int) (m : int) : (term201 n m) = (term213 n m).
Proof. exact (TRANS (@lem2498735 n m) (@lem2498750 n m)). Qed.
Lemma lem2498752 (n : int) (m : int) : (term200 n m) = (term214 n m).
Proof. exact (MK_COMB (@lem2498732 m) (@lem2498751 n m)). Qed.
Lemma lem2498753 (n : int) (m : int) : (term199 n m) = (term214 n m).
Proof. exact (TRANS (@lem2498721 n m) (@lem2498752 n m)). Qed.
Lemma lem2498754 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2498755 (n : int) (m : int) : (term215 n m) = (term216 n m).
Proof. exact (MK_COMB (@lem2498754) (@lem2498753 n m)). Qed.
Lemma lem2498757 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498758 (n : int) (m : int) : (term217 n m) = (term218 n m).
Proof. exact (@lem2498757 (term219 n m) m). Qed.
Lemma lem2498760 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498761 (n : int) (m : int) : (term220 n m) = (term221 n m).
Proof. exact (@lem2498760 (term137 n m) term164). Qed.
Lemma lem2498763 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498764 (n : int) (m : int) : (term201 n m) = (term202 n m).
Proof. exact (@lem2498763 (term203 n) m). Qed.
Lemma lem2498766 (x : int) (y : int) : (term204 x y) = (term205 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2498767 (n : int) : (term206 n) = (term207 n).
Proof. exact (@lem2498766 term39 n). Qed.
Lemma lem2498769 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498770 : term173 = term174.
Proof. exact (@lem2498769 (NUMERAL 0)). Qed.
Lemma lem2498771 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2498772 : term208 = term209.
Proof. exact (MK_COMB (@lem2498771) (@lem2498770)). Qed.
Lemma lem2498773 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2498774 (n : int) : (term207 n) = (term210 n).
Proof. exact (MK_COMB (@lem2498772) (@lem2498773 n)). Qed.
Lemma lem2498775 (n : int) : (term206 n) = (term210 n).
Proof. exact (TRANS (@lem2498767 n) (@lem2498774 n)). Qed.
Lemma lem2498776 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2498777 (n : int) : (term211 n) = (term212 n).
Proof. exact (MK_COMB (@lem2498776) (@lem2498775 n)). Qed.
Lemma lem2498778 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2498779 (n : int) (m : int) : (term202 n m) = (term213 n m).
Proof. exact (MK_COMB (@lem2498777 n) (@lem2498778 m)). Qed.
Lemma lem2498780 (n : int) (m : int) : (term201 n m) = (term213 n m).
Proof. exact (TRANS (@lem2498764 n m) (@lem2498779 n m)). Qed.
Lemma lem2498781 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2498782 (n : int) (m : int) : (term222 n m) = (term223 n m).
Proof. exact (MK_COMB (@lem2498781) (@lem2498780 n m)). Qed.
Lemma lem2498784 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498785 : term166 = term167.
Proof. exact (@lem2498784 term168). Qed.
Lemma lem2498786 (n : int) (m : int) : (term221 n m) = (term224 n m).
Proof. exact (MK_COMB (@lem2498782 n m) (@lem2498785)). Qed.
Lemma lem2498787 (n : int) (m : int) : (term220 n m) = (term224 n m).
Proof. exact (TRANS (@lem2498761 n m) (@lem2498786 n m)). Qed.
Lemma lem2498788 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498789 (n : int) (m : int) : (term225 n m) = (term226 n m).
Proof. exact (MK_COMB (@lem2498788) (@lem2498787 n m)). Qed.
Lemma lem2498790 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2498791 (n : int) (m : int) : (term218 n m) = (term227 n m).
Proof. exact (MK_COMB (@lem2498789 n m) (@lem2498790 m)). Qed.
Lemma lem2498792 (n : int) (m : int) : (term217 n m) = (term227 n m).
Proof. exact (TRANS (@lem2498758 n m) (@lem2498791 n m)). Qed.
Lemma lem2498793 (n : int) (m : int) : (term198 n m) = (term228 n m).
Proof. exact (MK_COMB (@lem2498755 n m) (@lem2498792 n m)). Qed.
Lemma lem2498794 (n : int) (m : int) : (term197 n m) = (term228 n m).
Proof. exact (TRANS (@lem2498718 n m) (@lem2498793 n m)). Qed.
Lemma lem2498796 (y : int) (x : int) : (term229 x y) = (term194 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2498797 (m : int) : (term230 m) = (term157 m).
Proof. exact (@lem2498796 m term39). Qed.
Lemma lem2498799 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498800 (m : int) : (term157 m) = (term158 m).
Proof. exact (@lem2498799 (term159 m) term39). Qed.
Lemma lem2498802 (x : int) (y : int) : (term160 x y) = (term161 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2498803 (m : int) : (term162 m) = (term163 m).
Proof. exact (@lem2498802 m term164). Qed.
Lemma lem2498805 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498806 : term166 = term167.
Proof. exact (@lem2498805 term168). Qed.
Lemma lem2498807 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2498808 (m : int) : (term163 m) = (term170 m).
Proof. exact (MK_COMB (@lem2498807 m) (@lem2498806)). Qed.
Lemma lem2498809 (m : int) : (term162 m) = (term170 m).
Proof. exact (TRANS (@lem2498803 m) (@lem2498808 m)). Qed.
Lemma lem2498810 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498811 (m : int) : (term171 m) = (term172 m).
Proof. exact (MK_COMB (@lem2498810) (@lem2498809 m)). Qed.
Lemma lem2498813 (n : nat) : (term165 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2498814 : term173 = term174.
Proof. exact (@lem2498813 (NUMERAL 0)). Qed.
Lemma lem2498815 (m : int) : (term158 m) = (term175 m).
Proof. exact (MK_COMB (@lem2498811 m) (@lem2498814)). Qed.
Lemma lem2498816 (m : int) : (term157 m) = (term175 m).
Proof. exact (TRANS (@lem2498800 m) (@lem2498815 m)). Qed.
Lemma lem2498817 (m : int) : (term230 m) = (term175 m).
Proof. exact (TRANS (@lem2498797 m) (@lem2498816 m)). Qed.
Lemma lem2498819 (y : int) (x : int) : (term231 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2498820 (n : int) (m : int) : (term232 m n) = (term233 n m).
Proof. exact (@lem2498819 (int_abs n) m). Qed.
Lemma lem2498822 (x : int) (y : int) : (int_le x y) = (term156 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2498823 (n : int) (m : int) : (term233 n m) = (term234 n m).
Proof. exact (@lem2498822 (int_abs n) m). Qed.
Lemma lem2498825 (x : int) : (term235 x) = (term236 x).
Proof. exact (EQ_MP (@lem2318515 x) (@lem2318514 x)). Qed.
Lemma lem2498826 (n : int) : (term235 n) = (term236 n).
Proof. exact (@lem2498825 n). Qed.
Lemma lem2498827 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2498828 (n : int) : (term237 n) = (term238 n).
Proof. exact (MK_COMB (@lem2498827) (@lem2498826 n)). Qed.
Lemma lem2498829 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2498830 (n : int) (m : int) : (term234 n m) = (term239 n m).
Proof. exact (MK_COMB (@lem2498828 n) (@lem2498829 m)). Qed.
Lemma lem2498831 (n : int) (m : int) : (term233 n m) = (term239 n m).
Proof. exact (TRANS (@lem2498823 n m) (@lem2498830 n m)). Qed.
Lemma lem2498832 (n : int) (m : int) : (term232 m n) = (term239 n m).
Proof. exact (TRANS (@lem2498820 n m) (@lem2498831 n m)). Qed.
Lemma lem2498833 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2498834 (m : int) : (term240 m) = (term177 m).
Proof. exact (MK_COMB (@lem2498833) (@lem2498817 m)). Qed.
Lemma lem2498835 (n : int) (m : int) : (term131 m n) = (term241 n m).
Proof. exact (MK_COMB (@lem2498834 m) (@lem2498832 n m)). Qed.
Lemma lem2498836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2498837 (n : int) (m : int) : (term133 n m) = (term242 n m).
Proof. exact (MK_COMB (@lem2498836) (@lem2498794 n m)). Qed.
Lemma lem2498838 (n : int) (m : int) : (term135 m n) = (term243 n m).
Proof. exact (MK_COMB (@lem2498837 n m) (@lem2498835 n m)). Qed.
Lemma lem2498839 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498840 (m : int) (n : int) : (term139 m n) = (term244 m n).
Proof. exact (MK_COMB (@lem2498839) (@lem2498715 m n)). Qed.
Lemma lem2498841 (n : int) (m : int) : (term141 m n) = (term245 n m).
Proof. exact (MK_COMB (@lem2498840 m n) (@lem2498838 n m)). Qed.
Lemma lem2498842 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498843 (m : int) : (term119 m) = (term246 m).
Proof. exact (MK_COMB (@lem2498842) (@lem2498694 m)). Qed.
Lemma lem2498844 (n : int) (m : int) : (term145 m n) = (term247 n m).
Proof. exact (MK_COMB (@lem2498843 m) (@lem2498841 n m)). Qed.
Lemma lem2498845 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2498846 (n : int) : (term148 n) = (term248 n).
Proof. exact (MK_COMB (@lem2498845) (@lem2498681 n)). Qed.
Lemma lem2498847 (n : int) (m : int) : (term150 m n) = (term249 n m).
Proof. exact (MK_COMB (@lem2498846 n) (@lem2498844 n m)). Qed.
Lemma lem2498848 (n : int) (m : int) : (term151 m n) = (term249 n m).
Proof. exact (TRANS (@lem2498634 m n) (@lem2498847 n m)). Qed.
Lemma lem2498852 (t : Prop) : (term250 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2498928 (n : int) (m : int) : (term251 n m) = (term249 n m).
Proof. exact (@lem2498852 (term249 n m)). Qed.
Lemma lem2498929 (n : int) : (term175 n) = (term252 n).
Proof. exact (@lem1988287 term174 (term170 n)). Qed.
Lemma lem2498941 (n : int) : (term253 n) = (term254 n).
Proof. exact (@lem1982792 term174 (term170 n)). Qed.
Lemma lem2498942 (n : int) : (term255 n) = (term256 n).
Proof. exact (@lem1982781 (real_of_int n) term257 term167). Qed.
Lemma lem2498944 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2498945 : term167 = term259.
Proof. exact (@lem2498944 term168). Qed.
Lemma lem2498947 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2498948 : term257 = term262.
Proof. exact (@lem2498947 term168). Qed.
Lemma lem2498949 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2498950 : term263 = term264.
Proof. exact (MK_COMB (@lem2498949) (@lem2498948)). Qed.
Lemma lem2498951 : term265 = term266.
Proof. exact (MK_COMB (@lem2498950) (@lem2498945)). Qed.
Lemma lem2498952 : term266 = term267.
Proof. exact (@lem1981613 term257 term167 term167 term167). Qed.
Lemma lem2498954 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2498955 : term270 = term271.
Proof. exact (@lem2498954 term168 term168). Qed.
Lemma lem2498956 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2498957 : term273 = term168.
Proof. exact (EQ_MP (@lem2498956) (@lem940073)). Qed.
Lemma lem2498958 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2498959 : term271 = term167.
Proof. exact (MK_COMB (@lem2498958) (@lem2498957)). Qed.
Lemma lem2498960 : term270 = term167.
Proof. exact (TRANS (@lem2498955) (@lem2498959)). Qed.
Lemma lem2498962 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2498963 : term265 = term276.
Proof. exact (@lem2498962 term168 term168). Qed.
Lemma lem2498964 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2498965 : term273 = term168.
Proof. exact (EQ_MP (@lem2498964) (@lem940073)). Qed.
Lemma lem2498966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2498967 : term271 = term167.
Proof. exact (MK_COMB (@lem2498966) (@lem2498965)). Qed.
Lemma lem2498968 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2498969 : term276 = term257.
Proof. exact (MK_COMB (@lem2498968) (@lem2498967)). Qed.
Lemma lem2498970 : term265 = term257.
Proof. exact (TRANS (@lem2498963) (@lem2498969)). Qed.
Lemma lem2498971 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2498972 : term277 = term278.
Proof. exact (MK_COMB (@lem2498971) (@lem2498970)). Qed.
Lemma lem2498973 : term267 = term262.
Proof. exact (MK_COMB (@lem2498972) (@lem2498960)). Qed.
Lemma lem2498974 : term266 = term262.
Proof. exact (TRANS (@lem2498952) (@lem2498973)). Qed.
Lemma lem2498975 : term265 = term262.
Proof. exact (TRANS (@lem2498951) (@lem2498974)). Qed.
Lemma lem2498977 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2498978 : term262 = term257.
Proof. exact (@lem2498977 term257). Qed.
Lemma lem2498979 : term265 = term257.
Proof. exact (TRANS (@lem2498975) (@lem2498978)). Qed.
Lemma lem2498982 (n : int) : (term280 n) = (term280 n).
Proof. exact (eq_refl (term280 n)). Qed.
Lemma lem2498983 (n : int) : (term256 n) = (term281 n).
Proof. exact (MK_COMB (@lem2498982 n) (@lem2498979)). Qed.
Lemma lem2498984 (n : int) : (term255 n) = (term281 n).
Proof. exact (TRANS (@lem2498942 n) (@lem2498983 n)). Qed.
Lemma lem2498985 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2498986 (n : int) : (term254 n) = (term282 n).
Proof. exact (MK_COMB (@lem2498985) (@lem2498984 n)). Qed.
Lemma lem2498987 (n : int) : (term282 n) = (term281 n).
Proof. exact (@lem1982721 (term281 n)). Qed.
Lemma lem2498988 (n : int) : (term254 n) = (term281 n).
Proof. exact (TRANS (@lem2498986 n) (@lem2498987 n)). Qed.
Lemma lem2498990 (n : int) : (term253 n) = (term281 n).
Proof. exact (TRANS (@lem2498941 n) (@lem2498988 n)). Qed.
Lemma lem2498991 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2498992 (n : int) : (term283 n) = (term284 n).
Proof. exact (MK_COMB (@lem2498991) (@lem2498990 n)). Qed.
Lemma lem2498993 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2498994 (n : int) : (term252 n) = (term285 n).
Proof. exact (MK_COMB (@lem2498992 n) (@lem2498993)). Qed.
Lemma lem2498995 (n : int) : (term175 n) = (term285 n).
Proof. exact (TRANS (@lem2498929 n) (@lem2498994 n)). Qed.
Lemma lem2498996 (n : int) : (term188 n) = (term286 n).
Proof. exact (@lem1988287 (real_of_int n) term185). Qed.
Lemma lem2499003 : term185 = term167.
Proof. exact (@lem1982721 term167). Qed.
Lemma lem2499006 (n : int) : (term287 n) = (term287 n).
Proof. exact (eq_refl (term287 n)). Qed.
Lemma lem2499007 (n : int) : (term288 n) = (term289 n).
Proof. exact (MK_COMB (@lem2499006 n) (@lem2499003)). Qed.
Lemma lem2499008 (n : int) : (term289 n) = (term290 n).
Proof. exact (@lem1982792 (real_of_int n) term167). Qed.
Lemma lem2499010 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499011 : term167 = term259.
Proof. exact (@lem2499010 term168). Qed.
Lemma lem2499013 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499014 : term257 = term262.
Proof. exact (@lem2499013 term168). Qed.
Lemma lem2499015 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499016 : term263 = term264.
Proof. exact (MK_COMB (@lem2499015) (@lem2499014)). Qed.
Lemma lem2499017 : term265 = term266.
Proof. exact (MK_COMB (@lem2499016) (@lem2499011)). Qed.
Lemma lem2499018 : term266 = term267.
Proof. exact (@lem1981613 term257 term167 term167 term167). Qed.
Lemma lem2499020 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499021 : term270 = term271.
Proof. exact (@lem2499020 term168 term168). Qed.
Lemma lem2499022 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499023 : term273 = term168.
Proof. exact (EQ_MP (@lem2499022) (@lem940073)). Qed.
Lemma lem2499024 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499025 : term271 = term167.
Proof. exact (MK_COMB (@lem2499024) (@lem2499023)). Qed.
Lemma lem2499026 : term270 = term167.
Proof. exact (TRANS (@lem2499021) (@lem2499025)). Qed.
Lemma lem2499028 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499029 : term265 = term276.
Proof. exact (@lem2499028 term168 term168). Qed.
Lemma lem2499030 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499031 : term273 = term168.
Proof. exact (EQ_MP (@lem2499030) (@lem940073)). Qed.
Lemma lem2499032 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499033 : term271 = term167.
Proof. exact (MK_COMB (@lem2499032) (@lem2499031)). Qed.
Lemma lem2499034 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499035 : term276 = term257.
Proof. exact (MK_COMB (@lem2499034) (@lem2499033)). Qed.
Lemma lem2499036 : term265 = term257.
Proof. exact (TRANS (@lem2499029) (@lem2499035)). Qed.
Lemma lem2499037 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2499038 : term277 = term278.
Proof. exact (MK_COMB (@lem2499037) (@lem2499036)). Qed.
Lemma lem2499039 : term267 = term262.
Proof. exact (MK_COMB (@lem2499038) (@lem2499026)). Qed.
Lemma lem2499040 : term266 = term262.
Proof. exact (TRANS (@lem2499018) (@lem2499039)). Qed.
Lemma lem2499041 : term265 = term262.
Proof. exact (TRANS (@lem2499017) (@lem2499040)). Qed.
Lemma lem2499043 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2499044 : term262 = term257.
Proof. exact (@lem2499043 term257). Qed.
Lemma lem2499045 : term265 = term257.
Proof. exact (TRANS (@lem2499041) (@lem2499044)). Qed.
Lemma lem2499046 (n : int) : (term169 n) = (term169 n).
Proof. exact (eq_refl (term169 n)). Qed.
Lemma lem2499049 (n : int) : (term290 n) = (term291 n).
Proof. exact (MK_COMB (@lem2499046 n) (@lem2499045)). Qed.
Lemma lem2499050 (n : int) : (term289 n) = (term291 n).
Proof. exact (TRANS (@lem2499008 n) (@lem2499049 n)). Qed.
Lemma lem2499051 (n : int) : (term288 n) = (term291 n).
Proof. exact (TRANS (@lem2499007 n) (@lem2499050 n)). Qed.
Lemma lem2499052 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499053 (n : int) : (term292 n) = (term293 n).
Proof. exact (MK_COMB (@lem2499052) (@lem2499051 n)). Qed.
Lemma lem2499054 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499055 (n : int) : (term286 n) = (term294 n).
Proof. exact (MK_COMB (@lem2499053 n) (@lem2499054)). Qed.
Lemma lem2499056 (n : int) : (term188 n) = (term294 n).
Proof. exact (TRANS (@lem2498996 n) (@lem2499055 n)). Qed.
Lemma lem2499057 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499058 (n : int) : (term177 n) = (term295 n).
Proof. exact (MK_COMB (@lem2499057) (@lem2498995 n)). Qed.
Lemma lem2499059 (n : int) : (term189 n) = (term296 n).
Proof. exact (MK_COMB (@lem2499058 n) (@lem2499056 n)). Qed.
Lemma lem2499060 (m : int) : (term193 m) = (term297 m).
Proof. exact (@lem1988287 (real_of_int m) term174). Qed.
Lemma lem2499066 (m : int) : (term298 m) = (term299 m).
Proof. exact (@lem1982792 (real_of_int m) term174). Qed.
Lemma lem2499068 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499069 : term174 = term300.
Proof. exact (@lem2499068 (NUMERAL 0)). Qed.
Lemma lem2499071 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499072 : term257 = term262.
Proof. exact (@lem2499071 term168). Qed.
Lemma lem2499073 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499074 : term263 = term264.
Proof. exact (MK_COMB (@lem2499073) (@lem2499072)). Qed.
Lemma lem2499075 : term301 = term302.
Proof. exact (MK_COMB (@lem2499074) (@lem2499069)). Qed.
Lemma lem2499076 : term302 = term303.
Proof. exact (@lem1981613 term257 term174 term167 term167). Qed.
Lemma lem2499078 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499079 : term270 = term271.
Proof. exact (@lem2499078 term168 term168). Qed.
Lemma lem2499080 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499081 : term273 = term168.
Proof. exact (EQ_MP (@lem2499080) (@lem940073)). Qed.
Lemma lem2499082 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499083 : term271 = term167.
Proof. exact (MK_COMB (@lem2499082) (@lem2499081)). Qed.
Lemma lem2499084 : term270 = term167.
Proof. exact (TRANS (@lem2499079) (@lem2499083)). Qed.
Lemma lem2499086 (x : nat) : (term304 x) = term174.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem2499087 : term301 = term174.
Proof. exact (@lem2499086 term168). Qed.
Lemma lem2499088 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2499089 : term305 = term306.
Proof. exact (MK_COMB (@lem2499088) (@lem2499087)). Qed.
Lemma lem2499090 : term303 = term300.
Proof. exact (MK_COMB (@lem2499089) (@lem2499084)). Qed.
Lemma lem2499091 : term302 = term300.
Proof. exact (TRANS (@lem2499076) (@lem2499090)). Qed.
Lemma lem2499092 : term301 = term300.
Proof. exact (TRANS (@lem2499075) (@lem2499091)). Qed.
Lemma lem2499094 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2499095 : term300 = term174.
Proof. exact (@lem2499094 term174). Qed.
Lemma lem2499096 : term301 = term174.
Proof. exact (TRANS (@lem2499092) (@lem2499095)). Qed.
Lemma lem2499097 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2499098 (m : int) : (term299 m) = (term307 m).
Proof. exact (MK_COMB (@lem2499097 m) (@lem2499096)). Qed.
Lemma lem2499099 (m : int) : (term307 m) = (real_of_int m).
Proof. exact (@lem1982723 (real_of_int m)). Qed.
Lemma lem2499100 (m : int) : (term299 m) = (real_of_int m).
Proof. exact (TRANS (@lem2499098 m) (@lem2499099 m)). Qed.
Lemma lem2499102 (m : int) : (term298 m) = (real_of_int m).
Proof. exact (TRANS (@lem2499066 m) (@lem2499100 m)). Qed.
Lemma lem2499103 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499104 (m : int) : (term308 m) = (term309 m).
Proof. exact (MK_COMB (@lem2499103) (@lem2499102 m)). Qed.
Lemma lem2499105 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499106 (m : int) : (term297 m) = (term310 m).
Proof. exact (MK_COMB (@lem2499104 m) (@lem2499105)). Qed.
Lemma lem2499107 (m : int) : (term193 m) = (term310 m).
Proof. exact (TRANS (@lem2499060 m) (@lem2499106 m)). Qed.
Lemma lem2499108 (n : int) (m : int) : (term196 m n) = (term311 n m).
Proof. exact (@lem1988287 (real_of_int n) (term170 m)). Qed.
Lemma lem2499120 (n : int) (m : int) : (term312 n m) = (term313 n m).
Proof. exact (@lem1982792 (real_of_int n) (term170 m)). Qed.
Lemma lem2499121 (m : int) : (term255 m) = (term256 m).
Proof. exact (@lem1982781 (real_of_int m) term257 term167). Qed.
Lemma lem2499123 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499124 : term167 = term259.
Proof. exact (@lem2499123 term168). Qed.
Lemma lem2499126 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499127 : term257 = term262.
Proof. exact (@lem2499126 term168). Qed.
Lemma lem2499128 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499129 : term263 = term264.
Proof. exact (MK_COMB (@lem2499128) (@lem2499127)). Qed.
Lemma lem2499130 : term265 = term266.
Proof. exact (MK_COMB (@lem2499129) (@lem2499124)). Qed.
Lemma lem2499131 : term266 = term267.
Proof. exact (@lem1981613 term257 term167 term167 term167). Qed.
Lemma lem2499133 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499134 : term270 = term271.
Proof. exact (@lem2499133 term168 term168). Qed.
Lemma lem2499135 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499136 : term273 = term168.
Proof. exact (EQ_MP (@lem2499135) (@lem940073)). Qed.
Lemma lem2499137 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499138 : term271 = term167.
Proof. exact (MK_COMB (@lem2499137) (@lem2499136)). Qed.
Lemma lem2499139 : term270 = term167.
Proof. exact (TRANS (@lem2499134) (@lem2499138)). Qed.
Lemma lem2499141 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499142 : term265 = term276.
Proof. exact (@lem2499141 term168 term168). Qed.
Lemma lem2499143 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499144 : term273 = term168.
Proof. exact (EQ_MP (@lem2499143) (@lem940073)). Qed.
Lemma lem2499145 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499146 : term271 = term167.
Proof. exact (MK_COMB (@lem2499145) (@lem2499144)). Qed.
Lemma lem2499147 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499148 : term276 = term257.
Proof. exact (MK_COMB (@lem2499147) (@lem2499146)). Qed.
Lemma lem2499149 : term265 = term257.
Proof. exact (TRANS (@lem2499142) (@lem2499148)). Qed.
Lemma lem2499150 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2499151 : term277 = term278.
Proof. exact (MK_COMB (@lem2499150) (@lem2499149)). Qed.
Lemma lem2499152 : term267 = term262.
Proof. exact (MK_COMB (@lem2499151) (@lem2499139)). Qed.
Lemma lem2499153 : term266 = term262.
Proof. exact (TRANS (@lem2499131) (@lem2499152)). Qed.
Lemma lem2499154 : term265 = term262.
Proof. exact (TRANS (@lem2499130) (@lem2499153)). Qed.
Lemma lem2499156 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2499157 : term262 = term257.
Proof. exact (@lem2499156 term257). Qed.
Lemma lem2499158 : term265 = term257.
Proof. exact (TRANS (@lem2499154) (@lem2499157)). Qed.
Lemma lem2499161 (m : int) : (term280 m) = (term280 m).
Proof. exact (eq_refl (term280 m)). Qed.
Lemma lem2499162 (m : int) : (term256 m) = (term281 m).
Proof. exact (MK_COMB (@lem2499161 m) (@lem2499158)). Qed.
Lemma lem2499163 (m : int) : (term255 m) = (term281 m).
Proof. exact (TRANS (@lem2499121 m) (@lem2499162 m)). Qed.
Lemma lem2499164 (n : int) : (term169 n) = (term169 n).
Proof. exact (eq_refl (term169 n)). Qed.
Lemma lem2499165 (n : int) (m : int) : (term313 n m) = (term314 n m).
Proof. exact (MK_COMB (@lem2499164 n) (@lem2499163 m)). Qed.
Lemma lem2499170 (m : int) (n : int) : (term314 n m) = (term315 m n).
Proof. exact (@lem1982757 (term316 m) (real_of_int n) term257). Qed.
Lemma lem2499171 (m : int) (n : int) : (term313 n m) = (term315 m n).
Proof. exact (TRANS (@lem2499165 n m) (@lem2499170 m n)). Qed.
Lemma lem2499173 (m : int) (n : int) : (term312 n m) = (term315 m n).
Proof. exact (TRANS (@lem2499120 n m) (@lem2499171 m n)). Qed.
Lemma lem2499174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499175 (m : int) (n : int) : (term317 n m) = (term318 m n).
Proof. exact (MK_COMB (@lem2499174) (@lem2499173 m n)). Qed.
Lemma lem2499176 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499177 (m : int) (n : int) : (term311 n m) = (term319 m n).
Proof. exact (MK_COMB (@lem2499175 m n) (@lem2499176)). Qed.
Lemma lem2499178 (m : int) (n : int) : (term196 m n) = (term319 m n).
Proof. exact (TRANS (@lem2499108 n m) (@lem2499177 m n)). Qed.
Lemma lem2499179 (n : int) (m : int) : (term214 n m) = (term320 n m).
Proof. exact (@lem1988287 (term213 n m) (term170 m)). Qed.
Lemma lem2499186 (m : int) : (term170 m) = (term170 m).
Proof. exact (eq_refl (term170 m)). Qed.
Lemma lem2499187 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2499194 (n : int) : (term210 n) = term174.
Proof. exact (@lem1982729 (real_of_int n)). Qed.
Lemma lem2499195 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499196 (n : int) : (term212 n) = term184.
Proof. exact (MK_COMB (@lem2499195) (@lem2499194 n)). Qed.
Lemma lem2499197 (n : int) (m : int) : (term213 n m) = (term321 m).
Proof. exact (MK_COMB (@lem2499196 n) (@lem2499187 m)). Qed.
Lemma lem2499198 (m : int) : (term321 m) = (real_of_int m).
Proof. exact (@lem1982721 (real_of_int m)). Qed.
Lemma lem2499199 (n : int) (m : int) : (term213 n m) = (real_of_int m).
Proof. exact (TRANS (@lem2499197 n m) (@lem2499198 m)). Qed.
Lemma lem2499200 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2499201 (n : int) (m : int) : (term322 n m) = (term287 m).
Proof. exact (MK_COMB (@lem2499200) (@lem2499199 n m)). Qed.
Lemma lem2499202 (n : int) (m : int) : (term323 n m) = (term324 m).
Proof. exact (MK_COMB (@lem2499201 n m) (@lem2499186 m)). Qed.
Lemma lem2499203 (m : int) : (term324 m) = (term325 m).
Proof. exact (@lem1982792 (real_of_int m) (term170 m)). Qed.
Lemma lem2499204 (m : int) : (term255 m) = (term256 m).
Proof. exact (@lem1982781 (real_of_int m) term257 term167). Qed.
Lemma lem2499206 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499207 : term167 = term259.
Proof. exact (@lem2499206 term168). Qed.
Lemma lem2499209 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499210 : term257 = term262.
Proof. exact (@lem2499209 term168). Qed.
Lemma lem2499211 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499212 : term263 = term264.
Proof. exact (MK_COMB (@lem2499211) (@lem2499210)). Qed.
Lemma lem2499213 : term265 = term266.
Proof. exact (MK_COMB (@lem2499212) (@lem2499207)). Qed.
Lemma lem2499214 : term266 = term267.
Proof. exact (@lem1981613 term257 term167 term167 term167). Qed.
Lemma lem2499216 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499217 : term270 = term271.
Proof. exact (@lem2499216 term168 term168). Qed.
Lemma lem2499218 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499219 : term273 = term168.
Proof. exact (EQ_MP (@lem2499218) (@lem940073)). Qed.
Lemma lem2499220 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499221 : term271 = term167.
Proof. exact (MK_COMB (@lem2499220) (@lem2499219)). Qed.
Lemma lem2499222 : term270 = term167.
Proof. exact (TRANS (@lem2499217) (@lem2499221)). Qed.
Lemma lem2499224 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499225 : term265 = term276.
Proof. exact (@lem2499224 term168 term168). Qed.
Lemma lem2499226 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499227 : term273 = term168.
Proof. exact (EQ_MP (@lem2499226) (@lem940073)). Qed.
Lemma lem2499228 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499229 : term271 = term167.
Proof. exact (MK_COMB (@lem2499228) (@lem2499227)). Qed.
Lemma lem2499230 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499231 : term276 = term257.
Proof. exact (MK_COMB (@lem2499230) (@lem2499229)). Qed.
Lemma lem2499232 : term265 = term257.
Proof. exact (TRANS (@lem2499225) (@lem2499231)). Qed.
Lemma lem2499233 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2499234 : term277 = term278.
Proof. exact (MK_COMB (@lem2499233) (@lem2499232)). Qed.
Lemma lem2499235 : term267 = term262.
Proof. exact (MK_COMB (@lem2499234) (@lem2499222)). Qed.
Lemma lem2499236 : term266 = term262.
Proof. exact (TRANS (@lem2499214) (@lem2499235)). Qed.
Lemma lem2499237 : term265 = term262.
Proof. exact (TRANS (@lem2499213) (@lem2499236)). Qed.
Lemma lem2499239 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2499240 : term262 = term257.
Proof. exact (@lem2499239 term257). Qed.
Lemma lem2499241 : term265 = term257.
Proof. exact (TRANS (@lem2499237) (@lem2499240)). Qed.
Lemma lem2499244 (m : int) : (term280 m) = (term280 m).
Proof. exact (eq_refl (term280 m)). Qed.
Lemma lem2499245 (m : int) : (term256 m) = (term281 m).
Proof. exact (MK_COMB (@lem2499244 m) (@lem2499241)). Qed.
Lemma lem2499246 (m : int) : (term255 m) = (term281 m).
Proof. exact (TRANS (@lem2499204 m) (@lem2499245 m)). Qed.
Lemma lem2499247 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2499248 (m : int) : (term325 m) = (term326 m).
Proof. exact (MK_COMB (@lem2499247 m) (@lem2499246 m)). Qed.
Lemma lem2499249 (m : int) : (term326 m) = (term327 m).
Proof. exact (@lem1982763 (real_of_int m) (term316 m) term257). Qed.
Lemma lem2499250 (m : int) : (term328 m) = (term329 m).
Proof. exact (@lem1982715 term257 (real_of_int m)). Qed.
Lemma lem2499252 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499253 : term167 = term259.
Proof. exact (@lem2499252 term168). Qed.
Lemma lem2499255 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499256 : term257 = term262.
Proof. exact (@lem2499255 term168). Qed.
Lemma lem2499257 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499258 : term330 = term331.
Proof. exact (MK_COMB (@lem2499257) (@lem2499256)). Qed.
Lemma lem2499259 : term332 = term333.
Proof. exact (MK_COMB (@lem2499258) (@lem2499253)). Qed.
Lemma lem2499260 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2499262 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499263 : term336 = term337.
Proof. exact (@lem2499262 (NUMERAL 0) term168). Qed.
Lemma lem2499264 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499265 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499266 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499265 h1) (fun h1 : term337 = True => @lem2499264)). Qed.
Lemma lem2499267 : term337 = True.
Proof. exact (EQ_MP (@lem2499266) (@lem2499264)). Qed.
Lemma lem2499268 : term336 = True.
Proof. exact (TRANS (@lem2499263) (@lem2499267)). Qed.
Lemma lem2499269 : True = term336.
Proof. exact (SYM (@lem2499268)). Qed.
Lemma lem2499270 : term336.
Proof. exact (EQ_MP (@lem2499269) (@lem0)). Qed.
Lemma lem2499271 : term339.
Proof. exact (@lem2499260 (@lem2499270)). Qed.
Lemma lem2499273 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499274 : term336 = term337.
Proof. exact (@lem2499273 (NUMERAL 0) term168). Qed.
Lemma lem2499275 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499276 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499277 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499276 h1) (fun h1 : term337 = True => @lem2499275)). Qed.
Lemma lem2499278 : term337 = True.
Proof. exact (EQ_MP (@lem2499277) (@lem2499275)). Qed.
Lemma lem2499279 : term336 = True.
Proof. exact (TRANS (@lem2499274) (@lem2499278)). Qed.
Lemma lem2499280 : True = term336.
Proof. exact (SYM (@lem2499279)). Qed.
Lemma lem2499281 : term336.
Proof. exact (EQ_MP (@lem2499280) (@lem0)). Qed.
Lemma lem2499282 : term340.
Proof. exact (@lem2499271 (@lem2499281)). Qed.
Lemma lem2499284 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499285 : term336 = term337.
Proof. exact (@lem2499284 (NUMERAL 0) term168). Qed.
Lemma lem2499286 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499287 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499288 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499287 h1) (fun h1 : term337 = True => @lem2499286)). Qed.
Lemma lem2499289 : term337 = True.
Proof. exact (EQ_MP (@lem2499288) (@lem2499286)). Qed.
Lemma lem2499290 : term336 = True.
Proof. exact (TRANS (@lem2499285) (@lem2499289)). Qed.
Lemma lem2499291 : True = term336.
Proof. exact (SYM (@lem2499290)). Qed.
Lemma lem2499292 : term336.
Proof. exact (EQ_MP (@lem2499291) (@lem0)). Qed.
Lemma lem2499293 : term341.
Proof. exact (@lem2499282 (@lem2499292)). Qed.
Lemma lem2499295 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499296 : term270 = term271.
Proof. exact (@lem2499295 term168 term168). Qed.
Lemma lem2499297 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499298 : term273 = term168.
Proof. exact (EQ_MP (@lem2499297) (@lem940073)). Qed.
Lemma lem2499299 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499300 : term271 = term167.
Proof. exact (MK_COMB (@lem2499299) (@lem2499298)). Qed.
Lemma lem2499301 : term270 = term167.
Proof. exact (TRANS (@lem2499296) (@lem2499300)). Qed.
Lemma lem2499303 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499304 : term265 = term276.
Proof. exact (@lem2499303 term168 term168). Qed.
Lemma lem2499305 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499306 : term273 = term168.
Proof. exact (EQ_MP (@lem2499305) (@lem940073)). Qed.
Lemma lem2499307 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499308 : term271 = term167.
Proof. exact (MK_COMB (@lem2499307) (@lem2499306)). Qed.
Lemma lem2499309 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499310 : term276 = term257.
Proof. exact (MK_COMB (@lem2499309) (@lem2499308)). Qed.
Lemma lem2499311 : term265 = term257.
Proof. exact (TRANS (@lem2499304) (@lem2499310)). Qed.
Lemma lem2499312 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499313 : term342 = term330.
Proof. exact (MK_COMB (@lem2499312) (@lem2499311)). Qed.
Lemma lem2499314 : term343 = term332.
Proof. exact (MK_COMB (@lem2499313) (@lem2499301)). Qed.
Lemma lem2499316 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2499317 : term332 = term174.
Proof. exact (@lem2499316 term168). Qed.
Lemma lem2499318 : term343 = term174.
Proof. exact (TRANS (@lem2499314) (@lem2499317)). Qed.
Lemma lem2499319 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499320 : term345 = term209.
Proof. exact (MK_COMB (@lem2499319) (@lem2499318)). Qed.
Lemma lem2499321 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2499322 : term346 = term347.
Proof. exact (MK_COMB (@lem2499320) (@lem2499321)). Qed.
Lemma lem2499324 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2499325 : term347 = term174.
Proof. exact (@lem2499324 term168). Qed.
Lemma lem2499326 : term346 = term174.
Proof. exact (TRANS (@lem2499322) (@lem2499325)). Qed.
Lemma lem2499328 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499329 : term270 = term271.
Proof. exact (@lem2499328 term168 term168). Qed.
Lemma lem2499330 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499331 : term273 = term168.
Proof. exact (EQ_MP (@lem2499330) (@lem940073)). Qed.
Lemma lem2499332 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499333 : term271 = term167.
Proof. exact (MK_COMB (@lem2499332) (@lem2499331)). Qed.
Lemma lem2499334 : term270 = term167.
Proof. exact (TRANS (@lem2499329) (@lem2499333)). Qed.
Lemma lem2499335 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2499336 : term349 = term347.
Proof. exact (MK_COMB (@lem2499335) (@lem2499334)). Qed.
Lemma lem2499338 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2499339 : term347 = term174.
Proof. exact (@lem2499338 term168). Qed.
Lemma lem2499340 : term349 = term174.
Proof. exact (TRANS (@lem2499336) (@lem2499339)). Qed.
Lemma lem2499341 : term174 = term349.
Proof. exact (SYM (@lem2499340)). Qed.
Lemma lem2499342 : term346 = term349.
Proof. exact (TRANS (@lem2499326) (@lem2499341)). Qed.
Lemma lem2499343 : term333 = term300.
Proof. exact (@lem2499293 (@lem2499342)). Qed.
Lemma lem2499344 : term332 = term300.
Proof. exact (TRANS (@lem2499259) (@lem2499343)). Qed.
Lemma lem2499346 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2499347 : term300 = term174.
Proof. exact (@lem2499346 term174). Qed.
Lemma lem2499348 : term332 = term174.
Proof. exact (TRANS (@lem2499344) (@lem2499347)). Qed.
Lemma lem2499349 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499350 : term350 = term209.
Proof. exact (MK_COMB (@lem2499349) (@lem2499348)). Qed.
Lemma lem2499351 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2499352 (m : int) : (term329 m) = (term210 m).
Proof. exact (MK_COMB (@lem2499350) (@lem2499351 m)). Qed.
Lemma lem2499353 (m : int) : (term328 m) = (term210 m).
Proof. exact (TRANS (@lem2499250 m) (@lem2499352 m)). Qed.
Lemma lem2499354 (m : int) : (term210 m) = term174.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2499355 (m : int) : (term328 m) = term174.
Proof. exact (TRANS (@lem2499353 m) (@lem2499354 m)). Qed.
Lemma lem2499356 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499357 (m : int) : (term351 m) = term184.
Proof. exact (MK_COMB (@lem2499356) (@lem2499355 m)). Qed.
Lemma lem2499358 : term257 = term257.
Proof. exact (eq_refl term257). Qed.
Lemma lem2499359 (m : int) : (term327 m) = term352.
Proof. exact (MK_COMB (@lem2499357 m) (@lem2499358)). Qed.
Lemma lem2499360 (m : int) : (term326 m) = term352.
Proof. exact (TRANS (@lem2499249 m) (@lem2499359 m)). Qed.
Lemma lem2499361 : term352 = term257.
Proof. exact (@lem1982721 term257). Qed.
Lemma lem2499362 (m : int) : (term326 m) = term257.
Proof. exact (TRANS (@lem2499360 m) (@lem2499361)). Qed.
Lemma lem2499363 (m : int) : (term325 m) = term257.
Proof. exact (TRANS (@lem2499248 m) (@lem2499362 m)). Qed.
Lemma lem2499364 (m : int) : (term324 m) = term257.
Proof. exact (TRANS (@lem2499203 m) (@lem2499363 m)). Qed.
Lemma lem2499365 (n : int) (m : int) : (term323 n m) = term257.
Proof. exact (TRANS (@lem2499202 n m) (@lem2499364 m)). Qed.
Lemma lem2499366 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499367 (n : int) (m : int) : (term353 n m) = term354.
Proof. exact (MK_COMB (@lem2499366) (@lem2499365 n m)). Qed.
Lemma lem2499368 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499369 (n : int) (m : int) : (term320 n m) = term355.
Proof. exact (MK_COMB (@lem2499367 n m) (@lem2499368)). Qed.
Lemma lem2499370 (n : int) (m : int) : (term214 n m) = term355.
Proof. exact (TRANS (@lem2499179 n m) (@lem2499369 n m)). Qed.
Lemma lem2499371 (n : int) (m : int) : (term227 n m) = (term356 n m).
Proof. exact (@lem1988287 (real_of_int m) (term224 n m)). Qed.
Lemma lem2499372 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2499373 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2499380 (n : int) : (term210 n) = term174.
Proof. exact (@lem1982729 (real_of_int n)). Qed.
Lemma lem2499381 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499382 (n : int) : (term212 n) = term184.
Proof. exact (MK_COMB (@lem2499381) (@lem2499380 n)). Qed.
Lemma lem2499383 (n : int) (m : int) : (term213 n m) = (term321 m).
Proof. exact (MK_COMB (@lem2499382 n) (@lem2499373 m)). Qed.
Lemma lem2499384 (m : int) : (term321 m) = (real_of_int m).
Proof. exact (@lem1982721 (real_of_int m)). Qed.
Lemma lem2499385 (n : int) (m : int) : (term213 n m) = (real_of_int m).
Proof. exact (TRANS (@lem2499383 n m) (@lem2499384 m)). Qed.
Lemma lem2499386 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499387 (n : int) (m : int) : (term223 n m) = (term169 m).
Proof. exact (MK_COMB (@lem2499386) (@lem2499385 n m)). Qed.
Lemma lem2499390 (n : int) (m : int) : (term224 n m) = (term170 m).
Proof. exact (MK_COMB (@lem2499387 n m) (@lem2499372)). Qed.
Lemma lem2499393 (m : int) : (term287 m) = (term287 m).
Proof. exact (eq_refl (term287 m)). Qed.
Lemma lem2499394 (n : int) (m : int) : (term357 n m) = (term324 m).
Proof. exact (MK_COMB (@lem2499393 m) (@lem2499390 n m)). Qed.
Lemma lem2499395 (m : int) : (term324 m) = (term325 m).
Proof. exact (@lem1982792 (real_of_int m) (term170 m)). Qed.
Lemma lem2499396 (m : int) : (term255 m) = (term256 m).
Proof. exact (@lem1982781 (real_of_int m) term257 term167). Qed.
Lemma lem2499398 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499399 : term167 = term259.
Proof. exact (@lem2499398 term168). Qed.
Lemma lem2499401 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499402 : term257 = term262.
Proof. exact (@lem2499401 term168). Qed.
Lemma lem2499403 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499404 : term263 = term264.
Proof. exact (MK_COMB (@lem2499403) (@lem2499402)). Qed.
Lemma lem2499405 : term265 = term266.
Proof. exact (MK_COMB (@lem2499404) (@lem2499399)). Qed.
Lemma lem2499406 : term266 = term267.
Proof. exact (@lem1981613 term257 term167 term167 term167). Qed.
Lemma lem2499408 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499409 : term270 = term271.
Proof. exact (@lem2499408 term168 term168). Qed.
Lemma lem2499410 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499411 : term273 = term168.
Proof. exact (EQ_MP (@lem2499410) (@lem940073)). Qed.
Lemma lem2499412 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499413 : term271 = term167.
Proof. exact (MK_COMB (@lem2499412) (@lem2499411)). Qed.
Lemma lem2499414 : term270 = term167.
Proof. exact (TRANS (@lem2499409) (@lem2499413)). Qed.
Lemma lem2499416 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499417 : term265 = term276.
Proof. exact (@lem2499416 term168 term168). Qed.
Lemma lem2499418 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499419 : term273 = term168.
Proof. exact (EQ_MP (@lem2499418) (@lem940073)). Qed.
Lemma lem2499420 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499421 : term271 = term167.
Proof. exact (MK_COMB (@lem2499420) (@lem2499419)). Qed.
Lemma lem2499422 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499423 : term276 = term257.
Proof. exact (MK_COMB (@lem2499422) (@lem2499421)). Qed.
Lemma lem2499424 : term265 = term257.
Proof. exact (TRANS (@lem2499417) (@lem2499423)). Qed.
Lemma lem2499425 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2499426 : term277 = term278.
Proof. exact (MK_COMB (@lem2499425) (@lem2499424)). Qed.
Lemma lem2499427 : term267 = term262.
Proof. exact (MK_COMB (@lem2499426) (@lem2499414)). Qed.
Lemma lem2499428 : term266 = term262.
Proof. exact (TRANS (@lem2499406) (@lem2499427)). Qed.
Lemma lem2499429 : term265 = term262.
Proof. exact (TRANS (@lem2499405) (@lem2499428)). Qed.
Lemma lem2499431 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2499432 : term262 = term257.
Proof. exact (@lem2499431 term257). Qed.
Lemma lem2499433 : term265 = term257.
Proof. exact (TRANS (@lem2499429) (@lem2499432)). Qed.
Lemma lem2499436 (m : int) : (term280 m) = (term280 m).
Proof. exact (eq_refl (term280 m)). Qed.
Lemma lem2499437 (m : int) : (term256 m) = (term281 m).
Proof. exact (MK_COMB (@lem2499436 m) (@lem2499433)). Qed.
Lemma lem2499438 (m : int) : (term255 m) = (term281 m).
Proof. exact (TRANS (@lem2499396 m) (@lem2499437 m)). Qed.
Lemma lem2499439 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2499440 (m : int) : (term325 m) = (term326 m).
Proof. exact (MK_COMB (@lem2499439 m) (@lem2499438 m)). Qed.
Lemma lem2499441 (m : int) : (term326 m) = (term327 m).
Proof. exact (@lem1982763 (real_of_int m) (term316 m) term257). Qed.
Lemma lem2499442 (m : int) : (term328 m) = (term329 m).
Proof. exact (@lem1982715 term257 (real_of_int m)). Qed.
Lemma lem2499444 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499445 : term167 = term259.
Proof. exact (@lem2499444 term168). Qed.
Lemma lem2499447 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499448 : term257 = term262.
Proof. exact (@lem2499447 term168). Qed.
Lemma lem2499449 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499450 : term330 = term331.
Proof. exact (MK_COMB (@lem2499449) (@lem2499448)). Qed.
Lemma lem2499451 : term332 = term333.
Proof. exact (MK_COMB (@lem2499450) (@lem2499445)). Qed.
Lemma lem2499452 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2499454 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499455 : term336 = term337.
Proof. exact (@lem2499454 (NUMERAL 0) term168). Qed.
Lemma lem2499456 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499457 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499458 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499457 h1) (fun h1 : term337 = True => @lem2499456)). Qed.
Lemma lem2499459 : term337 = True.
Proof. exact (EQ_MP (@lem2499458) (@lem2499456)). Qed.
Lemma lem2499460 : term336 = True.
Proof. exact (TRANS (@lem2499455) (@lem2499459)). Qed.
Lemma lem2499461 : True = term336.
Proof. exact (SYM (@lem2499460)). Qed.
Lemma lem2499462 : term336.
Proof. exact (EQ_MP (@lem2499461) (@lem0)). Qed.
Lemma lem2499463 : term339.
Proof. exact (@lem2499452 (@lem2499462)). Qed.
Lemma lem2499465 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499466 : term336 = term337.
Proof. exact (@lem2499465 (NUMERAL 0) term168). Qed.
Lemma lem2499467 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499468 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499469 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499468 h1) (fun h1 : term337 = True => @lem2499467)). Qed.
Lemma lem2499470 : term337 = True.
Proof. exact (EQ_MP (@lem2499469) (@lem2499467)). Qed.
Lemma lem2499471 : term336 = True.
Proof. exact (TRANS (@lem2499466) (@lem2499470)). Qed.
Lemma lem2499472 : True = term336.
Proof. exact (SYM (@lem2499471)). Qed.
Lemma lem2499473 : term336.
Proof. exact (EQ_MP (@lem2499472) (@lem0)). Qed.
Lemma lem2499474 : term340.
Proof. exact (@lem2499463 (@lem2499473)). Qed.
Lemma lem2499476 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499477 : term336 = term337.
Proof. exact (@lem2499476 (NUMERAL 0) term168). Qed.
Lemma lem2499478 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499479 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499480 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499479 h1) (fun h1 : term337 = True => @lem2499478)). Qed.
Lemma lem2499481 : term337 = True.
Proof. exact (EQ_MP (@lem2499480) (@lem2499478)). Qed.
Lemma lem2499482 : term336 = True.
Proof. exact (TRANS (@lem2499477) (@lem2499481)). Qed.
Lemma lem2499483 : True = term336.
Proof. exact (SYM (@lem2499482)). Qed.
Lemma lem2499484 : term336.
Proof. exact (EQ_MP (@lem2499483) (@lem0)). Qed.
Lemma lem2499485 : term341.
Proof. exact (@lem2499474 (@lem2499484)). Qed.
Lemma lem2499487 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499488 : term270 = term271.
Proof. exact (@lem2499487 term168 term168). Qed.
Lemma lem2499489 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499490 : term273 = term168.
Proof. exact (EQ_MP (@lem2499489) (@lem940073)). Qed.
Lemma lem2499491 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499492 : term271 = term167.
Proof. exact (MK_COMB (@lem2499491) (@lem2499490)). Qed.
Lemma lem2499493 : term270 = term167.
Proof. exact (TRANS (@lem2499488) (@lem2499492)). Qed.
Lemma lem2499495 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499496 : term265 = term276.
Proof. exact (@lem2499495 term168 term168). Qed.
Lemma lem2499497 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499498 : term273 = term168.
Proof. exact (EQ_MP (@lem2499497) (@lem940073)). Qed.
Lemma lem2499499 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499500 : term271 = term167.
Proof. exact (MK_COMB (@lem2499499) (@lem2499498)). Qed.
Lemma lem2499501 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499502 : term276 = term257.
Proof. exact (MK_COMB (@lem2499501) (@lem2499500)). Qed.
Lemma lem2499503 : term265 = term257.
Proof. exact (TRANS (@lem2499496) (@lem2499502)). Qed.
Lemma lem2499504 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499505 : term342 = term330.
Proof. exact (MK_COMB (@lem2499504) (@lem2499503)). Qed.
Lemma lem2499506 : term343 = term332.
Proof. exact (MK_COMB (@lem2499505) (@lem2499493)). Qed.
Lemma lem2499508 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2499509 : term332 = term174.
Proof. exact (@lem2499508 term168). Qed.
Lemma lem2499510 : term343 = term174.
Proof. exact (TRANS (@lem2499506) (@lem2499509)). Qed.
Lemma lem2499511 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499512 : term345 = term209.
Proof. exact (MK_COMB (@lem2499511) (@lem2499510)). Qed.
Lemma lem2499513 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2499514 : term346 = term347.
Proof. exact (MK_COMB (@lem2499512) (@lem2499513)). Qed.
Lemma lem2499516 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2499517 : term347 = term174.
Proof. exact (@lem2499516 term168). Qed.
Lemma lem2499518 : term346 = term174.
Proof. exact (TRANS (@lem2499514) (@lem2499517)). Qed.
Lemma lem2499520 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499521 : term270 = term271.
Proof. exact (@lem2499520 term168 term168). Qed.
Lemma lem2499522 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499523 : term273 = term168.
Proof. exact (EQ_MP (@lem2499522) (@lem940073)). Qed.
Lemma lem2499524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499525 : term271 = term167.
Proof. exact (MK_COMB (@lem2499524) (@lem2499523)). Qed.
Lemma lem2499526 : term270 = term167.
Proof. exact (TRANS (@lem2499521) (@lem2499525)). Qed.
Lemma lem2499527 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2499528 : term349 = term347.
Proof. exact (MK_COMB (@lem2499527) (@lem2499526)). Qed.
Lemma lem2499530 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2499531 : term347 = term174.
Proof. exact (@lem2499530 term168). Qed.
Lemma lem2499532 : term349 = term174.
Proof. exact (TRANS (@lem2499528) (@lem2499531)). Qed.
Lemma lem2499533 : term174 = term349.
Proof. exact (SYM (@lem2499532)). Qed.
Lemma lem2499534 : term346 = term349.
Proof. exact (TRANS (@lem2499518) (@lem2499533)). Qed.
Lemma lem2499535 : term333 = term300.
Proof. exact (@lem2499485 (@lem2499534)). Qed.
Lemma lem2499536 : term332 = term300.
Proof. exact (TRANS (@lem2499451) (@lem2499535)). Qed.
Lemma lem2499538 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2499539 : term300 = term174.
Proof. exact (@lem2499538 term174). Qed.
Lemma lem2499540 : term332 = term174.
Proof. exact (TRANS (@lem2499536) (@lem2499539)). Qed.
Lemma lem2499541 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499542 : term350 = term209.
Proof. exact (MK_COMB (@lem2499541) (@lem2499540)). Qed.
Lemma lem2499543 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2499544 (m : int) : (term329 m) = (term210 m).
Proof. exact (MK_COMB (@lem2499542) (@lem2499543 m)). Qed.
Lemma lem2499545 (m : int) : (term328 m) = (term210 m).
Proof. exact (TRANS (@lem2499442 m) (@lem2499544 m)). Qed.
Lemma lem2499546 (m : int) : (term210 m) = term174.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2499547 (m : int) : (term328 m) = term174.
Proof. exact (TRANS (@lem2499545 m) (@lem2499546 m)). Qed.
Lemma lem2499548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2499549 (m : int) : (term351 m) = term184.
Proof. exact (MK_COMB (@lem2499548) (@lem2499547 m)). Qed.
Lemma lem2499550 : term257 = term257.
Proof. exact (eq_refl term257). Qed.
Lemma lem2499551 (m : int) : (term327 m) = term352.
Proof. exact (MK_COMB (@lem2499549 m) (@lem2499550)). Qed.
Lemma lem2499552 (m : int) : (term326 m) = term352.
Proof. exact (TRANS (@lem2499441 m) (@lem2499551 m)). Qed.
Lemma lem2499553 : term352 = term257.
Proof. exact (@lem1982721 term257). Qed.
Lemma lem2499554 (m : int) : (term326 m) = term257.
Proof. exact (TRANS (@lem2499552 m) (@lem2499553)). Qed.
Lemma lem2499555 (m : int) : (term325 m) = term257.
Proof. exact (TRANS (@lem2499440 m) (@lem2499554 m)). Qed.
Lemma lem2499556 (m : int) : (term324 m) = term257.
Proof. exact (TRANS (@lem2499395 m) (@lem2499555 m)). Qed.
Lemma lem2499557 (n : int) (m : int) : (term357 n m) = term257.
Proof. exact (TRANS (@lem2499394 n m) (@lem2499556 m)). Qed.
Lemma lem2499558 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499559 (n : int) (m : int) : (term358 n m) = term354.
Proof. exact (MK_COMB (@lem2499558) (@lem2499557 n m)). Qed.
Lemma lem2499560 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499561 (n : int) (m : int) : (term356 n m) = term355.
Proof. exact (MK_COMB (@lem2499559 n m) (@lem2499560)). Qed.
Lemma lem2499562 (n : int) (m : int) : (term227 n m) = term355.
Proof. exact (TRANS (@lem2499371 n m) (@lem2499561 n m)). Qed.
Lemma lem2499563 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499564 (n : int) (m : int) : (term216 n m) = term359.
Proof. exact (MK_COMB (@lem2499563) (@lem2499370 n m)). Qed.
Lemma lem2499565 (n : int) (m : int) : (term228 n m) = term360.
Proof. exact (MK_COMB (@lem2499564 n m) (@lem2499562 n m)). Qed.
Lemma lem2499566 (m : int) : (term175 m) = (term252 m).
Proof. exact (@lem1988287 term174 (term170 m)). Qed.
Lemma lem2499578 (m : int) : (term253 m) = (term254 m).
Proof. exact (@lem1982792 term174 (term170 m)). Qed.
Lemma lem2499579 (m : int) : (term255 m) = (term256 m).
Proof. exact (@lem1982781 (real_of_int m) term257 term167). Qed.
Lemma lem2499581 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499582 : term167 = term259.
Proof. exact (@lem2499581 term168). Qed.
Lemma lem2499584 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499585 : term257 = term262.
Proof. exact (@lem2499584 term168). Qed.
Lemma lem2499586 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2499587 : term263 = term264.
Proof. exact (MK_COMB (@lem2499586) (@lem2499585)). Qed.
Lemma lem2499588 : term265 = term266.
Proof. exact (MK_COMB (@lem2499587) (@lem2499582)). Qed.
Lemma lem2499589 : term266 = term267.
Proof. exact (@lem1981613 term257 term167 term167 term167). Qed.
Lemma lem2499591 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2499592 : term270 = term271.
Proof. exact (@lem2499591 term168 term168). Qed.
Lemma lem2499593 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499594 : term273 = term168.
Proof. exact (EQ_MP (@lem2499593) (@lem940073)). Qed.
Lemma lem2499595 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499596 : term271 = term167.
Proof. exact (MK_COMB (@lem2499595) (@lem2499594)). Qed.
Lemma lem2499597 : term270 = term167.
Proof. exact (TRANS (@lem2499592) (@lem2499596)). Qed.
Lemma lem2499599 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499600 : term265 = term276.
Proof. exact (@lem2499599 term168 term168). Qed.
Lemma lem2499601 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499602 : term273 = term168.
Proof. exact (EQ_MP (@lem2499601) (@lem940073)). Qed.
Lemma lem2499603 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499604 : term271 = term167.
Proof. exact (MK_COMB (@lem2499603) (@lem2499602)). Qed.
Lemma lem2499605 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499606 : term276 = term257.
Proof. exact (MK_COMB (@lem2499605) (@lem2499604)). Qed.
Lemma lem2499607 : term265 = term257.
Proof. exact (TRANS (@lem2499600) (@lem2499606)). Qed.
Lemma lem2499608 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2499609 : term277 = term278.
Proof. exact (MK_COMB (@lem2499608) (@lem2499607)). Qed.
Lemma lem2499610 : term267 = term262.
Proof. exact (MK_COMB (@lem2499609) (@lem2499597)). Qed.
Lemma lem2499611 : term266 = term262.
Proof. exact (TRANS (@lem2499589) (@lem2499610)). Qed.
Lemma lem2499612 : term265 = term262.
Proof. exact (TRANS (@lem2499588) (@lem2499611)). Qed.
Lemma lem2499614 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2499615 : term262 = term257.
Proof. exact (@lem2499614 term257). Qed.
Lemma lem2499616 : term265 = term257.
Proof. exact (TRANS (@lem2499612) (@lem2499615)). Qed.
Lemma lem2499619 (m : int) : (term280 m) = (term280 m).
Proof. exact (eq_refl (term280 m)). Qed.
Lemma lem2499620 (m : int) : (term256 m) = (term281 m).
Proof. exact (MK_COMB (@lem2499619 m) (@lem2499616)). Qed.
Lemma lem2499621 (m : int) : (term255 m) = (term281 m).
Proof. exact (TRANS (@lem2499579 m) (@lem2499620 m)). Qed.
Lemma lem2499622 : term184 = term184.
Proof. exact (eq_refl term184). Qed.
Lemma lem2499623 (m : int) : (term254 m) = (term282 m).
Proof. exact (MK_COMB (@lem2499622) (@lem2499621 m)). Qed.
Lemma lem2499624 (m : int) : (term282 m) = (term281 m).
Proof. exact (@lem1982721 (term281 m)). Qed.
Lemma lem2499625 (m : int) : (term254 m) = (term281 m).
Proof. exact (TRANS (@lem2499623 m) (@lem2499624 m)). Qed.
Lemma lem2499627 (m : int) : (term253 m) = (term281 m).
Proof. exact (TRANS (@lem2499578 m) (@lem2499625 m)). Qed.
Lemma lem2499628 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499629 (m : int) : (term283 m) = (term284 m).
Proof. exact (MK_COMB (@lem2499628) (@lem2499627 m)). Qed.
Lemma lem2499630 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499631 (m : int) : (term252 m) = (term285 m).
Proof. exact (MK_COMB (@lem2499629 m) (@lem2499630)). Qed.
Lemma lem2499632 (m : int) : (term175 m) = (term285 m).
Proof. exact (TRANS (@lem2499566 m) (@lem2499631 m)). Qed.
Lemma lem2499633 (m : int) (n : int) : (term239 n m) = (term361 m n).
Proof. exact (@lem1988287 (real_of_int m) (term236 n)). Qed.
Lemma lem2499641 (m : int) (n : int) : (term362 m n) = (term363 m n).
Proof. exact (@lem1982792 (real_of_int m) (term236 n)). Qed.
Lemma lem2499646 (n : int) (m : int) : (term363 m n) = (term364 n m).
Proof. exact (@lem1982761 (term365 n) (real_of_int m)). Qed.
Lemma lem2499648 (n : int) (m : int) : (term362 m n) = (term364 n m).
Proof. exact (TRANS (@lem2499641 m n) (@lem2499646 n m)). Qed.
Lemma lem2499649 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499650 (n : int) (m : int) : (term366 m n) = (term367 n m).
Proof. exact (MK_COMB (@lem2499649) (@lem2499648 n m)). Qed.
Lemma lem2499651 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499652 (n : int) (m : int) : (term361 m n) = (term368 n m).
Proof. exact (MK_COMB (@lem2499650 n m) (@lem2499651)). Qed.
Lemma lem2499653 (n : int) (m : int) : (term239 n m) = (term368 n m).
Proof. exact (TRANS (@lem2499633 m n) (@lem2499652 n m)). Qed.
Lemma lem2499654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499655 (m : int) : (term177 m) = (term295 m).
Proof. exact (MK_COMB (@lem2499654) (@lem2499632 m)). Qed.
Lemma lem2499656 (n : int) (m : int) : (term241 n m) = (term369 n m).
Proof. exact (MK_COMB (@lem2499655 m) (@lem2499653 n m)). Qed.
Lemma lem2499657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499658 (n : int) (m : int) : (term242 n m) = term370.
Proof. exact (MK_COMB (@lem2499657) (@lem2499565 n m)). Qed.
Lemma lem2499659 (n : int) (m : int) : (term243 n m) = (term371 n m).
Proof. exact (MK_COMB (@lem2499658 n m) (@lem2499656 n m)). Qed.
Lemma lem2499660 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2499661 (m : int) (n : int) : (term244 m n) = (term372 m n).
Proof. exact (MK_COMB (@lem2499660) (@lem2499178 m n)). Qed.
Lemma lem2499662 (n : int) (m : int) : (term245 n m) = (term373 n m).
Proof. exact (MK_COMB (@lem2499661 m n) (@lem2499659 n m)). Qed.
Lemma lem2499663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2499664 (m : int) : (term246 m) = (term374 m).
Proof. exact (MK_COMB (@lem2499663) (@lem2499107 m)). Qed.
Lemma lem2499665 (n : int) (m : int) : (term247 n m) = (term375 n m).
Proof. exact (MK_COMB (@lem2499664 m) (@lem2499662 n m)). Qed.
Lemma lem2499666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2499667 (n : int) : (term248 n) = (term376 n).
Proof. exact (MK_COMB (@lem2499666) (@lem2499059 n)). Qed.
Lemma lem2499668 (n : int) (m : int) : (term249 n m) = (term377 n m).
Proof. exact (MK_COMB (@lem2499667 n) (@lem2499665 n m)). Qed.
Lemma lem2499675 (n : int) (m : int) : (term251 n m) = (term377 n m).
Proof. exact (TRANS (@lem2498928 n m) (@lem2499668 n m)). Qed.
Lemma lem2499693 (n : int) (m : int) : (term373 n m) = (term378 n m).
Proof. exact (@lem19158 term360 (term319 m n) (term369 n m)). Qed.
Lemma lem2499700 (n : int) (m : int) : (term379 n m) = (term380 n m).
Proof. exact (@lem19158 (term285 m) (term319 m n) (term368 n m)). Qed.
Lemma lem2499707 (m : int) (n : int) : (term381 m n) = (term382 m n).
Proof. exact (@lem19158 term355 (term319 m n) term355). Qed.
Lemma lem2499708 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499709 (m : int) (n : int) : (term383 m n) = (term384 m n).
Proof. exact (MK_COMB (@lem2499708) (@lem2499707 m n)). Qed.
Lemma lem2499710 (n : int) (m : int) : (term378 n m) = (term385 n m).
Proof. exact (MK_COMB (@lem2499709 m n) (@lem2499700 n m)). Qed.
Lemma lem2499712 (n : int) (m : int) : (term373 n m) = (term385 n m).
Proof. exact (TRANS (@lem2499693 n m) (@lem2499710 n m)). Qed.
Lemma lem2499715 (m : int) : (term374 m) = (term374 m).
Proof. exact (eq_refl (term374 m)). Qed.
Lemma lem2499716 (n : int) (m : int) : (term375 n m) = (term386 n m).
Proof. exact (MK_COMB (@lem2499715 m) (@lem2499712 n m)). Qed.
Lemma lem2499717 (n : int) (m : int) : (term386 n m) = (term387 n m).
Proof. exact (@lem19158 (term382 m n) (term310 m) (term380 n m)). Qed.
Lemma lem2499724 (n : int) (m : int) : (term388 n m) = (term389 n m).
Proof. exact (@lem19158 (term390 n m) (term310 m) (term391 n m)). Qed.
Lemma lem2499731 (m : int) (n : int) : (term392 m n) = (term393 m n).
Proof. exact (@lem19158 (term394 m n) (term310 m) (term394 m n)). Qed.
Lemma lem2499732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499733 (m : int) (n : int) : (term395 m n) = (term396 m n).
Proof. exact (MK_COMB (@lem2499732) (@lem2499731 m n)). Qed.
Lemma lem2499734 (n : int) (m : int) : (term387 n m) = (term397 n m).
Proof. exact (MK_COMB (@lem2499733 m n) (@lem2499724 n m)). Qed.
Lemma lem2499735 (n : int) (m : int) : (term386 n m) = (term397 n m).
Proof. exact (TRANS (@lem2499717 n m) (@lem2499734 n m)). Qed.
Lemma lem2499736 (n : int) (m : int) : (term375 n m) = (term397 n m).
Proof. exact (TRANS (@lem2499716 n m) (@lem2499735 n m)). Qed.
Lemma lem2499743 (n : int) : (term376 n) = (term376 n).
Proof. exact (eq_refl (term376 n)). Qed.
Lemma lem2499744 (n : int) (m : int) : (term377 n m) = (term398 n m).
Proof. exact (MK_COMB (@lem2499743 n) (@lem2499736 n m)). Qed.
Lemma lem2499745 (n : int) (m : int) : (term398 n m) = (term399 n m).
Proof. exact (@lem19158 (term393 m n) (term296 n) (term389 n m)). Qed.
Lemma lem2499746 (n : int) (m : int) : (term400 n m) = (term401 n m).
Proof. exact (@lem19158 (term402 n m) (term296 n) (term403 n m)). Qed.
Lemma lem2499753 (n : int) (m : int) : (term404 n m) = (term405 n m).
Proof. exact (@lem19367 (term285 n) (term294 n) (term403 n m)). Qed.
Lemma lem2499760 (n : int) (m : int) : (term406 n m) = (term407 n m).
Proof. exact (@lem19367 (term285 n) (term294 n) (term402 n m)). Qed.
Lemma lem2499761 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499762 (n : int) (m : int) : (term408 n m) = (term409 n m).
Proof. exact (MK_COMB (@lem2499761) (@lem2499760 n m)). Qed.
Lemma lem2499763 (n : int) (m : int) : (term401 n m) = (term410 n m).
Proof. exact (MK_COMB (@lem2499762 n m) (@lem2499753 n m)). Qed.
Lemma lem2499764 (n : int) (m : int) : (term400 n m) = (term410 n m).
Proof. exact (TRANS (@lem2499746 n m) (@lem2499763 n m)). Qed.
Lemma lem2499765 (m : int) (n : int) : (term411 m n) = (term412 m n).
Proof. exact (@lem19158 (term413 m n) (term296 n) (term413 m n)). Qed.
Lemma lem2499772 (m : int) (n : int) : (term414 m n) = (term415 m n).
Proof. exact (@lem19367 (term285 n) (term294 n) (term413 m n)). Qed.
Lemma lem2499779 (m : int) (n : int) : (term414 m n) = (term415 m n).
Proof. exact (@lem19367 (term285 n) (term294 n) (term413 m n)). Qed.
Lemma lem2499780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499781 (m : int) (n : int) : (term416 m n) = (term417 m n).
Proof. exact (MK_COMB (@lem2499780) (@lem2499779 m n)). Qed.
Lemma lem2499782 (m : int) (n : int) : (term412 m n) = (term418 m n).
Proof. exact (MK_COMB (@lem2499781 m n) (@lem2499772 m n)). Qed.
Lemma lem2499783 (m : int) (n : int) : (term411 m n) = (term418 m n).
Proof. exact (TRANS (@lem2499765 m n) (@lem2499782 m n)). Qed.
Lemma lem2499784 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499785 (m : int) (n : int) : (term419 m n) = (term420 m n).
Proof. exact (MK_COMB (@lem2499784) (@lem2499783 m n)). Qed.
Lemma lem2499786 (n : int) (m : int) : (term399 n m) = (term421 n m).
Proof. exact (MK_COMB (@lem2499785 m n) (@lem2499764 n m)). Qed.
Lemma lem2499787 (n : int) (m : int) : (term398 n m) = (term421 n m).
Proof. exact (TRANS (@lem2499745 n m) (@lem2499786 n m)). Qed.
Lemma lem2499788 (n : int) (m : int) : (term377 n m) = (term421 n m).
Proof. exact (TRANS (@lem2499744 n m) (@lem2499787 n m)). Qed.
Lemma lem2499789 (n : int) (m : int) : (term251 n m) = (term421 n m).
Proof. exact (TRANS (@lem2499675 n m) (@lem2499788 n m)). Qed.
Lemma lem2499821 (a : real) (x : real) (r : real) : (term422 x a r) = (term423 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2499822 (m : int) (n : int) : (term368 n m) = (term424 m n).
Proof. exact (@lem2499821 (real_of_int m) (real_of_int n) term174). Qed.
Lemma lem2499829 (n : int) : (term425 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2499832 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2499835 (m : int) (n : int) : (term426 m n) = (term161 m n).
Proof. exact (MK_COMB (@lem2499832 m) (@lem2499829 n)). Qed.
Lemma lem2499836 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499837 (m : int) (n : int) : (term427 m n) = (term428 m n).
Proof. exact (MK_COMB (@lem2499836) (@lem2499835 m n)). Qed.
Lemma lem2499838 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499839 (m : int) (n : int) : (term429 m n) = (term430 m n).
Proof. exact (MK_COMB (@lem2499837 m n) (@lem2499838)). Qed.
Lemma lem2499858 (m : int) (n : int) : (term431 m n) = (term431 m n).
Proof. exact (eq_refl (term431 m n)). Qed.
Lemma lem2499859 (m : int) (n : int) : (term424 m n) = (term432 m n).
Proof. exact (MK_COMB (@lem2499858 m n) (@lem2499839 m n)). Qed.
Lemma lem2499860 (m : int) (n : int) : (term368 n m) = (term432 m n).
Proof. exact (TRANS (@lem2499822 m n) (@lem2499859 m n)). Qed.
Lemma lem2499861 (m : int) (n : int) : (term372 m n) = (term372 m n).
Proof. exact (eq_refl (term372 m n)). Qed.
Lemma lem2499862 (m : int) (n : int) : (term391 n m) = (term433 m n).
Proof. exact (MK_COMB (@lem2499861 m n) (@lem2499860 m n)). Qed.
Lemma lem2499863 (m : int) : (term374 m) = (term374 m).
Proof. exact (eq_refl (term374 m)). Qed.
Lemma lem2499864 (m : int) (n : int) : (term403 n m) = (term434 m n).
Proof. exact (MK_COMB (@lem2499863 m) (@lem2499862 m n)). Qed.
Lemma lem2499865 (n : int) : (term435 n) = (term435 n).
Proof. exact (eq_refl (term435 n)). Qed.
Lemma lem2499868 (m : int) (n : int) : (term436 n m) = (term437 m n).
Proof. exact (MK_COMB (@lem2499865 n) (@lem2499864 m n)). Qed.
Lemma lem2499870 (a : real) (x : real) (r : real) : (term422 x a r) = (term423 a x r).
Proof. exact (proj1 (@lem1482679 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem2499871 (m : int) (n : int) : (term368 n m) = (term424 m n).
Proof. exact (@lem2499870 (real_of_int m) (real_of_int n) term174). Qed.
Lemma lem2499878 (n : int) : (term425 n) = (real_of_int n).
Proof. exact (@lem1982733 (real_of_int n)). Qed.
Lemma lem2499881 (m : int) : (term169 m) = (term169 m).
Proof. exact (eq_refl (term169 m)). Qed.
Lemma lem2499884 (m : int) (n : int) : (term426 m n) = (term161 m n).
Proof. exact (MK_COMB (@lem2499881 m) (@lem2499878 n)). Qed.
Lemma lem2499885 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2499886 (m : int) (n : int) : (term427 m n) = (term428 m n).
Proof. exact (MK_COMB (@lem2499885) (@lem2499884 m n)). Qed.
Lemma lem2499887 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2499888 (m : int) (n : int) : (term429 m n) = (term430 m n).
Proof. exact (MK_COMB (@lem2499886 m n) (@lem2499887)). Qed.
Lemma lem2499907 (m : int) (n : int) : (term431 m n) = (term431 m n).
Proof. exact (eq_refl (term431 m n)). Qed.
Lemma lem2499908 (m : int) (n : int) : (term424 m n) = (term432 m n).
Proof. exact (MK_COMB (@lem2499907 m n) (@lem2499888 m n)). Qed.
Lemma lem2499909 (m : int) (n : int) : (term368 n m) = (term432 m n).
Proof. exact (TRANS (@lem2499871 m n) (@lem2499908 m n)). Qed.
Lemma lem2499910 (m : int) (n : int) : (term372 m n) = (term372 m n).
Proof. exact (eq_refl (term372 m n)). Qed.
Lemma lem2499911 (m : int) (n : int) : (term391 n m) = (term433 m n).
Proof. exact (MK_COMB (@lem2499910 m n) (@lem2499909 m n)). Qed.
Lemma lem2499912 (m : int) : (term374 m) = (term374 m).
Proof. exact (eq_refl (term374 m)). Qed.
Lemma lem2499913 (m : int) (n : int) : (term403 n m) = (term434 m n).
Proof. exact (MK_COMB (@lem2499912 m) (@lem2499911 m n)). Qed.
Lemma lem2499914 (n : int) : (term438 n) = (term438 n).
Proof. exact (eq_refl (term438 n)). Qed.
Lemma lem2499917 (m : int) (n : int) : (term439 n m) = (term440 m n).
Proof. exact (MK_COMB (@lem2499914 n) (@lem2499913 m n)). Qed.
Lemma lem2499918 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2499919 (m : int) (n : int) : (term441 n m) = (term442 m n).
Proof. exact (MK_COMB (@lem2499918) (@lem2499868 m n)). Qed.
Lemma lem2499920 (m : int) (n : int) : (term405 n m) = (term443 m n).
Proof. exact (MK_COMB (@lem2499919 m n) (@lem2499917 m n)). Qed.
Lemma lem2499922 (n : int) (m : int) : (term409 n m) = (term409 n m).
Proof. exact (eq_refl (term409 n m)). Qed.
Lemma lem2499923 (m : int) (n : int) : (term410 n m) = (term444 m n).
Proof. exact (MK_COMB (@lem2499922 n m) (@lem2499920 m n)). Qed.
Lemma lem2499925 (m : int) (n : int) : (term420 m n) = (term420 m n).
Proof. exact (eq_refl (term420 m n)). Qed.
Lemma lem2499926 (m : int) (n : int) : (term421 n m) = (term445 m n).
Proof. exact (MK_COMB (@lem2499925 m n) (@lem2499923 m n)). Qed.
Lemma lem2499927 (m : int) (n : int) (h1 : term445 m n) : term445 m n.
Proof. exact (h1). Qed.
Lemma lem2499928 (m : int) (n : int) (h1 : term418 m n) : term418 m n.
Proof. exact (h1). Qed.
Lemma lem2499929 (m : int) (n : int) (h1 : term415 m n) : term415 m n.
Proof. exact (h1). Qed.
Lemma lem2499930 (m : int) (n : int) (h1 : term446 m n) : term446 m n.
Proof. exact (h1). Qed.
Lemma lem2499931 (m : int) (n : int) (h1 : term446 m n) : term413 m n.
Proof. exact (proj2 (@lem2499930 m n h1)). Qed.
Lemma lem2499933 (m : int) (n : int) (h1 : term446 m n) : term394 m n.
Proof. exact (proj2 (@lem2499931 m n h1)). Qed.
Lemma lem2499935 (m : int) (n : int) (h1 : term446 m n) : term355.
Proof. exact (proj2 (@lem2499933 m n h1)). Qed.
Lemma lem2499938 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2499939 : term355 = term447.
Proof. exact (@lem2499938 term174 term257). Qed.
Lemma lem2499941 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2499942 : term257 = term262.
Proof. exact (@lem2499941 term168). Qed.
Lemma lem2499944 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2499945 : term174 = term300.
Proof. exact (@lem2499944 (NUMERAL 0)). Qed.
Lemma lem2499946 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2499947 : term192 = term448.
Proof. exact (MK_COMB (@lem2499946) (@lem2499945)). Qed.
Lemma lem2499948 : term447 = term449.
Proof. exact (MK_COMB (@lem2499947) (@lem2499942)). Qed.
Lemma lem2499949 : term450.
Proof. exact (@lem1980026 term174 term167 term257 term167). Qed.
Lemma lem2499951 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499952 : term336 = term337.
Proof. exact (@lem2499951 (NUMERAL 0) term168). Qed.
Lemma lem2499953 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499954 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499955 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499954 h1) (fun h1 : term337 = True => @lem2499953)). Qed.
Lemma lem2499956 : term337 = True.
Proof. exact (EQ_MP (@lem2499955) (@lem2499953)). Qed.
Lemma lem2499957 : term336 = True.
Proof. exact (TRANS (@lem2499952) (@lem2499956)). Qed.
Lemma lem2499958 : True = term336.
Proof. exact (SYM (@lem2499957)). Qed.
Lemma lem2499959 : term336.
Proof. exact (EQ_MP (@lem2499958) (@lem0)). Qed.
Lemma lem2499960 : term451.
Proof. exact (@lem2499949 (@lem2499959)). Qed.
Lemma lem2499962 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2499963 : term336 = term337.
Proof. exact (@lem2499962 (NUMERAL 0) term168). Qed.
Lemma lem2499964 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499965 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2499966 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499965 h1) (fun h1 : term337 = True => @lem2499964)). Qed.
Lemma lem2499967 : term337 = True.
Proof. exact (EQ_MP (@lem2499966) (@lem2499964)). Qed.
Lemma lem2499968 : term336 = True.
Proof. exact (TRANS (@lem2499963) (@lem2499967)). Qed.
Lemma lem2499969 : True = term336.
Proof. exact (SYM (@lem2499968)). Qed.
Lemma lem2499970 : term336.
Proof. exact (EQ_MP (@lem2499969) (@lem0)). Qed.
Lemma lem2499971 : term449 = term452.
Proof. exact (@lem2499960 (@lem2499970)). Qed.
Lemma lem2499973 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2499974 : term265 = term276.
Proof. exact (@lem2499973 term168 term168). Qed.
Lemma lem2499975 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2499976 : term273 = term168.
Proof. exact (EQ_MP (@lem2499975) (@lem940073)). Qed.
Lemma lem2499977 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2499978 : term271 = term167.
Proof. exact (MK_COMB (@lem2499977) (@lem2499976)). Qed.
Lemma lem2499979 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2499980 : term276 = term257.
Proof. exact (MK_COMB (@lem2499979) (@lem2499978)). Qed.
Lemma lem2499981 : term265 = term257.
Proof. exact (TRANS (@lem2499974) (@lem2499980)). Qed.
Lemma lem2499983 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2499984 : term347 = term174.
Proof. exact (@lem2499983 term168). Qed.
Lemma lem2499985 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2499986 : term453 = term192.
Proof. exact (MK_COMB (@lem2499985) (@lem2499984)). Qed.
Lemma lem2499987 : term452 = term447.
Proof. exact (MK_COMB (@lem2499986) (@lem2499981)). Qed.
Lemma lem2499989 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2499990 : term447 = term456.
Proof. exact (@lem2499989 (NUMERAL 0) term168). Qed.
Lemma lem2499991 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2499992 (h1 : term338 = (BIT1 0)) : (term168 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2499993 : (term338 = (BIT1 0)) = ((term168 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2499992 h1) (fun h1 : (term168 = (NUMERAL 0)) = False => @lem2499991)). Qed.
Lemma lem2499994 : (term168 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2499993) (@lem2499991)). Qed.
Lemma lem2499995 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2499996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2499997 : term457 = (and True).
Proof. exact (MK_COMB (@lem2499996) (@lem2499995)). Qed.
Lemma lem2499998 : term456 = (True /\ False).
Proof. exact (MK_COMB (@lem2499997) (@lem2499994)). Qed.
Lemma lem2500000 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2500001 : term456 = False.
Proof. exact (TRANS (@lem2499998) (@lem2500000)). Qed.
Lemma lem2500002 : term447 = False.
Proof. exact (TRANS (@lem2499990) (@lem2500001)). Qed.
Lemma lem2500003 : term452 = False.
Proof. exact (TRANS (@lem2499987) (@lem2500002)). Qed.
Lemma lem2500004 : term449 = False.
Proof. exact (TRANS (@lem2499971) (@lem2500003)). Qed.
Lemma lem2500005 : term447 = False.
Proof. exact (TRANS (@lem2499948) (@lem2500004)). Qed.
Lemma lem2500006 : term355 = False.
Proof. exact (TRANS (@lem2499939) (@lem2500005)). Qed.
Lemma lem2500007 (m : int) (n : int) (h1 : term446 m n) : False.
Proof. exact (EQ_MP (@lem2500006) (@lem2499935 m n h1)). Qed.
Lemma lem2500008 (m : int) (n : int) (h1 : term458 m n) : term458 m n.
Proof. exact (h1). Qed.
Lemma lem2500009 (m : int) (n : int) (h1 : term458 m n) : term413 m n.
Proof. exact (proj2 (@lem2500008 m n h1)). Qed.
Lemma lem2500011 (m : int) (n : int) (h1 : term458 m n) : term394 m n.
Proof. exact (proj2 (@lem2500009 m n h1)). Qed.
Lemma lem2500013 (m : int) (n : int) (h1 : term458 m n) : term355.
Proof. exact (proj2 (@lem2500011 m n h1)). Qed.
Lemma lem2500016 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2500017 : term355 = term447.
Proof. exact (@lem2500016 term174 term257). Qed.
Lemma lem2500019 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500020 : term257 = term262.
Proof. exact (@lem2500019 term168). Qed.
Lemma lem2500022 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500023 : term174 = term300.
Proof. exact (@lem2500022 (NUMERAL 0)). Qed.
Lemma lem2500024 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500025 : term192 = term448.
Proof. exact (MK_COMB (@lem2500024) (@lem2500023)). Qed.
Lemma lem2500026 : term447 = term449.
Proof. exact (MK_COMB (@lem2500025) (@lem2500020)). Qed.
Lemma lem2500027 : term450.
Proof. exact (@lem1980026 term174 term167 term257 term167). Qed.
Lemma lem2500029 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500030 : term336 = term337.
Proof. exact (@lem2500029 (NUMERAL 0) term168). Qed.
Lemma lem2500031 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500032 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500033 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500032 h1) (fun h1 : term337 = True => @lem2500031)). Qed.
Lemma lem2500034 : term337 = True.
Proof. exact (EQ_MP (@lem2500033) (@lem2500031)). Qed.
Lemma lem2500035 : term336 = True.
Proof. exact (TRANS (@lem2500030) (@lem2500034)). Qed.
Lemma lem2500036 : True = term336.
Proof. exact (SYM (@lem2500035)). Qed.
Lemma lem2500037 : term336.
Proof. exact (EQ_MP (@lem2500036) (@lem0)). Qed.
Lemma lem2500038 : term451.
Proof. exact (@lem2500027 (@lem2500037)). Qed.
Lemma lem2500040 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500041 : term336 = term337.
Proof. exact (@lem2500040 (NUMERAL 0) term168). Qed.
Lemma lem2500042 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500043 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500044 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500043 h1) (fun h1 : term337 = True => @lem2500042)). Qed.
Lemma lem2500045 : term337 = True.
Proof. exact (EQ_MP (@lem2500044) (@lem2500042)). Qed.
Lemma lem2500046 : term336 = True.
Proof. exact (TRANS (@lem2500041) (@lem2500045)). Qed.
Lemma lem2500047 : True = term336.
Proof. exact (SYM (@lem2500046)). Qed.
Lemma lem2500048 : term336.
Proof. exact (EQ_MP (@lem2500047) (@lem0)). Qed.
Lemma lem2500049 : term449 = term452.
Proof. exact (@lem2500038 (@lem2500048)). Qed.
Lemma lem2500051 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500052 : term265 = term276.
Proof. exact (@lem2500051 term168 term168). Qed.
Lemma lem2500053 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500054 : term273 = term168.
Proof. exact (EQ_MP (@lem2500053) (@lem940073)). Qed.
Lemma lem2500055 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500056 : term271 = term167.
Proof. exact (MK_COMB (@lem2500055) (@lem2500054)). Qed.
Lemma lem2500057 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500058 : term276 = term257.
Proof. exact (MK_COMB (@lem2500057) (@lem2500056)). Qed.
Lemma lem2500059 : term265 = term257.
Proof. exact (TRANS (@lem2500052) (@lem2500058)). Qed.
Lemma lem2500061 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500062 : term347 = term174.
Proof. exact (@lem2500061 term168). Qed.
Lemma lem2500063 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500064 : term453 = term192.
Proof. exact (MK_COMB (@lem2500063) (@lem2500062)). Qed.
Lemma lem2500065 : term452 = term447.
Proof. exact (MK_COMB (@lem2500064) (@lem2500059)). Qed.
Lemma lem2500067 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2500068 : term447 = term456.
Proof. exact (@lem2500067 (NUMERAL 0) term168). Qed.
Lemma lem2500069 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500070 (h1 : term338 = (BIT1 0)) : (term168 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2500071 : (term338 = (BIT1 0)) = ((term168 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500070 h1) (fun h1 : (term168 = (NUMERAL 0)) = False => @lem2500069)). Qed.
Lemma lem2500072 : (term168 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2500071) (@lem2500069)). Qed.
Lemma lem2500073 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2500074 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2500075 : term457 = (and True).
Proof. exact (MK_COMB (@lem2500074) (@lem2500073)). Qed.
Lemma lem2500076 : term456 = (True /\ False).
Proof. exact (MK_COMB (@lem2500075) (@lem2500072)). Qed.
Lemma lem2500078 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2500079 : term456 = False.
Proof. exact (TRANS (@lem2500076) (@lem2500078)). Qed.
Lemma lem2500080 : term447 = False.
Proof. exact (TRANS (@lem2500068) (@lem2500079)). Qed.
Lemma lem2500081 : term452 = False.
Proof. exact (TRANS (@lem2500065) (@lem2500080)). Qed.
Lemma lem2500082 : term449 = False.
Proof. exact (TRANS (@lem2500049) (@lem2500081)). Qed.
Lemma lem2500083 : term447 = False.
Proof. exact (TRANS (@lem2500026) (@lem2500082)). Qed.
Lemma lem2500084 : term355 = False.
Proof. exact (TRANS (@lem2500017) (@lem2500083)). Qed.
Lemma lem2500085 (m : int) (n : int) (h1 : term458 m n) : False.
Proof. exact (EQ_MP (@lem2500084) (@lem2500013 m n h1)). Qed.
Lemma lem2500086 (m : int) (n : int) (h1 : term415 m n) : False.
Proof. exact (or_elim (@lem2499929 m n h1) (fun h0 : term446 m n => @lem2500007 m n h0) (fun h0 : term458 m n => @lem2500085 m n h0)). Qed.
Lemma lem2500087 (m : int) (n : int) (h1 : term415 m n) : term415 m n.
Proof. exact (h1). Qed.
Lemma lem2500088 (m : int) (n : int) (h1 : term446 m n) : term446 m n.
Proof. exact (h1). Qed.
Lemma lem2500089 (m : int) (n : int) (h1 : term446 m n) : term413 m n.
Proof. exact (proj2 (@lem2500088 m n h1)). Qed.
Lemma lem2500091 (m : int) (n : int) (h1 : term446 m n) : term394 m n.
Proof. exact (proj2 (@lem2500089 m n h1)). Qed.
Lemma lem2500093 (m : int) (n : int) (h1 : term446 m n) : term355.
Proof. exact (proj2 (@lem2500091 m n h1)). Qed.
Lemma lem2500096 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2500097 : term355 = term447.
Proof. exact (@lem2500096 term174 term257). Qed.
Lemma lem2500099 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500100 : term257 = term262.
Proof. exact (@lem2500099 term168). Qed.
Lemma lem2500102 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500103 : term174 = term300.
Proof. exact (@lem2500102 (NUMERAL 0)). Qed.
Lemma lem2500104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500105 : term192 = term448.
Proof. exact (MK_COMB (@lem2500104) (@lem2500103)). Qed.
Lemma lem2500106 : term447 = term449.
Proof. exact (MK_COMB (@lem2500105) (@lem2500100)). Qed.
Lemma lem2500107 : term450.
Proof. exact (@lem1980026 term174 term167 term257 term167). Qed.
Lemma lem2500109 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500110 : term336 = term337.
Proof. exact (@lem2500109 (NUMERAL 0) term168). Qed.
Lemma lem2500111 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500112 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500113 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500112 h1) (fun h1 : term337 = True => @lem2500111)). Qed.
Lemma lem2500114 : term337 = True.
Proof. exact (EQ_MP (@lem2500113) (@lem2500111)). Qed.
Lemma lem2500115 : term336 = True.
Proof. exact (TRANS (@lem2500110) (@lem2500114)). Qed.
Lemma lem2500116 : True = term336.
Proof. exact (SYM (@lem2500115)). Qed.
Lemma lem2500117 : term336.
Proof. exact (EQ_MP (@lem2500116) (@lem0)). Qed.
Lemma lem2500118 : term451.
Proof. exact (@lem2500107 (@lem2500117)). Qed.
Lemma lem2500120 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500121 : term336 = term337.
Proof. exact (@lem2500120 (NUMERAL 0) term168). Qed.
Lemma lem2500122 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500123 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500124 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500123 h1) (fun h1 : term337 = True => @lem2500122)). Qed.
Lemma lem2500125 : term337 = True.
Proof. exact (EQ_MP (@lem2500124) (@lem2500122)). Qed.
Lemma lem2500126 : term336 = True.
Proof. exact (TRANS (@lem2500121) (@lem2500125)). Qed.
Lemma lem2500127 : True = term336.
Proof. exact (SYM (@lem2500126)). Qed.
Lemma lem2500128 : term336.
Proof. exact (EQ_MP (@lem2500127) (@lem0)). Qed.
Lemma lem2500129 : term449 = term452.
Proof. exact (@lem2500118 (@lem2500128)). Qed.
Lemma lem2500131 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500132 : term265 = term276.
Proof. exact (@lem2500131 term168 term168). Qed.
Lemma lem2500133 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500134 : term273 = term168.
Proof. exact (EQ_MP (@lem2500133) (@lem940073)). Qed.
Lemma lem2500135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500136 : term271 = term167.
Proof. exact (MK_COMB (@lem2500135) (@lem2500134)). Qed.
Lemma lem2500137 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500138 : term276 = term257.
Proof. exact (MK_COMB (@lem2500137) (@lem2500136)). Qed.
Lemma lem2500139 : term265 = term257.
Proof. exact (TRANS (@lem2500132) (@lem2500138)). Qed.
Lemma lem2500141 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500142 : term347 = term174.
Proof. exact (@lem2500141 term168). Qed.
Lemma lem2500143 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500144 : term453 = term192.
Proof. exact (MK_COMB (@lem2500143) (@lem2500142)). Qed.
Lemma lem2500145 : term452 = term447.
Proof. exact (MK_COMB (@lem2500144) (@lem2500139)). Qed.
Lemma lem2500147 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2500148 : term447 = term456.
Proof. exact (@lem2500147 (NUMERAL 0) term168). Qed.
Lemma lem2500149 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500150 (h1 : term338 = (BIT1 0)) : (term168 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2500151 : (term338 = (BIT1 0)) = ((term168 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500150 h1) (fun h1 : (term168 = (NUMERAL 0)) = False => @lem2500149)). Qed.
Lemma lem2500152 : (term168 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2500151) (@lem2500149)). Qed.
Lemma lem2500153 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2500154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2500155 : term457 = (and True).
Proof. exact (MK_COMB (@lem2500154) (@lem2500153)). Qed.
Lemma lem2500156 : term456 = (True /\ False).
Proof. exact (MK_COMB (@lem2500155) (@lem2500152)). Qed.
Lemma lem2500158 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2500159 : term456 = False.
Proof. exact (TRANS (@lem2500156) (@lem2500158)). Qed.
Lemma lem2500160 : term447 = False.
Proof. exact (TRANS (@lem2500148) (@lem2500159)). Qed.
Lemma lem2500161 : term452 = False.
Proof. exact (TRANS (@lem2500145) (@lem2500160)). Qed.
Lemma lem2500162 : term449 = False.
Proof. exact (TRANS (@lem2500129) (@lem2500161)). Qed.
Lemma lem2500163 : term447 = False.
Proof. exact (TRANS (@lem2500106) (@lem2500162)). Qed.
Lemma lem2500164 : term355 = False.
Proof. exact (TRANS (@lem2500097) (@lem2500163)). Qed.
Lemma lem2500165 (m : int) (n : int) (h1 : term446 m n) : False.
Proof. exact (EQ_MP (@lem2500164) (@lem2500093 m n h1)). Qed.
Lemma lem2500166 (m : int) (n : int) (h1 : term458 m n) : term458 m n.
Proof. exact (h1). Qed.
Lemma lem2500167 (m : int) (n : int) (h1 : term458 m n) : term413 m n.
Proof. exact (proj2 (@lem2500166 m n h1)). Qed.
Lemma lem2500169 (m : int) (n : int) (h1 : term458 m n) : term394 m n.
Proof. exact (proj2 (@lem2500167 m n h1)). Qed.
Lemma lem2500171 (m : int) (n : int) (h1 : term458 m n) : term355.
Proof. exact (proj2 (@lem2500169 m n h1)). Qed.
Lemma lem2500174 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2500175 : term355 = term447.
Proof. exact (@lem2500174 term174 term257). Qed.
Lemma lem2500177 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500178 : term257 = term262.
Proof. exact (@lem2500177 term168). Qed.
Lemma lem2500180 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500181 : term174 = term300.
Proof. exact (@lem2500180 (NUMERAL 0)). Qed.
Lemma lem2500182 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500183 : term192 = term448.
Proof. exact (MK_COMB (@lem2500182) (@lem2500181)). Qed.
Lemma lem2500184 : term447 = term449.
Proof. exact (MK_COMB (@lem2500183) (@lem2500178)). Qed.
Lemma lem2500185 : term450.
Proof. exact (@lem1980026 term174 term167 term257 term167). Qed.
Lemma lem2500187 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500188 : term336 = term337.
Proof. exact (@lem2500187 (NUMERAL 0) term168). Qed.
Lemma lem2500189 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500190 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500191 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500190 h1) (fun h1 : term337 = True => @lem2500189)). Qed.
Lemma lem2500192 : term337 = True.
Proof. exact (EQ_MP (@lem2500191) (@lem2500189)). Qed.
Lemma lem2500193 : term336 = True.
Proof. exact (TRANS (@lem2500188) (@lem2500192)). Qed.
Lemma lem2500194 : True = term336.
Proof. exact (SYM (@lem2500193)). Qed.
Lemma lem2500195 : term336.
Proof. exact (EQ_MP (@lem2500194) (@lem0)). Qed.
Lemma lem2500196 : term451.
Proof. exact (@lem2500185 (@lem2500195)). Qed.
Lemma lem2500198 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500199 : term336 = term337.
Proof. exact (@lem2500198 (NUMERAL 0) term168). Qed.
Lemma lem2500200 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500201 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500202 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500201 h1) (fun h1 : term337 = True => @lem2500200)). Qed.
Lemma lem2500203 : term337 = True.
Proof. exact (EQ_MP (@lem2500202) (@lem2500200)). Qed.
Lemma lem2500204 : term336 = True.
Proof. exact (TRANS (@lem2500199) (@lem2500203)). Qed.
Lemma lem2500205 : True = term336.
Proof. exact (SYM (@lem2500204)). Qed.
Lemma lem2500206 : term336.
Proof. exact (EQ_MP (@lem2500205) (@lem0)). Qed.
Lemma lem2500207 : term449 = term452.
Proof. exact (@lem2500196 (@lem2500206)). Qed.
Lemma lem2500209 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500210 : term265 = term276.
Proof. exact (@lem2500209 term168 term168). Qed.
Lemma lem2500211 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500212 : term273 = term168.
Proof. exact (EQ_MP (@lem2500211) (@lem940073)). Qed.
Lemma lem2500213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500214 : term271 = term167.
Proof. exact (MK_COMB (@lem2500213) (@lem2500212)). Qed.
Lemma lem2500215 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500216 : term276 = term257.
Proof. exact (MK_COMB (@lem2500215) (@lem2500214)). Qed.
Lemma lem2500217 : term265 = term257.
Proof. exact (TRANS (@lem2500210) (@lem2500216)). Qed.
Lemma lem2500219 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500220 : term347 = term174.
Proof. exact (@lem2500219 term168). Qed.
Lemma lem2500221 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500222 : term453 = term192.
Proof. exact (MK_COMB (@lem2500221) (@lem2500220)). Qed.
Lemma lem2500223 : term452 = term447.
Proof. exact (MK_COMB (@lem2500222) (@lem2500217)). Qed.
Lemma lem2500225 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2500226 : term447 = term456.
Proof. exact (@lem2500225 (NUMERAL 0) term168). Qed.
Lemma lem2500227 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500228 (h1 : term338 = (BIT1 0)) : (term168 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2500229 : (term338 = (BIT1 0)) = ((term168 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500228 h1) (fun h1 : (term168 = (NUMERAL 0)) = False => @lem2500227)). Qed.
Lemma lem2500230 : (term168 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2500229) (@lem2500227)). Qed.
Lemma lem2500231 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2500232 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2500233 : term457 = (and True).
Proof. exact (MK_COMB (@lem2500232) (@lem2500231)). Qed.
Lemma lem2500234 : term456 = (True /\ False).
Proof. exact (MK_COMB (@lem2500233) (@lem2500230)). Qed.
Lemma lem2500236 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2500237 : term456 = False.
Proof. exact (TRANS (@lem2500234) (@lem2500236)). Qed.
Lemma lem2500238 : term447 = False.
Proof. exact (TRANS (@lem2500226) (@lem2500237)). Qed.
Lemma lem2500239 : term452 = False.
Proof. exact (TRANS (@lem2500223) (@lem2500238)). Qed.
Lemma lem2500240 : term449 = False.
Proof. exact (TRANS (@lem2500207) (@lem2500239)). Qed.
Lemma lem2500241 : term447 = False.
Proof. exact (TRANS (@lem2500184) (@lem2500240)). Qed.
Lemma lem2500242 : term355 = False.
Proof. exact (TRANS (@lem2500175) (@lem2500241)). Qed.
Lemma lem2500243 (m : int) (n : int) (h1 : term458 m n) : False.
Proof. exact (EQ_MP (@lem2500242) (@lem2500171 m n h1)). Qed.
Lemma lem2500244 (m : int) (n : int) (h1 : term415 m n) : False.
Proof. exact (or_elim (@lem2500087 m n h1) (fun h0 : term446 m n => @lem2500165 m n h0) (fun h0 : term458 m n => @lem2500243 m n h0)). Qed.
Lemma lem2500245 (m : int) (n : int) (h1 : term418 m n) : False.
Proof. exact (or_elim (@lem2499928 m n h1) (fun h0 : term415 m n => @lem2500086 m n h0) (fun h0 : term415 m n => @lem2500244 m n h0)). Qed.
Lemma lem2500246 (m : int) (n : int) (h1 : term444 m n) : term444 m n.
Proof. exact (h1). Qed.
Lemma lem2500247 (n : int) (m : int) (h1 : term407 n m) : term407 n m.
Proof. exact (h1). Qed.
Lemma lem2500248 (n : int) (m : int) (h1 : term459 n m) : term459 n m.
Proof. exact (h1). Qed.
Lemma lem2500249 (n : int) (m : int) (h1 : term459 n m) : term402 n m.
Proof. exact (proj2 (@lem2500248 n m h1)). Qed.
Lemma lem2500250 (n : int) (m : int) (h1 : term459 n m) : term285 n.
Proof. exact (proj1 (@lem2500248 n m h1)). Qed.
Lemma lem2500251 (n : int) (m : int) (h1 : term459 n m) : term390 n m.
Proof. exact (proj2 (@lem2500249 n m h1)). Qed.
Lemma lem2500252 (n : int) (m : int) (h1 : term459 n m) : term310 m.
Proof. exact (proj1 (@lem2500249 n m h1)). Qed.
Lemma lem2500254 (n : int) (m : int) (h1 : term459 n m) : term319 m n.
Proof. exact (proj1 (@lem2500251 n m h1)). Qed.
Lemma lem2500256 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2500257 : term460 = term336.
Proof. exact (@lem2500256 term174 term167). Qed.
Lemma lem2500259 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500260 : term167 = term259.
Proof. exact (@lem2500259 term168). Qed.
Lemma lem2500262 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500263 : term174 = term300.
Proof. exact (@lem2500262 (NUMERAL 0)). Qed.
Lemma lem2500264 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500265 : term461 = term462.
Proof. exact (MK_COMB (@lem2500264) (@lem2500263)). Qed.
Lemma lem2500266 : term336 = term463.
Proof. exact (MK_COMB (@lem2500265) (@lem2500260)). Qed.
Lemma lem2500267 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2500269 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500270 : term336 = term337.
Proof. exact (@lem2500269 (NUMERAL 0) term168). Qed.
Lemma lem2500271 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500272 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500273 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500272 h1) (fun h1 : term337 = True => @lem2500271)). Qed.
Lemma lem2500274 : term337 = True.
Proof. exact (EQ_MP (@lem2500273) (@lem2500271)). Qed.
Lemma lem2500275 : term336 = True.
Proof. exact (TRANS (@lem2500270) (@lem2500274)). Qed.
Lemma lem2500276 : True = term336.
Proof. exact (SYM (@lem2500275)). Qed.
Lemma lem2500277 : term336.
Proof. exact (EQ_MP (@lem2500276) (@lem0)). Qed.
Lemma lem2500278 : term465.
Proof. exact (@lem2500267 (@lem2500277)). Qed.
Lemma lem2500280 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500281 : term336 = term337.
Proof. exact (@lem2500280 (NUMERAL 0) term168). Qed.
Lemma lem2500282 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500283 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500284 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500283 h1) (fun h1 : term337 = True => @lem2500282)). Qed.
Lemma lem2500285 : term337 = True.
Proof. exact (EQ_MP (@lem2500284) (@lem2500282)). Qed.
Lemma lem2500286 : term336 = True.
Proof. exact (TRANS (@lem2500281) (@lem2500285)). Qed.
Lemma lem2500287 : True = term336.
Proof. exact (SYM (@lem2500286)). Qed.
Lemma lem2500288 : term336.
Proof. exact (EQ_MP (@lem2500287) (@lem0)). Qed.
Lemma lem2500289 : term463 = term466.
Proof. exact (@lem2500278 (@lem2500288)). Qed.
Lemma lem2500291 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500292 : term270 = term271.
Proof. exact (@lem2500291 term168 term168). Qed.
Lemma lem2500293 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500294 : term273 = term168.
Proof. exact (EQ_MP (@lem2500293) (@lem940073)). Qed.
Lemma lem2500295 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500296 : term271 = term167.
Proof. exact (MK_COMB (@lem2500295) (@lem2500294)). Qed.
Lemma lem2500297 : term270 = term167.
Proof. exact (TRANS (@lem2500292) (@lem2500296)). Qed.
Lemma lem2500299 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500300 : term347 = term174.
Proof. exact (@lem2500299 term168). Qed.
Lemma lem2500301 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500302 : term467 = term461.
Proof. exact (MK_COMB (@lem2500301) (@lem2500300)). Qed.
Lemma lem2500303 : term466 = term336.
Proof. exact (MK_COMB (@lem2500302) (@lem2500297)). Qed.
Lemma lem2500305 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500306 : term336 = term337.
Proof. exact (@lem2500305 (NUMERAL 0) term168). Qed.
Lemma lem2500307 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500308 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500309 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500308 h1) (fun h1 : term337 = True => @lem2500307)). Qed.
Lemma lem2500310 : term337 = True.
Proof. exact (EQ_MP (@lem2500309) (@lem2500307)). Qed.
Lemma lem2500311 : term336 = True.
Proof. exact (TRANS (@lem2500306) (@lem2500310)). Qed.
Lemma lem2500312 : term466 = True.
Proof. exact (TRANS (@lem2500303) (@lem2500311)). Qed.
Lemma lem2500313 : term463 = True.
Proof. exact (TRANS (@lem2500289) (@lem2500312)). Qed.
Lemma lem2500314 : term336 = True.
Proof. exact (TRANS (@lem2500266) (@lem2500313)). Qed.
Lemma lem2500315 : term460 = True.
Proof. exact (TRANS (@lem2500257) (@lem2500314)). Qed.
Lemma lem2500316 : True = term460.
Proof. exact (SYM (@lem2500315)). Qed.
Lemma lem2500317 : term460.
Proof. exact (EQ_MP (@lem2500316) (@lem0)). Qed.
Lemma lem2500318 (n : int) (m : int) (h1 : term459 n m) : term468 m.
Proof. exact (conj (@lem2500317) (@lem2500252 n m h1)). Qed.
Lemma lem2500320 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2500321 (m : int) : term470 m.
Proof. exact (@lem2500320 term167 (real_of_int m)). Qed.
Lemma lem2500322 (n : int) (m : int) (h1 : term459 n m) : term471 m.
Proof. exact (@lem2500321 m (@lem2500318 n m h1)). Qed.
Lemma lem2500323 (m : int) : (term425 m) = (real_of_int m).
Proof. exact (@lem1982733 (real_of_int m)). Qed.
Lemma lem2500324 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2500325 (m : int) : (term472 m) = (term309 m).
Proof. exact (MK_COMB (@lem2500324) (@lem2500323 m)). Qed.
Lemma lem2500326 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2500327 (m : int) : (term471 m) = (term310 m).
Proof. exact (MK_COMB (@lem2500325 m) (@lem2500326)). Qed.
Lemma lem2500328 (n : int) (m : int) (h1 : term459 n m) : term310 m.
Proof. exact (EQ_MP (@lem2500327 m) (@lem2500322 n m h1)). Qed.
Lemma lem2500330 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2500331 : term460 = term336.
Proof. exact (@lem2500330 term174 term167). Qed.
Lemma lem2500333 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500334 : term167 = term259.
Proof. exact (@lem2500333 term168). Qed.
Lemma lem2500336 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500337 : term174 = term300.
Proof. exact (@lem2500336 (NUMERAL 0)). Qed.
Lemma lem2500338 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500339 : term461 = term462.
Proof. exact (MK_COMB (@lem2500338) (@lem2500337)). Qed.
Lemma lem2500340 : term336 = term463.
Proof. exact (MK_COMB (@lem2500339) (@lem2500334)). Qed.
Lemma lem2500341 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2500343 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500344 : term336 = term337.
Proof. exact (@lem2500343 (NUMERAL 0) term168). Qed.
Lemma lem2500345 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500346 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500347 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500346 h1) (fun h1 : term337 = True => @lem2500345)). Qed.
Lemma lem2500348 : term337 = True.
Proof. exact (EQ_MP (@lem2500347) (@lem2500345)). Qed.
Lemma lem2500349 : term336 = True.
Proof. exact (TRANS (@lem2500344) (@lem2500348)). Qed.
Lemma lem2500350 : True = term336.
Proof. exact (SYM (@lem2500349)). Qed.
Lemma lem2500351 : term336.
Proof. exact (EQ_MP (@lem2500350) (@lem0)). Qed.
Lemma lem2500352 : term465.
Proof. exact (@lem2500341 (@lem2500351)). Qed.
Lemma lem2500354 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500355 : term336 = term337.
Proof. exact (@lem2500354 (NUMERAL 0) term168). Qed.
Lemma lem2500356 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500357 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500358 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500357 h1) (fun h1 : term337 = True => @lem2500356)). Qed.
Lemma lem2500359 : term337 = True.
Proof. exact (EQ_MP (@lem2500358) (@lem2500356)). Qed.
Lemma lem2500360 : term336 = True.
Proof. exact (TRANS (@lem2500355) (@lem2500359)). Qed.
Lemma lem2500361 : True = term336.
Proof. exact (SYM (@lem2500360)). Qed.
Lemma lem2500362 : term336.
Proof. exact (EQ_MP (@lem2500361) (@lem0)). Qed.
Lemma lem2500363 : term463 = term466.
Proof. exact (@lem2500352 (@lem2500362)). Qed.
Lemma lem2500365 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500366 : term270 = term271.
Proof. exact (@lem2500365 term168 term168). Qed.
Lemma lem2500367 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500368 : term273 = term168.
Proof. exact (EQ_MP (@lem2500367) (@lem940073)). Qed.
Lemma lem2500369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500370 : term271 = term167.
Proof. exact (MK_COMB (@lem2500369) (@lem2500368)). Qed.
Lemma lem2500371 : term270 = term167.
Proof. exact (TRANS (@lem2500366) (@lem2500370)). Qed.
Lemma lem2500373 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500374 : term347 = term174.
Proof. exact (@lem2500373 term168). Qed.
Lemma lem2500375 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500376 : term467 = term461.
Proof. exact (MK_COMB (@lem2500375) (@lem2500374)). Qed.
Lemma lem2500377 : term466 = term336.
Proof. exact (MK_COMB (@lem2500376) (@lem2500371)). Qed.
Lemma lem2500379 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500380 : term336 = term337.
Proof. exact (@lem2500379 (NUMERAL 0) term168). Qed.
Lemma lem2500381 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500382 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500383 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500382 h1) (fun h1 : term337 = True => @lem2500381)). Qed.
Lemma lem2500384 : term337 = True.
Proof. exact (EQ_MP (@lem2500383) (@lem2500381)). Qed.
Lemma lem2500385 : term336 = True.
Proof. exact (TRANS (@lem2500380) (@lem2500384)). Qed.
Lemma lem2500386 : term466 = True.
Proof. exact (TRANS (@lem2500377) (@lem2500385)). Qed.
Lemma lem2500387 : term463 = True.
Proof. exact (TRANS (@lem2500363) (@lem2500386)). Qed.
Lemma lem2500388 : term336 = True.
Proof. exact (TRANS (@lem2500340) (@lem2500387)). Qed.
Lemma lem2500389 : term460 = True.
Proof. exact (TRANS (@lem2500331) (@lem2500388)). Qed.
Lemma lem2500390 : True = term460.
Proof. exact (SYM (@lem2500389)). Qed.
Lemma lem2500391 : term460.
Proof. exact (EQ_MP (@lem2500390) (@lem0)). Qed.
Lemma lem2500392 (n : int) (m : int) (h1 : term459 n m) : term473 m n.
Proof. exact (conj (@lem2500391) (@lem2500254 n m h1)). Qed.
Lemma lem2500394 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2500395 (m : int) (n : int) : term474 m n.
Proof. exact (@lem2500394 term167 (term315 m n)). Qed.
Lemma lem2500396 (n : int) (m : int) (h1 : term459 n m) : term475 m n.
Proof. exact (@lem2500395 m n (@lem2500392 n m h1)). Qed.
Lemma lem2500397 (m : int) (n : int) : (term476 m n) = (term315 m n).
Proof. exact (@lem1982733 (term315 m n)). Qed.
Lemma lem2500398 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2500399 (m : int) (n : int) : (term477 m n) = (term318 m n).
Proof. exact (MK_COMB (@lem2500398) (@lem2500397 m n)). Qed.
Lemma lem2500400 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2500401 (m : int) (n : int) : (term475 m n) = (term319 m n).
Proof. exact (MK_COMB (@lem2500399 m n) (@lem2500400)). Qed.
Lemma lem2500402 (n : int) (m : int) (h1 : term459 n m) : term319 m n.
Proof. exact (EQ_MP (@lem2500401 m n) (@lem2500396 n m h1)). Qed.
Lemma lem2500404 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2500405 : term460 = term336.
Proof. exact (@lem2500404 term174 term167). Qed.
Lemma lem2500407 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500408 : term167 = term259.
Proof. exact (@lem2500407 term168). Qed.
Lemma lem2500410 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500411 : term174 = term300.
Proof. exact (@lem2500410 (NUMERAL 0)). Qed.
Lemma lem2500412 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500413 : term461 = term462.
Proof. exact (MK_COMB (@lem2500412) (@lem2500411)). Qed.
Lemma lem2500414 : term336 = term463.
Proof. exact (MK_COMB (@lem2500413) (@lem2500408)). Qed.
Lemma lem2500415 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2500417 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500418 : term336 = term337.
Proof. exact (@lem2500417 (NUMERAL 0) term168). Qed.
Lemma lem2500419 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500420 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500421 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500420 h1) (fun h1 : term337 = True => @lem2500419)). Qed.
Lemma lem2500422 : term337 = True.
Proof. exact (EQ_MP (@lem2500421) (@lem2500419)). Qed.
Lemma lem2500423 : term336 = True.
Proof. exact (TRANS (@lem2500418) (@lem2500422)). Qed.
Lemma lem2500424 : True = term336.
Proof. exact (SYM (@lem2500423)). Qed.
Lemma lem2500425 : term336.
Proof. exact (EQ_MP (@lem2500424) (@lem0)). Qed.
Lemma lem2500426 : term465.
Proof. exact (@lem2500415 (@lem2500425)). Qed.
Lemma lem2500428 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500429 : term336 = term337.
Proof. exact (@lem2500428 (NUMERAL 0) term168). Qed.
Lemma lem2500430 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500431 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500432 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500431 h1) (fun h1 : term337 = True => @lem2500430)). Qed.
Lemma lem2500433 : term337 = True.
Proof. exact (EQ_MP (@lem2500432) (@lem2500430)). Qed.
Lemma lem2500434 : term336 = True.
Proof. exact (TRANS (@lem2500429) (@lem2500433)). Qed.
Lemma lem2500435 : True = term336.
Proof. exact (SYM (@lem2500434)). Qed.
Lemma lem2500436 : term336.
Proof. exact (EQ_MP (@lem2500435) (@lem0)). Qed.
Lemma lem2500437 : term463 = term466.
Proof. exact (@lem2500426 (@lem2500436)). Qed.
Lemma lem2500439 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500440 : term270 = term271.
Proof. exact (@lem2500439 term168 term168). Qed.
Lemma lem2500441 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500442 : term273 = term168.
Proof. exact (EQ_MP (@lem2500441) (@lem940073)). Qed.
Lemma lem2500443 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500444 : term271 = term167.
Proof. exact (MK_COMB (@lem2500443) (@lem2500442)). Qed.
Lemma lem2500445 : term270 = term167.
Proof. exact (TRANS (@lem2500440) (@lem2500444)). Qed.
Lemma lem2500447 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500448 : term347 = term174.
Proof. exact (@lem2500447 term168). Qed.
Lemma lem2500449 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500450 : term467 = term461.
Proof. exact (MK_COMB (@lem2500449) (@lem2500448)). Qed.
Lemma lem2500451 : term466 = term336.
Proof. exact (MK_COMB (@lem2500450) (@lem2500445)). Qed.
Lemma lem2500453 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500454 : term336 = term337.
Proof. exact (@lem2500453 (NUMERAL 0) term168). Qed.
Lemma lem2500455 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500456 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500457 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500456 h1) (fun h1 : term337 = True => @lem2500455)). Qed.
Lemma lem2500458 : term337 = True.
Proof. exact (EQ_MP (@lem2500457) (@lem2500455)). Qed.
Lemma lem2500459 : term336 = True.
Proof. exact (TRANS (@lem2500454) (@lem2500458)). Qed.
Lemma lem2500460 : term466 = True.
Proof. exact (TRANS (@lem2500451) (@lem2500459)). Qed.
Lemma lem2500461 : term463 = True.
Proof. exact (TRANS (@lem2500437) (@lem2500460)). Qed.
Lemma lem2500462 : term336 = True.
Proof. exact (TRANS (@lem2500414) (@lem2500461)). Qed.
Lemma lem2500463 : term460 = True.
Proof. exact (TRANS (@lem2500405) (@lem2500462)). Qed.
Lemma lem2500464 : True = term460.
Proof. exact (SYM (@lem2500463)). Qed.
Lemma lem2500465 : term460.
Proof. exact (EQ_MP (@lem2500464) (@lem0)). Qed.
Lemma lem2500466 (n : int) (m : int) (h1 : term459 n m) : term478 n.
Proof. exact (conj (@lem2500465) (@lem2500250 n m h1)). Qed.
Lemma lem2500468 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2500469 (n : int) : term479 n.
Proof. exact (@lem2500468 term167 (term281 n)). Qed.
Lemma lem2500470 (n : int) (m : int) (h1 : term459 n m) : term480 n.
Proof. exact (@lem2500469 n (@lem2500466 n m h1)). Qed.
Lemma lem2500471 (n : int) : (term481 n) = (term281 n).
Proof. exact (@lem1982733 (term281 n)). Qed.
Lemma lem2500472 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2500473 (n : int) : (term482 n) = (term284 n).
Proof. exact (MK_COMB (@lem2500472) (@lem2500471 n)). Qed.
Lemma lem2500474 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2500475 (n : int) : (term480 n) = (term285 n).
Proof. exact (MK_COMB (@lem2500473 n) (@lem2500474)). Qed.
Lemma lem2500476 (n : int) (m : int) (h1 : term459 n m) : term285 n.
Proof. exact (EQ_MP (@lem2500475 n) (@lem2500470 n m h1)). Qed.
Lemma lem2500477 (n : int) (m : int) (h1 : term459 n m) : term483 m n.
Proof. exact (conj (@lem2500476 n m h1) (@lem2500402 n m h1)). Qed.
Lemma lem2500479 (x : real) (y : real) : term484 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2500480 (m : int) (n : int) : term485 m n.
Proof. exact (@lem2500479 (term281 n) (term315 m n)). Qed.
Lemma lem2500481 (n : int) (m : int) (h1 : term459 n m) : term486 m n.
Proof. exact (@lem2500480 m n (@lem2500477 n m h1)). Qed.
Lemma lem2500482 (m : int) (n : int) : (term487 m n) = (term488 m n).
Proof. exact (@lem1982757 (term316 m) (term281 n) (term291 n)). Qed.
Lemma lem2500483 (n : int) : (term489 n) = (term490 n).
Proof. exact (@lem1982753 (term316 n) (real_of_int n) term257 term257). Qed.
Lemma lem2500484 (n : int) : (term491 n) = (term329 n).
Proof. exact (@lem1982713 term257 (real_of_int n)). Qed.
Lemma lem2500486 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500487 : term167 = term259.
Proof. exact (@lem2500486 term168). Qed.
Lemma lem2500489 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500490 : term257 = term262.
Proof. exact (@lem2500489 term168). Qed.
Lemma lem2500491 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500492 : term330 = term331.
Proof. exact (MK_COMB (@lem2500491) (@lem2500490)). Qed.
Lemma lem2500493 : term332 = term333.
Proof. exact (MK_COMB (@lem2500492) (@lem2500487)). Qed.
Lemma lem2500494 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2500496 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500497 : term336 = term337.
Proof. exact (@lem2500496 (NUMERAL 0) term168). Qed.
Lemma lem2500498 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500499 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500500 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500499 h1) (fun h1 : term337 = True => @lem2500498)). Qed.
Lemma lem2500501 : term337 = True.
Proof. exact (EQ_MP (@lem2500500) (@lem2500498)). Qed.
Lemma lem2500502 : term336 = True.
Proof. exact (TRANS (@lem2500497) (@lem2500501)). Qed.
Lemma lem2500503 : True = term336.
Proof. exact (SYM (@lem2500502)). Qed.
Lemma lem2500504 : term336.
Proof. exact (EQ_MP (@lem2500503) (@lem0)). Qed.
Lemma lem2500505 : term339.
Proof. exact (@lem2500494 (@lem2500504)). Qed.
Lemma lem2500507 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500508 : term336 = term337.
Proof. exact (@lem2500507 (NUMERAL 0) term168). Qed.
Lemma lem2500509 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500510 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500511 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500510 h1) (fun h1 : term337 = True => @lem2500509)). Qed.
Lemma lem2500512 : term337 = True.
Proof. exact (EQ_MP (@lem2500511) (@lem2500509)). Qed.
Lemma lem2500513 : term336 = True.
Proof. exact (TRANS (@lem2500508) (@lem2500512)). Qed.
Lemma lem2500514 : True = term336.
Proof. exact (SYM (@lem2500513)). Qed.
Lemma lem2500515 : term336.
Proof. exact (EQ_MP (@lem2500514) (@lem0)). Qed.
Lemma lem2500516 : term340.
Proof. exact (@lem2500505 (@lem2500515)). Qed.
Lemma lem2500518 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500519 : term336 = term337.
Proof. exact (@lem2500518 (NUMERAL 0) term168). Qed.
Lemma lem2500520 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500521 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500522 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500521 h1) (fun h1 : term337 = True => @lem2500520)). Qed.
Lemma lem2500523 : term337 = True.
Proof. exact (EQ_MP (@lem2500522) (@lem2500520)). Qed.
Lemma lem2500524 : term336 = True.
Proof. exact (TRANS (@lem2500519) (@lem2500523)). Qed.
Lemma lem2500525 : True = term336.
Proof. exact (SYM (@lem2500524)). Qed.
Lemma lem2500526 : term336.
Proof. exact (EQ_MP (@lem2500525) (@lem0)). Qed.
Lemma lem2500527 : term341.
Proof. exact (@lem2500516 (@lem2500526)). Qed.
Lemma lem2500529 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500530 : term270 = term271.
Proof. exact (@lem2500529 term168 term168). Qed.
Lemma lem2500531 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500532 : term273 = term168.
Proof. exact (EQ_MP (@lem2500531) (@lem940073)). Qed.
Lemma lem2500533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500534 : term271 = term167.
Proof. exact (MK_COMB (@lem2500533) (@lem2500532)). Qed.
Lemma lem2500535 : term270 = term167.
Proof. exact (TRANS (@lem2500530) (@lem2500534)). Qed.
Lemma lem2500537 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500538 : term265 = term276.
Proof. exact (@lem2500537 term168 term168). Qed.
Lemma lem2500539 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500540 : term273 = term168.
Proof. exact (EQ_MP (@lem2500539) (@lem940073)). Qed.
Lemma lem2500541 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500542 : term271 = term167.
Proof. exact (MK_COMB (@lem2500541) (@lem2500540)). Qed.
Lemma lem2500543 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500544 : term276 = term257.
Proof. exact (MK_COMB (@lem2500543) (@lem2500542)). Qed.
Lemma lem2500545 : term265 = term257.
Proof. exact (TRANS (@lem2500538) (@lem2500544)). Qed.
Lemma lem2500546 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500547 : term342 = term330.
Proof. exact (MK_COMB (@lem2500546) (@lem2500545)). Qed.
Lemma lem2500548 : term343 = term332.
Proof. exact (MK_COMB (@lem2500547) (@lem2500535)). Qed.
Lemma lem2500550 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2500551 : term332 = term174.
Proof. exact (@lem2500550 term168). Qed.
Lemma lem2500552 : term343 = term174.
Proof. exact (TRANS (@lem2500548) (@lem2500551)). Qed.
Lemma lem2500553 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2500554 : term345 = term209.
Proof. exact (MK_COMB (@lem2500553) (@lem2500552)). Qed.
Lemma lem2500555 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2500556 : term346 = term347.
Proof. exact (MK_COMB (@lem2500554) (@lem2500555)). Qed.
Lemma lem2500558 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500559 : term347 = term174.
Proof. exact (@lem2500558 term168). Qed.
Lemma lem2500560 : term346 = term174.
Proof. exact (TRANS (@lem2500556) (@lem2500559)). Qed.
Lemma lem2500562 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500563 : term270 = term271.
Proof. exact (@lem2500562 term168 term168). Qed.
Lemma lem2500564 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500565 : term273 = term168.
Proof. exact (EQ_MP (@lem2500564) (@lem940073)). Qed.
Lemma lem2500566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500567 : term271 = term167.
Proof. exact (MK_COMB (@lem2500566) (@lem2500565)). Qed.
Lemma lem2500568 : term270 = term167.
Proof. exact (TRANS (@lem2500563) (@lem2500567)). Qed.
Lemma lem2500569 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2500570 : term349 = term347.
Proof. exact (MK_COMB (@lem2500569) (@lem2500568)). Qed.
Lemma lem2500572 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500573 : term347 = term174.
Proof. exact (@lem2500572 term168). Qed.
Lemma lem2500574 : term349 = term174.
Proof. exact (TRANS (@lem2500570) (@lem2500573)). Qed.
Lemma lem2500575 : term174 = term349.
Proof. exact (SYM (@lem2500574)). Qed.
Lemma lem2500576 : term346 = term349.
Proof. exact (TRANS (@lem2500560) (@lem2500575)). Qed.
Lemma lem2500577 : term333 = term300.
Proof. exact (@lem2500527 (@lem2500576)). Qed.
Lemma lem2500578 : term332 = term300.
Proof. exact (TRANS (@lem2500493) (@lem2500577)). Qed.
Lemma lem2500580 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2500581 : term300 = term174.
Proof. exact (@lem2500580 term174). Qed.
Lemma lem2500582 : term332 = term174.
Proof. exact (TRANS (@lem2500578) (@lem2500581)). Qed.
Lemma lem2500583 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2500584 : term350 = term209.
Proof. exact (MK_COMB (@lem2500583) (@lem2500582)). Qed.
Lemma lem2500585 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2500586 (n : int) : (term329 n) = (term210 n).
Proof. exact (MK_COMB (@lem2500584) (@lem2500585 n)). Qed.
Lemma lem2500587 (n : int) : (term491 n) = (term210 n).
Proof. exact (TRANS (@lem2500484 n) (@lem2500586 n)). Qed.
Lemma lem2500588 (n : int) : (term210 n) = term174.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2500589 (n : int) : (term491 n) = term174.
Proof. exact (TRANS (@lem2500587 n) (@lem2500588 n)). Qed.
Lemma lem2500590 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500591 (n : int) : (term492 n) = term184.
Proof. exact (MK_COMB (@lem2500590) (@lem2500589 n)). Qed.
Lemma lem2500593 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500594 : term257 = term262.
Proof. exact (@lem2500593 term168). Qed.
Lemma lem2500596 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500597 : term257 = term262.
Proof. exact (@lem2500596 term168). Qed.
Lemma lem2500598 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500599 : term330 = term331.
Proof. exact (MK_COMB (@lem2500598) (@lem2500597)). Qed.
Lemma lem2500600 : term493 = term494.
Proof. exact (MK_COMB (@lem2500599) (@lem2500594)). Qed.
Lemma lem2500601 : term495.
Proof. exact (@lem1981473 term257 term167 term257 term167 term496 term167). Qed.
Lemma lem2500603 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500604 : term336 = term337.
Proof. exact (@lem2500603 (NUMERAL 0) term168). Qed.
Lemma lem2500605 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500606 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500607 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500606 h1) (fun h1 : term337 = True => @lem2500605)). Qed.
Lemma lem2500608 : term337 = True.
Proof. exact (EQ_MP (@lem2500607) (@lem2500605)). Qed.
Lemma lem2500609 : term336 = True.
Proof. exact (TRANS (@lem2500604) (@lem2500608)). Qed.
Lemma lem2500610 : True = term336.
Proof. exact (SYM (@lem2500609)). Qed.
Lemma lem2500611 : term336.
Proof. exact (EQ_MP (@lem2500610) (@lem0)). Qed.
Lemma lem2500612 : term497.
Proof. exact (@lem2500601 (@lem2500611)). Qed.
Lemma lem2500614 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500615 : term336 = term337.
Proof. exact (@lem2500614 (NUMERAL 0) term168). Qed.
Lemma lem2500616 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500617 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500618 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500617 h1) (fun h1 : term337 = True => @lem2500616)). Qed.
Lemma lem2500619 : term337 = True.
Proof. exact (EQ_MP (@lem2500618) (@lem2500616)). Qed.
Lemma lem2500620 : term336 = True.
Proof. exact (TRANS (@lem2500615) (@lem2500619)). Qed.
Lemma lem2500621 : True = term336.
Proof. exact (SYM (@lem2500620)). Qed.
Lemma lem2500622 : term336.
Proof. exact (EQ_MP (@lem2500621) (@lem0)). Qed.
Lemma lem2500623 : term498.
Proof. exact (@lem2500612 (@lem2500622)). Qed.
Lemma lem2500625 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500626 : term336 = term337.
Proof. exact (@lem2500625 (NUMERAL 0) term168). Qed.
Lemma lem2500627 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500628 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500629 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500628 h1) (fun h1 : term337 = True => @lem2500627)). Qed.
Lemma lem2500630 : term337 = True.
Proof. exact (EQ_MP (@lem2500629) (@lem2500627)). Qed.
Lemma lem2500631 : term336 = True.
Proof. exact (TRANS (@lem2500626) (@lem2500630)). Qed.
Lemma lem2500632 : True = term336.
Proof. exact (SYM (@lem2500631)). Qed.
Lemma lem2500633 : term336.
Proof. exact (EQ_MP (@lem2500632) (@lem0)). Qed.
Lemma lem2500634 : term499.
Proof. exact (@lem2500623 (@lem2500633)). Qed.
Lemma lem2500636 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500637 : term265 = term276.
Proof. exact (@lem2500636 term168 term168). Qed.
Lemma lem2500638 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500639 : term273 = term168.
Proof. exact (EQ_MP (@lem2500638) (@lem940073)). Qed.
Lemma lem2500640 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500641 : term271 = term167.
Proof. exact (MK_COMB (@lem2500640) (@lem2500639)). Qed.
Lemma lem2500642 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500643 : term276 = term257.
Proof. exact (MK_COMB (@lem2500642) (@lem2500641)). Qed.
Lemma lem2500644 : term265 = term257.
Proof. exact (TRANS (@lem2500637) (@lem2500643)). Qed.
Lemma lem2500646 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500647 : term265 = term276.
Proof. exact (@lem2500646 term168 term168). Qed.
Lemma lem2500648 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500649 : term273 = term168.
Proof. exact (EQ_MP (@lem2500648) (@lem940073)). Qed.
Lemma lem2500650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500651 : term271 = term167.
Proof. exact (MK_COMB (@lem2500650) (@lem2500649)). Qed.
Lemma lem2500652 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500653 : term276 = term257.
Proof. exact (MK_COMB (@lem2500652) (@lem2500651)). Qed.
Lemma lem2500654 : term265 = term257.
Proof. exact (TRANS (@lem2500647) (@lem2500653)). Qed.
Lemma lem2500655 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500656 : term342 = term330.
Proof. exact (MK_COMB (@lem2500655) (@lem2500654)). Qed.
Lemma lem2500657 : term500 = term493.
Proof. exact (MK_COMB (@lem2500656) (@lem2500644)). Qed.
Lemma lem2500658 : term493 = term501.
Proof. exact (@lem1367763 term168 term168). Qed.
Lemma lem2500659 : term502 = term503.
Proof. exact (@lem706885). Qed.
Lemma lem2500660 : (term502 = term503) = (term504 = term505).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term503). Qed.
Lemma lem2500661 : term504 = term505.
Proof. exact (EQ_MP (@lem2500660) (@lem2500659)). Qed.
Lemma lem2500662 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500663 : term506 = term507.
Proof. exact (MK_COMB (@lem2500662) (@lem2500661)). Qed.
Lemma lem2500664 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500665 : term501 = term496.
Proof. exact (MK_COMB (@lem2500664) (@lem2500663)). Qed.
Lemma lem2500666 : term493 = term496.
Proof. exact (TRANS (@lem2500658) (@lem2500665)). Qed.
Lemma lem2500667 : term500 = term496.
Proof. exact (TRANS (@lem2500657) (@lem2500666)). Qed.
Lemma lem2500668 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2500669 : term508 = term509.
Proof. exact (MK_COMB (@lem2500668) (@lem2500667)). Qed.
Lemma lem2500670 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2500671 : term510 = term511.
Proof. exact (MK_COMB (@lem2500669) (@lem2500670)). Qed.
Lemma lem2500673 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500674 : term511 = term512.
Proof. exact (@lem2500673 term505 term168). Qed.
Lemma lem2500675 : term513 = term503.
Proof. exact (@lem996237 term503). Qed.
Lemma lem2500676 : (term513 = term503) = (term514 = term505).
Proof. exact (@lem1007663 term503 (BIT1 0) term503). Qed.
Lemma lem2500677 : term514 = term505.
Proof. exact (EQ_MP (@lem2500676) (@lem2500675)). Qed.
Lemma lem2500678 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500679 : term515 = term507.
Proof. exact (MK_COMB (@lem2500678) (@lem2500677)). Qed.
Lemma lem2500680 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500681 : term512 = term496.
Proof. exact (MK_COMB (@lem2500680) (@lem2500679)). Qed.
Lemma lem2500682 : term511 = term496.
Proof. exact (TRANS (@lem2500674) (@lem2500681)). Qed.
Lemma lem2500683 : term510 = term496.
Proof. exact (TRANS (@lem2500671) (@lem2500682)). Qed.
Lemma lem2500685 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500686 : term270 = term271.
Proof. exact (@lem2500685 term168 term168). Qed.
Lemma lem2500687 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500688 : term273 = term168.
Proof. exact (EQ_MP (@lem2500687) (@lem940073)). Qed.
Lemma lem2500689 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500690 : term271 = term167.
Proof. exact (MK_COMB (@lem2500689) (@lem2500688)). Qed.
Lemma lem2500691 : term270 = term167.
Proof. exact (TRANS (@lem2500686) (@lem2500690)). Qed.
Lemma lem2500692 : term509 = term509.
Proof. exact (eq_refl term509). Qed.
Lemma lem2500693 : term516 = term511.
Proof. exact (MK_COMB (@lem2500692) (@lem2500691)). Qed.
Lemma lem2500695 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500696 : term511 = term512.
Proof. exact (@lem2500695 term505 term168). Qed.
Lemma lem2500697 : term513 = term503.
Proof. exact (@lem996237 term503). Qed.
Lemma lem2500698 : (term513 = term503) = (term514 = term505).
Proof. exact (@lem1007663 term503 (BIT1 0) term503). Qed.
Lemma lem2500699 : term514 = term505.
Proof. exact (EQ_MP (@lem2500698) (@lem2500697)). Qed.
Lemma lem2500700 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500701 : term515 = term507.
Proof. exact (MK_COMB (@lem2500700) (@lem2500699)). Qed.
Lemma lem2500702 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500703 : term512 = term496.
Proof. exact (MK_COMB (@lem2500702) (@lem2500701)). Qed.
Lemma lem2500704 : term511 = term496.
Proof. exact (TRANS (@lem2500696) (@lem2500703)). Qed.
Lemma lem2500705 : term516 = term496.
Proof. exact (TRANS (@lem2500693) (@lem2500704)). Qed.
Lemma lem2500706 : term496 = term516.
Proof. exact (SYM (@lem2500705)). Qed.
Lemma lem2500707 : term510 = term516.
Proof. exact (TRANS (@lem2500683) (@lem2500706)). Qed.
Lemma lem2500708 : term494 = term517.
Proof. exact (@lem2500634 (@lem2500707)). Qed.
Lemma lem2500709 : term493 = term517.
Proof. exact (TRANS (@lem2500600) (@lem2500708)). Qed.
Lemma lem2500711 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2500712 : term517 = term496.
Proof. exact (@lem2500711 term496). Qed.
Lemma lem2500713 : term493 = term496.
Proof. exact (TRANS (@lem2500709) (@lem2500712)). Qed.
Lemma lem2500714 (n : int) : (term490 n) = term518.
Proof. exact (MK_COMB (@lem2500591 n) (@lem2500713)). Qed.
Lemma lem2500715 (n : int) : (term489 n) = term518.
Proof. exact (TRANS (@lem2500483 n) (@lem2500714 n)). Qed.
Lemma lem2500716 : term518 = term496.
Proof. exact (@lem1982721 term496). Qed.
Lemma lem2500717 (n : int) : (term489 n) = term496.
Proof. exact (TRANS (@lem2500715 n) (@lem2500716)). Qed.
Lemma lem2500718 (m : int) : (term280 m) = (term280 m).
Proof. exact (eq_refl (term280 m)). Qed.
Lemma lem2500719 (n : int) (m : int) : (term488 m n) = (term519 m).
Proof. exact (MK_COMB (@lem2500718 m) (@lem2500717 n)). Qed.
Lemma lem2500720 (n : int) (m : int) : (term487 m n) = (term519 m).
Proof. exact (TRANS (@lem2500482 m n) (@lem2500719 n m)). Qed.
Lemma lem2500721 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2500722 (n : int) (m : int) : (term520 m n) = (term521 m).
Proof. exact (MK_COMB (@lem2500721) (@lem2500720 n m)). Qed.
Lemma lem2500723 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2500724 (n : int) (m : int) : (term486 m n) = (term522 m).
Proof. exact (MK_COMB (@lem2500722 n m) (@lem2500723)). Qed.
Lemma lem2500725 (n : int) (m : int) (h1 : term459 n m) : term522 m.
Proof. exact (EQ_MP (@lem2500724 n m) (@lem2500481 n m h1)). Qed.
Lemma lem2500727 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2500728 : term460 = term336.
Proof. exact (@lem2500727 term174 term167). Qed.
Lemma lem2500730 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500731 : term167 = term259.
Proof. exact (@lem2500730 term168). Qed.
Lemma lem2500733 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500734 : term174 = term300.
Proof. exact (@lem2500733 (NUMERAL 0)). Qed.
Lemma lem2500735 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500736 : term461 = term462.
Proof. exact (MK_COMB (@lem2500735) (@lem2500734)). Qed.
Lemma lem2500737 : term336 = term463.
Proof. exact (MK_COMB (@lem2500736) (@lem2500731)). Qed.
Lemma lem2500738 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2500740 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500741 : term336 = term337.
Proof. exact (@lem2500740 (NUMERAL 0) term168). Qed.
Lemma lem2500742 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500743 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500744 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500743 h1) (fun h1 : term337 = True => @lem2500742)). Qed.
Lemma lem2500745 : term337 = True.
Proof. exact (EQ_MP (@lem2500744) (@lem2500742)). Qed.
Lemma lem2500746 : term336 = True.
Proof. exact (TRANS (@lem2500741) (@lem2500745)). Qed.
Lemma lem2500747 : True = term336.
Proof. exact (SYM (@lem2500746)). Qed.
Lemma lem2500748 : term336.
Proof. exact (EQ_MP (@lem2500747) (@lem0)). Qed.
Lemma lem2500749 : term465.
Proof. exact (@lem2500738 (@lem2500748)). Qed.
Lemma lem2500751 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500752 : term336 = term337.
Proof. exact (@lem2500751 (NUMERAL 0) term168). Qed.
Lemma lem2500753 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500754 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500755 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500754 h1) (fun h1 : term337 = True => @lem2500753)). Qed.
Lemma lem2500756 : term337 = True.
Proof. exact (EQ_MP (@lem2500755) (@lem2500753)). Qed.
Lemma lem2500757 : term336 = True.
Proof. exact (TRANS (@lem2500752) (@lem2500756)). Qed.
Lemma lem2500758 : True = term336.
Proof. exact (SYM (@lem2500757)). Qed.
Lemma lem2500759 : term336.
Proof. exact (EQ_MP (@lem2500758) (@lem0)). Qed.
Lemma lem2500760 : term463 = term466.
Proof. exact (@lem2500749 (@lem2500759)). Qed.
Lemma lem2500762 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500763 : term270 = term271.
Proof. exact (@lem2500762 term168 term168). Qed.
Lemma lem2500764 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500765 : term273 = term168.
Proof. exact (EQ_MP (@lem2500764) (@lem940073)). Qed.
Lemma lem2500766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500767 : term271 = term167.
Proof. exact (MK_COMB (@lem2500766) (@lem2500765)). Qed.
Lemma lem2500768 : term270 = term167.
Proof. exact (TRANS (@lem2500763) (@lem2500767)). Qed.
Lemma lem2500770 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500771 : term347 = term174.
Proof. exact (@lem2500770 term168). Qed.
Lemma lem2500772 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2500773 : term467 = term461.
Proof. exact (MK_COMB (@lem2500772) (@lem2500771)). Qed.
Lemma lem2500774 : term466 = term336.
Proof. exact (MK_COMB (@lem2500773) (@lem2500768)). Qed.
Lemma lem2500776 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500777 : term336 = term337.
Proof. exact (@lem2500776 (NUMERAL 0) term168). Qed.
Lemma lem2500778 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500779 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500780 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500779 h1) (fun h1 : term337 = True => @lem2500778)). Qed.
Lemma lem2500781 : term337 = True.
Proof. exact (EQ_MP (@lem2500780) (@lem2500778)). Qed.
Lemma lem2500782 : term336 = True.
Proof. exact (TRANS (@lem2500777) (@lem2500781)). Qed.
Lemma lem2500783 : term466 = True.
Proof. exact (TRANS (@lem2500774) (@lem2500782)). Qed.
Lemma lem2500784 : term463 = True.
Proof. exact (TRANS (@lem2500760) (@lem2500783)). Qed.
Lemma lem2500785 : term336 = True.
Proof. exact (TRANS (@lem2500737) (@lem2500784)). Qed.
Lemma lem2500786 : term460 = True.
Proof. exact (TRANS (@lem2500728) (@lem2500785)). Qed.
Lemma lem2500787 : True = term460.
Proof. exact (SYM (@lem2500786)). Qed.
Lemma lem2500788 : term460.
Proof. exact (EQ_MP (@lem2500787) (@lem0)). Qed.
Lemma lem2500789 (n : int) (m : int) (h1 : term459 n m) : term523 m.
Proof. exact (conj (@lem2500788) (@lem2500725 n m h1)). Qed.
Lemma lem2500791 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2500792 (m : int) : term524 m.
Proof. exact (@lem2500791 term167 (term519 m)). Qed.
Lemma lem2500793 (n : int) (m : int) (h1 : term459 n m) : term525 m.
Proof. exact (@lem2500792 m (@lem2500789 n m h1)). Qed.
Lemma lem2500794 (m : int) : (term526 m) = (term519 m).
Proof. exact (@lem1982733 (term519 m)). Qed.
Lemma lem2500795 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2500796 (m : int) : (term527 m) = (term521 m).
Proof. exact (MK_COMB (@lem2500795) (@lem2500794 m)). Qed.
Lemma lem2500797 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2500798 (m : int) : (term525 m) = (term522 m).
Proof. exact (MK_COMB (@lem2500796 m) (@lem2500797)). Qed.
Lemma lem2500799 (n : int) (m : int) (h1 : term459 n m) : term522 m.
Proof. exact (EQ_MP (@lem2500798 m) (@lem2500793 n m h1)). Qed.
Lemma lem2500800 (n : int) (m : int) (h1 : term459 n m) : term528 m.
Proof. exact (conj (@lem2500799 n m h1) (@lem2500328 n m h1)). Qed.
Lemma lem2500802 (x : real) (y : real) : term484 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2500803 (m : int) : term529 m.
Proof. exact (@lem2500802 (term519 m) (real_of_int m)). Qed.
Lemma lem2500804 (n : int) (m : int) (h1 : term459 n m) : term530 m.
Proof. exact (@lem2500803 m (@lem2500800 n m h1)). Qed.
Lemma lem2500805 (m : int) : (term531 m) = (term532 m).
Proof. exact (@lem1982759 (term316 m) (real_of_int m) term496). Qed.
Lemma lem2500806 (m : int) : (term491 m) = (term329 m).
Proof. exact (@lem1982713 term257 (real_of_int m)). Qed.
Lemma lem2500808 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500809 : term167 = term259.
Proof. exact (@lem2500808 term168). Qed.
Lemma lem2500811 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500812 : term257 = term262.
Proof. exact (@lem2500811 term168). Qed.
Lemma lem2500813 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500814 : term330 = term331.
Proof. exact (MK_COMB (@lem2500813) (@lem2500812)). Qed.
Lemma lem2500815 : term332 = term333.
Proof. exact (MK_COMB (@lem2500814) (@lem2500809)). Qed.
Lemma lem2500816 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2500818 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500819 : term336 = term337.
Proof. exact (@lem2500818 (NUMERAL 0) term168). Qed.
Lemma lem2500820 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500821 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500822 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500821 h1) (fun h1 : term337 = True => @lem2500820)). Qed.
Lemma lem2500823 : term337 = True.
Proof. exact (EQ_MP (@lem2500822) (@lem2500820)). Qed.
Lemma lem2500824 : term336 = True.
Proof. exact (TRANS (@lem2500819) (@lem2500823)). Qed.
Lemma lem2500825 : True = term336.
Proof. exact (SYM (@lem2500824)). Qed.
Lemma lem2500826 : term336.
Proof. exact (EQ_MP (@lem2500825) (@lem0)). Qed.
Lemma lem2500827 : term339.
Proof. exact (@lem2500816 (@lem2500826)). Qed.
Lemma lem2500829 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500830 : term336 = term337.
Proof. exact (@lem2500829 (NUMERAL 0) term168). Qed.
Lemma lem2500831 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500832 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500833 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500832 h1) (fun h1 : term337 = True => @lem2500831)). Qed.
Lemma lem2500834 : term337 = True.
Proof. exact (EQ_MP (@lem2500833) (@lem2500831)). Qed.
Lemma lem2500835 : term336 = True.
Proof. exact (TRANS (@lem2500830) (@lem2500834)). Qed.
Lemma lem2500836 : True = term336.
Proof. exact (SYM (@lem2500835)). Qed.
Lemma lem2500837 : term336.
Proof. exact (EQ_MP (@lem2500836) (@lem0)). Qed.
Lemma lem2500838 : term340.
Proof. exact (@lem2500827 (@lem2500837)). Qed.
Lemma lem2500840 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500841 : term336 = term337.
Proof. exact (@lem2500840 (NUMERAL 0) term168). Qed.
Lemma lem2500842 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500843 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500844 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500843 h1) (fun h1 : term337 = True => @lem2500842)). Qed.
Lemma lem2500845 : term337 = True.
Proof. exact (EQ_MP (@lem2500844) (@lem2500842)). Qed.
Lemma lem2500846 : term336 = True.
Proof. exact (TRANS (@lem2500841) (@lem2500845)). Qed.
Lemma lem2500847 : True = term336.
Proof. exact (SYM (@lem2500846)). Qed.
Lemma lem2500848 : term336.
Proof. exact (EQ_MP (@lem2500847) (@lem0)). Qed.
Lemma lem2500849 : term341.
Proof. exact (@lem2500838 (@lem2500848)). Qed.
Lemma lem2500851 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500852 : term270 = term271.
Proof. exact (@lem2500851 term168 term168). Qed.
Lemma lem2500853 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500854 : term273 = term168.
Proof. exact (EQ_MP (@lem2500853) (@lem940073)). Qed.
Lemma lem2500855 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500856 : term271 = term167.
Proof. exact (MK_COMB (@lem2500855) (@lem2500854)). Qed.
Lemma lem2500857 : term270 = term167.
Proof. exact (TRANS (@lem2500852) (@lem2500856)). Qed.
Lemma lem2500859 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500860 : term265 = term276.
Proof. exact (@lem2500859 term168 term168). Qed.
Lemma lem2500861 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500862 : term273 = term168.
Proof. exact (EQ_MP (@lem2500861) (@lem940073)). Qed.
Lemma lem2500863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500864 : term271 = term167.
Proof. exact (MK_COMB (@lem2500863) (@lem2500862)). Qed.
Lemma lem2500865 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500866 : term276 = term257.
Proof. exact (MK_COMB (@lem2500865) (@lem2500864)). Qed.
Lemma lem2500867 : term265 = term257.
Proof. exact (TRANS (@lem2500860) (@lem2500866)). Qed.
Lemma lem2500868 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500869 : term342 = term330.
Proof. exact (MK_COMB (@lem2500868) (@lem2500867)). Qed.
Lemma lem2500870 : term343 = term332.
Proof. exact (MK_COMB (@lem2500869) (@lem2500857)). Qed.
Lemma lem2500872 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2500873 : term332 = term174.
Proof. exact (@lem2500872 term168). Qed.
Lemma lem2500874 : term343 = term174.
Proof. exact (TRANS (@lem2500870) (@lem2500873)). Qed.
Lemma lem2500875 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2500876 : term345 = term209.
Proof. exact (MK_COMB (@lem2500875) (@lem2500874)). Qed.
Lemma lem2500877 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2500878 : term346 = term347.
Proof. exact (MK_COMB (@lem2500876) (@lem2500877)). Qed.
Lemma lem2500880 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500881 : term347 = term174.
Proof. exact (@lem2500880 term168). Qed.
Lemma lem2500882 : term346 = term174.
Proof. exact (TRANS (@lem2500878) (@lem2500881)). Qed.
Lemma lem2500884 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2500885 : term270 = term271.
Proof. exact (@lem2500884 term168 term168). Qed.
Lemma lem2500886 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2500887 : term273 = term168.
Proof. exact (EQ_MP (@lem2500886) (@lem940073)). Qed.
Lemma lem2500888 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500889 : term271 = term167.
Proof. exact (MK_COMB (@lem2500888) (@lem2500887)). Qed.
Lemma lem2500890 : term270 = term167.
Proof. exact (TRANS (@lem2500885) (@lem2500889)). Qed.
Lemma lem2500891 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2500892 : term349 = term347.
Proof. exact (MK_COMB (@lem2500891) (@lem2500890)). Qed.
Lemma lem2500894 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500895 : term347 = term174.
Proof. exact (@lem2500894 term168). Qed.
Lemma lem2500896 : term349 = term174.
Proof. exact (TRANS (@lem2500892) (@lem2500895)). Qed.
Lemma lem2500897 : term174 = term349.
Proof. exact (SYM (@lem2500896)). Qed.
Lemma lem2500898 : term346 = term349.
Proof. exact (TRANS (@lem2500882) (@lem2500897)). Qed.
Lemma lem2500899 : term333 = term300.
Proof. exact (@lem2500849 (@lem2500898)). Qed.
Lemma lem2500900 : term332 = term300.
Proof. exact (TRANS (@lem2500815) (@lem2500899)). Qed.
Lemma lem2500902 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2500903 : term300 = term174.
Proof. exact (@lem2500902 term174). Qed.
Lemma lem2500904 : term332 = term174.
Proof. exact (TRANS (@lem2500900) (@lem2500903)). Qed.
Lemma lem2500905 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2500906 : term350 = term209.
Proof. exact (MK_COMB (@lem2500905) (@lem2500904)). Qed.
Lemma lem2500907 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2500908 (m : int) : (term329 m) = (term210 m).
Proof. exact (MK_COMB (@lem2500906) (@lem2500907 m)). Qed.
Lemma lem2500909 (m : int) : (term491 m) = (term210 m).
Proof. exact (TRANS (@lem2500806 m) (@lem2500908 m)). Qed.
Lemma lem2500910 (m : int) : (term210 m) = term174.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2500911 (m : int) : (term491 m) = term174.
Proof. exact (TRANS (@lem2500909 m) (@lem2500910 m)). Qed.
Lemma lem2500912 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2500913 (m : int) : (term492 m) = term184.
Proof. exact (MK_COMB (@lem2500912) (@lem2500911 m)). Qed.
Lemma lem2500914 : term496 = term496.
Proof. exact (eq_refl term496). Qed.
Lemma lem2500915 (m : int) : (term532 m) = term518.
Proof. exact (MK_COMB (@lem2500913 m) (@lem2500914)). Qed.
Lemma lem2500916 (m : int) : (term531 m) = term518.
Proof. exact (TRANS (@lem2500805 m) (@lem2500915 m)). Qed.
Lemma lem2500917 : term518 = term496.
Proof. exact (@lem1982721 term496). Qed.
Lemma lem2500918 (m : int) : (term531 m) = term496.
Proof. exact (TRANS (@lem2500916 m) (@lem2500917)). Qed.
Lemma lem2500919 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2500920 (m : int) : (term533 m) = term534.
Proof. exact (MK_COMB (@lem2500919) (@lem2500918 m)). Qed.
Lemma lem2500921 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2500922 (m : int) : (term530 m) = term535.
Proof. exact (MK_COMB (@lem2500920 m) (@lem2500921)). Qed.
Lemma lem2500923 (n : int) (m : int) (h1 : term459 n m) : term535.
Proof. exact (EQ_MP (@lem2500922 m) (@lem2500804 n m h1)). Qed.
Lemma lem2500925 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2500926 : term535 = term536.
Proof. exact (@lem2500925 term174 term496). Qed.
Lemma lem2500928 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2500929 : term496 = term517.
Proof. exact (@lem2500928 term505). Qed.
Lemma lem2500931 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2500932 : term174 = term300.
Proof. exact (@lem2500931 (NUMERAL 0)). Qed.
Lemma lem2500933 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500934 : term192 = term448.
Proof. exact (MK_COMB (@lem2500933) (@lem2500932)). Qed.
Lemma lem2500935 : term536 = term537.
Proof. exact (MK_COMB (@lem2500934) (@lem2500929)). Qed.
Lemma lem2500936 : term538.
Proof. exact (@lem1980026 term174 term167 term496 term167). Qed.
Lemma lem2500938 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500939 : term336 = term337.
Proof. exact (@lem2500938 (NUMERAL 0) term168). Qed.
Lemma lem2500940 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500941 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500942 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500941 h1) (fun h1 : term337 = True => @lem2500940)). Qed.
Lemma lem2500943 : term337 = True.
Proof. exact (EQ_MP (@lem2500942) (@lem2500940)). Qed.
Lemma lem2500944 : term336 = True.
Proof. exact (TRANS (@lem2500939) (@lem2500943)). Qed.
Lemma lem2500945 : True = term336.
Proof. exact (SYM (@lem2500944)). Qed.
Lemma lem2500946 : term336.
Proof. exact (EQ_MP (@lem2500945) (@lem0)). Qed.
Lemma lem2500947 : term539.
Proof. exact (@lem2500936 (@lem2500946)). Qed.
Lemma lem2500949 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2500950 : term336 = term337.
Proof. exact (@lem2500949 (NUMERAL 0) term168). Qed.
Lemma lem2500951 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2500952 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2500953 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2500952 h1) (fun h1 : term337 = True => @lem2500951)). Qed.
Lemma lem2500954 : term337 = True.
Proof. exact (EQ_MP (@lem2500953) (@lem2500951)). Qed.
Lemma lem2500955 : term336 = True.
Proof. exact (TRANS (@lem2500950) (@lem2500954)). Qed.
Lemma lem2500956 : True = term336.
Proof. exact (SYM (@lem2500955)). Qed.
Lemma lem2500957 : term336.
Proof. exact (EQ_MP (@lem2500956) (@lem0)). Qed.
Lemma lem2500958 : term537 = term540.
Proof. exact (@lem2500947 (@lem2500957)). Qed.
Lemma lem2500960 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2500961 : term511 = term512.
Proof. exact (@lem2500960 term505 term168). Qed.
Lemma lem2500962 : term513 = term503.
Proof. exact (@lem996237 term503). Qed.
Lemma lem2500963 : (term513 = term503) = (term514 = term505).
Proof. exact (@lem1007663 term503 (BIT1 0) term503). Qed.
Lemma lem2500964 : term514 = term505.
Proof. exact (EQ_MP (@lem2500963) (@lem2500962)). Qed.
Lemma lem2500965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2500966 : term515 = term507.
Proof. exact (MK_COMB (@lem2500965) (@lem2500964)). Qed.
Lemma lem2500967 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2500968 : term512 = term496.
Proof. exact (MK_COMB (@lem2500967) (@lem2500966)). Qed.
Lemma lem2500969 : term511 = term496.
Proof. exact (TRANS (@lem2500961) (@lem2500968)). Qed.
Lemma lem2500971 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2500972 : term347 = term174.
Proof. exact (@lem2500971 term168). Qed.
Lemma lem2500973 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2500974 : term453 = term192.
Proof. exact (MK_COMB (@lem2500973) (@lem2500972)). Qed.
Lemma lem2500975 : term540 = term536.
Proof. exact (MK_COMB (@lem2500974) (@lem2500969)). Qed.
Lemma lem2500977 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2500978 : term536 = term541.
Proof. exact (@lem2500977 (NUMERAL 0) term505). Qed.
Lemma lem2500979 : term542 = term503.
Proof. exact (@lem912803). Qed.
Lemma lem2500980 (h1 : term542 = term503) : (term505 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term503 h1). Qed.
Lemma lem2500981 : (term542 = term503) = ((term505 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term542 = term503 => @lem2500980 h1) (fun h1 : (term505 = (NUMERAL 0)) = False => @lem2500979)). Qed.
Lemma lem2500982 : (term505 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2500981) (@lem2500979)). Qed.
Lemma lem2500983 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2500984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2500985 : term457 = (and True).
Proof. exact (MK_COMB (@lem2500984) (@lem2500983)). Qed.
Lemma lem2500986 : term541 = (True /\ False).
Proof. exact (MK_COMB (@lem2500985) (@lem2500982)). Qed.
Lemma lem2500988 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2500989 : term541 = False.
Proof. exact (TRANS (@lem2500986) (@lem2500988)). Qed.
Lemma lem2500990 : term536 = False.
Proof. exact (TRANS (@lem2500978) (@lem2500989)). Qed.
Lemma lem2500991 : term540 = False.
Proof. exact (TRANS (@lem2500975) (@lem2500990)). Qed.
Lemma lem2500992 : term537 = False.
Proof. exact (TRANS (@lem2500958) (@lem2500991)). Qed.
Lemma lem2500993 : term536 = False.
Proof. exact (TRANS (@lem2500935) (@lem2500992)). Qed.
Lemma lem2500994 : term535 = False.
Proof. exact (TRANS (@lem2500926) (@lem2500993)). Qed.
Lemma lem2500995 (n : int) (m : int) (h1 : term459 n m) : False.
Proof. exact (EQ_MP (@lem2500994) (@lem2500923 n m h1)). Qed.
Lemma lem2500996 (n : int) (m : int) (h1 : term543 n m) : term543 n m.
Proof. exact (h1). Qed.
Lemma lem2500997 (n : int) (m : int) (h1 : term543 n m) : term402 n m.
Proof. exact (proj2 (@lem2500996 n m h1)). Qed.
Lemma lem2500999 (n : int) (m : int) (h1 : term543 n m) : term390 n m.
Proof. exact (proj2 (@lem2500997 n m h1)). Qed.
Lemma lem2501000 (n : int) (m : int) (h1 : term543 n m) : term310 m.
Proof. exact (proj1 (@lem2500997 n m h1)). Qed.
Lemma lem2501001 (n : int) (m : int) (h1 : term543 n m) : term285 m.
Proof. exact (proj2 (@lem2500999 n m h1)). Qed.
Lemma lem2501004 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2501005 : term460 = term336.
Proof. exact (@lem2501004 term174 term167). Qed.
Lemma lem2501007 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501008 : term167 = term259.
Proof. exact (@lem2501007 term168). Qed.
Lemma lem2501010 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501011 : term174 = term300.
Proof. exact (@lem2501010 (NUMERAL 0)). Qed.
Lemma lem2501012 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501013 : term461 = term462.
Proof. exact (MK_COMB (@lem2501012) (@lem2501011)). Qed.
Lemma lem2501014 : term336 = term463.
Proof. exact (MK_COMB (@lem2501013) (@lem2501008)). Qed.
Lemma lem2501015 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2501017 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501018 : term336 = term337.
Proof. exact (@lem2501017 (NUMERAL 0) term168). Qed.
Lemma lem2501019 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501020 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501021 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501020 h1) (fun h1 : term337 = True => @lem2501019)). Qed.
Lemma lem2501022 : term337 = True.
Proof. exact (EQ_MP (@lem2501021) (@lem2501019)). Qed.
Lemma lem2501023 : term336 = True.
Proof. exact (TRANS (@lem2501018) (@lem2501022)). Qed.
Lemma lem2501024 : True = term336.
Proof. exact (SYM (@lem2501023)). Qed.
Lemma lem2501025 : term336.
Proof. exact (EQ_MP (@lem2501024) (@lem0)). Qed.
Lemma lem2501026 : term465.
Proof. exact (@lem2501015 (@lem2501025)). Qed.
Lemma lem2501028 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501029 : term336 = term337.
Proof. exact (@lem2501028 (NUMERAL 0) term168). Qed.
Lemma lem2501030 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501031 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501032 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501031 h1) (fun h1 : term337 = True => @lem2501030)). Qed.
Lemma lem2501033 : term337 = True.
Proof. exact (EQ_MP (@lem2501032) (@lem2501030)). Qed.
Lemma lem2501034 : term336 = True.
Proof. exact (TRANS (@lem2501029) (@lem2501033)). Qed.
Lemma lem2501035 : True = term336.
Proof. exact (SYM (@lem2501034)). Qed.
Lemma lem2501036 : term336.
Proof. exact (EQ_MP (@lem2501035) (@lem0)). Qed.
Lemma lem2501037 : term463 = term466.
Proof. exact (@lem2501026 (@lem2501036)). Qed.
Lemma lem2501039 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501040 : term270 = term271.
Proof. exact (@lem2501039 term168 term168). Qed.
Lemma lem2501041 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501042 : term273 = term168.
Proof. exact (EQ_MP (@lem2501041) (@lem940073)). Qed.
Lemma lem2501043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501044 : term271 = term167.
Proof. exact (MK_COMB (@lem2501043) (@lem2501042)). Qed.
Lemma lem2501045 : term270 = term167.
Proof. exact (TRANS (@lem2501040) (@lem2501044)). Qed.
Lemma lem2501047 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501048 : term347 = term174.
Proof. exact (@lem2501047 term168). Qed.
Lemma lem2501049 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501050 : term467 = term461.
Proof. exact (MK_COMB (@lem2501049) (@lem2501048)). Qed.
Lemma lem2501051 : term466 = term336.
Proof. exact (MK_COMB (@lem2501050) (@lem2501045)). Qed.
Lemma lem2501053 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501054 : term336 = term337.
Proof. exact (@lem2501053 (NUMERAL 0) term168). Qed.
Lemma lem2501055 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501056 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501057 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501056 h1) (fun h1 : term337 = True => @lem2501055)). Qed.
Lemma lem2501058 : term337 = True.
Proof. exact (EQ_MP (@lem2501057) (@lem2501055)). Qed.
Lemma lem2501059 : term336 = True.
Proof. exact (TRANS (@lem2501054) (@lem2501058)). Qed.
Lemma lem2501060 : term466 = True.
Proof. exact (TRANS (@lem2501051) (@lem2501059)). Qed.
Lemma lem2501061 : term463 = True.
Proof. exact (TRANS (@lem2501037) (@lem2501060)). Qed.
Lemma lem2501062 : term336 = True.
Proof. exact (TRANS (@lem2501014) (@lem2501061)). Qed.
Lemma lem2501063 : term460 = True.
Proof. exact (TRANS (@lem2501005) (@lem2501062)). Qed.
Lemma lem2501064 : True = term460.
Proof. exact (SYM (@lem2501063)). Qed.
Lemma lem2501065 : term460.
Proof. exact (EQ_MP (@lem2501064) (@lem0)). Qed.
Lemma lem2501066 (n : int) (m : int) (h1 : term543 n m) : term468 m.
Proof. exact (conj (@lem2501065) (@lem2501000 n m h1)). Qed.
Lemma lem2501068 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2501069 (m : int) : term470 m.
Proof. exact (@lem2501068 term167 (real_of_int m)). Qed.
Lemma lem2501070 (n : int) (m : int) (h1 : term543 n m) : term471 m.
Proof. exact (@lem2501069 m (@lem2501066 n m h1)). Qed.
Lemma lem2501071 (m : int) : (term425 m) = (real_of_int m).
Proof. exact (@lem1982733 (real_of_int m)). Qed.
Lemma lem2501072 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501073 (m : int) : (term472 m) = (term309 m).
Proof. exact (MK_COMB (@lem2501072) (@lem2501071 m)). Qed.
Lemma lem2501074 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501075 (m : int) : (term471 m) = (term310 m).
Proof. exact (MK_COMB (@lem2501073 m) (@lem2501074)). Qed.
Lemma lem2501076 (n : int) (m : int) (h1 : term543 n m) : term310 m.
Proof. exact (EQ_MP (@lem2501075 m) (@lem2501070 n m h1)). Qed.
Lemma lem2501078 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2501079 : term460 = term336.
Proof. exact (@lem2501078 term174 term167). Qed.
Lemma lem2501081 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501082 : term167 = term259.
Proof. exact (@lem2501081 term168). Qed.
Lemma lem2501084 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501085 : term174 = term300.
Proof. exact (@lem2501084 (NUMERAL 0)). Qed.
Lemma lem2501086 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501087 : term461 = term462.
Proof. exact (MK_COMB (@lem2501086) (@lem2501085)). Qed.
Lemma lem2501088 : term336 = term463.
Proof. exact (MK_COMB (@lem2501087) (@lem2501082)). Qed.
Lemma lem2501089 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2501091 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501092 : term336 = term337.
Proof. exact (@lem2501091 (NUMERAL 0) term168). Qed.
Lemma lem2501093 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501094 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501095 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501094 h1) (fun h1 : term337 = True => @lem2501093)). Qed.
Lemma lem2501096 : term337 = True.
Proof. exact (EQ_MP (@lem2501095) (@lem2501093)). Qed.
Lemma lem2501097 : term336 = True.
Proof. exact (TRANS (@lem2501092) (@lem2501096)). Qed.
Lemma lem2501098 : True = term336.
Proof. exact (SYM (@lem2501097)). Qed.
Lemma lem2501099 : term336.
Proof. exact (EQ_MP (@lem2501098) (@lem0)). Qed.
Lemma lem2501100 : term465.
Proof. exact (@lem2501089 (@lem2501099)). Qed.
Lemma lem2501102 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501103 : term336 = term337.
Proof. exact (@lem2501102 (NUMERAL 0) term168). Qed.
Lemma lem2501104 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501105 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501106 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501105 h1) (fun h1 : term337 = True => @lem2501104)). Qed.
Lemma lem2501107 : term337 = True.
Proof. exact (EQ_MP (@lem2501106) (@lem2501104)). Qed.
Lemma lem2501108 : term336 = True.
Proof. exact (TRANS (@lem2501103) (@lem2501107)). Qed.
Lemma lem2501109 : True = term336.
Proof. exact (SYM (@lem2501108)). Qed.
Lemma lem2501110 : term336.
Proof. exact (EQ_MP (@lem2501109) (@lem0)). Qed.
Lemma lem2501111 : term463 = term466.
Proof. exact (@lem2501100 (@lem2501110)). Qed.
Lemma lem2501113 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501114 : term270 = term271.
Proof. exact (@lem2501113 term168 term168). Qed.
Lemma lem2501115 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501116 : term273 = term168.
Proof. exact (EQ_MP (@lem2501115) (@lem940073)). Qed.
Lemma lem2501117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501118 : term271 = term167.
Proof. exact (MK_COMB (@lem2501117) (@lem2501116)). Qed.
Lemma lem2501119 : term270 = term167.
Proof. exact (TRANS (@lem2501114) (@lem2501118)). Qed.
Lemma lem2501121 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501122 : term347 = term174.
Proof. exact (@lem2501121 term168). Qed.
Lemma lem2501123 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501124 : term467 = term461.
Proof. exact (MK_COMB (@lem2501123) (@lem2501122)). Qed.
Lemma lem2501125 : term466 = term336.
Proof. exact (MK_COMB (@lem2501124) (@lem2501119)). Qed.
Lemma lem2501127 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501128 : term336 = term337.
Proof. exact (@lem2501127 (NUMERAL 0) term168). Qed.
Lemma lem2501129 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501130 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501131 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501130 h1) (fun h1 : term337 = True => @lem2501129)). Qed.
Lemma lem2501132 : term337 = True.
Proof. exact (EQ_MP (@lem2501131) (@lem2501129)). Qed.
Lemma lem2501133 : term336 = True.
Proof. exact (TRANS (@lem2501128) (@lem2501132)). Qed.
Lemma lem2501134 : term466 = True.
Proof. exact (TRANS (@lem2501125) (@lem2501133)). Qed.
Lemma lem2501135 : term463 = True.
Proof. exact (TRANS (@lem2501111) (@lem2501134)). Qed.
Lemma lem2501136 : term336 = True.
Proof. exact (TRANS (@lem2501088) (@lem2501135)). Qed.
Lemma lem2501137 : term460 = True.
Proof. exact (TRANS (@lem2501079) (@lem2501136)). Qed.
Lemma lem2501138 : True = term460.
Proof. exact (SYM (@lem2501137)). Qed.
Lemma lem2501139 : term460.
Proof. exact (EQ_MP (@lem2501138) (@lem0)). Qed.
Lemma lem2501140 (n : int) (m : int) (h1 : term543 n m) : term478 m.
Proof. exact (conj (@lem2501139) (@lem2501001 n m h1)). Qed.
Lemma lem2501142 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2501143 (m : int) : term479 m.
Proof. exact (@lem2501142 term167 (term281 m)). Qed.
Lemma lem2501144 (n : int) (m : int) (h1 : term543 n m) : term480 m.
Proof. exact (@lem2501143 m (@lem2501140 n m h1)). Qed.
Lemma lem2501145 (m : int) : (term481 m) = (term281 m).
Proof. exact (@lem1982733 (term281 m)). Qed.
Lemma lem2501146 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501147 (m : int) : (term482 m) = (term284 m).
Proof. exact (MK_COMB (@lem2501146) (@lem2501145 m)). Qed.
Lemma lem2501148 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501149 (m : int) : (term480 m) = (term285 m).
Proof. exact (MK_COMB (@lem2501147 m) (@lem2501148)). Qed.
Lemma lem2501150 (n : int) (m : int) (h1 : term543 n m) : term285 m.
Proof. exact (EQ_MP (@lem2501149 m) (@lem2501144 n m h1)). Qed.
Lemma lem2501151 (n : int) (m : int) (h1 : term543 n m) : term544 m.
Proof. exact (conj (@lem2501150 n m h1) (@lem2501076 n m h1)). Qed.
Lemma lem2501153 (x : real) (y : real) : term484 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2501154 (m : int) : term545 m.
Proof. exact (@lem2501153 (term281 m) (real_of_int m)). Qed.
Lemma lem2501155 (n : int) (m : int) (h1 : term543 n m) : term546 m.
Proof. exact (@lem2501154 m (@lem2501151 n m h1)). Qed.
Lemma lem2501156 (m : int) : (term547 m) = (term548 m).
Proof. exact (@lem1982759 (term316 m) (real_of_int m) term257). Qed.
Lemma lem2501157 (m : int) : (term491 m) = (term329 m).
Proof. exact (@lem1982713 term257 (real_of_int m)). Qed.
Lemma lem2501159 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501160 : term167 = term259.
Proof. exact (@lem2501159 term168). Qed.
Lemma lem2501162 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2501163 : term257 = term262.
Proof. exact (@lem2501162 term168). Qed.
Lemma lem2501164 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501165 : term330 = term331.
Proof. exact (MK_COMB (@lem2501164) (@lem2501163)). Qed.
Lemma lem2501166 : term332 = term333.
Proof. exact (MK_COMB (@lem2501165) (@lem2501160)). Qed.
Lemma lem2501167 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2501169 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501170 : term336 = term337.
Proof. exact (@lem2501169 (NUMERAL 0) term168). Qed.
Lemma lem2501171 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501172 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501173 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501172 h1) (fun h1 : term337 = True => @lem2501171)). Qed.
Lemma lem2501174 : term337 = True.
Proof. exact (EQ_MP (@lem2501173) (@lem2501171)). Qed.
Lemma lem2501175 : term336 = True.
Proof. exact (TRANS (@lem2501170) (@lem2501174)). Qed.
Lemma lem2501176 : True = term336.
Proof. exact (SYM (@lem2501175)). Qed.
Lemma lem2501177 : term336.
Proof. exact (EQ_MP (@lem2501176) (@lem0)). Qed.
Lemma lem2501178 : term339.
Proof. exact (@lem2501167 (@lem2501177)). Qed.
Lemma lem2501180 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501181 : term336 = term337.
Proof. exact (@lem2501180 (NUMERAL 0) term168). Qed.
Lemma lem2501182 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501183 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501184 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501183 h1) (fun h1 : term337 = True => @lem2501182)). Qed.
Lemma lem2501185 : term337 = True.
Proof. exact (EQ_MP (@lem2501184) (@lem2501182)). Qed.
Lemma lem2501186 : term336 = True.
Proof. exact (TRANS (@lem2501181) (@lem2501185)). Qed.
Lemma lem2501187 : True = term336.
Proof. exact (SYM (@lem2501186)). Qed.
Lemma lem2501188 : term336.
Proof. exact (EQ_MP (@lem2501187) (@lem0)). Qed.
Lemma lem2501189 : term340.
Proof. exact (@lem2501178 (@lem2501188)). Qed.
Lemma lem2501191 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501192 : term336 = term337.
Proof. exact (@lem2501191 (NUMERAL 0) term168). Qed.
Lemma lem2501193 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501194 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501195 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501194 h1) (fun h1 : term337 = True => @lem2501193)). Qed.
Lemma lem2501196 : term337 = True.
Proof. exact (EQ_MP (@lem2501195) (@lem2501193)). Qed.
Lemma lem2501197 : term336 = True.
Proof. exact (TRANS (@lem2501192) (@lem2501196)). Qed.
Lemma lem2501198 : True = term336.
Proof. exact (SYM (@lem2501197)). Qed.
Lemma lem2501199 : term336.
Proof. exact (EQ_MP (@lem2501198) (@lem0)). Qed.
Lemma lem2501200 : term341.
Proof. exact (@lem2501189 (@lem2501199)). Qed.
Lemma lem2501202 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501203 : term270 = term271.
Proof. exact (@lem2501202 term168 term168). Qed.
Lemma lem2501204 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501205 : term273 = term168.
Proof. exact (EQ_MP (@lem2501204) (@lem940073)). Qed.
Lemma lem2501206 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501207 : term271 = term167.
Proof. exact (MK_COMB (@lem2501206) (@lem2501205)). Qed.
Lemma lem2501208 : term270 = term167.
Proof. exact (TRANS (@lem2501203) (@lem2501207)). Qed.
Lemma lem2501210 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2501211 : term265 = term276.
Proof. exact (@lem2501210 term168 term168). Qed.
Lemma lem2501212 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501213 : term273 = term168.
Proof. exact (EQ_MP (@lem2501212) (@lem940073)). Qed.
Lemma lem2501214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501215 : term271 = term167.
Proof. exact (MK_COMB (@lem2501214) (@lem2501213)). Qed.
Lemma lem2501216 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2501217 : term276 = term257.
Proof. exact (MK_COMB (@lem2501216) (@lem2501215)). Qed.
Lemma lem2501218 : term265 = term257.
Proof. exact (TRANS (@lem2501211) (@lem2501217)). Qed.
Lemma lem2501219 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501220 : term342 = term330.
Proof. exact (MK_COMB (@lem2501219) (@lem2501218)). Qed.
Lemma lem2501221 : term343 = term332.
Proof. exact (MK_COMB (@lem2501220) (@lem2501208)). Qed.
Lemma lem2501223 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2501224 : term332 = term174.
Proof. exact (@lem2501223 term168). Qed.
Lemma lem2501225 : term343 = term174.
Proof. exact (TRANS (@lem2501221) (@lem2501224)). Qed.
Lemma lem2501226 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2501227 : term345 = term209.
Proof. exact (MK_COMB (@lem2501226) (@lem2501225)). Qed.
Lemma lem2501228 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2501229 : term346 = term347.
Proof. exact (MK_COMB (@lem2501227) (@lem2501228)). Qed.
Lemma lem2501231 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501232 : term347 = term174.
Proof. exact (@lem2501231 term168). Qed.
Lemma lem2501233 : term346 = term174.
Proof. exact (TRANS (@lem2501229) (@lem2501232)). Qed.
Lemma lem2501235 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501236 : term270 = term271.
Proof. exact (@lem2501235 term168 term168). Qed.
Lemma lem2501237 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501238 : term273 = term168.
Proof. exact (EQ_MP (@lem2501237) (@lem940073)). Qed.
Lemma lem2501239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501240 : term271 = term167.
Proof. exact (MK_COMB (@lem2501239) (@lem2501238)). Qed.
Lemma lem2501241 : term270 = term167.
Proof. exact (TRANS (@lem2501236) (@lem2501240)). Qed.
Lemma lem2501242 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2501243 : term349 = term347.
Proof. exact (MK_COMB (@lem2501242) (@lem2501241)). Qed.
Lemma lem2501245 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501246 : term347 = term174.
Proof. exact (@lem2501245 term168). Qed.
Lemma lem2501247 : term349 = term174.
Proof. exact (TRANS (@lem2501243) (@lem2501246)). Qed.
Lemma lem2501248 : term174 = term349.
Proof. exact (SYM (@lem2501247)). Qed.
Lemma lem2501249 : term346 = term349.
Proof. exact (TRANS (@lem2501233) (@lem2501248)). Qed.
Lemma lem2501250 : term333 = term300.
Proof. exact (@lem2501200 (@lem2501249)). Qed.
Lemma lem2501251 : term332 = term300.
Proof. exact (TRANS (@lem2501166) (@lem2501250)). Qed.
Lemma lem2501253 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2501254 : term300 = term174.
Proof. exact (@lem2501253 term174). Qed.
Lemma lem2501255 : term332 = term174.
Proof. exact (TRANS (@lem2501251) (@lem2501254)). Qed.
Lemma lem2501256 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2501257 : term350 = term209.
Proof. exact (MK_COMB (@lem2501256) (@lem2501255)). Qed.
Lemma lem2501258 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2501259 (m : int) : (term329 m) = (term210 m).
Proof. exact (MK_COMB (@lem2501257) (@lem2501258 m)). Qed.
Lemma lem2501260 (m : int) : (term491 m) = (term210 m).
Proof. exact (TRANS (@lem2501157 m) (@lem2501259 m)). Qed.
Lemma lem2501261 (m : int) : (term210 m) = term174.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2501262 (m : int) : (term491 m) = term174.
Proof. exact (TRANS (@lem2501260 m) (@lem2501261 m)). Qed.
Lemma lem2501263 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501264 (m : int) : (term492 m) = term184.
Proof. exact (MK_COMB (@lem2501263) (@lem2501262 m)). Qed.
Lemma lem2501265 : term257 = term257.
Proof. exact (eq_refl term257). Qed.
Lemma lem2501266 (m : int) : (term548 m) = term352.
Proof. exact (MK_COMB (@lem2501264 m) (@lem2501265)). Qed.
Lemma lem2501267 (m : int) : (term547 m) = term352.
Proof. exact (TRANS (@lem2501156 m) (@lem2501266 m)). Qed.
Lemma lem2501268 : term352 = term257.
Proof. exact (@lem1982721 term257). Qed.
Lemma lem2501269 (m : int) : (term547 m) = term257.
Proof. exact (TRANS (@lem2501267 m) (@lem2501268)). Qed.
Lemma lem2501270 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501271 (m : int) : (term549 m) = term354.
Proof. exact (MK_COMB (@lem2501270) (@lem2501269 m)). Qed.
Lemma lem2501272 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501273 (m : int) : (term546 m) = term355.
Proof. exact (MK_COMB (@lem2501271 m) (@lem2501272)). Qed.
Lemma lem2501274 (n : int) (m : int) (h1 : term543 n m) : term355.
Proof. exact (EQ_MP (@lem2501273 m) (@lem2501155 n m h1)). Qed.
Lemma lem2501276 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2501277 : term355 = term447.
Proof. exact (@lem2501276 term174 term257). Qed.
Lemma lem2501279 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2501280 : term257 = term262.
Proof. exact (@lem2501279 term168). Qed.
Lemma lem2501282 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501283 : term174 = term300.
Proof. exact (@lem2501282 (NUMERAL 0)). Qed.
Lemma lem2501284 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2501285 : term192 = term448.
Proof. exact (MK_COMB (@lem2501284) (@lem2501283)). Qed.
Lemma lem2501286 : term447 = term449.
Proof. exact (MK_COMB (@lem2501285) (@lem2501280)). Qed.
Lemma lem2501287 : term450.
Proof. exact (@lem1980026 term174 term167 term257 term167). Qed.
Lemma lem2501289 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501290 : term336 = term337.
Proof. exact (@lem2501289 (NUMERAL 0) term168). Qed.
Lemma lem2501291 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501292 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501293 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501292 h1) (fun h1 : term337 = True => @lem2501291)). Qed.
Lemma lem2501294 : term337 = True.
Proof. exact (EQ_MP (@lem2501293) (@lem2501291)). Qed.
Lemma lem2501295 : term336 = True.
Proof. exact (TRANS (@lem2501290) (@lem2501294)). Qed.
Lemma lem2501296 : True = term336.
Proof. exact (SYM (@lem2501295)). Qed.
Lemma lem2501297 : term336.
Proof. exact (EQ_MP (@lem2501296) (@lem0)). Qed.
Lemma lem2501298 : term451.
Proof. exact (@lem2501287 (@lem2501297)). Qed.
Lemma lem2501300 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501301 : term336 = term337.
Proof. exact (@lem2501300 (NUMERAL 0) term168). Qed.
Lemma lem2501302 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501303 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501304 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501303 h1) (fun h1 : term337 = True => @lem2501302)). Qed.
Lemma lem2501305 : term337 = True.
Proof. exact (EQ_MP (@lem2501304) (@lem2501302)). Qed.
Lemma lem2501306 : term336 = True.
Proof. exact (TRANS (@lem2501301) (@lem2501305)). Qed.
Lemma lem2501307 : True = term336.
Proof. exact (SYM (@lem2501306)). Qed.
Lemma lem2501308 : term336.
Proof. exact (EQ_MP (@lem2501307) (@lem0)). Qed.
Lemma lem2501309 : term449 = term452.
Proof. exact (@lem2501298 (@lem2501308)). Qed.
Lemma lem2501311 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2501312 : term265 = term276.
Proof. exact (@lem2501311 term168 term168). Qed.
Lemma lem2501313 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501314 : term273 = term168.
Proof. exact (EQ_MP (@lem2501313) (@lem940073)). Qed.
Lemma lem2501315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501316 : term271 = term167.
Proof. exact (MK_COMB (@lem2501315) (@lem2501314)). Qed.
Lemma lem2501317 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2501318 : term276 = term257.
Proof. exact (MK_COMB (@lem2501317) (@lem2501316)). Qed.
Lemma lem2501319 : term265 = term257.
Proof. exact (TRANS (@lem2501312) (@lem2501318)). Qed.
Lemma lem2501321 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501322 : term347 = term174.
Proof. exact (@lem2501321 term168). Qed.
Lemma lem2501323 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2501324 : term453 = term192.
Proof. exact (MK_COMB (@lem2501323) (@lem2501322)). Qed.
Lemma lem2501325 : term452 = term447.
Proof. exact (MK_COMB (@lem2501324) (@lem2501319)). Qed.
Lemma lem2501327 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2501328 : term447 = term456.
Proof. exact (@lem2501327 (NUMERAL 0) term168). Qed.
Lemma lem2501329 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501330 (h1 : term338 = (BIT1 0)) : (term168 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2501331 : (term338 = (BIT1 0)) = ((term168 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501330 h1) (fun h1 : (term168 = (NUMERAL 0)) = False => @lem2501329)). Qed.
Lemma lem2501332 : (term168 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2501331) (@lem2501329)). Qed.
Lemma lem2501333 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2501334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2501335 : term457 = (and True).
Proof. exact (MK_COMB (@lem2501334) (@lem2501333)). Qed.
Lemma lem2501336 : term456 = (True /\ False).
Proof. exact (MK_COMB (@lem2501335) (@lem2501332)). Qed.
Lemma lem2501338 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2501339 : term456 = False.
Proof. exact (TRANS (@lem2501336) (@lem2501338)). Qed.
Lemma lem2501340 : term447 = False.
Proof. exact (TRANS (@lem2501328) (@lem2501339)). Qed.
Lemma lem2501341 : term452 = False.
Proof. exact (TRANS (@lem2501325) (@lem2501340)). Qed.
Lemma lem2501342 : term449 = False.
Proof. exact (TRANS (@lem2501309) (@lem2501341)). Qed.
Lemma lem2501343 : term447 = False.
Proof. exact (TRANS (@lem2501286) (@lem2501342)). Qed.
Lemma lem2501344 : term355 = False.
Proof. exact (TRANS (@lem2501277) (@lem2501343)). Qed.
Lemma lem2501345 (n : int) (m : int) (h1 : term543 n m) : False.
Proof. exact (EQ_MP (@lem2501344) (@lem2501274 n m h1)). Qed.
Lemma lem2501346 (n : int) (m : int) (h1 : term407 n m) : False.
Proof. exact (or_elim (@lem2500247 n m h1) (fun h0 : term459 n m => @lem2500995 n m h0) (fun h0 : term543 n m => @lem2501345 n m h0)). Qed.
Lemma lem2501347 (m : int) (n : int) (h1 : term443 m n) : term443 m n.
Proof. exact (h1). Qed.
Lemma lem2501348 (m : int) (n : int) (h1 : term437 m n) : term437 m n.
Proof. exact (h1). Qed.
Lemma lem2501349 (m : int) (n : int) (h1 : term437 m n) : term434 m n.
Proof. exact (proj2 (@lem2501348 m n h1)). Qed.
Lemma lem2501351 (m : int) (n : int) (h1 : term437 m n) : term433 m n.
Proof. exact (proj2 (@lem2501349 m n h1)). Qed.
Lemma lem2501353 (m : int) (n : int) (h1 : term437 m n) : term432 m n.
Proof. exact (proj2 (@lem2501351 m n h1)). Qed.
Lemma lem2501354 (m : int) (n : int) (h1 : term437 m n) : term319 m n.
Proof. exact (proj1 (@lem2501351 m n h1)). Qed.
Lemma lem2501356 (m : int) (n : int) (h1 : term437 m n) : term550 m n.
Proof. exact (proj1 (@lem2501353 m n h1)). Qed.
Lemma lem2501358 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2501359 : term460 = term336.
Proof. exact (@lem2501358 term174 term167). Qed.
Lemma lem2501361 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501362 : term167 = term259.
Proof. exact (@lem2501361 term168). Qed.
Lemma lem2501364 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501365 : term174 = term300.
Proof. exact (@lem2501364 (NUMERAL 0)). Qed.
Lemma lem2501366 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501367 : term461 = term462.
Proof. exact (MK_COMB (@lem2501366) (@lem2501365)). Qed.
Lemma lem2501368 : term336 = term463.
Proof. exact (MK_COMB (@lem2501367) (@lem2501362)). Qed.
Lemma lem2501369 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2501371 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501372 : term336 = term337.
Proof. exact (@lem2501371 (NUMERAL 0) term168). Qed.
Lemma lem2501373 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501374 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501375 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501374 h1) (fun h1 : term337 = True => @lem2501373)). Qed.
Lemma lem2501376 : term337 = True.
Proof. exact (EQ_MP (@lem2501375) (@lem2501373)). Qed.
Lemma lem2501377 : term336 = True.
Proof. exact (TRANS (@lem2501372) (@lem2501376)). Qed.
Lemma lem2501378 : True = term336.
Proof. exact (SYM (@lem2501377)). Qed.
Lemma lem2501379 : term336.
Proof. exact (EQ_MP (@lem2501378) (@lem0)). Qed.
Lemma lem2501380 : term465.
Proof. exact (@lem2501369 (@lem2501379)). Qed.
Lemma lem2501382 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501383 : term336 = term337.
Proof. exact (@lem2501382 (NUMERAL 0) term168). Qed.
Lemma lem2501384 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501385 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501386 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501385 h1) (fun h1 : term337 = True => @lem2501384)). Qed.
Lemma lem2501387 : term337 = True.
Proof. exact (EQ_MP (@lem2501386) (@lem2501384)). Qed.
Lemma lem2501388 : term336 = True.
Proof. exact (TRANS (@lem2501383) (@lem2501387)). Qed.
Lemma lem2501389 : True = term336.
Proof. exact (SYM (@lem2501388)). Qed.
Lemma lem2501390 : term336.
Proof. exact (EQ_MP (@lem2501389) (@lem0)). Qed.
Lemma lem2501391 : term463 = term466.
Proof. exact (@lem2501380 (@lem2501390)). Qed.
Lemma lem2501393 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501394 : term270 = term271.
Proof. exact (@lem2501393 term168 term168). Qed.
Lemma lem2501395 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501396 : term273 = term168.
Proof. exact (EQ_MP (@lem2501395) (@lem940073)). Qed.
Lemma lem2501397 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501398 : term271 = term167.
Proof. exact (MK_COMB (@lem2501397) (@lem2501396)). Qed.
Lemma lem2501399 : term270 = term167.
Proof. exact (TRANS (@lem2501394) (@lem2501398)). Qed.
Lemma lem2501401 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501402 : term347 = term174.
Proof. exact (@lem2501401 term168). Qed.
Lemma lem2501403 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501404 : term467 = term461.
Proof. exact (MK_COMB (@lem2501403) (@lem2501402)). Qed.
Lemma lem2501405 : term466 = term336.
Proof. exact (MK_COMB (@lem2501404) (@lem2501399)). Qed.
Lemma lem2501407 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501408 : term336 = term337.
Proof. exact (@lem2501407 (NUMERAL 0) term168). Qed.
Lemma lem2501409 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501410 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501411 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501410 h1) (fun h1 : term337 = True => @lem2501409)). Qed.
Lemma lem2501412 : term337 = True.
Proof. exact (EQ_MP (@lem2501411) (@lem2501409)). Qed.
Lemma lem2501413 : term336 = True.
Proof. exact (TRANS (@lem2501408) (@lem2501412)). Qed.
Lemma lem2501414 : term466 = True.
Proof. exact (TRANS (@lem2501405) (@lem2501413)). Qed.
Lemma lem2501415 : term463 = True.
Proof. exact (TRANS (@lem2501391) (@lem2501414)). Qed.
Lemma lem2501416 : term336 = True.
Proof. exact (TRANS (@lem2501368) (@lem2501415)). Qed.
Lemma lem2501417 : term460 = True.
Proof. exact (TRANS (@lem2501359) (@lem2501416)). Qed.
Lemma lem2501418 : True = term460.
Proof. exact (SYM (@lem2501417)). Qed.
Lemma lem2501419 : term460.
Proof. exact (EQ_MP (@lem2501418) (@lem0)). Qed.
Lemma lem2501420 (m : int) (n : int) (h1 : term437 m n) : term551 m n.
Proof. exact (conj (@lem2501419) (@lem2501356 m n h1)). Qed.
Lemma lem2501422 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2501423 (m : int) (n : int) : term552 m n.
Proof. exact (@lem2501422 term167 (term553 m n)). Qed.
Lemma lem2501424 (m : int) (n : int) (h1 : term437 m n) : term554 m n.
Proof. exact (@lem2501423 m n (@lem2501420 m n h1)). Qed.
Lemma lem2501425 (m : int) (n : int) : (term555 m n) = (term553 m n).
Proof. exact (@lem1982733 (term553 m n)). Qed.
Lemma lem2501426 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501427 (m : int) (n : int) : (term556 m n) = (term557 m n).
Proof. exact (MK_COMB (@lem2501426) (@lem2501425 m n)). Qed.
Lemma lem2501428 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501429 (m : int) (n : int) : (term554 m n) = (term550 m n).
Proof. exact (MK_COMB (@lem2501427 m n) (@lem2501428)). Qed.
Lemma lem2501430 (m : int) (n : int) (h1 : term437 m n) : term550 m n.
Proof. exact (EQ_MP (@lem2501429 m n) (@lem2501424 m n h1)). Qed.
Lemma lem2501432 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2501433 : term460 = term336.
Proof. exact (@lem2501432 term174 term167). Qed.
Lemma lem2501435 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501436 : term167 = term259.
Proof. exact (@lem2501435 term168). Qed.
Lemma lem2501438 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501439 : term174 = term300.
Proof. exact (@lem2501438 (NUMERAL 0)). Qed.
Lemma lem2501440 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501441 : term461 = term462.
Proof. exact (MK_COMB (@lem2501440) (@lem2501439)). Qed.
Lemma lem2501442 : term336 = term463.
Proof. exact (MK_COMB (@lem2501441) (@lem2501436)). Qed.
Lemma lem2501443 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2501445 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501446 : term336 = term337.
Proof. exact (@lem2501445 (NUMERAL 0) term168). Qed.
Lemma lem2501447 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501448 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501449 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501448 h1) (fun h1 : term337 = True => @lem2501447)). Qed.
Lemma lem2501450 : term337 = True.
Proof. exact (EQ_MP (@lem2501449) (@lem2501447)). Qed.
Lemma lem2501451 : term336 = True.
Proof. exact (TRANS (@lem2501446) (@lem2501450)). Qed.
Lemma lem2501452 : True = term336.
Proof. exact (SYM (@lem2501451)). Qed.
Lemma lem2501453 : term336.
Proof. exact (EQ_MP (@lem2501452) (@lem0)). Qed.
Lemma lem2501454 : term465.
Proof. exact (@lem2501443 (@lem2501453)). Qed.
Lemma lem2501456 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501457 : term336 = term337.
Proof. exact (@lem2501456 (NUMERAL 0) term168). Qed.
Lemma lem2501458 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501459 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501460 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501459 h1) (fun h1 : term337 = True => @lem2501458)). Qed.
Lemma lem2501461 : term337 = True.
Proof. exact (EQ_MP (@lem2501460) (@lem2501458)). Qed.
Lemma lem2501462 : term336 = True.
Proof. exact (TRANS (@lem2501457) (@lem2501461)). Qed.
Lemma lem2501463 : True = term336.
Proof. exact (SYM (@lem2501462)). Qed.
Lemma lem2501464 : term336.
Proof. exact (EQ_MP (@lem2501463) (@lem0)). Qed.
Lemma lem2501465 : term463 = term466.
Proof. exact (@lem2501454 (@lem2501464)). Qed.
Lemma lem2501467 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501468 : term270 = term271.
Proof. exact (@lem2501467 term168 term168). Qed.
Lemma lem2501469 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501470 : term273 = term168.
Proof. exact (EQ_MP (@lem2501469) (@lem940073)). Qed.
Lemma lem2501471 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501472 : term271 = term167.
Proof. exact (MK_COMB (@lem2501471) (@lem2501470)). Qed.
Lemma lem2501473 : term270 = term167.
Proof. exact (TRANS (@lem2501468) (@lem2501472)). Qed.
Lemma lem2501475 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501476 : term347 = term174.
Proof. exact (@lem2501475 term168). Qed.
Lemma lem2501477 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501478 : term467 = term461.
Proof. exact (MK_COMB (@lem2501477) (@lem2501476)). Qed.
Lemma lem2501479 : term466 = term336.
Proof. exact (MK_COMB (@lem2501478) (@lem2501473)). Qed.
Lemma lem2501481 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501482 : term336 = term337.
Proof. exact (@lem2501481 (NUMERAL 0) term168). Qed.
Lemma lem2501483 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501484 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501485 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501484 h1) (fun h1 : term337 = True => @lem2501483)). Qed.
Lemma lem2501486 : term337 = True.
Proof. exact (EQ_MP (@lem2501485) (@lem2501483)). Qed.
Lemma lem2501487 : term336 = True.
Proof. exact (TRANS (@lem2501482) (@lem2501486)). Qed.
Lemma lem2501488 : term466 = True.
Proof. exact (TRANS (@lem2501479) (@lem2501487)). Qed.
Lemma lem2501489 : term463 = True.
Proof. exact (TRANS (@lem2501465) (@lem2501488)). Qed.
Lemma lem2501490 : term336 = True.
Proof. exact (TRANS (@lem2501442) (@lem2501489)). Qed.
Lemma lem2501491 : term460 = True.
Proof. exact (TRANS (@lem2501433) (@lem2501490)). Qed.
Lemma lem2501492 : True = term460.
Proof. exact (SYM (@lem2501491)). Qed.
Lemma lem2501493 : term460.
Proof. exact (EQ_MP (@lem2501492) (@lem0)). Qed.
Lemma lem2501494 (m : int) (n : int) (h1 : term437 m n) : term473 m n.
Proof. exact (conj (@lem2501493) (@lem2501354 m n h1)). Qed.
Lemma lem2501496 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2501497 (m : int) (n : int) : term474 m n.
Proof. exact (@lem2501496 term167 (term315 m n)). Qed.
Lemma lem2501498 (m : int) (n : int) (h1 : term437 m n) : term475 m n.
Proof. exact (@lem2501497 m n (@lem2501494 m n h1)). Qed.
Lemma lem2501499 (m : int) (n : int) : (term476 m n) = (term315 m n).
Proof. exact (@lem1982733 (term315 m n)). Qed.
Lemma lem2501500 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501501 (m : int) (n : int) : (term477 m n) = (term318 m n).
Proof. exact (MK_COMB (@lem2501500) (@lem2501499 m n)). Qed.
Lemma lem2501502 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501503 (m : int) (n : int) : (term475 m n) = (term319 m n).
Proof. exact (MK_COMB (@lem2501501 m n) (@lem2501502)). Qed.
Lemma lem2501504 (m : int) (n : int) (h1 : term437 m n) : term319 m n.
Proof. exact (EQ_MP (@lem2501503 m n) (@lem2501498 m n h1)). Qed.
Lemma lem2501505 (m : int) (n : int) (h1 : term437 m n) : term558 m n.
Proof. exact (conj (@lem2501504 m n h1) (@lem2501430 m n h1)). Qed.
Lemma lem2501507 (x : real) (y : real) : term484 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2501508 (m : int) (n : int) : term559 m n.
Proof. exact (@lem2501507 (term315 m n) (term553 m n)). Qed.
Lemma lem2501509 (m : int) (n : int) (h1 : term437 m n) : term560 m n.
Proof. exact (@lem2501508 m n (@lem2501505 m n h1)). Qed.
Lemma lem2501510 (m : int) (n : int) : (term561 m n) = (term562 m n).
Proof. exact (@lem1982753 (term316 m) (real_of_int m) (term291 n) (term316 n)). Qed.
Lemma lem2501511 (m : int) : (term491 m) = (term329 m).
Proof. exact (@lem1982713 term257 (real_of_int m)). Qed.
Lemma lem2501513 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501514 : term167 = term259.
Proof. exact (@lem2501513 term168). Qed.
Lemma lem2501516 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2501517 : term257 = term262.
Proof. exact (@lem2501516 term168). Qed.
Lemma lem2501518 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501519 : term330 = term331.
Proof. exact (MK_COMB (@lem2501518) (@lem2501517)). Qed.
Lemma lem2501520 : term332 = term333.
Proof. exact (MK_COMB (@lem2501519) (@lem2501514)). Qed.
Lemma lem2501521 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2501523 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501524 : term336 = term337.
Proof. exact (@lem2501523 (NUMERAL 0) term168). Qed.
Lemma lem2501525 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501526 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501527 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501526 h1) (fun h1 : term337 = True => @lem2501525)). Qed.
Lemma lem2501528 : term337 = True.
Proof. exact (EQ_MP (@lem2501527) (@lem2501525)). Qed.
Lemma lem2501529 : term336 = True.
Proof. exact (TRANS (@lem2501524) (@lem2501528)). Qed.
Lemma lem2501530 : True = term336.
Proof. exact (SYM (@lem2501529)). Qed.
Lemma lem2501531 : term336.
Proof. exact (EQ_MP (@lem2501530) (@lem0)). Qed.
Lemma lem2501532 : term339.
Proof. exact (@lem2501521 (@lem2501531)). Qed.
Lemma lem2501534 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501535 : term336 = term337.
Proof. exact (@lem2501534 (NUMERAL 0) term168). Qed.
Lemma lem2501536 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501537 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501538 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501537 h1) (fun h1 : term337 = True => @lem2501536)). Qed.
Lemma lem2501539 : term337 = True.
Proof. exact (EQ_MP (@lem2501538) (@lem2501536)). Qed.
Lemma lem2501540 : term336 = True.
Proof. exact (TRANS (@lem2501535) (@lem2501539)). Qed.
Lemma lem2501541 : True = term336.
Proof. exact (SYM (@lem2501540)). Qed.
Lemma lem2501542 : term336.
Proof. exact (EQ_MP (@lem2501541) (@lem0)). Qed.
Lemma lem2501543 : term340.
Proof. exact (@lem2501532 (@lem2501542)). Qed.
Lemma lem2501545 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501546 : term336 = term337.
Proof. exact (@lem2501545 (NUMERAL 0) term168). Qed.
Lemma lem2501547 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501548 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501549 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501548 h1) (fun h1 : term337 = True => @lem2501547)). Qed.
Lemma lem2501550 : term337 = True.
Proof. exact (EQ_MP (@lem2501549) (@lem2501547)). Qed.
Lemma lem2501551 : term336 = True.
Proof. exact (TRANS (@lem2501546) (@lem2501550)). Qed.
Lemma lem2501552 : True = term336.
Proof. exact (SYM (@lem2501551)). Qed.
Lemma lem2501553 : term336.
Proof. exact (EQ_MP (@lem2501552) (@lem0)). Qed.
Lemma lem2501554 : term341.
Proof. exact (@lem2501543 (@lem2501553)). Qed.
Lemma lem2501556 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501557 : term270 = term271.
Proof. exact (@lem2501556 term168 term168). Qed.
Lemma lem2501558 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501559 : term273 = term168.
Proof. exact (EQ_MP (@lem2501558) (@lem940073)). Qed.
Lemma lem2501560 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501561 : term271 = term167.
Proof. exact (MK_COMB (@lem2501560) (@lem2501559)). Qed.
Lemma lem2501562 : term270 = term167.
Proof. exact (TRANS (@lem2501557) (@lem2501561)). Qed.
Lemma lem2501564 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2501565 : term265 = term276.
Proof. exact (@lem2501564 term168 term168). Qed.
Lemma lem2501566 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501567 : term273 = term168.
Proof. exact (EQ_MP (@lem2501566) (@lem940073)). Qed.
Lemma lem2501568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501569 : term271 = term167.
Proof. exact (MK_COMB (@lem2501568) (@lem2501567)). Qed.
Lemma lem2501570 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2501571 : term276 = term257.
Proof. exact (MK_COMB (@lem2501570) (@lem2501569)). Qed.
Lemma lem2501572 : term265 = term257.
Proof. exact (TRANS (@lem2501565) (@lem2501571)). Qed.
Lemma lem2501573 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501574 : term342 = term330.
Proof. exact (MK_COMB (@lem2501573) (@lem2501572)). Qed.
Lemma lem2501575 : term343 = term332.
Proof. exact (MK_COMB (@lem2501574) (@lem2501562)). Qed.
Lemma lem2501577 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2501578 : term332 = term174.
Proof. exact (@lem2501577 term168). Qed.
Lemma lem2501579 : term343 = term174.
Proof. exact (TRANS (@lem2501575) (@lem2501578)). Qed.
Lemma lem2501580 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2501581 : term345 = term209.
Proof. exact (MK_COMB (@lem2501580) (@lem2501579)). Qed.
Lemma lem2501582 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2501583 : term346 = term347.
Proof. exact (MK_COMB (@lem2501581) (@lem2501582)). Qed.
Lemma lem2501585 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501586 : term347 = term174.
Proof. exact (@lem2501585 term168). Qed.
Lemma lem2501587 : term346 = term174.
Proof. exact (TRANS (@lem2501583) (@lem2501586)). Qed.
Lemma lem2501589 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501590 : term270 = term271.
Proof. exact (@lem2501589 term168 term168). Qed.
Lemma lem2501591 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501592 : term273 = term168.
Proof. exact (EQ_MP (@lem2501591) (@lem940073)). Qed.
Lemma lem2501593 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501594 : term271 = term167.
Proof. exact (MK_COMB (@lem2501593) (@lem2501592)). Qed.
Lemma lem2501595 : term270 = term167.
Proof. exact (TRANS (@lem2501590) (@lem2501594)). Qed.
Lemma lem2501596 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2501597 : term349 = term347.
Proof. exact (MK_COMB (@lem2501596) (@lem2501595)). Qed.
Lemma lem2501599 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501600 : term347 = term174.
Proof. exact (@lem2501599 term168). Qed.
Lemma lem2501601 : term349 = term174.
Proof. exact (TRANS (@lem2501597) (@lem2501600)). Qed.
Lemma lem2501602 : term174 = term349.
Proof. exact (SYM (@lem2501601)). Qed.
Lemma lem2501603 : term346 = term349.
Proof. exact (TRANS (@lem2501587) (@lem2501602)). Qed.
Lemma lem2501604 : term333 = term300.
Proof. exact (@lem2501554 (@lem2501603)). Qed.
Lemma lem2501605 : term332 = term300.
Proof. exact (TRANS (@lem2501520) (@lem2501604)). Qed.
Lemma lem2501607 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2501608 : term300 = term174.
Proof. exact (@lem2501607 term174). Qed.
Lemma lem2501609 : term332 = term174.
Proof. exact (TRANS (@lem2501605) (@lem2501608)). Qed.
Lemma lem2501610 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2501611 : term350 = term209.
Proof. exact (MK_COMB (@lem2501610) (@lem2501609)). Qed.
Lemma lem2501612 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2501613 (m : int) : (term329 m) = (term210 m).
Proof. exact (MK_COMB (@lem2501611) (@lem2501612 m)). Qed.
Lemma lem2501614 (m : int) : (term491 m) = (term210 m).
Proof. exact (TRANS (@lem2501511 m) (@lem2501613 m)). Qed.
Lemma lem2501615 (m : int) : (term210 m) = term174.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2501616 (m : int) : (term491 m) = term174.
Proof. exact (TRANS (@lem2501614 m) (@lem2501615 m)). Qed.
Lemma lem2501617 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501618 (m : int) : (term492 m) = term184.
Proof. exact (MK_COMB (@lem2501617) (@lem2501616 m)). Qed.
Lemma lem2501619 (n : int) : (term563 n) = (term327 n).
Proof. exact (@lem1982759 (real_of_int n) (term316 n) term257). Qed.
Lemma lem2501620 (n : int) : (term328 n) = (term329 n).
Proof. exact (@lem1982715 term257 (real_of_int n)). Qed.
Lemma lem2501622 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501623 : term167 = term259.
Proof. exact (@lem2501622 term168). Qed.
Lemma lem2501625 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2501626 : term257 = term262.
Proof. exact (@lem2501625 term168). Qed.
Lemma lem2501627 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501628 : term330 = term331.
Proof. exact (MK_COMB (@lem2501627) (@lem2501626)). Qed.
Lemma lem2501629 : term332 = term333.
Proof. exact (MK_COMB (@lem2501628) (@lem2501623)). Qed.
Lemma lem2501630 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2501632 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501633 : term336 = term337.
Proof. exact (@lem2501632 (NUMERAL 0) term168). Qed.
Lemma lem2501634 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501635 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501636 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501635 h1) (fun h1 : term337 = True => @lem2501634)). Qed.
Lemma lem2501637 : term337 = True.
Proof. exact (EQ_MP (@lem2501636) (@lem2501634)). Qed.
Lemma lem2501638 : term336 = True.
Proof. exact (TRANS (@lem2501633) (@lem2501637)). Qed.
Lemma lem2501639 : True = term336.
Proof. exact (SYM (@lem2501638)). Qed.
Lemma lem2501640 : term336.
Proof. exact (EQ_MP (@lem2501639) (@lem0)). Qed.
Lemma lem2501641 : term339.
Proof. exact (@lem2501630 (@lem2501640)). Qed.
Lemma lem2501643 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501644 : term336 = term337.
Proof. exact (@lem2501643 (NUMERAL 0) term168). Qed.
Lemma lem2501645 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501646 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501647 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501646 h1) (fun h1 : term337 = True => @lem2501645)). Qed.
Lemma lem2501648 : term337 = True.
Proof. exact (EQ_MP (@lem2501647) (@lem2501645)). Qed.
Lemma lem2501649 : term336 = True.
Proof. exact (TRANS (@lem2501644) (@lem2501648)). Qed.
Lemma lem2501650 : True = term336.
Proof. exact (SYM (@lem2501649)). Qed.
Lemma lem2501651 : term336.
Proof. exact (EQ_MP (@lem2501650) (@lem0)). Qed.
Lemma lem2501652 : term340.
Proof. exact (@lem2501641 (@lem2501651)). Qed.
Lemma lem2501654 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501655 : term336 = term337.
Proof. exact (@lem2501654 (NUMERAL 0) term168). Qed.
Lemma lem2501656 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501657 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501658 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501657 h1) (fun h1 : term337 = True => @lem2501656)). Qed.
Lemma lem2501659 : term337 = True.
Proof. exact (EQ_MP (@lem2501658) (@lem2501656)). Qed.
Lemma lem2501660 : term336 = True.
Proof. exact (TRANS (@lem2501655) (@lem2501659)). Qed.
Lemma lem2501661 : True = term336.
Proof. exact (SYM (@lem2501660)). Qed.
Lemma lem2501662 : term336.
Proof. exact (EQ_MP (@lem2501661) (@lem0)). Qed.
Lemma lem2501663 : term341.
Proof. exact (@lem2501652 (@lem2501662)). Qed.
Lemma lem2501665 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501666 : term270 = term271.
Proof. exact (@lem2501665 term168 term168). Qed.
Lemma lem2501667 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501668 : term273 = term168.
Proof. exact (EQ_MP (@lem2501667) (@lem940073)). Qed.
Lemma lem2501669 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501670 : term271 = term167.
Proof. exact (MK_COMB (@lem2501669) (@lem2501668)). Qed.
Lemma lem2501671 : term270 = term167.
Proof. exact (TRANS (@lem2501666) (@lem2501670)). Qed.
Lemma lem2501673 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2501674 : term265 = term276.
Proof. exact (@lem2501673 term168 term168). Qed.
Lemma lem2501675 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501676 : term273 = term168.
Proof. exact (EQ_MP (@lem2501675) (@lem940073)). Qed.
Lemma lem2501677 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501678 : term271 = term167.
Proof. exact (MK_COMB (@lem2501677) (@lem2501676)). Qed.
Lemma lem2501679 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2501680 : term276 = term257.
Proof. exact (MK_COMB (@lem2501679) (@lem2501678)). Qed.
Lemma lem2501681 : term265 = term257.
Proof. exact (TRANS (@lem2501674) (@lem2501680)). Qed.
Lemma lem2501682 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501683 : term342 = term330.
Proof. exact (MK_COMB (@lem2501682) (@lem2501681)). Qed.
Lemma lem2501684 : term343 = term332.
Proof. exact (MK_COMB (@lem2501683) (@lem2501671)). Qed.
Lemma lem2501686 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2501687 : term332 = term174.
Proof. exact (@lem2501686 term168). Qed.
Lemma lem2501688 : term343 = term174.
Proof. exact (TRANS (@lem2501684) (@lem2501687)). Qed.
Lemma lem2501689 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2501690 : term345 = term209.
Proof. exact (MK_COMB (@lem2501689) (@lem2501688)). Qed.
Lemma lem2501691 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2501692 : term346 = term347.
Proof. exact (MK_COMB (@lem2501690) (@lem2501691)). Qed.
Lemma lem2501694 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501695 : term347 = term174.
Proof. exact (@lem2501694 term168). Qed.
Lemma lem2501696 : term346 = term174.
Proof. exact (TRANS (@lem2501692) (@lem2501695)). Qed.
Lemma lem2501698 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501699 : term270 = term271.
Proof. exact (@lem2501698 term168 term168). Qed.
Lemma lem2501700 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501701 : term273 = term168.
Proof. exact (EQ_MP (@lem2501700) (@lem940073)). Qed.
Lemma lem2501702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501703 : term271 = term167.
Proof. exact (MK_COMB (@lem2501702) (@lem2501701)). Qed.
Lemma lem2501704 : term270 = term167.
Proof. exact (TRANS (@lem2501699) (@lem2501703)). Qed.
Lemma lem2501705 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2501706 : term349 = term347.
Proof. exact (MK_COMB (@lem2501705) (@lem2501704)). Qed.
Lemma lem2501708 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501709 : term347 = term174.
Proof. exact (@lem2501708 term168). Qed.
Lemma lem2501710 : term349 = term174.
Proof. exact (TRANS (@lem2501706) (@lem2501709)). Qed.
Lemma lem2501711 : term174 = term349.
Proof. exact (SYM (@lem2501710)). Qed.
Lemma lem2501712 : term346 = term349.
Proof. exact (TRANS (@lem2501696) (@lem2501711)). Qed.
Lemma lem2501713 : term333 = term300.
Proof. exact (@lem2501663 (@lem2501712)). Qed.
Lemma lem2501714 : term332 = term300.
Proof. exact (TRANS (@lem2501629) (@lem2501713)). Qed.
Lemma lem2501716 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2501717 : term300 = term174.
Proof. exact (@lem2501716 term174). Qed.
Lemma lem2501718 : term332 = term174.
Proof. exact (TRANS (@lem2501714) (@lem2501717)). Qed.
Lemma lem2501719 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2501720 : term350 = term209.
Proof. exact (MK_COMB (@lem2501719) (@lem2501718)). Qed.
Lemma lem2501721 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2501722 (n : int) : (term329 n) = (term210 n).
Proof. exact (MK_COMB (@lem2501720) (@lem2501721 n)). Qed.
Lemma lem2501723 (n : int) : (term328 n) = (term210 n).
Proof. exact (TRANS (@lem2501620 n) (@lem2501722 n)). Qed.
Lemma lem2501724 (n : int) : (term210 n) = term174.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2501725 (n : int) : (term328 n) = term174.
Proof. exact (TRANS (@lem2501723 n) (@lem2501724 n)). Qed.
Lemma lem2501726 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501727 (n : int) : (term351 n) = term184.
Proof. exact (MK_COMB (@lem2501726) (@lem2501725 n)). Qed.
Lemma lem2501728 : term257 = term257.
Proof. exact (eq_refl term257). Qed.
Lemma lem2501729 (n : int) : (term327 n) = term352.
Proof. exact (MK_COMB (@lem2501727 n) (@lem2501728)). Qed.
Lemma lem2501730 (n : int) : (term563 n) = term352.
Proof. exact (TRANS (@lem2501619 n) (@lem2501729 n)). Qed.
Lemma lem2501731 : term352 = term257.
Proof. exact (@lem1982721 term257). Qed.
Lemma lem2501732 (n : int) : (term563 n) = term257.
Proof. exact (TRANS (@lem2501730 n) (@lem2501731)). Qed.
Lemma lem2501733 (m : int) (n : int) : (term562 m n) = term352.
Proof. exact (MK_COMB (@lem2501618 m) (@lem2501732 n)). Qed.
Lemma lem2501734 (m : int) (n : int) : (term561 m n) = term352.
Proof. exact (TRANS (@lem2501510 m n) (@lem2501733 m n)). Qed.
Lemma lem2501735 : term352 = term257.
Proof. exact (@lem1982721 term257). Qed.
Lemma lem2501736 (m : int) (n : int) : (term561 m n) = term257.
Proof. exact (TRANS (@lem2501734 m n) (@lem2501735)). Qed.
Lemma lem2501737 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501738 (m : int) (n : int) : (term564 m n) = term354.
Proof. exact (MK_COMB (@lem2501737) (@lem2501736 m n)). Qed.
Lemma lem2501739 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501740 (m : int) (n : int) : (term560 m n) = term355.
Proof. exact (MK_COMB (@lem2501738 m n) (@lem2501739)). Qed.
Lemma lem2501741 (m : int) (n : int) (h1 : term437 m n) : term355.
Proof. exact (EQ_MP (@lem2501740 m n) (@lem2501509 m n h1)). Qed.
Lemma lem2501743 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2501744 : term355 = term447.
Proof. exact (@lem2501743 term174 term257). Qed.
Lemma lem2501746 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2501747 : term257 = term262.
Proof. exact (@lem2501746 term168). Qed.
Lemma lem2501749 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501750 : term174 = term300.
Proof. exact (@lem2501749 (NUMERAL 0)). Qed.
Lemma lem2501751 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2501752 : term192 = term448.
Proof. exact (MK_COMB (@lem2501751) (@lem2501750)). Qed.
Lemma lem2501753 : term447 = term449.
Proof. exact (MK_COMB (@lem2501752) (@lem2501747)). Qed.
Lemma lem2501754 : term450.
Proof. exact (@lem1980026 term174 term167 term257 term167). Qed.
Lemma lem2501756 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501757 : term336 = term337.
Proof. exact (@lem2501756 (NUMERAL 0) term168). Qed.
Lemma lem2501758 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501759 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501760 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501759 h1) (fun h1 : term337 = True => @lem2501758)). Qed.
Lemma lem2501761 : term337 = True.
Proof. exact (EQ_MP (@lem2501760) (@lem2501758)). Qed.
Lemma lem2501762 : term336 = True.
Proof. exact (TRANS (@lem2501757) (@lem2501761)). Qed.
Lemma lem2501763 : True = term336.
Proof. exact (SYM (@lem2501762)). Qed.
Lemma lem2501764 : term336.
Proof. exact (EQ_MP (@lem2501763) (@lem0)). Qed.
Lemma lem2501765 : term451.
Proof. exact (@lem2501754 (@lem2501764)). Qed.
Lemma lem2501767 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501768 : term336 = term337.
Proof. exact (@lem2501767 (NUMERAL 0) term168). Qed.
Lemma lem2501769 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501770 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501771 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501770 h1) (fun h1 : term337 = True => @lem2501769)). Qed.
Lemma lem2501772 : term337 = True.
Proof. exact (EQ_MP (@lem2501771) (@lem2501769)). Qed.
Lemma lem2501773 : term336 = True.
Proof. exact (TRANS (@lem2501768) (@lem2501772)). Qed.
Lemma lem2501774 : True = term336.
Proof. exact (SYM (@lem2501773)). Qed.
Lemma lem2501775 : term336.
Proof. exact (EQ_MP (@lem2501774) (@lem0)). Qed.
Lemma lem2501776 : term449 = term452.
Proof. exact (@lem2501765 (@lem2501775)). Qed.
Lemma lem2501778 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2501779 : term265 = term276.
Proof. exact (@lem2501778 term168 term168). Qed.
Lemma lem2501780 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501781 : term273 = term168.
Proof. exact (EQ_MP (@lem2501780) (@lem940073)). Qed.
Lemma lem2501782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501783 : term271 = term167.
Proof. exact (MK_COMB (@lem2501782) (@lem2501781)). Qed.
Lemma lem2501784 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2501785 : term276 = term257.
Proof. exact (MK_COMB (@lem2501784) (@lem2501783)). Qed.
Lemma lem2501786 : term265 = term257.
Proof. exact (TRANS (@lem2501779) (@lem2501785)). Qed.
Lemma lem2501788 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501789 : term347 = term174.
Proof. exact (@lem2501788 term168). Qed.
Lemma lem2501790 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2501791 : term453 = term192.
Proof. exact (MK_COMB (@lem2501790) (@lem2501789)). Qed.
Lemma lem2501792 : term452 = term447.
Proof. exact (MK_COMB (@lem2501791) (@lem2501786)). Qed.
Lemma lem2501794 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2501795 : term447 = term456.
Proof. exact (@lem2501794 (NUMERAL 0) term168). Qed.
Lemma lem2501796 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501797 (h1 : term338 = (BIT1 0)) : (term168 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2501798 : (term338 = (BIT1 0)) = ((term168 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501797 h1) (fun h1 : (term168 = (NUMERAL 0)) = False => @lem2501796)). Qed.
Lemma lem2501799 : (term168 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2501798) (@lem2501796)). Qed.
Lemma lem2501800 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2501801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2501802 : term457 = (and True).
Proof. exact (MK_COMB (@lem2501801) (@lem2501800)). Qed.
Lemma lem2501803 : term456 = (True /\ False).
Proof. exact (MK_COMB (@lem2501802) (@lem2501799)). Qed.
Lemma lem2501805 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2501806 : term456 = False.
Proof. exact (TRANS (@lem2501803) (@lem2501805)). Qed.
Lemma lem2501807 : term447 = False.
Proof. exact (TRANS (@lem2501795) (@lem2501806)). Qed.
Lemma lem2501808 : term452 = False.
Proof. exact (TRANS (@lem2501792) (@lem2501807)). Qed.
Lemma lem2501809 : term449 = False.
Proof. exact (TRANS (@lem2501776) (@lem2501808)). Qed.
Lemma lem2501810 : term447 = False.
Proof. exact (TRANS (@lem2501753) (@lem2501809)). Qed.
Lemma lem2501811 : term355 = False.
Proof. exact (TRANS (@lem2501744) (@lem2501810)). Qed.
Lemma lem2501812 (m : int) (n : int) (h1 : term437 m n) : False.
Proof. exact (EQ_MP (@lem2501811) (@lem2501741 m n h1)). Qed.
Lemma lem2501813 (m : int) (n : int) (h1 : term440 m n) : term440 m n.
Proof. exact (h1). Qed.
Lemma lem2501814 (m : int) (n : int) (h1 : term440 m n) : term434 m n.
Proof. exact (proj2 (@lem2501813 m n h1)). Qed.
Lemma lem2501816 (m : int) (n : int) (h1 : term440 m n) : term433 m n.
Proof. exact (proj2 (@lem2501814 m n h1)). Qed.
Lemma lem2501818 (m : int) (n : int) (h1 : term440 m n) : term432 m n.
Proof. exact (proj2 (@lem2501816 m n h1)). Qed.
Lemma lem2501819 (m : int) (n : int) (h1 : term440 m n) : term319 m n.
Proof. exact (proj1 (@lem2501816 m n h1)). Qed.
Lemma lem2501821 (m : int) (n : int) (h1 : term440 m n) : term550 m n.
Proof. exact (proj1 (@lem2501818 m n h1)). Qed.
Lemma lem2501823 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2501824 : term460 = term336.
Proof. exact (@lem2501823 term174 term167). Qed.
Lemma lem2501826 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501827 : term167 = term259.
Proof. exact (@lem2501826 term168). Qed.
Lemma lem2501829 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501830 : term174 = term300.
Proof. exact (@lem2501829 (NUMERAL 0)). Qed.
Lemma lem2501831 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501832 : term461 = term462.
Proof. exact (MK_COMB (@lem2501831) (@lem2501830)). Qed.
Lemma lem2501833 : term336 = term463.
Proof. exact (MK_COMB (@lem2501832) (@lem2501827)). Qed.
Lemma lem2501834 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2501836 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501837 : term336 = term337.
Proof. exact (@lem2501836 (NUMERAL 0) term168). Qed.
Lemma lem2501838 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501839 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501840 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501839 h1) (fun h1 : term337 = True => @lem2501838)). Qed.
Lemma lem2501841 : term337 = True.
Proof. exact (EQ_MP (@lem2501840) (@lem2501838)). Qed.
Lemma lem2501842 : term336 = True.
Proof. exact (TRANS (@lem2501837) (@lem2501841)). Qed.
Lemma lem2501843 : True = term336.
Proof. exact (SYM (@lem2501842)). Qed.
Lemma lem2501844 : term336.
Proof. exact (EQ_MP (@lem2501843) (@lem0)). Qed.
Lemma lem2501845 : term465.
Proof. exact (@lem2501834 (@lem2501844)). Qed.
Lemma lem2501847 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501848 : term336 = term337.
Proof. exact (@lem2501847 (NUMERAL 0) term168). Qed.
Lemma lem2501849 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501850 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501851 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501850 h1) (fun h1 : term337 = True => @lem2501849)). Qed.
Lemma lem2501852 : term337 = True.
Proof. exact (EQ_MP (@lem2501851) (@lem2501849)). Qed.
Lemma lem2501853 : term336 = True.
Proof. exact (TRANS (@lem2501848) (@lem2501852)). Qed.
Lemma lem2501854 : True = term336.
Proof. exact (SYM (@lem2501853)). Qed.
Lemma lem2501855 : term336.
Proof. exact (EQ_MP (@lem2501854) (@lem0)). Qed.
Lemma lem2501856 : term463 = term466.
Proof. exact (@lem2501845 (@lem2501855)). Qed.
Lemma lem2501858 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501859 : term270 = term271.
Proof. exact (@lem2501858 term168 term168). Qed.
Lemma lem2501860 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501861 : term273 = term168.
Proof. exact (EQ_MP (@lem2501860) (@lem940073)). Qed.
Lemma lem2501862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501863 : term271 = term167.
Proof. exact (MK_COMB (@lem2501862) (@lem2501861)). Qed.
Lemma lem2501864 : term270 = term167.
Proof. exact (TRANS (@lem2501859) (@lem2501863)). Qed.
Lemma lem2501866 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501867 : term347 = term174.
Proof. exact (@lem2501866 term168). Qed.
Lemma lem2501868 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501869 : term467 = term461.
Proof. exact (MK_COMB (@lem2501868) (@lem2501867)). Qed.
Lemma lem2501870 : term466 = term336.
Proof. exact (MK_COMB (@lem2501869) (@lem2501864)). Qed.
Lemma lem2501872 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501873 : term336 = term337.
Proof. exact (@lem2501872 (NUMERAL 0) term168). Qed.
Lemma lem2501874 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501875 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501876 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501875 h1) (fun h1 : term337 = True => @lem2501874)). Qed.
Lemma lem2501877 : term337 = True.
Proof. exact (EQ_MP (@lem2501876) (@lem2501874)). Qed.
Lemma lem2501878 : term336 = True.
Proof. exact (TRANS (@lem2501873) (@lem2501877)). Qed.
Lemma lem2501879 : term466 = True.
Proof. exact (TRANS (@lem2501870) (@lem2501878)). Qed.
Lemma lem2501880 : term463 = True.
Proof. exact (TRANS (@lem2501856) (@lem2501879)). Qed.
Lemma lem2501881 : term336 = True.
Proof. exact (TRANS (@lem2501833) (@lem2501880)). Qed.
Lemma lem2501882 : term460 = True.
Proof. exact (TRANS (@lem2501824) (@lem2501881)). Qed.
Lemma lem2501883 : True = term460.
Proof. exact (SYM (@lem2501882)). Qed.
Lemma lem2501884 : term460.
Proof. exact (EQ_MP (@lem2501883) (@lem0)). Qed.
Lemma lem2501885 (m : int) (n : int) (h1 : term440 m n) : term473 m n.
Proof. exact (conj (@lem2501884) (@lem2501819 m n h1)). Qed.
Lemma lem2501887 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2501888 (m : int) (n : int) : term474 m n.
Proof. exact (@lem2501887 term167 (term315 m n)). Qed.
Lemma lem2501889 (m : int) (n : int) (h1 : term440 m n) : term475 m n.
Proof. exact (@lem2501888 m n (@lem2501885 m n h1)). Qed.
Lemma lem2501890 (m : int) (n : int) : (term476 m n) = (term315 m n).
Proof. exact (@lem1982733 (term315 m n)). Qed.
Lemma lem2501891 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501892 (m : int) (n : int) : (term477 m n) = (term318 m n).
Proof. exact (MK_COMB (@lem2501891) (@lem2501890 m n)). Qed.
Lemma lem2501893 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501894 (m : int) (n : int) : (term475 m n) = (term319 m n).
Proof. exact (MK_COMB (@lem2501892 m n) (@lem2501893)). Qed.
Lemma lem2501895 (m : int) (n : int) (h1 : term440 m n) : term319 m n.
Proof. exact (EQ_MP (@lem2501894 m n) (@lem2501889 m n h1)). Qed.
Lemma lem2501897 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2501898 : term460 = term336.
Proof. exact (@lem2501897 term174 term167). Qed.
Lemma lem2501900 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501901 : term167 = term259.
Proof. exact (@lem2501900 term168). Qed.
Lemma lem2501903 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501904 : term174 = term300.
Proof. exact (@lem2501903 (NUMERAL 0)). Qed.
Lemma lem2501905 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501906 : term461 = term462.
Proof. exact (MK_COMB (@lem2501905) (@lem2501904)). Qed.
Lemma lem2501907 : term336 = term463.
Proof. exact (MK_COMB (@lem2501906) (@lem2501901)). Qed.
Lemma lem2501908 : term464.
Proof. exact (@lem1980255 term174 term167 term167 term167). Qed.
Lemma lem2501910 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501911 : term336 = term337.
Proof. exact (@lem2501910 (NUMERAL 0) term168). Qed.
Lemma lem2501912 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501913 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501914 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501913 h1) (fun h1 : term337 = True => @lem2501912)). Qed.
Lemma lem2501915 : term337 = True.
Proof. exact (EQ_MP (@lem2501914) (@lem2501912)). Qed.
Lemma lem2501916 : term336 = True.
Proof. exact (TRANS (@lem2501911) (@lem2501915)). Qed.
Lemma lem2501917 : True = term336.
Proof. exact (SYM (@lem2501916)). Qed.
Lemma lem2501918 : term336.
Proof. exact (EQ_MP (@lem2501917) (@lem0)). Qed.
Lemma lem2501919 : term465.
Proof. exact (@lem2501908 (@lem2501918)). Qed.
Lemma lem2501921 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501922 : term336 = term337.
Proof. exact (@lem2501921 (NUMERAL 0) term168). Qed.
Lemma lem2501923 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501924 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501925 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501924 h1) (fun h1 : term337 = True => @lem2501923)). Qed.
Lemma lem2501926 : term337 = True.
Proof. exact (EQ_MP (@lem2501925) (@lem2501923)). Qed.
Lemma lem2501927 : term336 = True.
Proof. exact (TRANS (@lem2501922) (@lem2501926)). Qed.
Lemma lem2501928 : True = term336.
Proof. exact (SYM (@lem2501927)). Qed.
Lemma lem2501929 : term336.
Proof. exact (EQ_MP (@lem2501928) (@lem0)). Qed.
Lemma lem2501930 : term463 = term466.
Proof. exact (@lem2501919 (@lem2501929)). Qed.
Lemma lem2501932 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2501933 : term270 = term271.
Proof. exact (@lem2501932 term168 term168). Qed.
Lemma lem2501934 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2501935 : term273 = term168.
Proof. exact (EQ_MP (@lem2501934) (@lem940073)). Qed.
Lemma lem2501936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2501937 : term271 = term167.
Proof. exact (MK_COMB (@lem2501936) (@lem2501935)). Qed.
Lemma lem2501938 : term270 = term167.
Proof. exact (TRANS (@lem2501933) (@lem2501937)). Qed.
Lemma lem2501940 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2501941 : term347 = term174.
Proof. exact (@lem2501940 term168). Qed.
Lemma lem2501942 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2501943 : term467 = term461.
Proof. exact (MK_COMB (@lem2501942) (@lem2501941)). Qed.
Lemma lem2501944 : term466 = term336.
Proof. exact (MK_COMB (@lem2501943) (@lem2501938)). Qed.
Lemma lem2501946 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501947 : term336 = term337.
Proof. exact (@lem2501946 (NUMERAL 0) term168). Qed.
Lemma lem2501948 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501949 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501950 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501949 h1) (fun h1 : term337 = True => @lem2501948)). Qed.
Lemma lem2501951 : term337 = True.
Proof. exact (EQ_MP (@lem2501950) (@lem2501948)). Qed.
Lemma lem2501952 : term336 = True.
Proof. exact (TRANS (@lem2501947) (@lem2501951)). Qed.
Lemma lem2501953 : term466 = True.
Proof. exact (TRANS (@lem2501944) (@lem2501952)). Qed.
Lemma lem2501954 : term463 = True.
Proof. exact (TRANS (@lem2501930) (@lem2501953)). Qed.
Lemma lem2501955 : term336 = True.
Proof. exact (TRANS (@lem2501907) (@lem2501954)). Qed.
Lemma lem2501956 : term460 = True.
Proof. exact (TRANS (@lem2501898) (@lem2501955)). Qed.
Lemma lem2501957 : True = term460.
Proof. exact (SYM (@lem2501956)). Qed.
Lemma lem2501958 : term460.
Proof. exact (EQ_MP (@lem2501957) (@lem0)). Qed.
Lemma lem2501959 (m : int) (n : int) (h1 : term440 m n) : term551 m n.
Proof. exact (conj (@lem2501958) (@lem2501821 m n h1)). Qed.
Lemma lem2501961 (x : real) (y : real) : term469 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2501962 (m : int) (n : int) : term552 m n.
Proof. exact (@lem2501961 term167 (term553 m n)). Qed.
Lemma lem2501963 (m : int) (n : int) (h1 : term440 m n) : term554 m n.
Proof. exact (@lem2501962 m n (@lem2501959 m n h1)). Qed.
Lemma lem2501964 (m : int) (n : int) : (term555 m n) = (term553 m n).
Proof. exact (@lem1982733 (term553 m n)). Qed.
Lemma lem2501965 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2501966 (m : int) (n : int) : (term556 m n) = (term557 m n).
Proof. exact (MK_COMB (@lem2501965) (@lem2501964 m n)). Qed.
Lemma lem2501967 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2501968 (m : int) (n : int) : (term554 m n) = (term550 m n).
Proof. exact (MK_COMB (@lem2501966 m n) (@lem2501967)). Qed.
Lemma lem2501969 (m : int) (n : int) (h1 : term440 m n) : term550 m n.
Proof. exact (EQ_MP (@lem2501968 m n) (@lem2501963 m n h1)). Qed.
Lemma lem2501970 (m : int) (n : int) (h1 : term440 m n) : term565 m n.
Proof. exact (conj (@lem2501969 m n h1) (@lem2501895 m n h1)). Qed.
Lemma lem2501972 (x : real) (y : real) : term484 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2501973 (m : int) (n : int) : term566 m n.
Proof. exact (@lem2501972 (term553 m n) (term315 m n)). Qed.
Lemma lem2501974 (m : int) (n : int) (h1 : term440 m n) : term567 m n.
Proof. exact (@lem2501973 m n (@lem2501970 m n h1)). Qed.
Lemma lem2501975 (m : int) (n : int) : (term568 m n) = (term569 m n).
Proof. exact (@lem1982753 (real_of_int m) (term316 m) (term316 n) (term291 n)). Qed.
Lemma lem2501976 (m : int) : (term328 m) = (term329 m).
Proof. exact (@lem1982715 term257 (real_of_int m)). Qed.
Lemma lem2501978 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2501979 : term167 = term259.
Proof. exact (@lem2501978 term168). Qed.
Lemma lem2501981 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2501982 : term257 = term262.
Proof. exact (@lem2501981 term168). Qed.
Lemma lem2501983 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2501984 : term330 = term331.
Proof. exact (MK_COMB (@lem2501983) (@lem2501982)). Qed.
Lemma lem2501985 : term332 = term333.
Proof. exact (MK_COMB (@lem2501984) (@lem2501979)). Qed.
Lemma lem2501986 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2501988 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2501989 : term336 = term337.
Proof. exact (@lem2501988 (NUMERAL 0) term168). Qed.
Lemma lem2501990 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2501991 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2501992 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2501991 h1) (fun h1 : term337 = True => @lem2501990)). Qed.
Lemma lem2501993 : term337 = True.
Proof. exact (EQ_MP (@lem2501992) (@lem2501990)). Qed.
Lemma lem2501994 : term336 = True.
Proof. exact (TRANS (@lem2501989) (@lem2501993)). Qed.
Lemma lem2501995 : True = term336.
Proof. exact (SYM (@lem2501994)). Qed.
Lemma lem2501996 : term336.
Proof. exact (EQ_MP (@lem2501995) (@lem0)). Qed.
Lemma lem2501997 : term339.
Proof. exact (@lem2501986 (@lem2501996)). Qed.
Lemma lem2501999 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2502000 : term336 = term337.
Proof. exact (@lem2501999 (NUMERAL 0) term168). Qed.
Lemma lem2502001 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502002 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2502003 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502002 h1) (fun h1 : term337 = True => @lem2502001)). Qed.
Lemma lem2502004 : term337 = True.
Proof. exact (EQ_MP (@lem2502003) (@lem2502001)). Qed.
Lemma lem2502005 : term336 = True.
Proof. exact (TRANS (@lem2502000) (@lem2502004)). Qed.
Lemma lem2502006 : True = term336.
Proof. exact (SYM (@lem2502005)). Qed.
Lemma lem2502007 : term336.
Proof. exact (EQ_MP (@lem2502006) (@lem0)). Qed.
Lemma lem2502008 : term340.
Proof. exact (@lem2501997 (@lem2502007)). Qed.
Lemma lem2502010 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2502011 : term336 = term337.
Proof. exact (@lem2502010 (NUMERAL 0) term168). Qed.
Lemma lem2502012 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502013 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2502014 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502013 h1) (fun h1 : term337 = True => @lem2502012)). Qed.
Lemma lem2502015 : term337 = True.
Proof. exact (EQ_MP (@lem2502014) (@lem2502012)). Qed.
Lemma lem2502016 : term336 = True.
Proof. exact (TRANS (@lem2502011) (@lem2502015)). Qed.
Lemma lem2502017 : True = term336.
Proof. exact (SYM (@lem2502016)). Qed.
Lemma lem2502018 : term336.
Proof. exact (EQ_MP (@lem2502017) (@lem0)). Qed.
Lemma lem2502019 : term341.
Proof. exact (@lem2502008 (@lem2502018)). Qed.
Lemma lem2502021 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2502022 : term270 = term271.
Proof. exact (@lem2502021 term168 term168). Qed.
Lemma lem2502023 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2502024 : term273 = term168.
Proof. exact (EQ_MP (@lem2502023) (@lem940073)). Qed.
Lemma lem2502025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2502026 : term271 = term167.
Proof. exact (MK_COMB (@lem2502025) (@lem2502024)). Qed.
Lemma lem2502027 : term270 = term167.
Proof. exact (TRANS (@lem2502022) (@lem2502026)). Qed.
Lemma lem2502029 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2502030 : term265 = term276.
Proof. exact (@lem2502029 term168 term168). Qed.
Lemma lem2502031 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2502032 : term273 = term168.
Proof. exact (EQ_MP (@lem2502031) (@lem940073)). Qed.
Lemma lem2502033 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2502034 : term271 = term167.
Proof. exact (MK_COMB (@lem2502033) (@lem2502032)). Qed.
Lemma lem2502035 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2502036 : term276 = term257.
Proof. exact (MK_COMB (@lem2502035) (@lem2502034)). Qed.
Lemma lem2502037 : term265 = term257.
Proof. exact (TRANS (@lem2502030) (@lem2502036)). Qed.
Lemma lem2502038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2502039 : term342 = term330.
Proof. exact (MK_COMB (@lem2502038) (@lem2502037)). Qed.
Lemma lem2502040 : term343 = term332.
Proof. exact (MK_COMB (@lem2502039) (@lem2502027)). Qed.
Lemma lem2502042 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2502043 : term332 = term174.
Proof. exact (@lem2502042 term168). Qed.
Lemma lem2502044 : term343 = term174.
Proof. exact (TRANS (@lem2502040) (@lem2502043)). Qed.
Lemma lem2502045 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2502046 : term345 = term209.
Proof. exact (MK_COMB (@lem2502045) (@lem2502044)). Qed.
Lemma lem2502047 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2502048 : term346 = term347.
Proof. exact (MK_COMB (@lem2502046) (@lem2502047)). Qed.
Lemma lem2502050 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2502051 : term347 = term174.
Proof. exact (@lem2502050 term168). Qed.
Lemma lem2502052 : term346 = term174.
Proof. exact (TRANS (@lem2502048) (@lem2502051)). Qed.
Lemma lem2502054 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2502055 : term270 = term271.
Proof. exact (@lem2502054 term168 term168). Qed.
Lemma lem2502056 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2502057 : term273 = term168.
Proof. exact (EQ_MP (@lem2502056) (@lem940073)). Qed.
Lemma lem2502058 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2502059 : term271 = term167.
Proof. exact (MK_COMB (@lem2502058) (@lem2502057)). Qed.
Lemma lem2502060 : term270 = term167.
Proof. exact (TRANS (@lem2502055) (@lem2502059)). Qed.
Lemma lem2502061 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2502062 : term349 = term347.
Proof. exact (MK_COMB (@lem2502061) (@lem2502060)). Qed.
Lemma lem2502064 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2502065 : term347 = term174.
Proof. exact (@lem2502064 term168). Qed.
Lemma lem2502066 : term349 = term174.
Proof. exact (TRANS (@lem2502062) (@lem2502065)). Qed.
Lemma lem2502067 : term174 = term349.
Proof. exact (SYM (@lem2502066)). Qed.
Lemma lem2502068 : term346 = term349.
Proof. exact (TRANS (@lem2502052) (@lem2502067)). Qed.
Lemma lem2502069 : term333 = term300.
Proof. exact (@lem2502019 (@lem2502068)). Qed.
Lemma lem2502070 : term332 = term300.
Proof. exact (TRANS (@lem2501985) (@lem2502069)). Qed.
Lemma lem2502072 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2502073 : term300 = term174.
Proof. exact (@lem2502072 term174). Qed.
Lemma lem2502074 : term332 = term174.
Proof. exact (TRANS (@lem2502070) (@lem2502073)). Qed.
Lemma lem2502075 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2502076 : term350 = term209.
Proof. exact (MK_COMB (@lem2502075) (@lem2502074)). Qed.
Lemma lem2502077 (m : int) : (real_of_int m) = (real_of_int m).
Proof. exact (eq_refl (real_of_int m)). Qed.
Lemma lem2502078 (m : int) : (term329 m) = (term210 m).
Proof. exact (MK_COMB (@lem2502076) (@lem2502077 m)). Qed.
Lemma lem2502079 (m : int) : (term328 m) = (term210 m).
Proof. exact (TRANS (@lem2501976 m) (@lem2502078 m)). Qed.
Lemma lem2502080 (m : int) : (term210 m) = term174.
Proof. exact (@lem1982719 (real_of_int m)). Qed.
Lemma lem2502081 (m : int) : (term328 m) = term174.
Proof. exact (TRANS (@lem2502079 m) (@lem2502080 m)). Qed.
Lemma lem2502082 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2502083 (m : int) : (term351 m) = term184.
Proof. exact (MK_COMB (@lem2502082) (@lem2502081 m)). Qed.
Lemma lem2502084 (n : int) : (term570 n) = (term548 n).
Proof. exact (@lem1982763 (term316 n) (real_of_int n) term257). Qed.
Lemma lem2502085 (n : int) : (term491 n) = (term329 n).
Proof. exact (@lem1982713 term257 (real_of_int n)). Qed.
Lemma lem2502087 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2502088 : term167 = term259.
Proof. exact (@lem2502087 term168). Qed.
Lemma lem2502090 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2502091 : term257 = term262.
Proof. exact (@lem2502090 term168). Qed.
Lemma lem2502092 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2502093 : term330 = term331.
Proof. exact (MK_COMB (@lem2502092) (@lem2502091)). Qed.
Lemma lem2502094 : term332 = term333.
Proof. exact (MK_COMB (@lem2502093) (@lem2502088)). Qed.
Lemma lem2502095 : term334.
Proof. exact (@lem1981473 term257 term167 term167 term167 term174 term167). Qed.
Lemma lem2502097 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2502098 : term336 = term337.
Proof. exact (@lem2502097 (NUMERAL 0) term168). Qed.
Lemma lem2502099 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502100 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2502101 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502100 h1) (fun h1 : term337 = True => @lem2502099)). Qed.
Lemma lem2502102 : term337 = True.
Proof. exact (EQ_MP (@lem2502101) (@lem2502099)). Qed.
Lemma lem2502103 : term336 = True.
Proof. exact (TRANS (@lem2502098) (@lem2502102)). Qed.
Lemma lem2502104 : True = term336.
Proof. exact (SYM (@lem2502103)). Qed.
Lemma lem2502105 : term336.
Proof. exact (EQ_MP (@lem2502104) (@lem0)). Qed.
Lemma lem2502106 : term339.
Proof. exact (@lem2502095 (@lem2502105)). Qed.
Lemma lem2502108 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2502109 : term336 = term337.
Proof. exact (@lem2502108 (NUMERAL 0) term168). Qed.
Lemma lem2502110 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502111 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2502112 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502111 h1) (fun h1 : term337 = True => @lem2502110)). Qed.
Lemma lem2502113 : term337 = True.
Proof. exact (EQ_MP (@lem2502112) (@lem2502110)). Qed.
Lemma lem2502114 : term336 = True.
Proof. exact (TRANS (@lem2502109) (@lem2502113)). Qed.
Lemma lem2502115 : True = term336.
Proof. exact (SYM (@lem2502114)). Qed.
Lemma lem2502116 : term336.
Proof. exact (EQ_MP (@lem2502115) (@lem0)). Qed.
Lemma lem2502117 : term340.
Proof. exact (@lem2502106 (@lem2502116)). Qed.
Lemma lem2502119 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2502120 : term336 = term337.
Proof. exact (@lem2502119 (NUMERAL 0) term168). Qed.
Lemma lem2502121 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502122 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2502123 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502122 h1) (fun h1 : term337 = True => @lem2502121)). Qed.
Lemma lem2502124 : term337 = True.
Proof. exact (EQ_MP (@lem2502123) (@lem2502121)). Qed.
Lemma lem2502125 : term336 = True.
Proof. exact (TRANS (@lem2502120) (@lem2502124)). Qed.
Lemma lem2502126 : True = term336.
Proof. exact (SYM (@lem2502125)). Qed.
Lemma lem2502127 : term336.
Proof. exact (EQ_MP (@lem2502126) (@lem0)). Qed.
Lemma lem2502128 : term341.
Proof. exact (@lem2502117 (@lem2502127)). Qed.
Lemma lem2502130 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2502131 : term270 = term271.
Proof. exact (@lem2502130 term168 term168). Qed.
Lemma lem2502132 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2502133 : term273 = term168.
Proof. exact (EQ_MP (@lem2502132) (@lem940073)). Qed.
Lemma lem2502134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2502135 : term271 = term167.
Proof. exact (MK_COMB (@lem2502134) (@lem2502133)). Qed.
Lemma lem2502136 : term270 = term167.
Proof. exact (TRANS (@lem2502131) (@lem2502135)). Qed.
Lemma lem2502138 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2502139 : term265 = term276.
Proof. exact (@lem2502138 term168 term168). Qed.
Lemma lem2502140 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2502141 : term273 = term168.
Proof. exact (EQ_MP (@lem2502140) (@lem940073)). Qed.
Lemma lem2502142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2502143 : term271 = term167.
Proof. exact (MK_COMB (@lem2502142) (@lem2502141)). Qed.
Lemma lem2502144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2502145 : term276 = term257.
Proof. exact (MK_COMB (@lem2502144) (@lem2502143)). Qed.
Lemma lem2502146 : term265 = term257.
Proof. exact (TRANS (@lem2502139) (@lem2502145)). Qed.
Lemma lem2502147 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2502148 : term342 = term330.
Proof. exact (MK_COMB (@lem2502147) (@lem2502146)). Qed.
Lemma lem2502149 : term343 = term332.
Proof. exact (MK_COMB (@lem2502148) (@lem2502136)). Qed.
Lemma lem2502151 (m : nat) : (term344 m) = term174.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2502152 : term332 = term174.
Proof. exact (@lem2502151 term168). Qed.
Lemma lem2502153 : term343 = term174.
Proof. exact (TRANS (@lem2502149) (@lem2502152)). Qed.
Lemma lem2502154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2502155 : term345 = term209.
Proof. exact (MK_COMB (@lem2502154) (@lem2502153)). Qed.
Lemma lem2502156 : term167 = term167.
Proof. exact (eq_refl term167). Qed.
Lemma lem2502157 : term346 = term347.
Proof. exact (MK_COMB (@lem2502155) (@lem2502156)). Qed.
Lemma lem2502159 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2502160 : term347 = term174.
Proof. exact (@lem2502159 term168). Qed.
Lemma lem2502161 : term346 = term174.
Proof. exact (TRANS (@lem2502157) (@lem2502160)). Qed.
Lemma lem2502163 (m : nat) (n : nat) : (term268 m n) = (term269 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2502164 : term270 = term271.
Proof. exact (@lem2502163 term168 term168). Qed.
Lemma lem2502165 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2502166 : term273 = term168.
Proof. exact (EQ_MP (@lem2502165) (@lem940073)). Qed.
Lemma lem2502167 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2502168 : term271 = term167.
Proof. exact (MK_COMB (@lem2502167) (@lem2502166)). Qed.
Lemma lem2502169 : term270 = term167.
Proof. exact (TRANS (@lem2502164) (@lem2502168)). Qed.
Lemma lem2502170 : term209 = term209.
Proof. exact (eq_refl term209). Qed.
Lemma lem2502171 : term349 = term347.
Proof. exact (MK_COMB (@lem2502170) (@lem2502169)). Qed.
Lemma lem2502173 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2502174 : term347 = term174.
Proof. exact (@lem2502173 term168). Qed.
Lemma lem2502175 : term349 = term174.
Proof. exact (TRANS (@lem2502171) (@lem2502174)). Qed.
Lemma lem2502176 : term174 = term349.
Proof. exact (SYM (@lem2502175)). Qed.
Lemma lem2502177 : term346 = term349.
Proof. exact (TRANS (@lem2502161) (@lem2502176)). Qed.
Lemma lem2502178 : term333 = term300.
Proof. exact (@lem2502128 (@lem2502177)). Qed.
Lemma lem2502179 : term332 = term300.
Proof. exact (TRANS (@lem2502094) (@lem2502178)). Qed.
Lemma lem2502181 (x : real) : (term279 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2502182 : term300 = term174.
Proof. exact (@lem2502181 term174). Qed.
Lemma lem2502183 : term332 = term174.
Proof. exact (TRANS (@lem2502179) (@lem2502182)). Qed.
Lemma lem2502184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2502185 : term350 = term209.
Proof. exact (MK_COMB (@lem2502184) (@lem2502183)). Qed.
Lemma lem2502186 (n : int) : (real_of_int n) = (real_of_int n).
Proof. exact (eq_refl (real_of_int n)). Qed.
Lemma lem2502187 (n : int) : (term329 n) = (term210 n).
Proof. exact (MK_COMB (@lem2502185) (@lem2502186 n)). Qed.
Lemma lem2502188 (n : int) : (term491 n) = (term210 n).
Proof. exact (TRANS (@lem2502085 n) (@lem2502187 n)). Qed.
Lemma lem2502189 (n : int) : (term210 n) = term174.
Proof. exact (@lem1982719 (real_of_int n)). Qed.
Lemma lem2502190 (n : int) : (term491 n) = term174.
Proof. exact (TRANS (@lem2502188 n) (@lem2502189 n)). Qed.
Lemma lem2502191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2502192 (n : int) : (term492 n) = term184.
Proof. exact (MK_COMB (@lem2502191) (@lem2502190 n)). Qed.
Lemma lem2502193 : term257 = term257.
Proof. exact (eq_refl term257). Qed.
Lemma lem2502194 (n : int) : (term548 n) = term352.
Proof. exact (MK_COMB (@lem2502192 n) (@lem2502193)). Qed.
Lemma lem2502195 (n : int) : (term570 n) = term352.
Proof. exact (TRANS (@lem2502084 n) (@lem2502194 n)). Qed.
Lemma lem2502196 : term352 = term257.
Proof. exact (@lem1982721 term257). Qed.
Lemma lem2502197 (n : int) : (term570 n) = term257.
Proof. exact (TRANS (@lem2502195 n) (@lem2502196)). Qed.
Lemma lem2502198 (m : int) (n : int) : (term569 m n) = term352.
Proof. exact (MK_COMB (@lem2502083 m) (@lem2502197 n)). Qed.
Lemma lem2502199 (m : int) (n : int) : (term568 m n) = term352.
Proof. exact (TRANS (@lem2501975 m n) (@lem2502198 m n)). Qed.
Lemma lem2502200 : term352 = term257.
Proof. exact (@lem1982721 term257). Qed.
Lemma lem2502201 (m : int) (n : int) : (term568 m n) = term257.
Proof. exact (TRANS (@lem2502199 m n) (@lem2502200)). Qed.
Lemma lem2502202 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2502203 (m : int) (n : int) : (term571 m n) = term354.
Proof. exact (MK_COMB (@lem2502202) (@lem2502201 m n)). Qed.
Lemma lem2502204 : term174 = term174.
Proof. exact (eq_refl term174). Qed.
Lemma lem2502205 (m : int) (n : int) : (term567 m n) = term355.
Proof. exact (MK_COMB (@lem2502203 m n) (@lem2502204)). Qed.
Lemma lem2502206 (m : int) (n : int) (h1 : term440 m n) : term355.
Proof. exact (EQ_MP (@lem2502205 m n) (@lem2501974 m n h1)). Qed.
Lemma lem2502208 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2502209 : term355 = term447.
Proof. exact (@lem2502208 term174 term257). Qed.
Lemma lem2502211 (x : nat) : (term260 x) = (term261 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2502212 : term257 = term262.
Proof. exact (@lem2502211 term168). Qed.
Lemma lem2502214 (x : nat) : (real_of_num x) = (term258 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2502215 : term174 = term300.
Proof. exact (@lem2502214 (NUMERAL 0)). Qed.
Lemma lem2502216 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2502217 : term192 = term448.
Proof. exact (MK_COMB (@lem2502216) (@lem2502215)). Qed.
Lemma lem2502218 : term447 = term449.
Proof. exact (MK_COMB (@lem2502217) (@lem2502212)). Qed.
Lemma lem2502219 : term450.
Proof. exact (@lem1980026 term174 term167 term257 term167). Qed.
Lemma lem2502221 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2502222 : term336 = term337.
Proof. exact (@lem2502221 (NUMERAL 0) term168). Qed.
Lemma lem2502223 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502224 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2502225 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502224 h1) (fun h1 : term337 = True => @lem2502223)). Qed.
Lemma lem2502226 : term337 = True.
Proof. exact (EQ_MP (@lem2502225) (@lem2502223)). Qed.
Lemma lem2502227 : term336 = True.
Proof. exact (TRANS (@lem2502222) (@lem2502226)). Qed.
Lemma lem2502228 : True = term336.
Proof. exact (SYM (@lem2502227)). Qed.
Lemma lem2502229 : term336.
Proof. exact (EQ_MP (@lem2502228) (@lem0)). Qed.
Lemma lem2502230 : term451.
Proof. exact (@lem2502219 (@lem2502229)). Qed.
Lemma lem2502232 (m : nat) (n : nat) : (term335 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2502233 : term336 = term337.
Proof. exact (@lem2502232 (NUMERAL 0) term168). Qed.
Lemma lem2502234 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502235 (h1 : term338 = (BIT1 0)) : term337 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2502236 : (term338 = (BIT1 0)) = (term337 = True).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502235 h1) (fun h1 : term337 = True => @lem2502234)). Qed.
Lemma lem2502237 : term337 = True.
Proof. exact (EQ_MP (@lem2502236) (@lem2502234)). Qed.
Lemma lem2502238 : term336 = True.
Proof. exact (TRANS (@lem2502233) (@lem2502237)). Qed.
Lemma lem2502239 : True = term336.
Proof. exact (SYM (@lem2502238)). Qed.
Lemma lem2502240 : term336.
Proof. exact (EQ_MP (@lem2502239) (@lem0)). Qed.
Lemma lem2502241 : term449 = term452.
Proof. exact (@lem2502230 (@lem2502240)). Qed.
Lemma lem2502243 (m : nat) (n : nat) : (term274 m n) = (term275 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2502244 : term265 = term276.
Proof. exact (@lem2502243 term168 term168). Qed.
Lemma lem2502245 : (term272 = (BIT1 0)) = (term273 = term168).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2502246 : term273 = term168.
Proof. exact (EQ_MP (@lem2502245) (@lem940073)). Qed.
Lemma lem2502247 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2502248 : term271 = term167.
Proof. exact (MK_COMB (@lem2502247) (@lem2502246)). Qed.
Lemma lem2502249 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2502250 : term276 = term257.
Proof. exact (MK_COMB (@lem2502249) (@lem2502248)). Qed.
Lemma lem2502251 : term265 = term257.
Proof. exact (TRANS (@lem2502244) (@lem2502250)). Qed.
Lemma lem2502253 (x : nat) : (term348 x) = term174.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2502254 : term347 = term174.
Proof. exact (@lem2502253 term168). Qed.
Lemma lem2502255 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2502256 : term453 = term192.
Proof. exact (MK_COMB (@lem2502255) (@lem2502254)). Qed.
Lemma lem2502257 : term452 = term447.
Proof. exact (MK_COMB (@lem2502256) (@lem2502251)). Qed.
Lemma lem2502259 (m : nat) (n : nat) : (term454 m n) = (term455 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2502260 : term447 = term456.
Proof. exact (@lem2502259 (NUMERAL 0) term168). Qed.
Lemma lem2502261 : term338 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2502262 (h1 : term338 = (BIT1 0)) : (term168 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2502263 : (term338 = (BIT1 0)) = ((term168 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term338 = (BIT1 0) => @lem2502262 h1) (fun h1 : (term168 = (NUMERAL 0)) = False => @lem2502261)). Qed.
Lemma lem2502264 : (term168 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2502263) (@lem2502261)). Qed.
Lemma lem2502265 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2502266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2502267 : term457 = (and True).
Proof. exact (MK_COMB (@lem2502266) (@lem2502265)). Qed.
Lemma lem2502268 : term456 = (True /\ False).
Proof. exact (MK_COMB (@lem2502267) (@lem2502264)). Qed.
Lemma lem2502270 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2502271 : term456 = False.
Proof. exact (TRANS (@lem2502268) (@lem2502270)). Qed.
Lemma lem2502272 : term447 = False.
Proof. exact (TRANS (@lem2502260) (@lem2502271)). Qed.
Lemma lem2502273 : term452 = False.
Proof. exact (TRANS (@lem2502257) (@lem2502272)). Qed.
Lemma lem2502274 : term449 = False.
Proof. exact (TRANS (@lem2502241) (@lem2502273)). Qed.
Lemma lem2502275 : term447 = False.
Proof. exact (TRANS (@lem2502218) (@lem2502274)). Qed.
Lemma lem2502276 : term355 = False.
Proof. exact (TRANS (@lem2502209) (@lem2502275)). Qed.
Lemma lem2502277 (m : int) (n : int) (h1 : term440 m n) : False.
Proof. exact (EQ_MP (@lem2502276) (@lem2502206 m n h1)). Qed.
Lemma lem2502278 (m : int) (n : int) (h1 : term443 m n) : False.
Proof. exact (or_elim (@lem2501347 m n h1) (fun h0 : term437 m n => @lem2501812 m n h0) (fun h0 : term440 m n => @lem2502277 m n h0)). Qed.
Lemma lem2502279 (m : int) (n : int) (h1 : term444 m n) : False.
Proof. exact (or_elim (@lem2500246 m n h1) (fun h0 : term407 n m => @lem2501346 n m h0) (fun h0 : term443 m n => @lem2502278 m n h0)). Qed.
Lemma lem2502280 (m : int) (n : int) (h1 : term445 m n) : False.
Proof. exact (or_elim (@lem2499927 m n h1) (fun h0 : term418 m n => @lem2500245 m n h0) (fun h0 : term444 m n => @lem2502279 m n h0)). Qed.
Lemma lem2502281 (n : int) (m : int) (h1 : term421 n m) : term421 n m.
Proof. exact (h1). Qed.
Lemma lem2502282 (n : int) (m : int) (h1 : term421 n m) : term445 m n.
Proof. exact (EQ_MP (@lem2499926 m n) (@lem2502281 n m h1)). Qed.
Lemma lem2502283 (n : int) (m : int) (h1 : term421 n m) : (term445 m n) = False.
Proof. exact (prop_ext (fun h2 : term445 m n => @lem2502280 m n h2) (fun h2 : False => @lem2502282 n m h1)). Qed.
Lemma lem2502284 (n : int) (m : int) (h1 : term421 n m) : False.
Proof. exact (EQ_MP (@lem2502283 n m h1) (@lem2502282 n m h1)). Qed.
Lemma lem2502285 (n : int) (m : int) (h1 : term251 n m) : term251 n m.
Proof. exact (h1). Qed.
Lemma lem2502286 (n : int) (m : int) (h1 : term251 n m) : term421 n m.
Proof. exact (EQ_MP (@lem2499789 n m) (@lem2502285 n m h1)). Qed.
Lemma lem2502287 (n : int) (m : int) (h1 : term251 n m) : (term421 n m) = False.
Proof. exact (prop_ext (fun h2 : term421 n m => @lem2502284 n m h2) (fun h2 : False => @lem2502286 n m h1)). Qed.
Lemma lem2502288 (n : int) (m : int) (h1 : term251 n m) : False.
Proof. exact (EQ_MP (@lem2502287 n m h1) (@lem2502286 n m h1)). Qed.
Lemma lem2502289 (n : int) (m : int) : term572 n m.
Proof. exact (fun h0 : term251 n m => @lem2502288 n m h0). Qed.
Lemma lem2502290 (n : int) (m : int) : term573 n m.
Proof. exact (@lem1386578 (term574 n m)). Qed.
Lemma lem2502293 (n : int) (m : int) : term574 n m.
Proof. exact (@lem2502290 n m (@lem2502289 n m)). Qed.
Lemma lem2502294 (m : int) (n : int) : (term249 n m) = (term151 m n).
Proof. exact (SYM (@lem2498848 n m)). Qed.
Lemma lem2502295 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2502296 (m : int) (n : int) : (term574 n m) = (term128 m n).
Proof. exact (MK_COMB (@lem2502295) (@lem2502294 m n)). Qed.
Lemma lem2502297 (m : int) (n : int) : term128 m n.
Proof. exact (EQ_MP (@lem2502296 m n) (@lem2502293 n m)). Qed.
Lemma lem2502298 (m : int) (n : int) : term129 m n.
Proof. exact (EQ_MP (@lem2498557 m n) (@lem2502297 m n)). Qed.
Lemma lem2502299 (m : int) (n : int) : (term129 m n) = ((term129 m n) = True).
Proof. exact (@lem7 (term129 m n)). Qed.
Lemma lem2502300 (m : int) (n : int) : (term129 m n) = True.
Proof. exact (EQ_MP (@lem2502299 m n) (@lem2502298 m n)). Qed.
Lemma lem2502301 (m : int) (n : int) : True = (term129 m n).
Proof. exact (SYM (@lem2502300 m n)). Qed.
Lemma lem2502302 (m : int) (n : int) : term129 m n.
Proof. exact (EQ_MP (@lem2502301 m n) (@lem0)). Qed.
Lemma lem2502303 (m : int) (n : int) (h1 : term41 n) : term152 m n.
Proof. exact (@lem2502302 m n (@lem2498187 n h1)). Qed.
Lemma lem2502304 (n : int) (m : int) (h1 : term41 n) (h2 : term105 m) : term147 m n.
Proof. exact (@lem2502303 m n h1 (@lem2498553 m h2)). Qed.
Lemma lem2502305 (m : int) (n : int) (h1 : term41 n) (h2 : term105 m) (h3 : int_lt m n) : term143 m n.
Proof. exact (@lem2502304 n m h1 h2 (@lem2498552 m n h3)). Qed.
Lemma lem2502306 (m : int) (n : int) (h1 : term41 n) (h2 : term105 m) (h3 : int_lt m n) : term575 n m.
Proof. exact (@lem2498556 n m (@lem2502305 m n h1 h2 h3)). Qed.
Lemma lem2502307 (m : int) (n : int) (h1 : term120 m n) : int_lt m n.
Proof. exact (proj2 (@lem2498551 m n h1)). Qed.
Lemma lem2502308 (m : int) (n : int) (h1 : term120 m n) : term105 m.
Proof. exact (proj1 (@lem2498551 m n h1)). Qed.
Lemma lem2502309 (m : int) (n : int) (h1 : term41 n) (h2 : term105 m) (h3 : int_lt m n) : (int_lt m n) = (term575 n m).
Proof. exact (prop_ext (fun h4 : int_lt m n => @lem2502306 m n h1 h2 h3) (fun h4 : term575 n m => @lem2498552 m n h3)). Qed.
Lemma lem2502310 (m : int) (n : int) (h1 : term41 n) (h2 : term105 m) (h3 : int_lt m n) : term575 n m.
Proof. exact (EQ_MP (@lem2502309 m n h1 h2 h3) (@lem2498552 m n h3)). Qed.
Lemma lem2502311 (m : int) (n : int) (h1 : term41 n) (h2 : term105 m) (h3 : int_lt m n) : (term105 m) = (term575 n m).
Proof. exact (prop_ext (fun h4 : term105 m => @lem2502310 m n h1 h2 h3) (fun h4 : term575 n m => @lem2498553 m h2)). Qed.
Lemma lem2502312 (m : int) (n : int) (h1 : term41 n) (h2 : term105 m) (h3 : int_lt m n) : term575 n m.
Proof. exact (EQ_MP (@lem2502311 m n h1 h2 h3) (@lem2498553 m h2)). Qed.
Lemma lem2502313 (n : int) (m : int) (h1 : term41 n) (h2 : term120 m n) (h3 : term105 m) : (int_lt m n) = (term575 n m).
Proof. exact (prop_ext (fun h4 : int_lt m n => @lem2502312 m n h1 h3 h4) (fun h4 : term575 n m => @lem2502307 m n h2)). Qed.
Lemma lem2502314 (n : int) (m : int) (h1 : term41 n) (h2 : term120 m n) (h3 : term105 m) : term575 n m.
Proof. exact (EQ_MP (@lem2502313 n m h1 h2 h3) (@lem2502307 m n h2)). Qed.
Lemma lem2502315 (m : int) (n : int) (h1 : term41 n) (h2 : term120 m n) : (term105 m) = (term575 n m).
Proof. exact (prop_ext (fun h3 : term105 m => @lem2502314 n m h1 h2 h3) (fun h3 : term575 n m => @lem2502308 m n h2)). Qed.
Lemma lem2502316 (m : int) (n : int) (h1 : term41 n) (h2 : term120 m n) : term575 n m.
Proof. exact (EQ_MP (@lem2502315 m n h1 h2) (@lem2502308 m n h2)). Qed.
Lemma lem2502317 (m : int) (n : int) (h1 : term41 n) : term126 n m.
Proof. exact (fun h0 : term120 m n => @lem2502316 m n h1 h0). Qed.
Lemma lem2502318 (m : int) (n : int) (h1 : term41 n) : term125 n m.
Proof. exact (EQ_MP (@lem2498550 n m) (@lem2502317 m n h1)). Qed.
Lemma lem2502319 (m : int) (n : int) (h1 : term41 n) : term93 n m.
Proof. exact (EQ_MP (@lem2498536 m n h1) (@lem2502318 m n h1)). Qed.
Lemma lem2502320 (n : int) (m : int) : term93 n m.
Proof. exact (or_elim (@lem2498185 n) (fun h0 : n = term39 => @lem2498439 m n h0) (fun h0 : term41 n => @lem2502319 m n h0)). Qed.
Lemma lem2502325 (m : int) : term96 m.
Proof. exact (fun n : int => @lem2502320 n m). Qed.
Lemma lem2502330 : term98.
Proof. exact (fun m : int => @lem2502325 m). Qed.
Lemma lem2502331 : term65.
Proof. exact (EQ_MP (@lem2498286) (@lem2502330)). Qed.
