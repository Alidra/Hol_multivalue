Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONSTR_INJ_term_abbrevs.
Require Import CONSTR_spec.
Require Import DEST_REC_INJ_spec.
Require Import FUN_EQ_THM_spec.
Require Import INJA_INJ_spec.
Require Import INJF_INJ_spec.
Require Import INJN_INJ_spec.
Require Import INJP_INJ_spec.
Require Import MK_REC_INJ_spec.
Require Import SUC_INJ_spec.
Require Import ZCONSTR_spec.
Require Import ZRECSPACE_RULES_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Lemma lem1060001 {A : Type'} (x : recspace A) : term0 A x.
Proof. exact (@lem1059772 A x). Qed.
Lemma lem1060002 {A : Type'} (x : recspace A) : (term0 A x) = (term1 A x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem1060003 {A : Type'} (x : recspace A) : term1 A x.
Proof. exact (EQ_MP (@lem1060002 A x) (@lem1060001 A x)). Qed.
Lemma lem1060004 {A : Type'} (x : recspace A) (y : recspace A) : term2 A x y.
Proof. exact (@lem1060003 A x y). Qed.
Lemma lem1060005 {A : Type'} (x : recspace A) (y : recspace A) : (term2 A x y) = (((@_dest_rec A x) = (@_dest_rec A y)) = (x = y)).
Proof. exact (eq_refl (term2 A x y)). Qed.
Lemma lem1060007 (m : nat) : term3 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem1060008 (m : nat) : (term3 m) = (term4 m).
Proof. exact (eq_refl (term3 m)). Qed.
Lemma lem1060009 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem1060008 m) (@lem1060007 m)). Qed.
Lemma lem1060010 (m : nat) (n : nat) : term5 m n.
Proof. exact (@lem1060009 m n). Qed.
Lemma lem1060011 (m : nat) (n : nat) : (term5 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term5 m n)). Qed.
Lemma lem1060013 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1060014 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem1060015 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem1060014 A B f) (@lem1060013 A B f)). Qed.
Lemma lem1060016 {A B : Type'} (f : A -> B) (g : A -> B) : term8 A B f g.
Proof. exact (@lem1060015 A B f g). Qed.
Lemma lem1060017 {A B : Type'} (f : A -> B) (g : A -> B) : (term8 A B f g) = ((f = g) = (term9 A B f g)).
Proof. exact (eq_refl (term8 A B f g)). Qed.
Lemma lem1060019 {A : Type'} (a1 : A) : term10 A a1.
Proof. exact (@lem1056144 A a1). Qed.
Lemma lem1060020 {A : Type'} (a1 : A) : (term10 A a1) = (term11 A a1).
Proof. exact (eq_refl (term10 A a1)). Qed.
Lemma lem1060021 {A : Type'} (a1 : A) : term11 A a1.
Proof. exact (EQ_MP (@lem1060020 A a1) (@lem1060019 A a1)). Qed.
Lemma lem1060022 {A : Type'} (a1 : A) (a2 : A) : term12 A a1 a2.
Proof. exact (@lem1060021 A a1 a2). Qed.
Lemma lem1060023 {A : Type'} (a1 : A) (a2 : A) : (term12 A a1 a2) = (((@INJA A a1) = (@INJA A a2)) = (a1 = a2)).
Proof. exact (eq_refl (term12 A a1 a2)). Qed.
Lemma lem1060025 {A : Type'} (f1 : type1600 A) : term13 A f1.
Proof. exact (@lem1056666 A f1). Qed.
Lemma lem1060026 {A : Type'} (f1 : type1600 A) : (term13 A f1) = (term14 A f1).
Proof. exact (eq_refl (term13 A f1)). Qed.
Lemma lem1060027 {A : Type'} (f1 : type1600 A) : term14 A f1.
Proof. exact (EQ_MP (@lem1060026 A f1) (@lem1060025 A f1)). Qed.
Lemma lem1060028 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : term15 A f1 f2.
Proof. exact (@lem1060027 A f1 f2). Qed.
Lemma lem1060029 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : (term15 A f1 f2) = (((@INJF A f1) = (@INJF A f2)) = (f1 = f2)).
Proof. exact (eq_refl (term15 A f1 f2)). Qed.
Lemma lem1060031 {A : Type'} (n1 : nat) : term16 A n1.
Proof. exact (@lem1055573 A n1). Qed.
Lemma lem1060032 {A : Type'} (n1 : nat) : (term16 A n1) = (term17 A n1).
Proof. exact (eq_refl (term16 A n1)). Qed.
Lemma lem1060033 {A : Type'} (n1 : nat) : term17 A n1.
Proof. exact (EQ_MP (@lem1060032 A n1) (@lem1060031 A n1)). Qed.
Lemma lem1060034 {A : Type'} (n1 : nat) (n2 : nat) : term18 A n1 n2.
Proof. exact (@lem1060033 A n1 n2). Qed.
Lemma lem1060035 {A : Type'} (n1 : nat) (n2 : nat) : (term18 A n1 n2) = (((@INJN A n1) = (@INJN A n2)) = (n1 = n2)).
Proof. exact (eq_refl (term18 A n1 n2)). Qed.
Lemma lem1060037 {A : Type'} (f1 : type1597 A) : term19 A f1.
Proof. exact (@lem1057571 A f1). Qed.
Lemma lem1060038 {A : Type'} (f1 : type1597 A) : (term19 A f1) = (term20 A f1).
Proof. exact (eq_refl (term19 A f1)). Qed.
Lemma lem1060039 {A : Type'} (f1 : type1597 A) : term20 A f1.
Proof. exact (EQ_MP (@lem1060038 A f1) (@lem1060037 A f1)). Qed.
Lemma lem1060040 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : term21 A f1 f1'.
Proof. exact (@lem1060039 A f1 f1'). Qed.
Lemma lem1060041 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : (term21 A f1 f1') = (term22 A f1 f1').
Proof. exact (eq_refl (term21 A f1 f1')). Qed.
Lemma lem1060042 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) : term22 A f1 f1'.
Proof. exact (EQ_MP (@lem1060041 A f1 f1') (@lem1060040 A f1 f1')). Qed.
Lemma lem1060043 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) : term23 A f1 f1' f2.
Proof. exact (@lem1060042 A f1 f1' f2). Qed.
Lemma lem1060044 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) : (term23 A f1 f1' f2) = (term24 A f1 f1' f2).
Proof. exact (eq_refl (term23 A f1 f1' f2)). Qed.
Lemma lem1060045 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) : term24 A f1 f1' f2.
Proof. exact (EQ_MP (@lem1060044 A f1 f1' f2) (@lem1060043 A f1 f1' f2)). Qed.
Lemma lem1060046 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : term25 A f1 f1' f2 f2'.
Proof. exact (@lem1060045 A f1 f1' f2 f2'). Qed.
Lemma lem1060047 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : (term25 A f1 f1' f2 f2') = (((@INJP A f1 f2) = (@INJP A f1' f2')) = (term26 A f1 f1' f2 f2')).
Proof. exact (eq_refl (term25 A f1 f1' f2 f2')). Qed.
Lemma lem1060049 {A : Type'} (c : nat) : term27 A c.
Proof. exact (@lem1057928 A c). Qed.
Lemma lem1060050 {A : Type'} (c : nat) : (term27 A c) = (term28 A c).
Proof. exact (eq_refl (term27 A c)). Qed.
Lemma lem1060051 {A : Type'} (c : nat) : term28 A c.
Proof. exact (EQ_MP (@lem1060050 A c) (@lem1060049 A c)). Qed.
Lemma lem1060052 {A : Type'} (c : nat) (i : A) : term29 A c i.
Proof. exact (@lem1060051 A c i). Qed.
Lemma lem1060053 {A : Type'} (c : nat) (i : A) : (term29 A c i) = (term30 A c i).
Proof. exact (eq_refl (term29 A c i)). Qed.
Lemma lem1060054 {A : Type'} (c : nat) (i : A) : term30 A c i.
Proof. exact (EQ_MP (@lem1060053 A c i) (@lem1060052 A c i)). Qed.
Lemma lem1060055 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term31 A c i r.
Proof. exact (@lem1060054 A c i r). Qed.
Lemma lem1060056 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term31 A c i r) = ((@ZCONSTR A c i r) = (term32 A c i r)).
Proof. exact (eq_refl (term31 A c i r)). Qed.
Lemma lem1060058 {A : Type'} : term33 A.
Proof. exact (proj2 (@lem1058926 A)). Qed.
Lemma lem1060059 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem1060060 {A : Type'} (c : nat) (h1 : term33 A) : term34 A c.
Proof. exact (@lem1060059 A h1 c). Qed.
Lemma lem1060061 {A : Type'} (c : nat) : (term34 A c) = (term35 A c).
Proof. exact (eq_refl (term34 A c)). Qed.
Lemma lem1060062 {A : Type'} (c : nat) (h1 : term33 A) : term35 A c.
Proof. exact (EQ_MP (@lem1060061 A c) (@lem1060060 A c h1)). Qed.
Lemma lem1060063 {A : Type'} (c : nat) (i : A) (h1 : term33 A) : term36 A c i.
Proof. exact (@lem1060062 A c h1 i). Qed.
Lemma lem1060064 {A : Type'} (c : nat) (i : A) : (term36 A c i) = (term37 A c i).
Proof. exact (eq_refl (term36 A c i)). Qed.
Lemma lem1060065 {A : Type'} (c : nat) (i : A) (h1 : term33 A) : term37 A c i.
Proof. exact (EQ_MP (@lem1060064 A c i) (@lem1060063 A c i h1)). Qed.
Lemma lem1060066 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term33 A) : term38 A c i r.
Proof. exact (@lem1060065 A c i h1 r). Qed.
Lemma lem1060067 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term38 A c i r) = (term39 A c i r).
Proof. exact (eq_refl (term38 A c i r)). Qed.
Lemma lem1060068 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term33 A) : term39 A c i r.
Proof. exact (EQ_MP (@lem1060067 A c i r) (@lem1060066 A c i r h1)). Qed.
Lemma lem1060069 {A : Type'} (r : type1600 A) (h1 : term40 A r) : term40 A r.
Proof. exact (h1). Qed.
Lemma lem1060070 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term33 A) (h2 : term40 A r) : term41 A c i r.
Proof. exact (@lem1060068 A c i r h1 (@lem1060069 A r h2)). Qed.
Lemma lem1060071 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term40 A r) : term42 A c i r.
Proof. exact (fun h0 : term33 A => @lem1060070 A c i r h0 h1). Qed.
Lemma lem1060072 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (h1). Qed.
Lemma lem1060073 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term33 A) (h2 : term40 A r) : term41 A c i r.
Proof. exact (@lem1060071 A c i r h2 (@lem1060072 A h1)). Qed.
Lemma lem1060074 {A : Type'} (c : nat) (i : A) (r : type1600 A) (h1 : term33 A) : term39 A c i r.
Proof. exact (fun h0 : term40 A r => @lem1060073 A c i r h1 h0). Qed.
Lemma lem1060075 {A : Type'} (c : nat) (i : A) (h1 : term33 A) : term37 A c i.
Proof. exact (fun r : type1600 A => @lem1060074 A c i r h1). Qed.
Lemma lem1060076 {A : Type'} (c : nat) (h1 : term33 A) : term35 A c.
Proof. exact (fun i : A => @lem1060075 A c i h1). Qed.
Lemma lem1060077 {A : Type'} (h1 : term33 A) : term33 A.
Proof. exact (fun c : nat => @lem1060076 A c h1). Qed.
Lemma lem1060078 {A : Type'} : term43 A.
Proof. exact (fun h0 : term33 A => @lem1060077 A h0). Qed.
Lemma lem1060079 {A : Type'} : term33 A.
Proof. exact (@lem1060078 A (@lem1060058 A)). Qed.
Lemma lem1060080 {A : Type'} (c : nat) : term34 A c.
Proof. exact (@lem1060079 A c). Qed.
Lemma lem1060081 {A : Type'} (c : nat) : (term34 A c) = (term35 A c).
Proof. exact (eq_refl (term34 A c)). Qed.
Lemma lem1060082 {A : Type'} (c : nat) : term35 A c.
Proof. exact (EQ_MP (@lem1060081 A c) (@lem1060080 A c)). Qed.
Lemma lem1060083 {A : Type'} (c : nat) (i : A) : term36 A c i.
Proof. exact (@lem1060082 A c i). Qed.
Lemma lem1060084 {A : Type'} (c : nat) (i : A) : (term36 A c i) = (term37 A c i).
Proof. exact (eq_refl (term36 A c i)). Qed.
Lemma lem1060085 {A : Type'} (c : nat) (i : A) : term37 A c i.
Proof. exact (EQ_MP (@lem1060084 A c i) (@lem1060083 A c i)). Qed.
Lemma lem1060086 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term38 A c i r.
Proof. exact (@lem1060085 A c i r). Qed.
Lemma lem1060087 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (term38 A c i r) = (term39 A c i r).
Proof. exact (eq_refl (term38 A c i r)). Qed.
Lemma lem1060089 {A : Type'} (x : type1597 A) : term44 A x.
Proof. exact (@lem1059697 A x). Qed.
Lemma lem1060090 {A : Type'} (x : type1597 A) : (term44 A x) = (term45 A x).
Proof. exact (eq_refl (term44 A x)). Qed.
Lemma lem1060091 {A : Type'} (x : type1597 A) : term45 A x.
Proof. exact (EQ_MP (@lem1060090 A x) (@lem1060089 A x)). Qed.
Lemma lem1060092 {A : Type'} (x : type1597 A) (y : type1597 A) : term46 A x y.
Proof. exact (@lem1060091 A x y). Qed.
Lemma lem1060093 {A : Type'} (x : type1597 A) (y : type1597 A) : (term46 A x y) = (term47 A x y).
Proof. exact (eq_refl (term46 A x y)). Qed.
Lemma lem1060095 {A : Type'} (c : nat) : term48 A c.
Proof. exact (@lem1059607 A c). Qed.
Lemma lem1060096 {A : Type'} (c : nat) : (term48 A c) = (term49 A c).
Proof. exact (eq_refl (term48 A c)). Qed.
Lemma lem1060097 {A : Type'} (c : nat) : term49 A c.
Proof. exact (EQ_MP (@lem1060096 A c) (@lem1060095 A c)). Qed.
Lemma lem1060098 {A : Type'} (c : nat) (i : A) : term50 A c i.
Proof. exact (@lem1060097 A c i). Qed.
Lemma lem1060099 {A : Type'} (c : nat) (i : A) : (term50 A c i) = (term51 A c i).
Proof. exact (eq_refl (term50 A c i)). Qed.
Lemma lem1060100 {A : Type'} (c : nat) (i : A) : term51 A c i.
Proof. exact (EQ_MP (@lem1060099 A c i) (@lem1060098 A c i)). Qed.
Lemma lem1060101 {A : Type'} (c : nat) (i : A) (r : type1614 A) : term52 A c i r.
Proof. exact (@lem1060100 A c i r). Qed.
Lemma lem1060102 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (term52 A c i r) = ((@CONSTR A c i r) = (term53 A c i r)).
Proof. exact (eq_refl (term52 A c i r)). Qed.
Lemma lem1060104 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : (@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) : (@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2).
Proof. exact (h1). Qed.
Lemma lem1060105 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : term54 A c1 c2 i1 i2 r1 r2.
Proof. exact (h1). Qed.
Lemma lem1060118 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : term55 A i1 i2 r1 r2.
Proof. exact (proj2 (@lem1060105 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060125 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : c1 = c2.
Proof. exact (proj1 (@lem1060105 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060126 {A : Type'} : (@CONSTR A) = (@CONSTR A).
Proof. exact (eq_refl (@CONSTR A)). Qed.
Lemma lem1060127 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : (@CONSTR A c1) = (@CONSTR A c2).
Proof. exact (MK_COMB (@lem1060126 A) (@lem1060125 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060129 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : i1 = i2.
Proof. exact (proj1 (@lem1060118 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060130 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : (@CONSTR A c1 i1) = (@CONSTR A c2 i2).
Proof. exact (MK_COMB (@lem1060127 A c1 c2 i1 i2 r1 r2 h1) (@lem1060129 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060132 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : r1 = r2.
Proof. exact (proj2 (@lem1060118 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060133 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : (@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2).
Proof. exact (MK_COMB (@lem1060130 A c1 c2 i1 i2 r1 r2 h1) (@lem1060132 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060134 {A : Type'} : (@eq (recspace A)) = (@eq (recspace A)).
Proof. exact (eq_refl (@eq (recspace A))). Qed.
Lemma lem1060135 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : (term56 A c1 i1 r1) = (term56 A c2 i2 r2).
Proof. exact (MK_COMB (@lem1060134 A) (@lem1060133 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060136 {A : Type'} (c2 : nat) (i2 : A) (r2 : type1614 A) : (@CONSTR A c2 i2 r2) = (@CONSTR A c2 i2 r2).
Proof. exact (eq_refl (@CONSTR A c2 i2 r2)). Qed.
Lemma lem1060137 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = ((@CONSTR A c2 i2 r2) = (@CONSTR A c2 i2 r2)).
Proof. exact (MK_COMB (@lem1060135 A c1 c2 i1 i2 r1 r2 h1) (@lem1060136 A c2 i2 r2)). Qed.
Lemma lem1060139 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1060140 {A : Type'} (x : recspace A) : (x = x) = True.
Proof. exact (@lem1060139 (recspace A) x). Qed.
Lemma lem1060141 {A : Type'} (c2 : nat) (i2 : A) (r2 : type1614 A) : ((@CONSTR A c2 i2 r2) = (@CONSTR A c2 i2 r2)) = True.
Proof. exact (@lem1060140 A (@CONSTR A c2 i2 r2)). Qed.
Lemma lem1060142 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = True.
Proof. exact (TRANS (@lem1060137 A c1 c2 i1 i2 r1 r2 h1) (@lem1060141 A c2 i2 r2)). Qed.
Lemma lem1060143 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : True = ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)).
Proof. exact (SYM (@lem1060142 A c1 c2 i1 i2 r1 r2 h1)). Qed.
Lemma lem1060144 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) (h1 : term54 A c1 c2 i1 i2 r1 r2) : (@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2).
Proof. exact (EQ_MP (@lem1060143 A c1 c2 i1 i2 r1 r2 h1) (@lem0)). Qed.
Lemma lem1060148 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term53 A c i r).
Proof. exact (EQ_MP (@lem1060102 A c i r) (@lem1060101 A c i r)). Qed.
Lemma lem1060149 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term53 A c i r).
Proof. exact (@lem1060148 A c i r). Qed.
Lemma lem1060150 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : (@CONSTR A c1 i1 r1) = (term53 A c1 i1 r1).
Proof. exact (@lem1060149 A c1 i1 r1). Qed.
Lemma lem1060151 {A : Type'} : (@eq (recspace A)) = (@eq (recspace A)).
Proof. exact (eq_refl (@eq (recspace A))). Qed.
Lemma lem1060152 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : (term56 A c1 i1 r1) = (term57 A c1 i1 r1).
Proof. exact (MK_COMB (@lem1060151 A) (@lem1060150 A c1 i1 r1)). Qed.
Lemma lem1060154 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term53 A c i r).
Proof. exact (EQ_MP (@lem1060102 A c i r) (@lem1060101 A c i r)). Qed.
Lemma lem1060155 {A : Type'} (c : nat) (i : A) (r : type1614 A) : (@CONSTR A c i r) = (term53 A c i r).
Proof. exact (@lem1060154 A c i r). Qed.
Lemma lem1060156 {A : Type'} (c2 : nat) (i2 : A) (r2 : type1614 A) : (@CONSTR A c2 i2 r2) = (term53 A c2 i2 r2).
Proof. exact (@lem1060155 A c2 i2 r2). Qed.
Lemma lem1060157 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = ((term53 A c1 i1 r1) = (term53 A c2 i2 r2)).
Proof. exact (MK_COMB (@lem1060152 A c1 i1 r1) (@lem1060156 A c2 i2 r2)). Qed.
Lemma lem1060160 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : (@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) : (term53 A c1 i1 r1) = (term53 A c2 i2 r2).
Proof. exact (EQ_MP (@lem1060157 A c1 i1 r1 c2 i2 r2) (@lem1060104 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060161 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : (term53 A c1 i1 r1) = (term53 A c2 i2 r2)) : (term53 A c1 i1 r1) = (term53 A c2 i2 r2).
Proof. exact (h1). Qed.
Lemma lem1060163 {A : Type'} (x : type1597 A) (y : type1597 A) : term47 A x y.
Proof. exact (EQ_MP (@lem1060093 A x y) (@lem1060092 A x y)). Qed.
Lemma lem1060164 {A : Type'} (x : type1597 A) (y : type1597 A) : term47 A x y.
Proof. exact (@lem1060163 A x y). Qed.
Lemma lem1060165 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : term58 A c1 i1 r1 c2 i2 r2.
Proof. exact (@lem1060164 A (term59 A c1 i1 r1) (term59 A c2 i2 r2)). Qed.
Lemma lem1060166 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : (term53 A c1 i1 r1) = (term53 A c2 i2 r2)) : term60 A c1 i1 r1 c2 i2 r2.
Proof. exact (@lem1060165 A c1 i1 r1 c2 i2 r2 (@lem1060161 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060167 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : term61 A c1 i1 r1 c2 i2 r2.
Proof. exact (h1). Qed.
Lemma lem1060169 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term39 A c i r.
Proof. exact (EQ_MP (@lem1060087 A c i r) (@lem1060086 A c i r)). Qed.
Lemma lem1060170 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term39 A c i r.
Proof. exact (@lem1060169 A c i r). Qed.
Lemma lem1060171 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : term62 A c1 i1 r1.
Proof. exact (@lem1060170 A c1 i1 (term63 A r1)). Qed.
Lemma lem1060173 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term39 A c i r.
Proof. exact (EQ_MP (@lem1060087 A c i r) (@lem1060086 A c i r)). Qed.
Lemma lem1060174 {A : Type'} (c : nat) (i : A) (r : type1600 A) : term39 A c i r.
Proof. exact (@lem1060173 A c i r). Qed.
Lemma lem1060175 {A : Type'} (c2 : nat) (i2 : A) (r2 : type1614 A) : term62 A c2 i2 r2.
Proof. exact (@lem1060174 A c2 i2 (term63 A r2)). Qed.
Lemma lem1060181 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term64 A r) = r).
Proof. exact (@axiom_10 A r). Qed.
Lemma lem1060182 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term64 A r) = r).
Proof. exact (@lem1060181 A r). Qed.
Lemma lem1060183 {A : Type'} (r1 : type1614 A) (n : nat) : (term65 A r1 n) = ((term66 A r1 n) = (term67 A r1 n)).
Proof. exact (@lem1060182 A (term67 A r1 n)). Qed.
Lemma lem1060187 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1060188 {A : Type'} (f : type1600 A) (y : nat) : (term69 A f y) = (f y).
Proof. exact (@lem1060187 nat (type1597 A) f y). Qed.
Lemma lem1060189 {A : Type'} (r1 : type1614 A) (n : nat) : (term70 A r1 n) = (term67 A r1 n).
Proof. exact (@lem1060188 A (term63 A r1) n). Qed.
Lemma lem1060190 {A : Type'} (r1 : type1614 A) (n : nat) : (term67 A r1 n) = (term71 A r1 n).
Proof. exact (eq_refl (term67 A r1 n)). Qed.
Lemma lem1060191 {A : Type'} (r1 : type1614 A) : (term72 A r1) = (term63 A r1).
Proof. exact (fun_ext (fun n : nat => @lem1060190 A r1 n)). Qed.
Lemma lem1060192 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1060193 {A : Type'} (r1 : type1614 A) (n : nat) : (term70 A r1 n) = (term67 A r1 n).
Proof. exact (MK_COMB (@lem1060191 A r1) (@lem1060192 n)). Qed.
Lemma lem1060194 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060195 {A : Type'} (r1 : type1614 A) (n : nat) : (term73 A r1 n) = (term74 A r1 n).
Proof. exact (MK_COMB (@lem1060194 A) (@lem1060193 A r1 n)). Qed.
Lemma lem1060196 {A : Type'} (r1 : type1614 A) (n : nat) : (term67 A r1 n) = (term71 A r1 n).
Proof. exact (eq_refl (term67 A r1 n)). Qed.
Lemma lem1060197 {A : Type'} (r1 : type1614 A) (n : nat) : ((term70 A r1 n) = (term67 A r1 n)) = ((term67 A r1 n) = (term71 A r1 n)).
Proof. exact (MK_COMB (@lem1060195 A r1 n) (@lem1060196 A r1 n)). Qed.
Lemma lem1060198 {A : Type'} (r1 : type1614 A) (n : nat) : (term67 A r1 n) = (term71 A r1 n).
Proof. exact (EQ_MP (@lem1060197 A r1 n) (@lem1060189 A r1 n)). Qed.
Lemma lem1060199 {A : Type'} : (@_mk_rec A) = (@_mk_rec A).
Proof. exact (eq_refl (@_mk_rec A)). Qed.
Lemma lem1060200 {A : Type'} (r1 : type1614 A) (n : nat) : (term75 A r1 n) = (term76 A r1 n).
Proof. exact (MK_COMB (@lem1060199 A) (@lem1060198 A r1 n)). Qed.
Lemma lem1060202 {A : Type'} (a : recspace A) : (term77 A a) = a.
Proof. exact (@axiom_9 A a). Qed.
Lemma lem1060203 {A : Type'} (a : recspace A) : (term77 A a) = a.
Proof. exact (@lem1060202 A a). Qed.
Lemma lem1060204 {A : Type'} (r1 : type1614 A) (n : nat) : (term76 A r1 n) = (r1 n).
Proof. exact (@lem1060203 A (r1 n)). Qed.
Lemma lem1060205 {A : Type'} (r1 : type1614 A) (n : nat) : (term75 A r1 n) = (r1 n).
Proof. exact (TRANS (@lem1060200 A r1 n) (@lem1060204 A r1 n)). Qed.
Lemma lem1060206 {A : Type'} : (@_dest_rec A) = (@_dest_rec A).
Proof. exact (eq_refl (@_dest_rec A)). Qed.
Lemma lem1060207 {A : Type'} (r1 : type1614 A) (n : nat) : (term66 A r1 n) = (term71 A r1 n).
Proof. exact (MK_COMB (@lem1060206 A) (@lem1060205 A r1 n)). Qed.
Lemma lem1060208 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060209 {A : Type'} (r1 : type1614 A) (n : nat) : (term78 A r1 n) = (term79 A r1 n).
Proof. exact (MK_COMB (@lem1060208 A) (@lem1060207 A r1 n)). Qed.
Lemma lem1060211 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1060212 {A : Type'} (f : type1600 A) (y : nat) : (term69 A f y) = (f y).
Proof. exact (@lem1060211 nat (type1597 A) f y). Qed.
Lemma lem1060213 {A : Type'} (r1 : type1614 A) (n : nat) : (term70 A r1 n) = (term67 A r1 n).
Proof. exact (@lem1060212 A (term63 A r1) n). Qed.
Lemma lem1060214 {A : Type'} (r1 : type1614 A) (n : nat) : (term67 A r1 n) = (term71 A r1 n).
Proof. exact (eq_refl (term67 A r1 n)). Qed.
Lemma lem1060215 {A : Type'} (r1 : type1614 A) : (term72 A r1) = (term63 A r1).
Proof. exact (fun_ext (fun n : nat => @lem1060214 A r1 n)). Qed.
Lemma lem1060216 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1060217 {A : Type'} (r1 : type1614 A) (n : nat) : (term70 A r1 n) = (term67 A r1 n).
Proof. exact (MK_COMB (@lem1060215 A r1) (@lem1060216 n)). Qed.
Lemma lem1060218 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060219 {A : Type'} (r1 : type1614 A) (n : nat) : (term73 A r1 n) = (term74 A r1 n).
Proof. exact (MK_COMB (@lem1060218 A) (@lem1060217 A r1 n)). Qed.
Lemma lem1060220 {A : Type'} (r1 : type1614 A) (n : nat) : (term67 A r1 n) = (term71 A r1 n).
Proof. exact (eq_refl (term67 A r1 n)). Qed.
Lemma lem1060221 {A : Type'} (r1 : type1614 A) (n : nat) : ((term70 A r1 n) = (term67 A r1 n)) = ((term67 A r1 n) = (term71 A r1 n)).
Proof. exact (MK_COMB (@lem1060219 A r1 n) (@lem1060220 A r1 n)). Qed.
Lemma lem1060222 {A : Type'} (r1 : type1614 A) (n : nat) : (term67 A r1 n) = (term71 A r1 n).
Proof. exact (EQ_MP (@lem1060221 A r1 n) (@lem1060213 A r1 n)). Qed.
Lemma lem1060223 {A : Type'} (r1 : type1614 A) (n : nat) : ((term66 A r1 n) = (term67 A r1 n)) = ((term71 A r1 n) = (term71 A r1 n)).
Proof. exact (MK_COMB (@lem1060209 A r1 n) (@lem1060222 A r1 n)). Qed.
Lemma lem1060225 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1060226 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1060225 (type1597 A) x). Qed.
Lemma lem1060227 {A : Type'} (r1 : type1614 A) (n : nat) : ((term71 A r1 n) = (term71 A r1 n)) = True.
Proof. exact (@lem1060226 A (term71 A r1 n)). Qed.
Lemma lem1060228 {A : Type'} (r1 : type1614 A) (n : nat) : ((term66 A r1 n) = (term67 A r1 n)) = True.
Proof. exact (TRANS (@lem1060223 A r1 n) (@lem1060227 A r1 n)). Qed.
Lemma lem1060229 {A : Type'} (r1 : type1614 A) (n : nat) : (term65 A r1 n) = True.
Proof. exact (TRANS (@lem1060183 A r1 n) (@lem1060228 A r1 n)). Qed.
Lemma lem1060230 {A : Type'} (r1 : type1614 A) : (term80 A r1) = term81.
Proof. exact (fun_ext (fun n : nat => @lem1060229 A r1 n)). Qed.
Lemma lem1060231 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060232 {A : Type'} (r1 : type1614 A) : (term82 A r1) = term83.
Proof. exact (MK_COMB (@lem1060231) (@lem1060230 A r1)). Qed.
Lemma lem1060234 {A : Type'} (t : Prop) : (term84 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1060235 (t : Prop) : (term85 t) = t.
Proof. exact (@lem1060234 nat t). Qed.
Lemma lem1060236 : term83 = True.
Proof. exact (@lem1060235 True). Qed.
Lemma lem1060237 {A : Type'} (r1 : type1614 A) : (term82 A r1) = True.
Proof. exact (TRANS (@lem1060232 A r1) (@lem1060236)). Qed.
Lemma lem1060238 {A : Type'} (r1 : type1614 A) : True = (term82 A r1).
Proof. exact (SYM (@lem1060237 A r1)). Qed.
Lemma lem1060239 {A : Type'} (r1 : type1614 A) : term82 A r1.
Proof. exact (EQ_MP (@lem1060238 A r1) (@lem0)). Qed.
Lemma lem1060245 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term64 A r) = r).
Proof. exact (@axiom_10 A r). Qed.
Lemma lem1060246 {A : Type'} (r : type1597 A) : (@ZRECSPACE A r) = ((term64 A r) = r).
Proof. exact (@lem1060245 A r). Qed.
Lemma lem1060247 {A : Type'} (r2 : type1614 A) (n : nat) : (term65 A r2 n) = ((term66 A r2 n) = (term67 A r2 n)).
Proof. exact (@lem1060246 A (term67 A r2 n)). Qed.
Lemma lem1060251 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1060252 {A : Type'} (f : type1600 A) (y : nat) : (term69 A f y) = (f y).
Proof. exact (@lem1060251 nat (type1597 A) f y). Qed.
Lemma lem1060253 {A : Type'} (r2 : type1614 A) (n : nat) : (term70 A r2 n) = (term67 A r2 n).
Proof. exact (@lem1060252 A (term63 A r2) n). Qed.
Lemma lem1060254 {A : Type'} (r2 : type1614 A) (n : nat) : (term67 A r2 n) = (term71 A r2 n).
Proof. exact (eq_refl (term67 A r2 n)). Qed.
Lemma lem1060255 {A : Type'} (r2 : type1614 A) : (term72 A r2) = (term63 A r2).
Proof. exact (fun_ext (fun n : nat => @lem1060254 A r2 n)). Qed.
Lemma lem1060256 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1060257 {A : Type'} (r2 : type1614 A) (n : nat) : (term70 A r2 n) = (term67 A r2 n).
Proof. exact (MK_COMB (@lem1060255 A r2) (@lem1060256 n)). Qed.
Lemma lem1060258 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060259 {A : Type'} (r2 : type1614 A) (n : nat) : (term73 A r2 n) = (term74 A r2 n).
Proof. exact (MK_COMB (@lem1060258 A) (@lem1060257 A r2 n)). Qed.
Lemma lem1060260 {A : Type'} (r2 : type1614 A) (n : nat) : (term67 A r2 n) = (term71 A r2 n).
Proof. exact (eq_refl (term67 A r2 n)). Qed.
Lemma lem1060261 {A : Type'} (r2 : type1614 A) (n : nat) : ((term70 A r2 n) = (term67 A r2 n)) = ((term67 A r2 n) = (term71 A r2 n)).
Proof. exact (MK_COMB (@lem1060259 A r2 n) (@lem1060260 A r2 n)). Qed.
Lemma lem1060262 {A : Type'} (r2 : type1614 A) (n : nat) : (term67 A r2 n) = (term71 A r2 n).
Proof. exact (EQ_MP (@lem1060261 A r2 n) (@lem1060253 A r2 n)). Qed.
Lemma lem1060263 {A : Type'} : (@_mk_rec A) = (@_mk_rec A).
Proof. exact (eq_refl (@_mk_rec A)). Qed.
Lemma lem1060264 {A : Type'} (r2 : type1614 A) (n : nat) : (term75 A r2 n) = (term76 A r2 n).
Proof. exact (MK_COMB (@lem1060263 A) (@lem1060262 A r2 n)). Qed.
Lemma lem1060266 {A : Type'} (a : recspace A) : (term77 A a) = a.
Proof. exact (@axiom_9 A a). Qed.
Lemma lem1060267 {A : Type'} (a : recspace A) : (term77 A a) = a.
Proof. exact (@lem1060266 A a). Qed.
Lemma lem1060268 {A : Type'} (r2 : type1614 A) (n : nat) : (term76 A r2 n) = (r2 n).
Proof. exact (@lem1060267 A (r2 n)). Qed.
Lemma lem1060269 {A : Type'} (r2 : type1614 A) (n : nat) : (term75 A r2 n) = (r2 n).
Proof. exact (TRANS (@lem1060264 A r2 n) (@lem1060268 A r2 n)). Qed.
Lemma lem1060270 {A : Type'} : (@_dest_rec A) = (@_dest_rec A).
Proof. exact (eq_refl (@_dest_rec A)). Qed.
Lemma lem1060271 {A : Type'} (r2 : type1614 A) (n : nat) : (term66 A r2 n) = (term71 A r2 n).
Proof. exact (MK_COMB (@lem1060270 A) (@lem1060269 A r2 n)). Qed.
Lemma lem1060272 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060273 {A : Type'} (r2 : type1614 A) (n : nat) : (term78 A r2 n) = (term79 A r2 n).
Proof. exact (MK_COMB (@lem1060272 A) (@lem1060271 A r2 n)). Qed.
Lemma lem1060275 {A B : Type'} (f : A -> B) (y : A) : (term68 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1060276 {A : Type'} (f : type1600 A) (y : nat) : (term69 A f y) = (f y).
Proof. exact (@lem1060275 nat (type1597 A) f y). Qed.
Lemma lem1060277 {A : Type'} (r2 : type1614 A) (n : nat) : (term70 A r2 n) = (term67 A r2 n).
Proof. exact (@lem1060276 A (term63 A r2) n). Qed.
Lemma lem1060278 {A : Type'} (r2 : type1614 A) (n : nat) : (term67 A r2 n) = (term71 A r2 n).
Proof. exact (eq_refl (term67 A r2 n)). Qed.
Lemma lem1060279 {A : Type'} (r2 : type1614 A) : (term72 A r2) = (term63 A r2).
Proof. exact (fun_ext (fun n : nat => @lem1060278 A r2 n)). Qed.
Lemma lem1060280 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1060281 {A : Type'} (r2 : type1614 A) (n : nat) : (term70 A r2 n) = (term67 A r2 n).
Proof. exact (MK_COMB (@lem1060279 A r2) (@lem1060280 n)). Qed.
Lemma lem1060282 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060283 {A : Type'} (r2 : type1614 A) (n : nat) : (term73 A r2 n) = (term74 A r2 n).
Proof. exact (MK_COMB (@lem1060282 A) (@lem1060281 A r2 n)). Qed.
Lemma lem1060284 {A : Type'} (r2 : type1614 A) (n : nat) : (term67 A r2 n) = (term71 A r2 n).
Proof. exact (eq_refl (term67 A r2 n)). Qed.
Lemma lem1060285 {A : Type'} (r2 : type1614 A) (n : nat) : ((term70 A r2 n) = (term67 A r2 n)) = ((term67 A r2 n) = (term71 A r2 n)).
Proof. exact (MK_COMB (@lem1060283 A r2 n) (@lem1060284 A r2 n)). Qed.
Lemma lem1060286 {A : Type'} (r2 : type1614 A) (n : nat) : (term67 A r2 n) = (term71 A r2 n).
Proof. exact (EQ_MP (@lem1060285 A r2 n) (@lem1060277 A r2 n)). Qed.
Lemma lem1060287 {A : Type'} (r2 : type1614 A) (n : nat) : ((term66 A r2 n) = (term67 A r2 n)) = ((term71 A r2 n) = (term71 A r2 n)).
Proof. exact (MK_COMB (@lem1060273 A r2 n) (@lem1060286 A r2 n)). Qed.
Lemma lem1060289 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1060290 {A : Type'} (x : type1597 A) : (x = x) = True.
Proof. exact (@lem1060289 (type1597 A) x). Qed.
Lemma lem1060291 {A : Type'} (r2 : type1614 A) (n : nat) : ((term71 A r2 n) = (term71 A r2 n)) = True.
Proof. exact (@lem1060290 A (term71 A r2 n)). Qed.
Lemma lem1060292 {A : Type'} (r2 : type1614 A) (n : nat) : ((term66 A r2 n) = (term67 A r2 n)) = True.
Proof. exact (TRANS (@lem1060287 A r2 n) (@lem1060291 A r2 n)). Qed.
Lemma lem1060293 {A : Type'} (r2 : type1614 A) (n : nat) : (term65 A r2 n) = True.
Proof. exact (TRANS (@lem1060247 A r2 n) (@lem1060292 A r2 n)). Qed.
Lemma lem1060294 {A : Type'} (r2 : type1614 A) : (term80 A r2) = term81.
Proof. exact (fun_ext (fun n : nat => @lem1060293 A r2 n)). Qed.
Lemma lem1060295 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060296 {A : Type'} (r2 : type1614 A) : (term82 A r2) = term83.
Proof. exact (MK_COMB (@lem1060295) (@lem1060294 A r2)). Qed.
Lemma lem1060298 {A : Type'} (t : Prop) : (term84 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1060299 (t : Prop) : (term85 t) = t.
Proof. exact (@lem1060298 nat t). Qed.
Lemma lem1060300 : term83 = True.
Proof. exact (@lem1060299 True). Qed.
Lemma lem1060301 {A : Type'} (r2 : type1614 A) : (term82 A r2) = True.
Proof. exact (TRANS (@lem1060296 A r2) (@lem1060300)). Qed.
Lemma lem1060302 {A : Type'} (r2 : type1614 A) : True = (term82 A r2).
Proof. exact (SYM (@lem1060301 A r2)). Qed.
Lemma lem1060303 {A : Type'} (r2 : type1614 A) : term82 A r2.
Proof. exact (EQ_MP (@lem1060302 A r2) (@lem0)). Qed.
Lemma lem1060304 {A : Type'} (c2 : nat) (i2 : A) (r2 : type1614 A) : term86 A c2 i2 r2.
Proof. exact (@lem1060175 A c2 i2 r2 (@lem1060303 A r2)). Qed.
Lemma lem1060305 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : term86 A c1 i1 r1.
Proof. exact (@lem1060171 A c1 i1 r1 (@lem1060239 A r1)). Qed.
Lemma lem1060306 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : term61 A c1 i1 r1 c2 i2 r2.
Proof. exact (conj (@lem1060305 A c1 i1 r1) (@lem1060304 A c2 i2 r2)). Qed.
Lemma lem1060307 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : term86 A c2 i2 r2.
Proof. exact (proj2 (@lem1060167 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060308 {A : Type'} (c2 : nat) (i2 : A) (r2 : type1614 A) : (term86 A c2 i2 r2) = ((term86 A c2 i2 r2) = True).
Proof. exact (@lem7 (term86 A c2 i2 r2)). Qed.
Lemma lem1060310 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : term86 A c1 i1 r1.
Proof. exact (proj1 (@lem1060167 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060311 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : (term86 A c1 i1 r1) = ((term86 A c1 i1 r1) = True).
Proof. exact (@lem7 (term86 A c1 i1 r1)). Qed.
Lemma lem1060320 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term86 A c1 i1 r1) = True.
Proof. exact (EQ_MP (@lem1060311 A c1 i1 r1) (@lem1060310 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060322 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term87 A c1 i1 r1) = (and True).
Proof. exact (MK_COMB (@lem1060321) (@lem1060320 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060324 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term86 A c2 i2 r2) = True.
Proof. exact (EQ_MP (@lem1060308 A c2 i2 r2) (@lem1060307 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060325 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term61 A c1 i1 r1 c2 i2 r2) = (True /\ True).
Proof. exact (MK_COMB (@lem1060322 A c1 i1 r1 c2 i2 r2 h1) (@lem1060324 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060327 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1060328 : (True /\ True) = True.
Proof. exact (@lem1060327 True). Qed.
Lemma lem1060329 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term61 A c1 i1 r1 c2 i2 r2) = True.
Proof. exact (TRANS (@lem1060325 A c1 i1 r1 c2 i2 r2 h1) (@lem1060328)). Qed.
Lemma lem1060330 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060331 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term88 A c1 i1 r1 c2 i2 r2) = (imp True).
Proof. exact (MK_COMB (@lem1060330) (@lem1060329 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060334 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : ((term59 A c1 i1 r1) = (term59 A c2 i2 r2)) = ((term59 A c1 i1 r1) = (term59 A c2 i2 r2)).
Proof. exact (eq_refl ((term59 A c1 i1 r1) = (term59 A c2 i2 r2))). Qed.
Lemma lem1060335 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term60 A c1 i1 r1 c2 i2 r2) = (term89 A c1 i1 r1 c2 i2 r2).
Proof. exact (MK_COMB (@lem1060331 A c1 i1 r1 c2 i2 r2 h1) (@lem1060334 A c1 i1 r1 c2 i2 r2)). Qed.
Lemma lem1060337 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1060338 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : (term89 A c1 i1 r1 c2 i2 r2) = ((term59 A c1 i1 r1) = (term59 A c2 i2 r2)).
Proof. exact (@lem1060337 ((term59 A c1 i1 r1) = (term59 A c2 i2 r2))). Qed.
Lemma lem1060341 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term60 A c1 i1 r1 c2 i2 r2) = ((term59 A c1 i1 r1) = (term59 A c2 i2 r2)).
Proof. exact (TRANS (@lem1060335 A c1 i1 r1 c2 i2 r2 h1) (@lem1060338 A c1 i1 r1 c2 i2 r2)). Qed.
Lemma lem1060342 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060343 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term90 A c1 i1 r1 c2 i2 r2) = (term91 A c1 i1 r1 c2 i2 r2).
Proof. exact (MK_COMB (@lem1060342) (@lem1060341 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060354 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term54 A c1 c2 i1 i2 r1 r2) = (term54 A c1 c2 i1 i2 r1 r2).
Proof. exact (eq_refl (term54 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060355 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term92 A c1 c2 i1 i2 r1 r2) = (term93 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060343 A c1 i1 r1 c2 i2 r2 h1) (@lem1060354 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060360 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term93 A c1 c2 i1 i2 r1 r2) = (term92 A c1 c2 i1 i2 r1 r2).
Proof. exact (SYM (@lem1060355 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060368 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (term32 A c i r).
Proof. exact (EQ_MP (@lem1060056 A c i r) (@lem1060055 A c i r)). Qed.
Lemma lem1060369 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (term32 A c i r).
Proof. exact (@lem1060368 A c i r). Qed.
Lemma lem1060370 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : (term59 A c1 i1 r1) = (term94 A c1 i1 r1).
Proof. exact (@lem1060369 A c1 i1 (term63 A r1)). Qed.
Lemma lem1060371 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060372 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : (term95 A c1 i1 r1) = (term96 A c1 i1 r1).
Proof. exact (MK_COMB (@lem1060371 A) (@lem1060370 A c1 i1 r1)). Qed.
Lemma lem1060374 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (term32 A c i r).
Proof. exact (EQ_MP (@lem1060056 A c i r) (@lem1060055 A c i r)). Qed.
Lemma lem1060375 {A : Type'} (c : nat) (i : A) (r : type1600 A) : (@ZCONSTR A c i r) = (term32 A c i r).
Proof. exact (@lem1060374 A c i r). Qed.
Lemma lem1060376 {A : Type'} (c2 : nat) (i2 : A) (r2 : type1614 A) : (term59 A c2 i2 r2) = (term94 A c2 i2 r2).
Proof. exact (@lem1060375 A c2 i2 (term63 A r2)). Qed.
Lemma lem1060377 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : ((term59 A c1 i1 r1) = (term59 A c2 i2 r2)) = ((term94 A c1 i1 r1) = (term94 A c2 i2 r2)).
Proof. exact (MK_COMB (@lem1060372 A c1 i1 r1) (@lem1060376 A c2 i2 r2)). Qed.
Lemma lem1060380 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060381 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : (term91 A c1 i1 r1 c2 i2 r2) = (term97 A c1 i1 r1 c2 i2 r2).
Proof. exact (MK_COMB (@lem1060380) (@lem1060377 A c1 i1 r1 c2 i2 r2)). Qed.
Lemma lem1060392 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term54 A c1 c2 i1 i2 r1 r2) = (term54 A c1 c2 i1 i2 r1 r2).
Proof. exact (eq_refl (term54 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060393 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term93 A c1 c2 i1 i2 r1 r2) = (term98 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060381 A c1 i1 r1 c2 i2 r2) (@lem1060392 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060398 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term98 A c1 c2 i1 i2 r1 r2) = (term93 A c1 c2 i1 i2 r1 r2).
Proof. exact (SYM (@lem1060393 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060404 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = (term26 A f1 f1' f2 f2').
Proof. exact (EQ_MP (@lem1060047 A f1 f1' f2 f2') (@lem1060046 A f1 f1' f2 f2')). Qed.
Lemma lem1060405 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = (term26 A f1 f1' f2 f2').
Proof. exact (@lem1060404 A f1 f1' f2 f2'). Qed.
Lemma lem1060406 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) (i2 : A) (r2 : type1614 A) : ((term94 A c1 i1 r1) = (term94 A c2 i2 r2)) = (term99 A c1 c2 i1 r1 i2 r2).
Proof. exact (@lem1060405 A (term100 A c1) (term100 A c2) (term101 A i1 r1) (term101 A i2 r2)). Qed.
Lemma lem1060410 {A : Type'} (n1 : nat) (n2 : nat) : ((@INJN A n1) = (@INJN A n2)) = (n1 = n2).
Proof. exact (EQ_MP (@lem1060035 A n1 n2) (@lem1060034 A n1 n2)). Qed.
Lemma lem1060411 {A : Type'} (c1 : nat) (c2 : nat) : ((term100 A c1) = (term100 A c2)) = ((S c1) = (S c2)).
Proof. exact (@lem1060410 A (S c1) (S c2)). Qed.
Lemma lem1060414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060415 {A : Type'} (c1 : nat) (c2 : nat) : (term102 A c1 c2) = (term103 c1 c2).
Proof. exact (MK_COMB (@lem1060414) (@lem1060411 A c1 c2)). Qed.
Lemma lem1060417 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = (term26 A f1 f1' f2 f2').
Proof. exact (EQ_MP (@lem1060047 A f1 f1' f2 f2') (@lem1060046 A f1 f1' f2 f2')). Qed.
Lemma lem1060418 {A : Type'} (f1 : type1597 A) (f1' : type1597 A) (f2 : type1597 A) (f2' : type1597 A) : ((@INJP A f1 f2) = (@INJP A f1' f2')) = (term26 A f1 f1' f2 f2').
Proof. exact (@lem1060417 A f1 f1' f2 f2'). Qed.
Lemma lem1060419 {A : Type'} (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((term101 A i1 r1) = (term101 A i2 r2)) = (term104 A i1 i2 r1 r2).
Proof. exact (@lem1060418 A (@INJA A i1) (@INJA A i2) (term105 A r1) (term105 A r2)). Qed.
Lemma lem1060423 {A : Type'} (a1 : A) (a2 : A) : ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Proof. exact (EQ_MP (@lem1060023 A a1 a2) (@lem1060022 A a1 a2)). Qed.
Lemma lem1060424 {A : Type'} (a1 : A) (a2 : A) : ((@INJA A a1) = (@INJA A a2)) = (a1 = a2).
Proof. exact (@lem1060423 A a1 a2). Qed.
Lemma lem1060425 {A : Type'} (i1 : A) (i2 : A) : ((@INJA A i1) = (@INJA A i2)) = (i1 = i2).
Proof. exact (@lem1060424 A i1 i2). Qed.
Lemma lem1060428 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060429 {A : Type'} (i1 : A) (i2 : A) : (term106 A i1 i2) = (term107 A i1 i2).
Proof. exact (MK_COMB (@lem1060428) (@lem1060425 A i1 i2)). Qed.
Lemma lem1060431 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Proof. exact (EQ_MP (@lem1060029 A f1 f2) (@lem1060028 A f1 f2)). Qed.
Lemma lem1060432 {A : Type'} (f1 : type1600 A) (f2 : type1600 A) : ((@INJF A f1) = (@INJF A f2)) = (f1 = f2).
Proof. exact (@lem1060431 A f1 f2). Qed.
Lemma lem1060433 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) : ((term105 A r1) = (term105 A r2)) = ((term63 A r1) = (term63 A r2)).
Proof. exact (@lem1060432 A (term63 A r1) (term63 A r2)). Qed.
Lemma lem1060436 {A : Type'} (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term104 A i1 i2 r1 r2) = (term108 A i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060429 A i1 i2) (@lem1060433 A r1 r2)). Qed.
Lemma lem1060439 {A : Type'} (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((term101 A i1 r1) = (term101 A i2 r2)) = (term108 A i1 i2 r1 r2).
Proof. exact (TRANS (@lem1060419 A i1 i2 r1 r2) (@lem1060436 A i1 i2 r1 r2)). Qed.
Lemma lem1060440 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term99 A c1 c2 i1 r1 i2 r2) = (term109 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060415 A c1 c2) (@lem1060439 A i1 i2 r1 r2)). Qed.
Lemma lem1060443 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((term94 A c1 i1 r1) = (term94 A c2 i2 r2)) = (term109 A c1 c2 i1 i2 r1 r2).
Proof. exact (TRANS (@lem1060406 A c1 c2 i1 r1 i2 r2) (@lem1060440 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060445 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term97 A c1 i1 r1 c2 i2 r2) = (term110 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060444) (@lem1060443 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060456 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term54 A c1 c2 i1 i2 r1 r2) = (term54 A c1 c2 i1 i2 r1 r2).
Proof. exact (eq_refl (term54 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060457 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term98 A c1 c2 i1 i2 r1 r2) = (term111 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060445 A c1 c2 i1 i2 r1 r2) (@lem1060456 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060460 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term111 A c1 c2 i1 i2 r1 r2) = (term98 A c1 c2 i1 i2 r1 r2).
Proof. exact (SYM (@lem1060457 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060478 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem1060017 A B f g) (@lem1060016 A B f g)). Qed.
Lemma lem1060479 {A : Type'} (f : type1600 A) (g : type1600 A) : (f = g) = (term112 A f g).
Proof. exact (@lem1060478 nat (type1597 A) f g). Qed.
Lemma lem1060480 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) : ((term63 A r1) = (term63 A r2)) = (term113 A r1 r2).
Proof. exact (@lem1060479 A (term63 A r1) (term63 A r2)). Qed.
Lemma lem1060481 {A : Type'} (i1 : A) (i2 : A) : (term107 A i1 i2) = (term107 A i1 i2).
Proof. exact (eq_refl (term107 A i1 i2)). Qed.
Lemma lem1060482 {A : Type'} (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term108 A i1 i2 r1 r2) = (term114 A i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060481 A i1 i2) (@lem1060480 A r1 r2)). Qed.
Lemma lem1060483 (c1 : nat) (c2 : nat) : (term103 c1 c2) = (term103 c1 c2).
Proof. exact (eq_refl (term103 c1 c2)). Qed.
Lemma lem1060484 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term109 A c1 c2 i1 i2 r1 r2) = (term115 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060483 c1 c2) (@lem1060482 A i1 i2 r1 r2)). Qed.
Lemma lem1060485 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060486 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term110 A c1 c2 i1 i2 r1 r2) = (term116 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060485) (@lem1060484 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060502 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem1060017 A B f g) (@lem1060016 A B f g)). Qed.
Lemma lem1060503 {A : Type'} (f : type1614 A) (g : type1614 A) : (f = g) = (term117 A f g).
Proof. exact (@lem1060502 nat (recspace A) f g). Qed.
Lemma lem1060504 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) : (r1 = r2) = (term117 A r1 r2).
Proof. exact (@lem1060503 A r1 r2). Qed.
Lemma lem1060505 {A : Type'} (i1 : A) (i2 : A) : (term107 A i1 i2) = (term107 A i1 i2).
Proof. exact (eq_refl (term107 A i1 i2)). Qed.
Lemma lem1060506 {A : Type'} (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term55 A i1 i2 r1 r2) = (term118 A i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060505 A i1 i2) (@lem1060504 A r1 r2)). Qed.
Lemma lem1060507 (c1 : nat) (c2 : nat) : (term119 c1 c2) = (term119 c1 c2).
Proof. exact (eq_refl (term119 c1 c2)). Qed.
Lemma lem1060508 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term54 A c1 c2 i1 i2 r1 r2) = (term120 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060507 c1 c2) (@lem1060506 A i1 i2 r1 r2)). Qed.
Lemma lem1060509 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term111 A c1 c2 i1 i2 r1 r2) = (term121 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060486 A c1 c2 i1 i2 r1 r2) (@lem1060508 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060510 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term121 A c1 c2 i1 i2 r1 r2) = (term111 A c1 c2 i1 i2 r1 r2).
Proof. exact (SYM (@lem1060509 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060511 {A : Type'} (r1 : type1614 A) (x : nat) : (term67 A r1 x) = (term71 A r1 x).
Proof. exact (eq_refl (term67 A r1 x)). Qed.
Lemma lem1060512 {A : Type'} : (@eq (nat -> A -> Prop)) = (@eq (nat -> A -> Prop)).
Proof. exact (eq_refl (@eq (nat -> A -> Prop))). Qed.
Lemma lem1060513 {A : Type'} (r1 : type1614 A) (x : nat) : (term74 A r1 x) = (term79 A r1 x).
Proof. exact (MK_COMB (@lem1060512 A) (@lem1060511 A r1 x)). Qed.
Lemma lem1060514 {A : Type'} (r2 : type1614 A) (x : nat) : (term67 A r2 x) = (term71 A r2 x).
Proof. exact (eq_refl (term67 A r2 x)). Qed.
Lemma lem1060515 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) (x : nat) : ((term67 A r1 x) = (term67 A r2 x)) = ((term71 A r1 x) = (term71 A r2 x)).
Proof. exact (MK_COMB (@lem1060513 A r1 x) (@lem1060514 A r2 x)). Qed.
Lemma lem1060516 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) : (term122 A r1 r2) = (term123 A r1 r2).
Proof. exact (fun_ext (fun x : nat => @lem1060515 A r1 r2 x)). Qed.
Lemma lem1060517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060518 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) : (term113 A r1 r2) = (term124 A r1 r2).
Proof. exact (MK_COMB (@lem1060517) (@lem1060516 A r1 r2)). Qed.
Lemma lem1060519 {A : Type'} (i1 : A) (i2 : A) : (term107 A i1 i2) = (term107 A i1 i2).
Proof. exact (eq_refl (term107 A i1 i2)). Qed.
Lemma lem1060520 {A : Type'} (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term114 A i1 i2 r1 r2) = (term125 A i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060519 A i1 i2) (@lem1060518 A r1 r2)). Qed.
Lemma lem1060521 (c1 : nat) (c2 : nat) : (term103 c1 c2) = (term103 c1 c2).
Proof. exact (eq_refl (term103 c1 c2)). Qed.
Lemma lem1060522 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term115 A c1 c2 i1 i2 r1 r2) = (term126 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060521 c1 c2) (@lem1060520 A i1 i2 r1 r2)). Qed.
Lemma lem1060523 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060524 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term116 A c1 c2 i1 i2 r1 r2) = (term127 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060523) (@lem1060522 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060525 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term120 A c1 c2 i1 i2 r1 r2) = (term120 A c1 c2 i1 i2 r1 r2).
Proof. exact (eq_refl (term120 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060526 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term121 A c1 c2 i1 i2 r1 r2) = (term128 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060524 A c1 c2 i1 i2 r1 r2) (@lem1060525 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060527 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term128 A c1 c2 i1 i2 r1 r2) = (term121 A c1 c2 i1 i2 r1 r2).
Proof. exact (SYM (@lem1060526 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060533 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem1060011 m n) (@lem1060010 m n)). Qed.
Lemma lem1060534 (c1 : nat) (c2 : nat) : ((S c1) = (S c2)) = (c1 = c2).
Proof. exact (@lem1060533 c1 c2). Qed.
Lemma lem1060537 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1060538 (c1 : nat) (c2 : nat) : (term103 c1 c2) = (term119 c1 c2).
Proof. exact (MK_COMB (@lem1060537) (@lem1060534 c1 c2)). Qed.
Lemma lem1060548 {A : Type'} (x : recspace A) (y : recspace A) : ((@_dest_rec A x) = (@_dest_rec A y)) = (x = y).
Proof. exact (EQ_MP (@lem1060005 A x y) (@lem1060004 A x y)). Qed.
Lemma lem1060549 {A : Type'} (x : recspace A) (y : recspace A) : ((@_dest_rec A x) = (@_dest_rec A y)) = (x = y).
Proof. exact (@lem1060548 A x y). Qed.
Lemma lem1060550 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) (x : nat) : ((term71 A r1 x) = (term71 A r2 x)) = ((r1 x) = (r2 x)).
Proof. exact (@lem1060549 A (r1 x) (r2 x)). Qed.
Lemma lem1060553 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) : (term123 A r1 r2) = (term129 A r1 r2).
Proof. exact (fun_ext (fun x : nat => @lem1060550 A r1 r2 x)). Qed.
Lemma lem1060554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1060555 {A : Type'} (r1 : type1614 A) (r2 : type1614 A) : (term124 A r1 r2) = (term117 A r1 r2).
Proof. exact (MK_COMB (@lem1060554) (@lem1060553 A r1 r2)). Qed.
Lemma lem1060560 {A : Type'} (i1 : A) (i2 : A) : (term107 A i1 i2) = (term107 A i1 i2).
Proof. exact (eq_refl (term107 A i1 i2)). Qed.
Lemma lem1060561 {A : Type'} (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term125 A i1 i2 r1 r2) = (term118 A i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060560 A i1 i2) (@lem1060555 A r1 r2)). Qed.
Lemma lem1060564 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term126 A c1 c2 i1 i2 r1 r2) = (term120 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060538 c1 c2) (@lem1060561 A i1 i2 r1 r2)). Qed.
Lemma lem1060567 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1060568 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term127 A c1 c2 i1 i2 r1 r2) = (term130 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060567) (@lem1060564 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060583 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term120 A c1 c2 i1 i2 r1 r2) = (term120 A c1 c2 i1 i2 r1 r2).
Proof. exact (eq_refl (term120 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060584 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term128 A c1 c2 i1 i2 r1 r2) = (term131 A c1 c2 i1 i2 r1 r2).
Proof. exact (MK_COMB (@lem1060568 A c1 c2 i1 i2 r1 r2) (@lem1060583 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060586 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem1060587 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term131 A c1 c2 i1 i2 r1 r2) = True.
Proof. exact (@lem1060586 (term120 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060588 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term128 A c1 c2 i1 i2 r1 r2) = True.
Proof. exact (TRANS (@lem1060584 A c1 c2 i1 i2 r1 r2) (@lem1060587 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060589 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : True = (term128 A c1 c2 i1 i2 r1 r2).
Proof. exact (SYM (@lem1060588 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060590 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term128 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060589 A c1 c2 i1 i2 r1 r2) (@lem0)). Qed.
Lemma lem1060591 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term121 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060527 A c1 c2 i1 i2 r1 r2) (@lem1060590 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060592 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term111 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060510 A c1 c2 i1 i2 r1 r2) (@lem1060591 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060593 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term98 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060460 A c1 c2 i1 i2 r1 r2) (@lem1060592 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060594 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term93 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060398 A c1 c2 i1 i2 r1 r2) (@lem1060593 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060595 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : term92 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060360 A c1 i1 r1 c2 i2 r2 h1) (@lem1060594 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060596 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : (term61 A c1 i1 r1 c2 i2 r2) = (term92 A c1 c2 i1 i2 r1 r2).
Proof. exact (prop_ext (fun h2 : term61 A c1 i1 r1 c2 i2 r2 => @lem1060595 A c1 i1 r1 c2 i2 r2 h1) (fun h2 : term92 A c1 c2 i1 i2 r1 r2 => @lem1060167 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060597 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : term61 A c1 i1 r1 c2 i2 r2) : term92 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060596 A c1 i1 r1 c2 i2 r2 h1) (@lem1060167 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060598 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term61 A c1 i1 r1 c2 i2 r2) = (term92 A c1 c2 i1 i2 r1 r2).
Proof. exact (prop_ext (fun h1 : term61 A c1 i1 r1 c2 i2 r2 => @lem1060597 A c1 i1 r1 c2 i2 r2 h1) (fun h1 : term92 A c1 c2 i1 i2 r1 r2 => @lem1060306 A c1 i1 r1 c2 i2 r2)). Qed.
Lemma lem1060599 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term92 A c1 c2 i1 i2 r1 r2.
Proof. exact (EQ_MP (@lem1060598 A c1 c2 i1 i2 r1 r2) (@lem1060306 A c1 i1 r1 c2 i2 r2)). Qed.
Lemma lem1060600 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : (term53 A c1 i1 r1) = (term53 A c2 i2 r2)) : term54 A c1 c2 i1 i2 r1 r2.
Proof. exact (@lem1060599 A c1 c2 i1 i2 r1 r2 (@lem1060166 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060601 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term132 A c1 c2 i1 i2 r1 r2.
Proof. exact (fun h0 : (term53 A c1 i1 r1) = (term53 A c2 i2 r2) => @lem1060600 A c1 i1 r1 c2 i2 r2 h0). Qed.
Lemma lem1060603 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) (h1 : (@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) : term54 A c1 c2 i1 i2 r1 r2.
Proof. exact (@lem1060601 A c1 c2 i1 i2 r1 r2 (@lem1060160 A c1 i1 r1 c2 i2 r2 h1)). Qed.
Lemma lem1060604 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : term133 A c1 i1 r1 c2 i2 r2.
Proof. exact (fun h0 : term54 A c1 c2 i1 i2 r1 r2 => @lem1060144 A c1 c2 i1 i2 r1 r2 h0). Qed.
Lemma lem1060605 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : term134 A c1 c2 i1 i2 r1 r2.
Proof. exact (fun h0 : (@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2) => @lem1060603 A c1 i1 r1 c2 i2 r2 h0). Qed.
Lemma lem1060606 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) (c2 : nat) (i2 : A) (r2 : type1614 A) : term135 A c1 i1 r1 c2 i2 r2.
Proof. exact (conj (@lem1060605 A c1 c2 i1 i2 r1 r2) (@lem1060604 A c1 i1 r1 c2 i2 r2)). Qed.
Lemma lem1060607 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : (term135 A c1 i1 r1 c2 i2 r2) = (((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term54 A c1 c2 i1 i2 r1 r2)).
Proof. exact (@lem32 ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) (term54 A c1 c2 i1 i2 r1 r2)). Qed.
Lemma lem1060608 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) (r2 : type1614 A) : ((@CONSTR A c1 i1 r1) = (@CONSTR A c2 i2 r2)) = (term54 A c1 c2 i1 i2 r1 r2).
Proof. exact (EQ_MP (@lem1060607 A c1 c2 i1 i2 r1 r2) (@lem1060606 A c1 i1 r1 c2 i2 r2)). Qed.
Lemma lem1060613 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (i2 : A) (r1 : type1614 A) : term136 A c1 c2 i1 i2 r1.
Proof. exact (fun r2 : type1614 A => @lem1060608 A c1 c2 i1 i2 r1 r2). Qed.
Lemma lem1060618 {A : Type'} (c1 : nat) (c2 : nat) (i1 : A) (r1 : type1614 A) : term137 A c1 c2 i1 r1.
Proof. exact (fun i2 : A => @lem1060613 A c1 c2 i1 i2 r1). Qed.
Lemma lem1060623 {A : Type'} (c1 : nat) (i1 : A) (r1 : type1614 A) : term138 A c1 i1 r1.
Proof. exact (fun c2 : nat => @lem1060618 A c1 c2 i1 r1). Qed.
Lemma lem1060628 {A : Type'} (c1 : nat) (i1 : A) : term139 A c1 i1.
Proof. exact (fun r1 : type1614 A => @lem1060623 A c1 i1 r1). Qed.
Lemma lem1060633 {A : Type'} (c1 : nat) : term140 A c1.
Proof. exact (fun i1 : A => @lem1060628 A c1 i1). Qed.
Lemma lem1060638 {A : Type'} : term141 A.
Proof. exact (fun c1 : nat => @lem1060633 A c1). Qed.
