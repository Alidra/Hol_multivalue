Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MAP_I_term_abbrevs.
Require Import FUN_EQ_THM_spec.
Require Import MAP_ID_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1200075 {_27941 : Type'} (l : list _27941) : term0 _27941 l.
Proof. exact (@lem1200074 _27941 l). Qed.
Lemma lem1200076 {_27941 : Type'} (l : list _27941) : (term0 _27941 l) = ((term1 _27941 l) = l).
Proof. exact (eq_refl (term0 _27941 l)). Qed.
Lemma lem1200078 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem1200079 {A B : Type'} (f : A -> B) : (term2 A B f) = (term3 A B f).
Proof. exact (eq_refl (term2 A B f)). Qed.
Lemma lem1200080 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (EQ_MP (@lem1200079 A B f) (@lem1200078 A B f)). Qed.
Lemma lem1200081 {A B : Type'} (f : A -> B) (g : A -> B) : term4 A B f g.
Proof. exact (@lem1200080 A B f g). Qed.
Lemma lem1200082 {A B : Type'} (f : A -> B) (g : A -> B) : (term4 A B f g) = ((f = g) = (term5 A B f g)).
Proof. exact (eq_refl (term4 A B f g)). Qed.
Lemma lem1200087 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term5 A B f g).
Proof. exact (EQ_MP (@lem1200082 A B f g) (@lem1200081 A B f g)). Qed.
Lemma lem1200088 {_27950 : Type'} (f : type1138 _27950) (g : type1138 _27950) : (f = g) = (term6 _27950 f g).
Proof. exact (@lem1200087 (list _27950) (list _27950) f g). Qed.
Lemma lem1200089 {_27950 : Type'} : ((@List.map _27950 _27950 (@I _27950)) = (@I (list _27950))) = (term7 _27950).
Proof. exact (@lem1200088 _27950 (@List.map _27950 _27950 (@I _27950)) (@I (list _27950))). Qed.
Lemma lem1200099 {A : Type'} : (@I A) = (term8 A).
Proof. exact (@I_def A). Qed.
Lemma lem1200100 {_27950 : Type'} : (@I _27950) = (term8 _27950).
Proof. exact (@lem1200099 _27950). Qed.
Lemma lem1200101 {_27950 : Type'} : (@List.map _27950 _27950) = (@List.map _27950 _27950).
Proof. exact (eq_refl (@List.map _27950 _27950)). Qed.
Lemma lem1200102 {_27950 : Type'} : (@List.map _27950 _27950 (@I _27950)) = (term9 _27950).
Proof. exact (MK_COMB (@lem1200101 _27950) (@lem1200100 _27950)). Qed.
Lemma lem1200103 {_27950 : Type'} (x : list _27950) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1200104 {_27950 : Type'} (x : list _27950) : (@List.map _27950 _27950 (@I _27950) x) = (term1 _27950 x).
Proof. exact (MK_COMB (@lem1200102 _27950) (@lem1200103 _27950 x)). Qed.
Lemma lem1200106 {_27941 : Type'} (l : list _27941) : (term1 _27941 l) = l.
Proof. exact (EQ_MP (@lem1200076 _27941 l) (@lem1200075 _27941 l)). Qed.
Lemma lem1200107 {_27950 : Type'} (l : list _27950) : (term1 _27950 l) = l.
Proof. exact (@lem1200106 _27950 l). Qed.
Lemma lem1200108 {_27950 : Type'} (x : list _27950) : (term1 _27950 x) = x.
Proof. exact (@lem1200107 _27950 x). Qed.
Lemma lem1200109 {_27950 : Type'} (x : list _27950) : (@List.map _27950 _27950 (@I _27950) x) = x.
Proof. exact (TRANS (@lem1200104 _27950 x) (@lem1200108 _27950 x)). Qed.
Lemma lem1200110 {_27950 : Type'} : (@eq (list _27950)) = (@eq (list _27950)).
Proof. exact (eq_refl (@eq (list _27950))). Qed.
Lemma lem1200111 {_27950 : Type'} (x : list _27950) : (term10 _27950 x) = (@eq (list _27950) x).
Proof. exact (MK_COMB (@lem1200110 _27950) (@lem1200109 _27950 x)). Qed.
Lemma lem1200113 {A : Type'} : (@I A) = (term8 A).
Proof. exact (@I_def A). Qed.
Lemma lem1200114 {_27950 : Type'} : (@I (list _27950)) = (term11 _27950).
Proof. exact (@lem1200113 (list _27950)). Qed.
Lemma lem1200115 {_27950 : Type'} (x : list _27950) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1200116 {_27950 : Type'} (x : list _27950) : (@I (list _27950) x) = (term12 _27950 x).
Proof. exact (MK_COMB (@lem1200114 _27950) (@lem1200115 _27950 x)). Qed.
Lemma lem1200118 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1200119 {_27950 : Type'} (f : type1138 _27950) (y : list _27950) : (term14 _27950 f y) = (f y).
Proof. exact (@lem1200118 (list _27950) (list _27950) f y). Qed.
Lemma lem1200120 {_27950 : Type'} (x : list _27950) : (term15 _27950 x) = (term12 _27950 x).
Proof. exact (@lem1200119 _27950 (term11 _27950) x). Qed.
Lemma lem1200121 {_27950 : Type'} (x : list _27950) : (term12 _27950 x) = x.
Proof. exact (eq_refl (term12 _27950 x)). Qed.
Lemma lem1200122 {_27950 : Type'} : (term16 _27950) = (term11 _27950).
Proof. exact (fun_ext (fun x : list _27950 => @lem1200121 _27950 x)). Qed.
Lemma lem1200123 {_27950 : Type'} (x : list _27950) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1200124 {_27950 : Type'} (x : list _27950) : (term15 _27950 x) = (term12 _27950 x).
Proof. exact (MK_COMB (@lem1200122 _27950) (@lem1200123 _27950 x)). Qed.
Lemma lem1200125 {_27950 : Type'} : (@eq (list _27950)) = (@eq (list _27950)).
Proof. exact (eq_refl (@eq (list _27950))). Qed.
Lemma lem1200126 {_27950 : Type'} (x : list _27950) : (term17 _27950 x) = (term18 _27950 x).
Proof. exact (MK_COMB (@lem1200125 _27950) (@lem1200124 _27950 x)). Qed.
Lemma lem1200127 {_27950 : Type'} (x : list _27950) : (term12 _27950 x) = x.
Proof. exact (eq_refl (term12 _27950 x)). Qed.
Lemma lem1200128 {_27950 : Type'} (x : list _27950) : ((term15 _27950 x) = (term12 _27950 x)) = ((term12 _27950 x) = x).
Proof. exact (MK_COMB (@lem1200126 _27950 x) (@lem1200127 _27950 x)). Qed.
Lemma lem1200129 {_27950 : Type'} (x : list _27950) : (term12 _27950 x) = x.
Proof. exact (EQ_MP (@lem1200128 _27950 x) (@lem1200120 _27950 x)). Qed.
Lemma lem1200130 {_27950 : Type'} (x : list _27950) : (@I (list _27950) x) = x.
Proof. exact (TRANS (@lem1200116 _27950 x) (@lem1200129 _27950 x)). Qed.
Lemma lem1200131 {_27950 : Type'} (x : list _27950) : ((@List.map _27950 _27950 (@I _27950) x) = (@I (list _27950) x)) = (x = x).
Proof. exact (MK_COMB (@lem1200111 _27950 x) (@lem1200130 _27950 x)). Qed.
Lemma lem1200133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1200134 {_27950 : Type'} (x : list _27950) : (x = x) = True.
Proof. exact (@lem1200133 (list _27950) x). Qed.
Lemma lem1200135 {_27950 : Type'} (x : list _27950) : ((@List.map _27950 _27950 (@I _27950) x) = (@I (list _27950) x)) = True.
Proof. exact (TRANS (@lem1200131 _27950 x) (@lem1200134 _27950 x)). Qed.
Lemma lem1200136 {_27950 : Type'} : (term19 _27950) = (term20 _27950).
Proof. exact (fun_ext (fun x : list _27950 => @lem1200135 _27950 x)). Qed.
Lemma lem1200137 {_27950 : Type'} : (@all (list _27950)) = (@all (list _27950)).
Proof. exact (eq_refl (@all (list _27950))). Qed.
Lemma lem1200138 {_27950 : Type'} : (term7 _27950) = (term21 _27950).
Proof. exact (MK_COMB (@lem1200137 _27950) (@lem1200136 _27950)). Qed.
Lemma lem1200140 {A : Type'} (t : Prop) : (term22 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1200141 {_27950 : Type'} (t : Prop) : (term23 _27950 t) = t.
Proof. exact (@lem1200140 (list _27950) t). Qed.
Lemma lem1200142 {_27950 : Type'} : (term21 _27950) = True.
Proof. exact (@lem1200141 _27950 True). Qed.
Lemma lem1200143 {_27950 : Type'} : (term7 _27950) = True.
Proof. exact (TRANS (@lem1200138 _27950) (@lem1200142 _27950)). Qed.
Lemma lem1200144 {_27950 : Type'} : ((@List.map _27950 _27950 (@I _27950)) = (@I (list _27950))) = True.
Proof. exact (TRANS (@lem1200089 _27950) (@lem1200143 _27950)). Qed.
Lemma lem1200145 {_27950 : Type'} : True = ((@List.map _27950 _27950 (@I _27950)) = (@I (list _27950))).
Proof. exact (SYM (@lem1200144 _27950)). Qed.
Lemma lem1200146 {_27950 : Type'} : (@List.map _27950 _27950 (@I _27950)) = (@I (list _27950)).
Proof. exact (EQ_MP (@lem1200145 _27950) (@lem0)). Qed.
