Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_SING_term_abbrevs.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_CROSS_spec.
Require Import IN_SING_spec.
Require Import PAIR_EQ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4327079 {A B : Type'} (x : A) : term0 A B x.
Proof. exact (@lem47438 A B x). Qed.
Lemma lem4327080 {A B : Type'} (x : A) : (term0 A B x) = (term1 A B x).
Proof. exact (eq_refl (term0 A B x)). Qed.
Lemma lem4327081 {A B : Type'} (x : A) : term1 A B x.
Proof. exact (EQ_MP (@lem4327080 A B x) (@lem4327079 A B x)). Qed.
Lemma lem4327082 {A B : Type'} (x : A) (y : B) : term2 A B x y.
Proof. exact (@lem4327081 A B x y). Qed.
Lemma lem4327083 {A B : Type'} (x : A) (y : B) : (term2 A B x y) = (term3 A B x y).
Proof. exact (eq_refl (term2 A B x y)). Qed.
Lemma lem4327084 {A B : Type'} (x : A) (y : B) : term3 A B x y.
Proof. exact (EQ_MP (@lem4327083 A B x y) (@lem4327082 A B x y)). Qed.
Lemma lem4327085 {A B : Type'} (x : A) (y : B) (a : A) : term4 A B x y a.
Proof. exact (@lem4327084 A B x y a). Qed.
Lemma lem4327086 {A B : Type'} (x : A) (a : A) (y : B) : (term4 A B x y a) = (term5 A B x a y).
Proof. exact (eq_refl (term4 A B x y a)). Qed.
Lemma lem4327087 {A B : Type'} (x : A) (a : A) (y : B) : term5 A B x a y.
Proof. exact (EQ_MP (@lem4327086 A B x a y) (@lem4327085 A B x y a)). Qed.
Lemma lem4327088 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : term6 A B x a y b.
Proof. exact (@lem4327087 A B x a y b). Qed.
Lemma lem4327089 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : (term6 A B x a y b) = (((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b)).
Proof. exact (eq_refl (term6 A B x a y b)). Qed.
Lemma lem4327091 {_103718 _103721 : Type'} (x : _103718) : term8 _103718 _103721 x.
Proof. exact (@lem4325365 _103718 _103721 x). Qed.
Lemma lem4327092 {_103718 _103721 : Type'} (x : _103718) : (term8 _103718 _103721 x) = (term9 _103718 _103721 x).
Proof. exact (eq_refl (term8 _103718 _103721 x)). Qed.
Lemma lem4327093 {_103718 _103721 : Type'} (x : _103718) : term9 _103718 _103721 x.
Proof. exact (EQ_MP (@lem4327092 _103718 _103721 x) (@lem4327091 _103718 _103721 x)). Qed.
Lemma lem4327094 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term10 _103718 _103721 x y.
Proof. exact (@lem4327093 _103718 _103721 x y). Qed.
Lemma lem4327095 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term10 _103718 _103721 x y) = (term11 _103718 _103721 x y).
Proof. exact (eq_refl (term10 _103718 _103721 x y)). Qed.
Lemma lem4327096 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : term11 _103718 _103721 x y.
Proof. exact (EQ_MP (@lem4327095 _103718 _103721 x y) (@lem4327094 _103718 _103721 x y)). Qed.
Lemma lem4327097 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) : term12 _103718 _103721 x y s.
Proof. exact (@lem4327096 _103718 _103721 x y s). Qed.
Lemma lem4327098 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term12 _103718 _103721 x y s) = (term13 _103718 _103721 x s y).
Proof. exact (eq_refl (term12 _103718 _103721 x y s)). Qed.
Lemma lem4327099 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : term13 _103718 _103721 x s y.
Proof. exact (EQ_MP (@lem4327098 _103718 _103721 x s y) (@lem4327097 _103718 _103721 x y s)). Qed.
Lemma lem4327100 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : term14 _103718 _103721 x s y t.
Proof. exact (@lem4327099 _103718 _103721 x s y t). Qed.
Lemma lem4327101 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term14 _103718 _103721 x s y t) = ((term15 _103718 _103721 x y s t) = (term16 _103718 _103721 x s y t)).
Proof. exact (eq_refl (term14 _103718 _103721 x s y t)). Qed.
Lemma lem4327103 {A : Type'} (x : A) : term17 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4327104 {A : Type'} (x : A) : (term17 A x) = (term18 A x).
Proof. exact (eq_refl (term17 A x)). Qed.
Lemma lem4327105 {A : Type'} (x : A) : term18 A x.
Proof. exact (EQ_MP (@lem4327104 A x) (@lem4327103 A x)). Qed.
Lemma lem4327106 {A : Type'} (x : A) (y : A) : term19 A x y.
Proof. exact (@lem4327105 A x y). Qed.
Lemma lem4327107 {A : Type'} (x : A) (y : A) : (term19 A x y) = ((term20 A x y) = (x = y)).
Proof. exact (eq_refl (term19 A x y)). Qed.
Lemma lem4327109 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term21 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4327110 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term21 _5106 _5107 P) = ((term22 _5106 _5107 P) = (term23 _5106 _5107 P)).
Proof. exact (eq_refl (term21 _5106 _5107 P)). Qed.
Lemma lem4327112 {A : Type'} (s : A -> Prop) : term24 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4327113 {A : Type'} (s : A -> Prop) : (term24 A s) = (term25 A s).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4327114 {A : Type'} (s : A -> Prop) : term25 A s.
Proof. exact (EQ_MP (@lem4327113 A s) (@lem4327112 A s)). Qed.
Lemma lem4327115 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term26 A s t.
Proof. exact (@lem4327114 A s t). Qed.
Lemma lem4327116 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term26 A s t) = ((s = t) = (term27 A s t)).
Proof. exact (eq_refl (term26 A s t)). Qed.
Lemma lem4327133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term27 A s t).
Proof. exact (EQ_MP (@lem4327116 A s t) (@lem4327115 A s t)). Qed.
Lemma lem4327134 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = t) = (term28 A B s t).
Proof. exact (@lem4327133 (prod A B) s t). Qed.
Lemma lem4327135 {A B : Type'} (x : A) (y : B) : ((term29 A B x y) = (term30 A B x y)) = (term31 A B x y).
Proof. exact (@lem4327134 A B (term29 A B x y) (term30 A B x y)). Qed.
Lemma lem4327141 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term22 _5106 _5107 P) = (term23 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4327110 _5106 _5107 P) (@lem4327109 _5106 _5107 P)). Qed.
Lemma lem4327142 {A B : Type'} (P : type1210 A B) : (term32 A B P) = (term33 A B P).
Proof. exact (@lem4327141 B A P). Qed.
Lemma lem4327143 {A B : Type'} (x : A) (y : B) : (term34 A B x y) = (term35 A B x y).
Proof. exact (@lem4327142 A B (term36 A B x y)). Qed.
Lemma lem4327144 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term37 A B x' y x) = ((term38 A B x x' y) = (term39 A B x x' y)).
Proof. exact (eq_refl (term37 A B x' y x)). Qed.
Lemma lem4327145 {A B : Type'} (x : A) (y : B) : (term40 A B x y) = (term36 A B x y).
Proof. exact (fun_ext (fun x' : prod A B => @lem4327144 A B x' x y)). Qed.
Lemma lem4327146 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4327147 {A B : Type'} (x : A) (y : B) : (term34 A B x y) = (term31 A B x y).
Proof. exact (MK_COMB (@lem4327146 A B) (@lem4327145 A B x y)). Qed.
Lemma lem4327148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327149 {A B : Type'} (x : A) (y : B) : (term41 A B x y) = (term42 A B x y).
Proof. exact (MK_COMB (@lem4327148) (@lem4327147 A B x y)). Qed.
Lemma lem4327150 {A B : Type'} (p1 : A) (p2 : B) (x : A) (y : B) : (term43 A B x y p1 p2) = ((term44 A B p1 p2 x y) = (term45 A B p1 p2 x y)).
Proof. exact (eq_refl (term43 A B x y p1 p2)). Qed.
Lemma lem4327151 {A B : Type'} (p1 : A) (x : A) (y : B) : (term46 A B x y p1) = (term47 A B p1 x y).
Proof. exact (fun_ext (fun p2 : B => @lem4327150 A B p1 p2 x y)). Qed.
Lemma lem4327152 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4327153 {A B : Type'} (p1 : A) (x : A) (y : B) : (term48 A B x y p1) = (term49 A B p1 x y).
Proof. exact (MK_COMB (@lem4327152 B) (@lem4327151 A B p1 x y)). Qed.
Lemma lem4327154 {A B : Type'} (x : A) (y : B) : (term50 A B x y) = (term51 A B x y).
Proof. exact (fun_ext (fun p1 : A => @lem4327153 A B p1 x y)). Qed.
Lemma lem4327155 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4327156 {A B : Type'} (x : A) (y : B) : (term35 A B x y) = (term52 A B x y).
Proof. exact (MK_COMB (@lem4327155 A) (@lem4327154 A B x y)). Qed.
Lemma lem4327157 {A B : Type'} (x : A) (y : B) : ((term34 A B x y) = (term35 A B x y)) = ((term31 A B x y) = (term52 A B x y)).
Proof. exact (MK_COMB (@lem4327149 A B x y) (@lem4327156 A B x y)). Qed.
Lemma lem4327158 {A B : Type'} (x : A) (y : B) : (term31 A B x y) = (term52 A B x y).
Proof. exact (EQ_MP (@lem4327157 A B x y) (@lem4327143 A B x y)). Qed.
Lemma lem4327165 {A B : Type'} (x : A) (y : B) : ((term29 A B x y) = (term30 A B x y)) = (term52 A B x y).
Proof. exact (TRANS (@lem4327135 A B x y) (@lem4327158 A B x y)). Qed.
Lemma lem4327177 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term15 _103718 _103721 x y s t) = (term16 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4327101 _103718 _103721 x s y t) (@lem4327100 _103718 _103721 x s y t)). Qed.
Lemma lem4327178 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term15 A B x y s t) = (term16 A B x s y t).
Proof. exact (@lem4327177 A B x s y t). Qed.
Lemma lem4327179 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : (term44 A B p1 p2 x y) = (term53 A B p1 x p2 y).
Proof. exact (@lem4327178 A B p1 (@INSERT A x (@EMPTY A)) p2 (@INSERT B y (@EMPTY B))). Qed.
Lemma lem4327183 {A : Type'} (x : A) (y : A) : (term20 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4327107 A x y) (@lem4327106 A x y)). Qed.
Lemma lem4327184 {A : Type'} (x : A) (y : A) : (term20 A x y) = (x = y).
Proof. exact (@lem4327183 A x y). Qed.
Lemma lem4327185 {A : Type'} (p1 : A) (x : A) : (term20 A p1 x) = (p1 = x).
Proof. exact (@lem4327184 A p1 x). Qed.
Lemma lem4327190 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4327191 {A : Type'} (p1 : A) (x : A) : (term54 A p1 x) = (term55 A p1 x).
Proof. exact (MK_COMB (@lem4327190) (@lem4327185 A p1 x)). Qed.
Lemma lem4327193 {A : Type'} (x : A) (y : A) : (term20 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4327107 A x y) (@lem4327106 A x y)). Qed.
Lemma lem4327194 {B : Type'} (x : B) (y : B) : (term20 B x y) = (x = y).
Proof. exact (@lem4327193 B x y). Qed.
Lemma lem4327195 {B : Type'} (p2 : B) (y : B) : (term20 B p2 y) = (p2 = y).
Proof. exact (@lem4327194 B p2 y). Qed.
Lemma lem4327200 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : (term53 A B p1 x p2 y) = (term7 A B p1 x p2 y).
Proof. exact (MK_COMB (@lem4327191 A p1 x) (@lem4327195 B p2 y)). Qed.
Lemma lem4327203 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : (term44 A B p1 p2 x y) = (term7 A B p1 x p2 y).
Proof. exact (TRANS (@lem4327179 A B p1 x p2 y) (@lem4327200 A B p1 x p2 y)). Qed.
Lemma lem4327204 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327205 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : (term56 A B p1 p2 x y) = (term57 A B p1 x p2 y).
Proof. exact (MK_COMB (@lem4327204) (@lem4327203 A B p1 x p2 y)). Qed.
Lemma lem4327207 {A : Type'} (x : A) (y : A) : (term20 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4327107 A x y) (@lem4327106 A x y)). Qed.
Lemma lem4327208 {A B : Type'} (x : prod A B) (y : prod A B) : (term58 A B x y) = (x = y).
Proof. exact (@lem4327207 (prod A B) x y). Qed.
Lemma lem4327209 {A B : Type'} (p1 : A) (p2 : B) (x : A) (y : B) : (term45 A B p1 p2 x y) = ((@pair A B p1 p2) = (@pair A B x y)).
Proof. exact (@lem4327208 A B (@pair A B p1 p2) (@pair A B x y)). Qed.
Lemma lem4327211 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b).
Proof. exact (EQ_MP (@lem4327089 A B x a y b) (@lem4327088 A B x a y b)). Qed.
Lemma lem4327212 {A B : Type'} (x : A) (a : A) (y : B) (b : B) : ((@pair A B x y) = (@pair A B a b)) = (term7 A B x a y b).
Proof. exact (@lem4327211 A B x a y b). Qed.
Lemma lem4327213 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : ((@pair A B p1 p2) = (@pair A B x y)) = (term7 A B p1 x p2 y).
Proof. exact (@lem4327212 A B p1 x p2 y). Qed.
Lemma lem4327216 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : (term45 A B p1 p2 x y) = (term7 A B p1 x p2 y).
Proof. exact (TRANS (@lem4327209 A B p1 p2 x y) (@lem4327213 A B p1 x p2 y)). Qed.
Lemma lem4327225 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : ((term44 A B p1 p2 x y) = (term45 A B p1 p2 x y)) = ((term7 A B p1 x p2 y) = (term7 A B p1 x p2 y)).
Proof. exact (MK_COMB (@lem4327205 A B p1 x p2 y) (@lem4327216 A B p1 x p2 y)). Qed.
Lemma lem4327227 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4327228 (x : Prop) : (x = x) = True.
Proof. exact (@lem4327227 Prop x). Qed.
Lemma lem4327229 {A B : Type'} (p1 : A) (x : A) (p2 : B) (y : B) : ((term7 A B p1 x p2 y) = (term7 A B p1 x p2 y)) = True.
Proof. exact (@lem4327228 (term7 A B p1 x p2 y)). Qed.
Lemma lem4327230 {A B : Type'} (p1 : A) (p2 : B) (x : A) (y : B) : ((term44 A B p1 p2 x y) = (term45 A B p1 p2 x y)) = True.
Proof. exact (TRANS (@lem4327225 A B p1 x p2 y) (@lem4327229 A B p1 x p2 y)). Qed.
Lemma lem4327231 {A B : Type'} (p1 : A) (x : A) (y : B) : (term47 A B p1 x y) = (term59 B).
Proof. exact (fun_ext (fun p2 : B => @lem4327230 A B p1 p2 x y)). Qed.
Lemma lem4327232 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4327233 {A B : Type'} (p1 : A) (x : A) (y : B) : (term49 A B p1 x y) = (term60 B).
Proof. exact (MK_COMB (@lem4327232 B) (@lem4327231 A B p1 x y)). Qed.
Lemma lem4327235 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327236 {B : Type'} (t : Prop) : (term61 B t) = t.
Proof. exact (@lem4327235 B t). Qed.
Lemma lem4327237 {B : Type'} : (term60 B) = True.
Proof. exact (@lem4327236 B True). Qed.
Lemma lem4327238 {A B : Type'} (p1 : A) (x : A) (y : B) : (term49 A B p1 x y) = True.
Proof. exact (TRANS (@lem4327233 A B p1 x y) (@lem4327237 B)). Qed.
Lemma lem4327239 {A B : Type'} (x : A) (y : B) : (term51 A B x y) = (term59 A).
Proof. exact (fun_ext (fun p1 : A => @lem4327238 A B p1 x y)). Qed.
Lemma lem4327240 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4327241 {A B : Type'} (x : A) (y : B) : (term52 A B x y) = (term60 A).
Proof. exact (MK_COMB (@lem4327240 A) (@lem4327239 A B x y)). Qed.
Lemma lem4327243 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327244 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (@lem4327243 A t). Qed.
Lemma lem4327245 {A : Type'} : (term60 A) = True.
Proof. exact (@lem4327244 A True). Qed.
Lemma lem4327246 {A B : Type'} (x : A) (y : B) : (term52 A B x y) = True.
Proof. exact (TRANS (@lem4327241 A B x y) (@lem4327245 A)). Qed.
Lemma lem4327247 {A B : Type'} (x : A) (y : B) : ((term29 A B x y) = (term30 A B x y)) = True.
Proof. exact (TRANS (@lem4327165 A B x y) (@lem4327246 A B x y)). Qed.
Lemma lem4327248 {A B : Type'} (x : A) : (term62 A B x) = (term59 B).
Proof. exact (fun_ext (fun y : B => @lem4327247 A B x y)). Qed.
Lemma lem4327249 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4327250 {A B : Type'} (x : A) : (term63 A B x) = (term60 B).
Proof. exact (MK_COMB (@lem4327249 B) (@lem4327248 A B x)). Qed.
Lemma lem4327252 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327253 {B : Type'} (t : Prop) : (term61 B t) = t.
Proof. exact (@lem4327252 B t). Qed.
Lemma lem4327254 {B : Type'} : (term60 B) = True.
Proof. exact (@lem4327253 B True). Qed.
Lemma lem4327255 {A B : Type'} (x : A) : (term63 A B x) = True.
Proof. exact (TRANS (@lem4327250 A B x) (@lem4327254 B)). Qed.
Lemma lem4327256 {A B : Type'} : (term64 A B) = (term59 A).
Proof. exact (fun_ext (fun x : A => @lem4327255 A B x)). Qed.
Lemma lem4327257 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4327258 {A B : Type'} : (term65 A B) = (term60 A).
Proof. exact (MK_COMB (@lem4327257 A) (@lem4327256 A B)). Qed.
Lemma lem4327260 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327261 {A : Type'} (t : Prop) : (term61 A t) = t.
Proof. exact (@lem4327260 A t). Qed.
Lemma lem4327262 {A : Type'} : (term60 A) = True.
Proof. exact (@lem4327261 A True). Qed.
Lemma lem4327263 {A B : Type'} : (term65 A B) = True.
Proof. exact (TRANS (@lem4327258 A B) (@lem4327262 A)). Qed.
Lemma lem4327264 {A B : Type'} : True = (term65 A B).
Proof. exact (SYM (@lem4327263 A B)). Qed.
Lemma lem4327265 {A B : Type'} : term65 A B.
Proof. exact (EQ_MP (@lem4327264 A B) (@lem0)). Qed.
