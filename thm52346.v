Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm52346_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm51886_spec.
Require Import thm51887_spec.
Require Import thm51892_spec.
Require Import thm51893_spec.
Lemma lem52071 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term0 A B f g).
Proof. exact (EQ_MP (@lem51893 A B f g) (@lem51892 A B f g)). Qed.
Lemma lem52072 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (g : type1219 _5284 _5296 _5299 _5300) : (f = g) = (term1 _5284 _5296 _5299 _5300 f g).
Proof. exact (@lem52071 (type1657 _5296 _5299 _5300) _5284 f g). Qed.
Lemma lem52073 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : ((term2 _5284 _5296 _5299 _5300 f) = f) = (term3 _5284 _5296 _5299 _5300 f).
Proof. exact (@lem52072 _5284 _5296 _5299 _5300 (term2 _5284 _5296 _5299 _5300 f) f). Qed.
Lemma lem52079 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = (term5 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51887 _5106 _5107 P) (@lem51886 _5106 _5107 P)). Qed.
Lemma lem52080 {_5296 _5299 _5300 : Type'} (P : type1202 _5296 _5299 _5300) : (term6 _5296 _5299 _5300 P) = (term7 _5296 _5299 _5300 P).
Proof. exact (@lem52079 (prod _5300 _5299) _5296 P). Qed.
Lemma lem52081 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term8 _5284 _5296 _5299 _5300 f) = (term9 _5284 _5296 _5299 _5300 f).
Proof. exact (@lem52080 _5296 _5299 _5300 (term10 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52082 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : type1657 _5296 _5299 _5300) : (term11 _5284 _5296 _5299 _5300 f x) = ((term12 _5284 _5296 _5299 _5300 f x) = (f x)).
Proof. exact (eq_refl (term11 _5284 _5296 _5299 _5300 f x)). Qed.
Lemma lem52083 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term13 _5284 _5296 _5299 _5300 f) = (term10 _5284 _5296 _5299 _5300 f).
Proof. exact (fun_ext (fun x : type1657 _5296 _5299 _5300 => @lem52082 _5284 _5296 _5299 _5300 f x)). Qed.
Lemma lem52084 {_5296 _5299 _5300 : Type'} : (@all (prod _5296 (prod _5300 _5299))) = (@all (prod _5296 (prod _5300 _5299))).
Proof. exact (eq_refl (@all (prod _5296 (prod _5300 _5299)))). Qed.
Lemma lem52085 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term8 _5284 _5296 _5299 _5300 f) = (term3 _5284 _5296 _5299 _5300 f).
Proof. exact (MK_COMB (@lem52084 _5296 _5299 _5300) (@lem52083 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem52087 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term14 _5284 _5296 _5299 _5300 f) = (term15 _5284 _5296 _5299 _5300 f).
Proof. exact (MK_COMB (@lem52086) (@lem52085 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52088 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p2 : prod _5300 _5299) : (term16 _5284 _5296 _5299 _5300 f p1 p2) = ((term17 _5284 _5296 _5299 _5300 f p1 p2) = (term18 _5284 _5296 _5299 _5300 f p1 p2)).
Proof. exact (eq_refl (term16 _5284 _5296 _5299 _5300 f p1 p2)). Qed.
Lemma lem52089 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term19 _5284 _5296 _5299 _5300 f p1) = (term20 _5284 _5296 _5299 _5300 f p1).
Proof. exact (fun_ext (fun p2 : prod _5300 _5299 => @lem52088 _5284 _5296 _5299 _5300 f p1 p2)). Qed.
Lemma lem52090 {_5299 _5300 : Type'} : (@all (prod _5300 _5299)) = (@all (prod _5300 _5299)).
Proof. exact (eq_refl (@all (prod _5300 _5299))). Qed.
Lemma lem52091 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term21 _5284 _5296 _5299 _5300 f p1) = (term22 _5284 _5296 _5299 _5300 f p1).
Proof. exact (MK_COMB (@lem52090 _5299 _5300) (@lem52089 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52092 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term23 _5284 _5296 _5299 _5300 f) = (term24 _5284 _5296 _5299 _5300 f).
Proof. exact (fun_ext (fun p1 : _5296 => @lem52091 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52093 {_5296 : Type'} : (@all _5296) = (@all _5296).
Proof. exact (eq_refl (@all _5296)). Qed.
Lemma lem52094 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term9 _5284 _5296 _5299 _5300 f) = (term25 _5284 _5296 _5299 _5300 f).
Proof. exact (MK_COMB (@lem52093 _5296) (@lem52092 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52095 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : ((term8 _5284 _5296 _5299 _5300 f) = (term9 _5284 _5296 _5299 _5300 f)) = ((term3 _5284 _5296 _5299 _5300 f) = (term25 _5284 _5296 _5299 _5300 f)).
Proof. exact (MK_COMB (@lem52087 _5284 _5296 _5299 _5300 f) (@lem52094 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52096 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term3 _5284 _5296 _5299 _5300 f) = (term25 _5284 _5296 _5299 _5300 f).
Proof. exact (EQ_MP (@lem52095 _5284 _5296 _5299 _5300 f) (@lem52081 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52103 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : ((term2 _5284 _5296 _5299 _5300 f) = f) = (term25 _5284 _5296 _5299 _5300 f).
Proof. exact (TRANS (@lem52073 _5284 _5296 _5299 _5300 f) (@lem52096 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52109 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term4 _5106 _5107 P) = (term5 _5106 _5107 P).
Proof. exact (EQ_MP (@lem51887 _5106 _5107 P) (@lem51886 _5106 _5107 P)). Qed.
Lemma lem52110 {_5299 _5300 : Type'} (P : type1223 _5299 _5300) : (term4 _5299 _5300 P) = (term5 _5299 _5300 P).
Proof. exact (@lem52109 _5299 _5300 P). Qed.
Lemma lem52111 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term26 _5284 _5296 _5299 _5300 f p1) = (term27 _5284 _5296 _5299 _5300 f p1).
Proof. exact (@lem52110 _5299 _5300 (term20 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52112 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p2 : prod _5300 _5299) : (term28 _5284 _5296 _5299 _5300 f p1 p2) = ((term17 _5284 _5296 _5299 _5300 f p1 p2) = (term18 _5284 _5296 _5299 _5300 f p1 p2)).
Proof. exact (eq_refl (term28 _5284 _5296 _5299 _5300 f p1 p2)). Qed.
Lemma lem52113 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term29 _5284 _5296 _5299 _5300 f p1) = (term20 _5284 _5296 _5299 _5300 f p1).
Proof. exact (fun_ext (fun p2 : prod _5300 _5299 => @lem52112 _5284 _5296 _5299 _5300 f p1 p2)). Qed.
Lemma lem52114 {_5299 _5300 : Type'} : (@all (prod _5300 _5299)) = (@all (prod _5300 _5299)).
Proof. exact (eq_refl (@all (prod _5300 _5299))). Qed.
Lemma lem52115 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term26 _5284 _5296 _5299 _5300 f p1) = (term22 _5284 _5296 _5299 _5300 f p1).
Proof. exact (MK_COMB (@lem52114 _5299 _5300) (@lem52113 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52116 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem52117 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term30 _5284 _5296 _5299 _5300 f p1) = (term31 _5284 _5296 _5299 _5300 f p1).
Proof. exact (MK_COMB (@lem52116) (@lem52115 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52118 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) (p2 : _5299) : (term32 _5284 _5296 _5299 _5300 f p1 p1' p2) = ((term33 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term34 _5284 _5296 _5299 _5300 f p1 p1' p2)).
Proof. exact (eq_refl (term32 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52119 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) : (term35 _5284 _5296 _5299 _5300 f p1 p1') = (term36 _5284 _5296 _5299 _5300 f p1 p1').
Proof. exact (fun_ext (fun p2 : _5299 => @lem52118 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52120 {_5299 : Type'} : (@all _5299) = (@all _5299).
Proof. exact (eq_refl (@all _5299)). Qed.
Lemma lem52121 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) : (term37 _5284 _5296 _5299 _5300 f p1 p1') = (term38 _5284 _5296 _5299 _5300 f p1 p1').
Proof. exact (MK_COMB (@lem52120 _5299) (@lem52119 _5284 _5296 _5299 _5300 f p1 p1')). Qed.
Lemma lem52122 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term39 _5284 _5296 _5299 _5300 f p1) = (term40 _5284 _5296 _5299 _5300 f p1).
Proof. exact (fun_ext (fun p1' : _5300 => @lem52121 _5284 _5296 _5299 _5300 f p1 p1')). Qed.
Lemma lem52123 {_5300 : Type'} : (@all _5300) = (@all _5300).
Proof. exact (eq_refl (@all _5300)). Qed.
Lemma lem52124 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term27 _5284 _5296 _5299 _5300 f p1) = (term41 _5284 _5296 _5299 _5300 f p1).
Proof. exact (MK_COMB (@lem52123 _5300) (@lem52122 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52125 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : ((term26 _5284 _5296 _5299 _5300 f p1) = (term27 _5284 _5296 _5299 _5300 f p1)) = ((term22 _5284 _5296 _5299 _5300 f p1) = (term41 _5284 _5296 _5299 _5300 f p1)).
Proof. exact (MK_COMB (@lem52117 _5284 _5296 _5299 _5300 f p1) (@lem52124 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52126 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term22 _5284 _5296 _5299 _5300 f p1) = (term41 _5284 _5296 _5299 _5300 f p1).
Proof. exact (EQ_MP (@lem52125 _5284 _5296 _5299 _5300 f p1) (@lem52111 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52143 {_5296 _5299 _5300 : Type'} (a0 : _5296) (a1 : prod _5300 _5299) : a0 = (term42 _5296 _5299 _5300 a0 a1).
Proof. exact (@lem51128 _5296 (prod _5300 _5299) a0 a1). Qed.
Lemma lem52144 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : x = (term43 _5296 _5299 _5300 x y z).
Proof. exact (@lem52143 _5296 _5299 _5300 x (@pair _5300 _5299 y z)). Qed.
Lemma lem52145 {_5296 _5299 _5300 : Type'} (a0 : _5296) (a1 : prod _5300 _5299) : a1 = (term44 _5296 _5299 _5300 a0 a1).
Proof. exact (@lem51159 _5296 (prod _5300 _5299) a0 a1). Qed.
Lemma lem52146 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (@pair _5300 _5299 y z) = (term45 _5296 _5299 _5300 x y z).
Proof. exact (@lem52145 _5296 _5299 _5300 x (@pair _5300 _5299 y z)). Qed.
Lemma lem52147 {_5296 : Type'} (x : _5296) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem52148 {_5296 : Type'} : (term46 _5296) = (term46 _5296).
Proof. exact (eq_refl (term46 _5296)). Qed.
Lemma lem52149 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term47 _5296 x) = (term48 _5296 _5299 _5300 x y z).
Proof. exact (MK_COMB (@lem52148 _5296) (@lem52144 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52150 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term48 _5296 _5299 _5300 x y z) = (term43 _5296 _5299 _5300 x y z).
Proof. exact (eq_refl (term48 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52151 {_5296 : Type'} (x : _5296) : (term49 _5296 x) = (term49 _5296 x).
Proof. exact (eq_refl (term49 _5296 x)). Qed.
Lemma lem52152 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term47 _5296 x) = (term48 _5296 _5299 _5300 x y z)) = ((term47 _5296 x) = (term43 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52151 _5296 x) (@lem52150 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52153 {_5296 : Type'} (x : _5296) : (term47 _5296 x) = x.
Proof. exact (eq_refl (term47 _5296 x)). Qed.
Lemma lem52154 {_5296 : Type'} : (@eq _5296) = (@eq _5296).
Proof. exact (eq_refl (@eq _5296)). Qed.
Lemma lem52155 {_5296 : Type'} (x : _5296) : (term49 _5296 x) = (@eq _5296 x).
Proof. exact (MK_COMB (@lem52154 _5296) (@lem52153 _5296 x)). Qed.
Lemma lem52156 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term43 _5296 _5299 _5300 x y z) = (term43 _5296 _5299 _5300 x y z).
Proof. exact (eq_refl (term43 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52157 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term47 _5296 x) = (term43 _5296 _5299 _5300 x y z)) = (x = (term43 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52155 _5296 x) (@lem52156 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52158 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term47 _5296 x) = (term48 _5296 _5299 _5300 x y z)) = (x = (term43 _5296 _5299 _5300 x y z)).
Proof. exact (TRANS (@lem52152 _5296 _5299 _5300 x y z) (@lem52157 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52159 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : x = (term43 _5296 _5299 _5300 x y z).
Proof. exact (EQ_MP (@lem52158 _5296 _5299 _5300 x y z) (@lem52149 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52160 {_5296 : Type'} (x : _5296) : (@eq _5296 x) = (@eq _5296 x).
Proof. exact (eq_refl (@eq _5296 x)). Qed.
Lemma lem52161 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (x = x) = (x = (term43 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52160 _5296 x) (@lem52159 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52162 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : x = (term43 _5296 _5299 _5300 x y z).
Proof. exact (EQ_MP (@lem52161 _5296 _5299 _5300 x y z) (@lem52147 _5296 x)). Qed.
Lemma lem52163 {_5299 _5300 : Type'} (a0 : _5300) (a1 : _5299) : a0 = (term50 _5299 _5300 a0 a1).
Proof. exact (@lem51128 _5300 _5299 a0 a1). Qed.
Lemma lem52164 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : y = (term50 _5299 _5300 y z).
Proof. exact (@lem52163 _5299 _5300 y z). Qed.
Lemma lem52165 {_5299 _5300 : Type'} (a0 : _5300) (a1 : _5299) : a1 = (term51 _5299 _5300 a0 a1).
Proof. exact (@lem51159 _5300 _5299 a0 a1). Qed.
Lemma lem52166 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : z = (term51 _5299 _5300 y z).
Proof. exact (@lem52165 _5299 _5300 y z). Qed.
Lemma lem52167 {_5300 : Type'} (y : _5300) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem52168 {_5300 : Type'} : (term46 _5300) = (term46 _5300).
Proof. exact (eq_refl (term46 _5300)). Qed.
Lemma lem52169 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term47 _5300 y) = (term52 _5299 _5300 y z).
Proof. exact (MK_COMB (@lem52168 _5300) (@lem52164 _5299 _5300 y z)). Qed.
Lemma lem52170 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term52 _5299 _5300 y z) = (term50 _5299 _5300 y z).
Proof. exact (eq_refl (term52 _5299 _5300 y z)). Qed.
Lemma lem52171 {_5300 : Type'} (y : _5300) : (term49 _5300 y) = (term49 _5300 y).
Proof. exact (eq_refl (term49 _5300 y)). Qed.
Lemma lem52172 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : ((term47 _5300 y) = (term52 _5299 _5300 y z)) = ((term47 _5300 y) = (term50 _5299 _5300 y z)).
Proof. exact (MK_COMB (@lem52171 _5300 y) (@lem52170 _5299 _5300 y z)). Qed.
Lemma lem52173 {_5300 : Type'} (y : _5300) : (term47 _5300 y) = y.
Proof. exact (eq_refl (term47 _5300 y)). Qed.
Lemma lem52174 {_5300 : Type'} : (@eq _5300) = (@eq _5300).
Proof. exact (eq_refl (@eq _5300)). Qed.
Lemma lem52175 {_5300 : Type'} (y : _5300) : (term49 _5300 y) = (@eq _5300 y).
Proof. exact (MK_COMB (@lem52174 _5300) (@lem52173 _5300 y)). Qed.
Lemma lem52176 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term50 _5299 _5300 y z) = (term50 _5299 _5300 y z).
Proof. exact (eq_refl (term50 _5299 _5300 y z)). Qed.
Lemma lem52177 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : ((term47 _5300 y) = (term50 _5299 _5300 y z)) = (y = (term50 _5299 _5300 y z)).
Proof. exact (MK_COMB (@lem52175 _5300 y) (@lem52176 _5299 _5300 y z)). Qed.
Lemma lem52178 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : ((term47 _5300 y) = (term52 _5299 _5300 y z)) = (y = (term50 _5299 _5300 y z)).
Proof. exact (TRANS (@lem52172 _5299 _5300 y z) (@lem52177 _5299 _5300 y z)). Qed.
Lemma lem52179 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : y = (term50 _5299 _5300 y z).
Proof. exact (EQ_MP (@lem52178 _5299 _5300 y z) (@lem52169 _5299 _5300 y z)). Qed.
Lemma lem52180 {_5300 : Type'} (y : _5300) : (@eq _5300 y) = (@eq _5300 y).
Proof. exact (eq_refl (@eq _5300 y)). Qed.
Lemma lem52181 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (y = y) = (y = (term50 _5299 _5300 y z)).
Proof. exact (MK_COMB (@lem52180 _5300 y) (@lem52179 _5299 _5300 y z)). Qed.
Lemma lem52182 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : y = (term50 _5299 _5300 y z).
Proof. exact (EQ_MP (@lem52181 _5299 _5300 y z) (@lem52167 _5300 y)). Qed.
Lemma lem52183 {_5299 : Type'} (z : _5299) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem52184 {_5299 : Type'} : (term46 _5299) = (term46 _5299).
Proof. exact (eq_refl (term46 _5299)). Qed.
Lemma lem52185 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term47 _5299 z) = (term53 _5299 _5300 y z).
Proof. exact (MK_COMB (@lem52184 _5299) (@lem52166 _5299 _5300 y z)). Qed.
Lemma lem52186 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term53 _5299 _5300 y z) = (term51 _5299 _5300 y z).
Proof. exact (eq_refl (term53 _5299 _5300 y z)). Qed.
Lemma lem52187 {_5299 : Type'} (z : _5299) : (term49 _5299 z) = (term49 _5299 z).
Proof. exact (eq_refl (term49 _5299 z)). Qed.
Lemma lem52188 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : ((term47 _5299 z) = (term53 _5299 _5300 y z)) = ((term47 _5299 z) = (term51 _5299 _5300 y z)).
Proof. exact (MK_COMB (@lem52187 _5299 z) (@lem52186 _5299 _5300 y z)). Qed.
Lemma lem52189 {_5299 : Type'} (z : _5299) : (term47 _5299 z) = z.
Proof. exact (eq_refl (term47 _5299 z)). Qed.
Lemma lem52190 {_5299 : Type'} : (@eq _5299) = (@eq _5299).
Proof. exact (eq_refl (@eq _5299)). Qed.
Lemma lem52191 {_5299 : Type'} (z : _5299) : (term49 _5299 z) = (@eq _5299 z).
Proof. exact (MK_COMB (@lem52190 _5299) (@lem52189 _5299 z)). Qed.
Lemma lem52192 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term51 _5299 _5300 y z) = (term51 _5299 _5300 y z).
Proof. exact (eq_refl (term51 _5299 _5300 y z)). Qed.
Lemma lem52193 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : ((term47 _5299 z) = (term51 _5299 _5300 y z)) = (z = (term51 _5299 _5300 y z)).
Proof. exact (MK_COMB (@lem52191 _5299 z) (@lem52192 _5299 _5300 y z)). Qed.
Lemma lem52194 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : ((term47 _5299 z) = (term53 _5299 _5300 y z)) = (z = (term51 _5299 _5300 y z)).
Proof. exact (TRANS (@lem52188 _5299 _5300 y z) (@lem52193 _5299 _5300 y z)). Qed.
Lemma lem52195 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : z = (term51 _5299 _5300 y z).
Proof. exact (EQ_MP (@lem52194 _5299 _5300 y z) (@lem52185 _5299 _5300 y z)). Qed.
Lemma lem52196 {_5299 : Type'} (z : _5299) : (@eq _5299 z) = (@eq _5299 z).
Proof. exact (eq_refl (@eq _5299 z)). Qed.
Lemma lem52197 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (z = z) = (z = (term51 _5299 _5300 y z)).
Proof. exact (MK_COMB (@lem52196 _5299 z) (@lem52195 _5299 _5300 y z)). Qed.
Lemma lem52198 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : z = (term51 _5299 _5300 y z).
Proof. exact (EQ_MP (@lem52197 _5299 _5300 y z) (@lem52183 _5299 z)). Qed.
Lemma lem52199 {_5299 _5300 : Type'} : (term54 _5299 _5300) = (term54 _5299 _5300).
Proof. exact (eq_refl (term54 _5299 _5300)). Qed.
Lemma lem52200 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term55 _5299 _5300 y z) = (term56 _5296 _5299 _5300 x y z).
Proof. exact (MK_COMB (@lem52199 _5299 _5300) (@lem52146 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52201 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term56 _5296 _5299 _5300 x y z) = (term57 _5296 _5299 _5300 x y z).
Proof. exact (eq_refl (term56 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52202 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term58 _5299 _5300 y z) = (term58 _5299 _5300 y z).
Proof. exact (eq_refl (term58 _5299 _5300 y z)). Qed.
Lemma lem52203 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term55 _5299 _5300 y z) = (term56 _5296 _5299 _5300 x y z)) = ((term55 _5299 _5300 y z) = (term57 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52202 _5299 _5300 y z) (@lem52201 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52204 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term55 _5299 _5300 y z) = (term50 _5299 _5300 y z).
Proof. exact (eq_refl (term55 _5299 _5300 y z)). Qed.
Lemma lem52205 {_5300 : Type'} : (@eq _5300) = (@eq _5300).
Proof. exact (eq_refl (@eq _5300)). Qed.
Lemma lem52206 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term58 _5299 _5300 y z) = (term59 _5299 _5300 y z).
Proof. exact (MK_COMB (@lem52205 _5300) (@lem52204 _5299 _5300 y z)). Qed.
Lemma lem52207 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term57 _5296 _5299 _5300 x y z) = (term57 _5296 _5299 _5300 x y z).
Proof. exact (eq_refl (term57 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52208 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term55 _5299 _5300 y z) = (term57 _5296 _5299 _5300 x y z)) = ((term50 _5299 _5300 y z) = (term57 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52206 _5299 _5300 y z) (@lem52207 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52209 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term55 _5299 _5300 y z) = (term56 _5296 _5299 _5300 x y z)) = ((term50 _5299 _5300 y z) = (term57 _5296 _5299 _5300 x y z)).
Proof. exact (TRANS (@lem52203 _5296 _5299 _5300 x y z) (@lem52208 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52210 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term50 _5299 _5300 y z) = (term57 _5296 _5299 _5300 x y z).
Proof. exact (EQ_MP (@lem52209 _5296 _5299 _5300 x y z) (@lem52200 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52211 {_5300 : Type'} (y : _5300) : (@eq _5300 y) = (@eq _5300 y).
Proof. exact (eq_refl (@eq _5300 y)). Qed.
Lemma lem52212 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (y = (term50 _5299 _5300 y z)) = (y = (term57 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52211 _5300 y) (@lem52210 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52213 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : y = (term57 _5296 _5299 _5300 x y z).
Proof. exact (EQ_MP (@lem52212 _5296 _5299 _5300 x y z) (@lem52182 _5299 _5300 y z)). Qed.
Lemma lem52214 {_5299 _5300 : Type'} : (term60 _5299 _5300) = (term60 _5299 _5300).
Proof. exact (eq_refl (term60 _5299 _5300)). Qed.
Lemma lem52215 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term61 _5299 _5300 y z) = (term62 _5296 _5299 _5300 x y z).
Proof. exact (MK_COMB (@lem52214 _5299 _5300) (@lem52146 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52216 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term62 _5296 _5299 _5300 x y z) = (term63 _5296 _5299 _5300 x y z).
Proof. exact (eq_refl (term62 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52217 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term64 _5299 _5300 y z) = (term64 _5299 _5300 y z).
Proof. exact (eq_refl (term64 _5299 _5300 y z)). Qed.
Lemma lem52218 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term61 _5299 _5300 y z) = (term62 _5296 _5299 _5300 x y z)) = ((term61 _5299 _5300 y z) = (term63 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52217 _5299 _5300 y z) (@lem52216 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52219 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term61 _5299 _5300 y z) = (term51 _5299 _5300 y z).
Proof. exact (eq_refl (term61 _5299 _5300 y z)). Qed.
Lemma lem52220 {_5299 : Type'} : (@eq _5299) = (@eq _5299).
Proof. exact (eq_refl (@eq _5299)). Qed.
Lemma lem52221 {_5299 _5300 : Type'} (y : _5300) (z : _5299) : (term64 _5299 _5300 y z) = (term65 _5299 _5300 y z).
Proof. exact (MK_COMB (@lem52220 _5299) (@lem52219 _5299 _5300 y z)). Qed.
Lemma lem52222 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term63 _5296 _5299 _5300 x y z) = (term63 _5296 _5299 _5300 x y z).
Proof. exact (eq_refl (term63 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52223 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term61 _5299 _5300 y z) = (term63 _5296 _5299 _5300 x y z)) = ((term51 _5299 _5300 y z) = (term63 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52221 _5299 _5300 y z) (@lem52222 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52224 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : ((term61 _5299 _5300 y z) = (term62 _5296 _5299 _5300 x y z)) = ((term51 _5299 _5300 y z) = (term63 _5296 _5299 _5300 x y z)).
Proof. exact (TRANS (@lem52218 _5296 _5299 _5300 x y z) (@lem52223 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52225 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (term51 _5299 _5300 y z) = (term63 _5296 _5299 _5300 x y z).
Proof. exact (EQ_MP (@lem52224 _5296 _5299 _5300 x y z) (@lem52215 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52226 {_5299 : Type'} (z : _5299) : (@eq _5299 z) = (@eq _5299 z).
Proof. exact (eq_refl (@eq _5299 z)). Qed.
Lemma lem52227 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : (z = (term51 _5299 _5300 y z)) = (z = (term63 _5296 _5299 _5300 x y z)).
Proof. exact (MK_COMB (@lem52226 _5299 z) (@lem52225 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52228 {_5296 _5299 _5300 : Type'} (x : _5296) (y : _5300) (z : _5299) : z = (term63 _5296 _5299 _5300 x y z).
Proof. exact (EQ_MP (@lem52227 _5296 _5299 _5300 x y z) (@lem52198 _5299 _5300 y z)). Qed.
Lemma lem52229 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term66 _5284 _5296 _5299 _5300 f) = (term66 _5284 _5296 _5299 _5300 f).
Proof. exact (eq_refl (term66 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52230 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term67 _5284 _5296 _5299 _5300 f x) = (term68 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (MK_COMB (@lem52229 _5284 _5296 _5299 _5300 f) (@lem52162 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52231 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term68 _5284 _5296 _5299 _5300 f x y z) = (term69 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term68 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52232 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : (term70 _5284 _5296 _5299 _5300 f x) = (term70 _5284 _5296 _5299 _5300 f x).
Proof. exact (eq_refl (term70 _5284 _5296 _5299 _5300 f x)). Qed.
Lemma lem52233 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term67 _5284 _5296 _5299 _5300 f x) = (term68 _5284 _5296 _5299 _5300 f x y z)) = ((term67 _5284 _5296 _5299 _5300 f x) = (term69 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (MK_COMB (@lem52232 _5284 _5296 _5299 _5300 f x) (@lem52231 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52234 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : (term67 _5284 _5296 _5299 _5300 f x) = (term71 _5284 _5296 _5299 _5300 f x).
Proof. exact (eq_refl (term67 _5284 _5296 _5299 _5300 f x)). Qed.
Lemma lem52235 {_5284 _5299 _5300 : Type'} : (@eq (_5300 -> _5299 -> _5284)) = (@eq (_5300 -> _5299 -> _5284)).
Proof. exact (eq_refl (@eq (_5300 -> _5299 -> _5284))). Qed.
Lemma lem52236 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : (term70 _5284 _5296 _5299 _5300 f x) = (term72 _5284 _5296 _5299 _5300 f x).
Proof. exact (MK_COMB (@lem52235 _5284 _5299 _5300) (@lem52234 _5284 _5296 _5299 _5300 f x)). Qed.
Lemma lem52237 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term69 _5284 _5296 _5299 _5300 f x y z) = (term69 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term69 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52238 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term67 _5284 _5296 _5299 _5300 f x) = (term69 _5284 _5296 _5299 _5300 f x y z)) = ((term71 _5284 _5296 _5299 _5300 f x) = (term69 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (MK_COMB (@lem52236 _5284 _5296 _5299 _5300 f x) (@lem52237 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52239 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term67 _5284 _5296 _5299 _5300 f x) = (term68 _5284 _5296 _5299 _5300 f x y z)) = ((term71 _5284 _5296 _5299 _5300 f x) = (term69 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (TRANS (@lem52233 _5284 _5296 _5299 _5300 f x y z) (@lem52238 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52240 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term71 _5284 _5296 _5299 _5300 f x) = (term69 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (EQ_MP (@lem52239 _5284 _5296 _5299 _5300 f x y z) (@lem52230 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52241 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term73 _5284 _5296 _5299 _5300 f x y) = (term74 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (MK_COMB (@lem52240 _5284 _5296 _5299 _5300 f x y z) (@lem52213 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52242 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term74 _5284 _5296 _5299 _5300 f x y z) = (term75 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term74 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52243 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : (term76 _5284 _5296 _5299 _5300 f x y) = (term76 _5284 _5296 _5299 _5300 f x y).
Proof. exact (eq_refl (term76 _5284 _5296 _5299 _5300 f x y)). Qed.
Lemma lem52244 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term73 _5284 _5296 _5299 _5300 f x y) = (term74 _5284 _5296 _5299 _5300 f x y z)) = ((term73 _5284 _5296 _5299 _5300 f x y) = (term75 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (MK_COMB (@lem52243 _5284 _5296 _5299 _5300 f x y) (@lem52242 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52245 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : (term73 _5284 _5296 _5299 _5300 f x y) = (term77 _5284 _5296 _5299 _5300 f x y).
Proof. exact (eq_refl (term73 _5284 _5296 _5299 _5300 f x y)). Qed.
Lemma lem52246 {_5284 _5299 : Type'} : (@eq (_5299 -> _5284)) = (@eq (_5299 -> _5284)).
Proof. exact (eq_refl (@eq (_5299 -> _5284))). Qed.
Lemma lem52247 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : (term76 _5284 _5296 _5299 _5300 f x y) = (term78 _5284 _5296 _5299 _5300 f x y).
Proof. exact (MK_COMB (@lem52246 _5284 _5299) (@lem52245 _5284 _5296 _5299 _5300 f x y)). Qed.
Lemma lem52248 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term75 _5284 _5296 _5299 _5300 f x y z) = (term75 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term75 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52249 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term73 _5284 _5296 _5299 _5300 f x y) = (term75 _5284 _5296 _5299 _5300 f x y z)) = ((term77 _5284 _5296 _5299 _5300 f x y) = (term75 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (MK_COMB (@lem52247 _5284 _5296 _5299 _5300 f x y) (@lem52248 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52250 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term73 _5284 _5296 _5299 _5300 f x y) = (term74 _5284 _5296 _5299 _5300 f x y z)) = ((term77 _5284 _5296 _5299 _5300 f x y) = (term75 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (TRANS (@lem52244 _5284 _5296 _5299 _5300 f x y z) (@lem52249 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52251 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term77 _5284 _5296 _5299 _5300 f x y) = (term75 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (EQ_MP (@lem52250 _5284 _5296 _5299 _5300 f x y z) (@lem52241 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52252 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term79 _5284 _5296 _5299 _5300 f x y z) = (term80 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (MK_COMB (@lem52251 _5284 _5296 _5299 _5300 f x y z) (@lem52228 _5296 _5299 _5300 x y z)). Qed.
Lemma lem52253 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term80 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term80 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52254 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term82 _5284 _5296 _5299 _5300 f x y z) = (term82 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term82 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52255 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term79 _5284 _5296 _5299 _5300 f x y z) = (term80 _5284 _5296 _5299 _5300 f x y z)) = ((term79 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (MK_COMB (@lem52254 _5284 _5296 _5299 _5300 f x y z) (@lem52253 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52256 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term79 _5284 _5296 _5299 _5300 f x y z) = (term34 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term79 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52257 {_5284 : Type'} : (@eq _5284) = (@eq _5284).
Proof. exact (eq_refl (@eq _5284)). Qed.
Lemma lem52258 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term82 _5284 _5296 _5299 _5300 f x y z) = (term83 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (MK_COMB (@lem52257 _5284) (@lem52256 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52259 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term81 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term81 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52260 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term79 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z)) = ((term34 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (MK_COMB (@lem52258 _5284 _5296 _5299 _5300 f x y z) (@lem52259 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52261 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term79 _5284 _5296 _5299 _5300 f x y z) = (term80 _5284 _5296 _5299 _5300 f x y z)) = ((term34 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (TRANS (@lem52255 _5284 _5296 _5299 _5300 f x y z) (@lem52260 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52262 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term34 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (EQ_MP (@lem52261 _5284 _5296 _5299 _5300 f x y z) (@lem52252 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52263 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term81 _5284 _5296 _5299 _5300 f x y z) = (term34 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (SYM (@lem52262 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52264 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term84 _5284 _5296 _5299 _5300 f x y z) = (term81 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term84 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52265 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term84 _5284 _5296 _5299 _5300 f x y z) = (term34 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (TRANS (@lem52264 _5284 _5296 _5299 _5300 f x y z) (@lem52263 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52266 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : term85 _5284 _5296 _5299 _5300 f x y.
Proof. exact (fun z : _5299 => @lem52265 _5284 _5296 _5299 _5300 f x y z). Qed.
Lemma lem52267 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : term86 _5284 _5296 _5299 _5300 f x.
Proof. exact (fun y : _5300 => @lem52266 _5284 _5296 _5299 _5300 f x y). Qed.
Lemma lem52268 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : term87 _5284 _5296 _5299 _5300 f.
Proof. exact (fun x : _5296 => @lem52267 _5284 _5296 _5299 _5300 f x). Qed.
Lemma lem52269 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : term88 _5284 _5296 _5299 _5300 f.
Proof. exact (ex_intro (term89 _5284 _5296 _5299 _5300 f) (term90 _5284 _5296 _5299 _5300 f) (@lem52268 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52271 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem52272 {_5284 : Type'} (a : _5284) (b : _5284) : (a = b) = (@GEQ _5284 a b).
Proof. exact (@lem52271 _5284 a b). Qed.
Lemma lem52273 {_5284 _5296 _5299 _5300 : Type'} (_1458 : type1219 _5284 _5296 _5299 _5300) (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : ((term34 _5284 _5296 _5299 _5300 _1458 x y z) = (term34 _5284 _5296 _5299 _5300 f x y z)) = (term91 _5284 _5296 _5299 _5300 _1458 f x y z).
Proof. exact (@lem52272 _5284 (term34 _5284 _5296 _5299 _5300 _1458 x y z) (term34 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52274 {_5284 _5296 _5299 _5300 : Type'} (_1458 : type1219 _5284 _5296 _5299 _5300) (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : (term92 _5284 _5296 _5299 _5300 _1458 f x y) = (term93 _5284 _5296 _5299 _5300 _1458 f x y).
Proof. exact (fun_ext (fun z : _5299 => @lem52273 _5284 _5296 _5299 _5300 _1458 f x y z)). Qed.
Lemma lem52275 {_5299 : Type'} : (@all _5299) = (@all _5299).
Proof. exact (eq_refl (@all _5299)). Qed.
Lemma lem52276 {_5284 _5296 _5299 _5300 : Type'} (_1458 : type1219 _5284 _5296 _5299 _5300) (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : (term94 _5284 _5296 _5299 _5300 _1458 f x y) = (term95 _5284 _5296 _5299 _5300 _1458 f x y).
Proof. exact (MK_COMB (@lem52275 _5299) (@lem52274 _5284 _5296 _5299 _5300 _1458 f x y)). Qed.
Lemma lem52277 {_5284 _5296 _5299 _5300 : Type'} (_1458 : type1219 _5284 _5296 _5299 _5300) (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : (term96 _5284 _5296 _5299 _5300 _1458 f x) = (term97 _5284 _5296 _5299 _5300 _1458 f x).
Proof. exact (fun_ext (fun y : _5300 => @lem52276 _5284 _5296 _5299 _5300 _1458 f x y)). Qed.
Lemma lem52278 {_5300 : Type'} : (@all _5300) = (@all _5300).
Proof. exact (eq_refl (@all _5300)). Qed.
Lemma lem52279 {_5284 _5296 _5299 _5300 : Type'} (_1458 : type1219 _5284 _5296 _5299 _5300) (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : (term98 _5284 _5296 _5299 _5300 _1458 f x) = (term99 _5284 _5296 _5299 _5300 _1458 f x).
Proof. exact (MK_COMB (@lem52278 _5300) (@lem52277 _5284 _5296 _5299 _5300 _1458 f x)). Qed.
Lemma lem52280 {_5284 _5296 _5299 _5300 : Type'} (_1458 : type1219 _5284 _5296 _5299 _5300) (f : type1219 _5284 _5296 _5299 _5300) : (term100 _5284 _5296 _5299 _5300 _1458 f) = (term101 _5284 _5296 _5299 _5300 _1458 f).
Proof. exact (fun_ext (fun x : _5296 => @lem52279 _5284 _5296 _5299 _5300 _1458 f x)). Qed.
Lemma lem52281 {_5296 : Type'} : (@all _5296) = (@all _5296).
Proof. exact (eq_refl (@all _5296)). Qed.
Lemma lem52282 {_5284 _5296 _5299 _5300 : Type'} (_1458 : type1219 _5284 _5296 _5299 _5300) (f : type1219 _5284 _5296 _5299 _5300) : (term102 _5284 _5296 _5299 _5300 _1458 f) = (term103 _5284 _5296 _5299 _5300 _1458 f).
Proof. exact (MK_COMB (@lem52281 _5296) (@lem52280 _5284 _5296 _5299 _5300 _1458 f)). Qed.
Lemma lem52283 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term89 _5284 _5296 _5299 _5300 f) = (term104 _5284 _5296 _5299 _5300 f).
Proof. exact (fun_ext (fun _1458 : type1219 _5284 _5296 _5299 _5300 => @lem52282 _5284 _5296 _5299 _5300 _1458 f)). Qed.
Lemma lem52284 {_5284 _5296 _5299 _5300 : Type'} : (@ex ((prod _5296 (prod _5300 _5299)) -> _5284)) = (@ex ((prod _5296 (prod _5300 _5299)) -> _5284)).
Proof. exact (eq_refl (@ex ((prod _5296 (prod _5300 _5299)) -> _5284))). Qed.
Lemma lem52285 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term88 _5284 _5296 _5299 _5300 f) = (term105 _5284 _5296 _5299 _5300 f).
Proof. exact (MK_COMB (@lem52284 _5284 _5296 _5299 _5300) (@lem52283 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52286 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : term105 _5284 _5296 _5299 _5300 f.
Proof. exact (EQ_MP (@lem52285 _5284 _5296 _5299 _5300 f) (@lem52269 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52288 {_5076 : Type'} (P : _5076 -> Prop) : term106 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem52289 {_5284 _5296 _5299 _5300 : Type'} (P : type328 _5284 _5296 _5299 _5300) : term107 _5284 _5296 _5299 _5300 P.
Proof. exact (@lem52288 (type1219 _5284 _5296 _5299 _5300) P). Qed.
Lemma lem52290 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : term108 _5284 _5296 _5299 _5300 f.
Proof. exact (@lem52289 _5284 _5296 _5299 _5300 (term104 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52291 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : term109 _5284 _5296 _5299 _5300 f.
Proof. exact (@lem52290 _5284 _5296 _5299 _5300 f (@lem52286 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52292 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term109 _5284 _5296 _5299 _5300 f) = (term110 _5284 _5296 _5299 _5300 f).
Proof. exact (eq_refl (term109 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52293 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : term110 _5284 _5296 _5299 _5300 f.
Proof. exact (EQ_MP (@lem52292 _5284 _5296 _5299 _5300 f) (@lem52291 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52294 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : term111 _5284 _5296 _5299 _5300 f x.
Proof. exact (@lem52293 _5284 _5296 _5299 _5300 f x). Qed.
Lemma lem52295 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : (term111 _5284 _5296 _5299 _5300 f x) = (term112 _5284 _5296 _5299 _5300 f x).
Proof. exact (eq_refl (term111 _5284 _5296 _5299 _5300 f x)). Qed.
Lemma lem52296 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) : term112 _5284 _5296 _5299 _5300 f x.
Proof. exact (EQ_MP (@lem52295 _5284 _5296 _5299 _5300 f x) (@lem52294 _5284 _5296 _5299 _5300 f x)). Qed.
Lemma lem52297 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : term113 _5284 _5296 _5299 _5300 f x y.
Proof. exact (@lem52296 _5284 _5296 _5299 _5300 f x y). Qed.
Lemma lem52298 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : (term113 _5284 _5296 _5299 _5300 f x y) = (term114 _5284 _5296 _5299 _5300 f x y).
Proof. exact (eq_refl (term113 _5284 _5296 _5299 _5300 f x y)). Qed.
Lemma lem52299 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) : term114 _5284 _5296 _5299 _5300 f x y.
Proof. exact (EQ_MP (@lem52298 _5284 _5296 _5299 _5300 f x y) (@lem52297 _5284 _5296 _5299 _5300 f x y)). Qed.
Lemma lem52300 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : term115 _5284 _5296 _5299 _5300 f x y z.
Proof. exact (@lem52299 _5284 _5296 _5299 _5300 f x y z). Qed.
Lemma lem52301 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term115 _5284 _5296 _5299 _5300 f x y z) = (term116 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (eq_refl (term115 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52302 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : term116 _5284 _5296 _5299 _5300 f x y z.
Proof. exact (EQ_MP (@lem52301 _5284 _5296 _5299 _5300 f x y z) (@lem52300 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52304 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem52305 {_5284 : Type'} (a : _5284) (b : _5284) : (@GEQ _5284 a b) = (a = b).
Proof. exact (@lem52304 _5284 a b). Qed.
Lemma lem52306 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term116 _5284 _5296 _5299 _5300 f x y z) = ((term33 _5284 _5296 _5299 _5300 f x y z) = (term34 _5284 _5296 _5299 _5300 f x y z)).
Proof. exact (@lem52305 _5284 (term33 _5284 _5296 _5299 _5300 f x y z) (term34 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52307 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term33 _5284 _5296 _5299 _5300 f x y z) = (term34 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (EQ_MP (@lem52306 _5284 _5296 _5299 _5300 f x y z) (@lem52302 _5284 _5296 _5299 _5300 f x y z)). Qed.
Lemma lem52308 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (x : _5296) (y : _5300) (z : _5299) : (term33 _5284 _5296 _5299 _5300 f x y z) = (term34 _5284 _5296 _5299 _5300 f x y z).
Proof. exact (@lem52307 _5284 _5296 _5299 _5300 f x y z). Qed.
Lemma lem52309 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) (p2 : _5299) : (term33 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term34 _5284 _5296 _5299 _5300 f p1 p1' p2).
Proof. exact (@lem52308 _5284 _5296 _5299 _5300 f p1 p1' p2). Qed.
Lemma lem52310 {_5284 : Type'} : (@eq _5284) = (@eq _5284).
Proof. exact (eq_refl (@eq _5284)). Qed.
Lemma lem52311 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) (p2 : _5299) : (term117 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term83 _5284 _5296 _5299 _5300 f p1 p1' p2).
Proof. exact (MK_COMB (@lem52310 _5284) (@lem52309 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52312 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) (p2 : _5299) : (term34 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term34 _5284 _5296 _5299 _5300 f p1 p1' p2).
Proof. exact (eq_refl (term34 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52313 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) (p2 : _5299) : ((term33 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term34 _5284 _5296 _5299 _5300 f p1 p1' p2)) = ((term34 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term34 _5284 _5296 _5299 _5300 f p1 p1' p2)).
Proof. exact (MK_COMB (@lem52311 _5284 _5296 _5299 _5300 f p1 p1' p2) (@lem52312 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52315 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem52316 {_5284 : Type'} (x : _5284) : (x = x) = True.
Proof. exact (@lem52315 _5284 x). Qed.
Lemma lem52317 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) (p2 : _5299) : ((term34 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term34 _5284 _5296 _5299 _5300 f p1 p1' p2)) = True.
Proof. exact (@lem52316 _5284 (term34 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52318 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) (p2 : _5299) : ((term33 _5284 _5296 _5299 _5300 f p1 p1' p2) = (term34 _5284 _5296 _5299 _5300 f p1 p1' p2)) = True.
Proof. exact (TRANS (@lem52313 _5284 _5296 _5299 _5300 f p1 p1' p2) (@lem52317 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52319 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) : (term36 _5284 _5296 _5299 _5300 f p1 p1') = (term118 _5299).
Proof. exact (fun_ext (fun p2 : _5299 => @lem52318 _5284 _5296 _5299 _5300 f p1 p1' p2)). Qed.
Lemma lem52320 {_5299 : Type'} : (@all _5299) = (@all _5299).
Proof. exact (eq_refl (@all _5299)). Qed.
Lemma lem52321 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) : (term38 _5284 _5296 _5299 _5300 f p1 p1') = (term119 _5299).
Proof. exact (MK_COMB (@lem52320 _5299) (@lem52319 _5284 _5296 _5299 _5300 f p1 p1')). Qed.
Lemma lem52323 {A : Type'} (t : Prop) : (term120 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52324 {_5299 : Type'} (t : Prop) : (term120 _5299 t) = t.
Proof. exact (@lem52323 _5299 t). Qed.
Lemma lem52325 {_5299 : Type'} : (term119 _5299) = True.
Proof. exact (@lem52324 _5299 True). Qed.
Lemma lem52326 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) (p1' : _5300) : (term38 _5284 _5296 _5299 _5300 f p1 p1') = True.
Proof. exact (TRANS (@lem52321 _5284 _5296 _5299 _5300 f p1 p1') (@lem52325 _5299)). Qed.
Lemma lem52327 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term40 _5284 _5296 _5299 _5300 f p1) = (term118 _5300).
Proof. exact (fun_ext (fun p1' : _5300 => @lem52326 _5284 _5296 _5299 _5300 f p1 p1')). Qed.
Lemma lem52328 {_5300 : Type'} : (@all _5300) = (@all _5300).
Proof. exact (eq_refl (@all _5300)). Qed.
Lemma lem52329 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term41 _5284 _5296 _5299 _5300 f p1) = (term119 _5300).
Proof. exact (MK_COMB (@lem52328 _5300) (@lem52327 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52331 {A : Type'} (t : Prop) : (term120 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52332 {_5300 : Type'} (t : Prop) : (term120 _5300 t) = t.
Proof. exact (@lem52331 _5300 t). Qed.
Lemma lem52333 {_5300 : Type'} : (term119 _5300) = True.
Proof. exact (@lem52332 _5300 True). Qed.
Lemma lem52334 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term41 _5284 _5296 _5299 _5300 f p1) = True.
Proof. exact (TRANS (@lem52329 _5284 _5296 _5299 _5300 f p1) (@lem52333 _5300)). Qed.
Lemma lem52335 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) (p1 : _5296) : (term22 _5284 _5296 _5299 _5300 f p1) = True.
Proof. exact (TRANS (@lem52126 _5284 _5296 _5299 _5300 f p1) (@lem52334 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52336 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term24 _5284 _5296 _5299 _5300 f) = (term118 _5296).
Proof. exact (fun_ext (fun p1 : _5296 => @lem52335 _5284 _5296 _5299 _5300 f p1)). Qed.
Lemma lem52337 {_5296 : Type'} : (@all _5296) = (@all _5296).
Proof. exact (eq_refl (@all _5296)). Qed.
Lemma lem52338 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term25 _5284 _5296 _5299 _5300 f) = (term119 _5296).
Proof. exact (MK_COMB (@lem52337 _5296) (@lem52336 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52340 {A : Type'} (t : Prop) : (term120 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem52341 {_5296 : Type'} (t : Prop) : (term120 _5296 t) = t.
Proof. exact (@lem52340 _5296 t). Qed.
Lemma lem52342 {_5296 : Type'} : (term119 _5296) = True.
Proof. exact (@lem52341 _5296 True). Qed.
Lemma lem52343 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term25 _5284 _5296 _5299 _5300 f) = True.
Proof. exact (TRANS (@lem52338 _5284 _5296 _5299 _5300 f) (@lem52342 _5296)). Qed.
Lemma lem52344 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : ((term2 _5284 _5296 _5299 _5300 f) = f) = True.
Proof. exact (TRANS (@lem52103 _5284 _5296 _5299 _5300 f) (@lem52343 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52345 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : True = ((term2 _5284 _5296 _5299 _5300 f) = f).
Proof. exact (SYM (@lem52344 _5284 _5296 _5299 _5300 f)). Qed.
Lemma lem52346 {_5284 _5296 _5299 _5300 : Type'} (f : type1219 _5284 _5296 _5299 _5300) : (term2 _5284 _5296 _5299 _5300 f) = f.
Proof. exact (EQ_MP (@lem52345 _5284 _5296 _5299 _5300 f) (@lem0)). Qed.
