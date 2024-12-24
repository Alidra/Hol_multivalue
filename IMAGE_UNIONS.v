Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_UNIONS_term_abbrevs.
Require Import CONJ_ASSOC_spec.
Require Import EXTENSION_spec.
Require Import IN_IMAGE_spec.
Require Import IN_UNIONS_spec.
Require Import LEFT_AND_EXISTS_THM_spec.
Require Import SWAP_EXISTS_THM_spec.
Require Import UNWIND_THM2_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
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
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem3395066 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3395067 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (SYM (@lem3395066 t1 t2 t3 h1)). Qed.
Lemma lem3395068 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (h1). Qed.
Lemma lem3395069 (t1 : Prop) (t2 : Prop) (t3 : Prop) (h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3)) : (term0 t1 t2 t3) = (term1 t1 t2 t3).
Proof. exact (SYM (@lem3395068 t1 t2 t3 h1)). Qed.
Lemma lem3395070 (t1 : Prop) (t2 : Prop) (t3 : Prop) : ((term0 t1 t2 t3) = (term1 t1 t2 t3)) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (prop_ext (fun h1 : (term0 t1 t2 t3) = (term1 t1 t2 t3) => @lem3395067 t1 t2 t3 h1) (fun h1 : (term1 t1 t2 t3) = (term0 t1 t2 t3) => @lem3395069 t1 t2 t3 h1)). Qed.
Lemma lem3395071 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (fun_ext (fun t3 : Prop => @lem3395070 t1 t2 t3)). Qed.
Lemma lem3395072 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3395073 (t1 : Prop) (t2 : Prop) : (term4 t1 t2) = (term5 t1 t2).
Proof. exact (MK_COMB (@lem3395072) (@lem3395071 t1 t2)). Qed.
Lemma lem3395074 (t1 : Prop) : (term6 t1) = (term7 t1).
Proof. exact (fun_ext (fun t2 : Prop => @lem3395073 t1 t2)). Qed.
Lemma lem3395075 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3395076 (t1 : Prop) : (term8 t1) = (term9 t1).
Proof. exact (MK_COMB (@lem3395075) (@lem3395074 t1)). Qed.
Lemma lem3395077 : term10 = term11.
Proof. exact (fun_ext (fun t1 : Prop => @lem3395076 t1)). Qed.
Lemma lem3395078 : (@all Prop) = (@all Prop).
Proof. exact (eq_refl (@all Prop)). Qed.
Lemma lem3395079 : term12 = term13.
Proof. exact (MK_COMB (@lem3395078) (@lem3395077)). Qed.
Lemma lem3395080 : term13.
Proof. exact (EQ_MP (@lem3395079) (@lem512)). Qed.
Lemma lem3395081 {A B : Type'} (y : B) : term14 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3395082 {A B : Type'} (y : B) : (term14 A B y) = (term15 A B y).
Proof. exact (eq_refl (term14 A B y)). Qed.
Lemma lem3395083 {A B : Type'} (y : B) : term15 A B y.
Proof. exact (EQ_MP (@lem3395082 A B y) (@lem3395081 A B y)). Qed.
Lemma lem3395084 {A B : Type'} (y : B) (s : A -> Prop) : term16 A B y s.
Proof. exact (@lem3395083 A B y s). Qed.
Lemma lem3395085 {A B : Type'} (y : B) (s : A -> Prop) : (term16 A B y s) = (term17 A B y s).
Proof. exact (eq_refl (term16 A B y s)). Qed.
Lemma lem3395086 {A B : Type'} (y : B) (s : A -> Prop) : term17 A B y s.
Proof. exact (EQ_MP (@lem3395085 A B y s) (@lem3395084 A B y s)). Qed.
Lemma lem3395087 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term18 A B y s f.
Proof. exact (@lem3395086 A B y s f). Qed.
Lemma lem3395088 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term18 A B y s f) = ((term19 A B y f s) = (term20 A B y f s)).
Proof. exact (eq_refl (term18 A B y s f)). Qed.
Lemma lem3395090 {A : Type'} (P : A -> Prop) : term21 A P.
Proof. exact (@lem4564 A P). Qed.
Lemma lem3395091 {A : Type'} (P : A -> Prop) : (term21 A P) = (term22 A P).
Proof. exact (eq_refl (term21 A P)). Qed.
Lemma lem3395092 {A : Type'} (P : A -> Prop) : term22 A P.
Proof. exact (EQ_MP (@lem3395091 A P) (@lem3395090 A P)). Qed.
Lemma lem3395093 {A : Type'} (P : A -> Prop) (a : A) : term23 A P a.
Proof. exact (@lem3395092 A P a). Qed.
Lemma lem3395094 {A : Type'} (P : A -> Prop) (a : A) : (term23 A P a) = ((term24 A a P) = (P a)).
Proof. exact (eq_refl (term23 A P a)). Qed.
Lemma lem3395096 (t1 : Prop) : term25 t1.
Proof. exact (@lem3395080 t1). Qed.
Lemma lem3395097 (t1 : Prop) : (term25 t1) = (term9 t1).
Proof. exact (eq_refl (term25 t1)). Qed.
Lemma lem3395098 (t1 : Prop) : term9 t1.
Proof. exact (EQ_MP (@lem3395097 t1) (@lem3395096 t1)). Qed.
Lemma lem3395099 (t1 : Prop) (t2 : Prop) : term26 t1 t2.
Proof. exact (@lem3395098 t1 t2). Qed.
Lemma lem3395100 (t1 : Prop) (t2 : Prop) : (term26 t1 t2) = (term5 t1 t2).
Proof. exact (eq_refl (term26 t1 t2)). Qed.
Lemma lem3395101 (t1 : Prop) (t2 : Prop) : term5 t1 t2.
Proof. exact (EQ_MP (@lem3395100 t1 t2) (@lem3395099 t1 t2)). Qed.
Lemma lem3395102 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term27 t1 t2 t3.
Proof. exact (@lem3395101 t1 t2 t3). Qed.
Lemma lem3395103 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term27 t1 t2 t3) = ((term1 t1 t2 t3) = (term0 t1 t2 t3)).
Proof. exact (eq_refl (term27 t1 t2 t3)). Qed.
Lemma lem3395105 {A B : Type'} (P : type1413 A B) : term28 A B P.
Proof. exact (@lem4848 A B P). Qed.
Lemma lem3395106 {A B : Type'} (P : type1413 A B) : (term28 A B P) = ((term29 A B P) = (term30 A B P)).
Proof. exact (eq_refl (term28 A B P)). Qed.
Lemma lem3395108 {A : Type'} (P : A -> Prop) : term31 A P.
Proof. exact (@lem5881 A P). Qed.
Lemma lem3395109 {A : Type'} (P : A -> Prop) : (term31 A P) = (term32 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem3395110 {A : Type'} (P : A -> Prop) : term32 A P.
Proof. exact (EQ_MP (@lem3395109 A P) (@lem3395108 A P)). Qed.
Lemma lem3395111 {A : Type'} (P : A -> Prop) (Q : Prop) : term33 A P Q.
Proof. exact (@lem3395110 A P Q). Qed.
Lemma lem3395112 {A : Type'} (P : A -> Prop) (Q : Prop) : (term33 A P Q) = ((term34 A P Q) = (term35 A P Q)).
Proof. exact (eq_refl (term33 A P Q)). Qed.
Lemma lem3395114 {A B : Type'} (y : B) : term14 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem3395115 {A B : Type'} (y : B) : (term14 A B y) = (term15 A B y).
Proof. exact (eq_refl (term14 A B y)). Qed.
Lemma lem3395116 {A B : Type'} (y : B) : term15 A B y.
Proof. exact (EQ_MP (@lem3395115 A B y) (@lem3395114 A B y)). Qed.
Lemma lem3395117 {A B : Type'} (y : B) (s : A -> Prop) : term16 A B y s.
Proof. exact (@lem3395116 A B y s). Qed.
Lemma lem3395118 {A B : Type'} (y : B) (s : A -> Prop) : (term16 A B y s) = (term17 A B y s).
Proof. exact (eq_refl (term16 A B y s)). Qed.
Lemma lem3395119 {A B : Type'} (y : B) (s : A -> Prop) : term17 A B y s.
Proof. exact (EQ_MP (@lem3395118 A B y s) (@lem3395117 A B y s)). Qed.
Lemma lem3395120 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term18 A B y s f.
Proof. exact (@lem3395119 A B y s f). Qed.
Lemma lem3395121 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term18 A B y s f) = ((term19 A B y f s) = (term20 A B y f s)).
Proof. exact (eq_refl (term18 A B y s f)). Qed.
Lemma lem3395123 {A : Type'} (s : type686 A) : term36 A s.
Proof. exact (@lem3205091 A s). Qed.
Lemma lem3395124 {A : Type'} (s : type686 A) : (term36 A s) = (term37 A s).
Proof. exact (eq_refl (term36 A s)). Qed.
Lemma lem3395125 {A : Type'} (s : type686 A) : term37 A s.
Proof. exact (EQ_MP (@lem3395124 A s) (@lem3395123 A s)). Qed.
Lemma lem3395126 {A : Type'} (s : type686 A) (x : A) : term38 A s x.
Proof. exact (@lem3395125 A s x). Qed.
Lemma lem3395127 {A : Type'} (s : type686 A) (x : A) : (term38 A s x) = ((term39 A x s) = (term40 A s x)).
Proof. exact (eq_refl (term38 A s x)). Qed.
Lemma lem3395129 {A : Type'} (s : A -> Prop) : term41 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem3395130 {A : Type'} (s : A -> Prop) : (term41 A s) = (term42 A s).
Proof. exact (eq_refl (term41 A s)). Qed.
Lemma lem3395131 {A : Type'} (s : A -> Prop) : term42 A s.
Proof. exact (EQ_MP (@lem3395130 A s) (@lem3395129 A s)). Qed.
Lemma lem3395132 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term43 A s t.
Proof. exact (@lem3395131 A s t). Qed.
Lemma lem3395133 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = ((s = t) = (term44 A s t)).
Proof. exact (eq_refl (term43 A s t)). Qed.
Lemma lem3395146 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term44 A s t).
Proof. exact (EQ_MP (@lem3395133 A s t) (@lem3395132 A s t)). Qed.
Lemma lem3395147 {_88202 : Type'} (s : _88202 -> Prop) (t : _88202 -> Prop) : (s = t) = (term44 _88202 s t).
Proof. exact (@lem3395146 _88202 s t). Qed.
Lemma lem3395148 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) : ((term45 _88193 _88202 f s) = (term46 _88193 _88202 f s)) = (term47 _88193 _88202 f s).
Proof. exact (@lem3395147 _88202 (term45 _88193 _88202 f s) (term46 _88193 _88202 f s)). Qed.
Lemma lem3395149 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term48 _88193 _88202 f) = (term49 _88193 _88202 f).
Proof. exact (fun_ext (fun s : type686 _88193 => @lem3395148 _88193 _88202 f s)). Qed.
Lemma lem3395150 {_88193 : Type'} : (@all ((_88193 -> Prop) -> Prop)) = (@all ((_88193 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_88193 -> Prop) -> Prop))). Qed.
Lemma lem3395151 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term50 _88193 _88202 f) = (term51 _88193 _88202 f).
Proof. exact (MK_COMB (@lem3395150 _88193) (@lem3395149 _88193 _88202 f)). Qed.
Lemma lem3395152 {_88193 _88202 : Type'} : (term52 _88193 _88202) = (term53 _88193 _88202).
Proof. exact (fun_ext (fun f : _88193 -> _88202 => @lem3395151 _88193 _88202 f)). Qed.
Lemma lem3395153 {_88193 _88202 : Type'} : (@all (_88193 -> _88202)) = (@all (_88193 -> _88202)).
Proof. exact (eq_refl (@all (_88193 -> _88202))). Qed.
Lemma lem3395154 {_88193 _88202 : Type'} : (term54 _88193 _88202) = (term55 _88193 _88202).
Proof. exact (MK_COMB (@lem3395153 _88193 _88202) (@lem3395152 _88193 _88202)). Qed.
Lemma lem3395155 {_88193 _88202 : Type'} : (term55 _88193 _88202) = (term54 _88193 _88202).
Proof. exact (SYM (@lem3395154 _88193 _88202)). Qed.
Lemma lem3395171 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term19 A B y f s) = (term20 A B y f s).
Proof. exact (EQ_MP (@lem3395121 A B y f s) (@lem3395120 A B y s f)). Qed.
Lemma lem3395172 {_88193 _88202 : Type'} (y : _88202) (f : _88193 -> _88202) (s : _88193 -> Prop) : (term19 _88193 _88202 y f s) = (term20 _88193 _88202 y f s).
Proof. exact (@lem3395171 _88193 _88202 y f s). Qed.
Lemma lem3395173 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term56 _88193 _88202 x f s) = (term57 _88193 _88202 x f s).
Proof. exact (@lem3395172 _88193 _88202 x f (@UNIONS _88193 s)). Qed.
Lemma lem3395183 {A : Type'} (s : type686 A) (x : A) : (term39 A x s) = (term40 A s x).
Proof. exact (EQ_MP (@lem3395127 A s x) (@lem3395126 A s x)). Qed.
Lemma lem3395184 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term39 _88193 x s) = (term40 _88193 s x).
Proof. exact (@lem3395183 _88193 s x). Qed.
Lemma lem3395191 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term58 _88193 _88202 x f x') = (term58 _88193 _88202 x f x').
Proof. exact (eq_refl (term58 _88193 _88202 x f x')). Qed.
Lemma lem3395192 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term59 _88193 _88202 x f x' s) = (term60 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3395191 _88193 _88202 x f x') (@lem3395184 _88193 s x')). Qed.
Lemma lem3395195 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term61 _88193 _88202 x f s) = (term62 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3395192 _88193 _88202 x f s x')). Qed.
Lemma lem3395196 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3395197 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term57 _88193 _88202 x f s) = (term63 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395196 _88193) (@lem3395195 _88193 _88202 x f s)). Qed.
Lemma lem3395202 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term56 _88193 _88202 x f s) = (term63 _88193 _88202 x f s).
Proof. exact (TRANS (@lem3395173 _88193 _88202 x f s) (@lem3395197 _88193 _88202 x f s)). Qed.
Lemma lem3395203 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3395204 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term64 _88193 _88202 x f s) = (term65 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395203) (@lem3395202 _88193 _88202 x f s)). Qed.
Lemma lem3395206 {A : Type'} (s : type686 A) (x : A) : (term39 A x s) = (term40 A s x).
Proof. exact (EQ_MP (@lem3395127 A s x) (@lem3395126 A s x)). Qed.
Lemma lem3395207 {_88202 : Type'} (s : type686 _88202) (x : _88202) : (term39 _88202 x s) = (term40 _88202 s x).
Proof. exact (@lem3395206 _88202 s x). Qed.
Lemma lem3395208 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term66 _88193 _88202 x f s) = (term67 _88193 _88202 f s x).
Proof. exact (@lem3395207 _88202 (term68 _88193 _88202 f s) x). Qed.
Lemma lem3395216 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term19 A B y f s) = (term20 A B y f s).
Proof. exact (EQ_MP (@lem3395121 A B y f s) (@lem3395120 A B y s f)). Qed.
Lemma lem3395217 {_88193 _88202 : Type'} (y : _88202 -> Prop) (f : type678 _88193 _88202) (s : type686 _88193) : (term69 _88193 _88202 y f s) = (term70 _88193 _88202 y f s).
Proof. exact (@lem3395216 (_88193 -> Prop) (_88202 -> Prop) y f s). Qed.
Lemma lem3395218 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (s : type686 _88193) : (term71 _88193 _88202 t f s) = (term72 _88193 _88202 t f s).
Proof. exact (@lem3395217 _88193 _88202 t (@IMAGE _88193 _88202 f) s). Qed.
Lemma lem3395227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3395228 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (s : type686 _88193) : (term73 _88193 _88202 t f s) = (term74 _88193 _88202 t f s).
Proof. exact (MK_COMB (@lem3395227) (@lem3395218 _88193 _88202 t f s)). Qed.
Lemma lem3395229 {_88202 : Type'} (x : _88202) (t : _88202 -> Prop) : (@IN _88202 x t) = (@IN _88202 x t).
Proof. exact (eq_refl (@IN _88202 x t)). Qed.
Lemma lem3395230 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term75 _88193 _88202 f s x t) = (term76 _88193 _88202 f s x t).
Proof. exact (MK_COMB (@lem3395228 _88193 _88202 t f s) (@lem3395229 _88202 x t)). Qed.
Lemma lem3395233 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term77 _88193 _88202 f s x) = (term78 _88193 _88202 f s x).
Proof. exact (fun_ext (fun t : _88202 -> Prop => @lem3395230 _88193 _88202 f s x t)). Qed.
Lemma lem3395234 {_88202 : Type'} : (@ex (_88202 -> Prop)) = (@ex (_88202 -> Prop)).
Proof. exact (eq_refl (@ex (_88202 -> Prop))). Qed.
Lemma lem3395235 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term67 _88193 _88202 f s x) = (term79 _88193 _88202 f s x).
Proof. exact (MK_COMB (@lem3395234 _88202) (@lem3395233 _88193 _88202 f s x)). Qed.
Lemma lem3395240 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term66 _88193 _88202 x f s) = (term79 _88193 _88202 f s x).
Proof. exact (TRANS (@lem3395208 _88193 _88202 f s x) (@lem3395235 _88193 _88202 f s x)). Qed.
Lemma lem3395241 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : ((term56 _88193 _88202 x f s) = (term66 _88193 _88202 x f s)) = ((term63 _88193 _88202 x f s) = (term79 _88193 _88202 f s x)).
Proof. exact (MK_COMB (@lem3395204 _88193 _88202 x f s) (@lem3395240 _88193 _88202 f s x)). Qed.
Lemma lem3395244 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) : (term80 _88193 _88202 f s) = (term81 _88193 _88202 f s).
Proof. exact (fun_ext (fun x : _88202 => @lem3395241 _88193 _88202 f s x)). Qed.
Lemma lem3395245 {_88202 : Type'} : (@all _88202) = (@all _88202).
Proof. exact (eq_refl (@all _88202)). Qed.
Lemma lem3395246 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) : (term47 _88193 _88202 f s) = (term82 _88193 _88202 f s).
Proof. exact (MK_COMB (@lem3395245 _88202) (@lem3395244 _88193 _88202 f s)). Qed.
Lemma lem3395251 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term49 _88193 _88202 f) = (term83 _88193 _88202 f).
Proof. exact (fun_ext (fun s : type686 _88193 => @lem3395246 _88193 _88202 f s)). Qed.
Lemma lem3395252 {_88193 : Type'} : (@all ((_88193 -> Prop) -> Prop)) = (@all ((_88193 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_88193 -> Prop) -> Prop))). Qed.
Lemma lem3395253 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term51 _88193 _88202 f) = (term84 _88193 _88202 f).
Proof. exact (MK_COMB (@lem3395252 _88193) (@lem3395251 _88193 _88202 f)). Qed.
Lemma lem3395258 {_88193 _88202 : Type'} : (term53 _88193 _88202) = (term85 _88193 _88202).
Proof. exact (fun_ext (fun f : _88193 -> _88202 => @lem3395253 _88193 _88202 f)). Qed.
Lemma lem3395259 {_88193 _88202 : Type'} : (@all (_88193 -> _88202)) = (@all (_88193 -> _88202)).
Proof. exact (eq_refl (@all (_88193 -> _88202))). Qed.
Lemma lem3395260 {_88193 _88202 : Type'} : (term55 _88193 _88202) = (term86 _88193 _88202).
Proof. exact (MK_COMB (@lem3395259 _88193 _88202) (@lem3395258 _88193 _88202)). Qed.
Lemma lem3395265 {_88193 _88202 : Type'} : (term86 _88193 _88202) = (term55 _88193 _88202).
Proof. exact (SYM (@lem3395260 _88193 _88202)). Qed.
Lemma lem3395299 {A : Type'} (P : A -> Prop) (Q : Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem3395112 A P Q) (@lem3395111 A P Q)). Qed.
Lemma lem3395300 {_88193 : Type'} (P : type686 _88193) (Q : Prop) : (term87 _88193 P Q) = (term88 _88193 P Q).
Proof. exact (@lem3395299 (_88193 -> Prop) P Q). Qed.
Lemma lem3395301 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term89 _88193 _88202 f s x t) = (term90 _88193 _88202 f s x t).
Proof. exact (@lem3395300 _88193 (term91 _88193 _88202 t f s) (@IN _88202 x t)). Qed.
Lemma lem3395302 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) : (term92 _88193 _88202 t f s x) = (term93 _88193 _88202 t f x s).
Proof. exact (eq_refl (term92 _88193 _88202 t f s x)). Qed.
Lemma lem3395303 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (s : type686 _88193) : (term94 _88193 _88202 t f s) = (term91 _88193 _88202 t f s).
Proof. exact (fun_ext (fun x : _88193 -> Prop => @lem3395302 _88193 _88202 t f x s)). Qed.
Lemma lem3395304 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395305 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (s : type686 _88193) : (term95 _88193 _88202 t f s) = (term72 _88193 _88202 t f s).
Proof. exact (MK_COMB (@lem3395304 _88193) (@lem3395303 _88193 _88202 t f s)). Qed.
Lemma lem3395306 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3395307 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (s : type686 _88193) : (term96 _88193 _88202 t f s) = (term74 _88193 _88202 t f s).
Proof. exact (MK_COMB (@lem3395306) (@lem3395305 _88193 _88202 t f s)). Qed.
Lemma lem3395308 {_88202 : Type'} (x : _88202) (t : _88202 -> Prop) : (@IN _88202 x t) = (@IN _88202 x t).
Proof. exact (eq_refl (@IN _88202 x t)). Qed.
Lemma lem3395309 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term89 _88193 _88202 f s x t) = (term76 _88193 _88202 f s x t).
Proof. exact (MK_COMB (@lem3395307 _88193 _88202 t f s) (@lem3395308 _88202 x t)). Qed.
Lemma lem3395310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3395311 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term97 _88193 _88202 f s x t) = (term98 _88193 _88202 f s x t).
Proof. exact (MK_COMB (@lem3395310) (@lem3395309 _88193 _88202 f s x t)). Qed.
Lemma lem3395312 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) : (term92 _88193 _88202 t f s x) = (term93 _88193 _88202 t f x s).
Proof. exact (eq_refl (term92 _88193 _88202 t f s x)). Qed.
Lemma lem3395313 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3395314 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) : (term99 _88193 _88202 t f s x) = (term100 _88193 _88202 t f x s).
Proof. exact (MK_COMB (@lem3395313) (@lem3395312 _88193 _88202 t f x s)). Qed.
Lemma lem3395315 {_88202 : Type'} (x : _88202) (t : _88202 -> Prop) : (@IN _88202 x t) = (@IN _88202 x t).
Proof. exact (eq_refl (@IN _88202 x t)). Qed.
Lemma lem3395316 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term101 _88193 _88202 f s x x' t) = (term102 _88193 _88202 f x s x' t).
Proof. exact (MK_COMB (@lem3395314 _88193 _88202 t f x s) (@lem3395315 _88202 x' t)). Qed.
Lemma lem3395317 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term103 _88193 _88202 f s x t) = (term104 _88193 _88202 f s x t).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3395316 _88193 _88202 f x' s x t)). Qed.
Lemma lem3395318 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395319 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term90 _88193 _88202 f s x t) = (term105 _88193 _88202 f s x t).
Proof. exact (MK_COMB (@lem3395318 _88193) (@lem3395317 _88193 _88202 f s x t)). Qed.
Lemma lem3395320 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : ((term89 _88193 _88202 f s x t) = (term90 _88193 _88202 f s x t)) = ((term76 _88193 _88202 f s x t) = (term105 _88193 _88202 f s x t)).
Proof. exact (MK_COMB (@lem3395311 _88193 _88202 f s x t) (@lem3395319 _88193 _88202 f s x t)). Qed.
Lemma lem3395321 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term76 _88193 _88202 f s x t) = (term105 _88193 _88202 f s x t).
Proof. exact (EQ_MP (@lem3395320 _88193 _88202 f s x t) (@lem3395301 _88193 _88202 f s x t)). Qed.
Lemma lem3395332 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term78 _88193 _88202 f s x) = (term106 _88193 _88202 f s x).
Proof. exact (fun_ext (fun t : _88202 -> Prop => @lem3395321 _88193 _88202 f s x t)). Qed.
Lemma lem3395333 {_88202 : Type'} : (@ex (_88202 -> Prop)) = (@ex (_88202 -> Prop)).
Proof. exact (eq_refl (@ex (_88202 -> Prop))). Qed.
Lemma lem3395334 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term79 _88193 _88202 f s x) = (term107 _88193 _88202 f s x).
Proof. exact (MK_COMB (@lem3395333 _88202) (@lem3395332 _88193 _88202 f s x)). Qed.
Lemma lem3395339 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term65 _88193 _88202 x f s) = (term65 _88193 _88202 x f s).
Proof. exact (eq_refl (term65 _88193 _88202 x f s)). Qed.
Lemma lem3395340 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : ((term63 _88193 _88202 x f s) = (term79 _88193 _88202 f s x)) = ((term63 _88193 _88202 x f s) = (term107 _88193 _88202 f s x)).
Proof. exact (MK_COMB (@lem3395339 _88193 _88202 x f s) (@lem3395334 _88193 _88202 f s x)). Qed.
Lemma lem3395343 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) : (term81 _88193 _88202 f s) = (term108 _88193 _88202 f s).
Proof. exact (fun_ext (fun x : _88202 => @lem3395340 _88193 _88202 f s x)). Qed.
Lemma lem3395344 {_88202 : Type'} : (@all _88202) = (@all _88202).
Proof. exact (eq_refl (@all _88202)). Qed.
Lemma lem3395345 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) : (term82 _88193 _88202 f s) = (term109 _88193 _88202 f s).
Proof. exact (MK_COMB (@lem3395344 _88202) (@lem3395343 _88193 _88202 f s)). Qed.
Lemma lem3395350 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term83 _88193 _88202 f) = (term110 _88193 _88202 f).
Proof. exact (fun_ext (fun s : type686 _88193 => @lem3395345 _88193 _88202 f s)). Qed.
Lemma lem3395351 {_88193 : Type'} : (@all ((_88193 -> Prop) -> Prop)) = (@all ((_88193 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_88193 -> Prop) -> Prop))). Qed.
Lemma lem3395352 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term84 _88193 _88202 f) = (term111 _88193 _88202 f).
Proof. exact (MK_COMB (@lem3395351 _88193) (@lem3395350 _88193 _88202 f)). Qed.
Lemma lem3395357 {_88193 _88202 : Type'} : (term85 _88193 _88202) = (term112 _88193 _88202).
Proof. exact (fun_ext (fun f : _88193 -> _88202 => @lem3395352 _88193 _88202 f)). Qed.
Lemma lem3395358 {_88193 _88202 : Type'} : (@all (_88193 -> _88202)) = (@all (_88193 -> _88202)).
Proof. exact (eq_refl (@all (_88193 -> _88202))). Qed.
Lemma lem3395359 {_88193 _88202 : Type'} : (term86 _88193 _88202) = (term113 _88193 _88202).
Proof. exact (MK_COMB (@lem3395358 _88193 _88202) (@lem3395357 _88193 _88202)). Qed.
Lemma lem3395364 {_88193 _88202 : Type'} : (term113 _88193 _88202) = (term86 _88193 _88202).
Proof. exact (SYM (@lem3395359 _88193 _88202)). Qed.
Lemma lem3395394 {A B : Type'} (P : type1413 A B) : (term29 A B P) = (term30 A B P).
Proof. exact (EQ_MP (@lem3395106 A B P) (@lem3395105 A B P)). Qed.
Lemma lem3395395 {_88193 _88202 : Type'} (P : type841 _88193 _88202) : (term114 _88193 _88202 P) = (term115 _88193 _88202 P).
Proof. exact (@lem3395394 (_88202 -> Prop) (_88193 -> Prop) P). Qed.
Lemma lem3395396 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term116 _88193 _88202 f s x) = (term117 _88193 _88202 f s x).
Proof. exact (@lem3395395 _88193 _88202 (term118 _88193 _88202 f s x)). Qed.
Lemma lem3395397 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term119 _88193 _88202 f s x t) = (term104 _88193 _88202 f s x t).
Proof. exact (eq_refl (term119 _88193 _88202 f s x t)). Qed.
Lemma lem3395398 {_88193 : Type'} (x : _88193 -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3395399 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) (x' : _88193 -> Prop) : (term120 _88193 _88202 f s x t x') = (term121 _88193 _88202 f s x t x').
Proof. exact (MK_COMB (@lem3395397 _88193 _88202 f s x t) (@lem3395398 _88193 x')). Qed.
Lemma lem3395400 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term121 _88193 _88202 f s x' t x) = (term102 _88193 _88202 f x s x' t).
Proof. exact (eq_refl (term121 _88193 _88202 f s x' t x)). Qed.
Lemma lem3395401 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term120 _88193 _88202 f s x' t x) = (term102 _88193 _88202 f x s x' t).
Proof. exact (TRANS (@lem3395399 _88193 _88202 f s x' t x) (@lem3395400 _88193 _88202 f x s x' t)). Qed.
Lemma lem3395402 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term122 _88193 _88202 f s x t) = (term104 _88193 _88202 f s x t).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3395401 _88193 _88202 f x' s x t)). Qed.
Lemma lem3395403 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395404 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term123 _88193 _88202 f s x t) = (term105 _88193 _88202 f s x t).
Proof. exact (MK_COMB (@lem3395403 _88193) (@lem3395402 _88193 _88202 f s x t)). Qed.
Lemma lem3395405 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term124 _88193 _88202 f s x) = (term106 _88193 _88202 f s x).
Proof. exact (fun_ext (fun t : _88202 -> Prop => @lem3395404 _88193 _88202 f s x t)). Qed.
Lemma lem3395406 {_88202 : Type'} : (@ex (_88202 -> Prop)) = (@ex (_88202 -> Prop)).
Proof. exact (eq_refl (@ex (_88202 -> Prop))). Qed.
Lemma lem3395407 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term116 _88193 _88202 f s x) = (term107 _88193 _88202 f s x).
Proof. exact (MK_COMB (@lem3395406 _88202) (@lem3395405 _88193 _88202 f s x)). Qed.
Lemma lem3395408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3395409 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term125 _88193 _88202 f s x) = (term126 _88193 _88202 f s x).
Proof. exact (MK_COMB (@lem3395408) (@lem3395407 _88193 _88202 f s x)). Qed.
Lemma lem3395410 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) : (term119 _88193 _88202 f s x t) = (term104 _88193 _88202 f s x t).
Proof. exact (eq_refl (term119 _88193 _88202 f s x t)). Qed.
Lemma lem3395411 {_88193 : Type'} (x : _88193 -> Prop) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3395412 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) (t : _88202 -> Prop) (x' : _88193 -> Prop) : (term120 _88193 _88202 f s x t x') = (term121 _88193 _88202 f s x t x').
Proof. exact (MK_COMB (@lem3395410 _88193 _88202 f s x t) (@lem3395411 _88193 x')). Qed.
Lemma lem3395413 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term121 _88193 _88202 f s x' t x) = (term102 _88193 _88202 f x s x' t).
Proof. exact (eq_refl (term121 _88193 _88202 f s x' t x)). Qed.
Lemma lem3395414 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term120 _88193 _88202 f s x' t x) = (term102 _88193 _88202 f x s x' t).
Proof. exact (TRANS (@lem3395412 _88193 _88202 f s x' t x) (@lem3395413 _88193 _88202 f x s x' t)). Qed.
Lemma lem3395415 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) : (term127 _88193 _88202 f s x' x) = (term128 _88193 _88202 f x s x').
Proof. exact (fun_ext (fun t : _88202 -> Prop => @lem3395414 _88193 _88202 f x s x' t)). Qed.
Lemma lem3395416 {_88202 : Type'} : (@ex (_88202 -> Prop)) = (@ex (_88202 -> Prop)).
Proof. exact (eq_refl (@ex (_88202 -> Prop))). Qed.
Lemma lem3395417 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) : (term129 _88193 _88202 f s x' x) = (term130 _88193 _88202 f x s x').
Proof. exact (MK_COMB (@lem3395416 _88202) (@lem3395415 _88193 _88202 f x s x')). Qed.
Lemma lem3395418 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term131 _88193 _88202 f s x) = (term132 _88193 _88202 f s x).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3395417 _88193 _88202 f x' s x)). Qed.
Lemma lem3395419 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395420 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term117 _88193 _88202 f s x) = (term133 _88193 _88202 f s x).
Proof. exact (MK_COMB (@lem3395419 _88193) (@lem3395418 _88193 _88202 f s x)). Qed.
Lemma lem3395421 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : ((term116 _88193 _88202 f s x) = (term117 _88193 _88202 f s x)) = ((term107 _88193 _88202 f s x) = (term133 _88193 _88202 f s x)).
Proof. exact (MK_COMB (@lem3395409 _88193 _88202 f s x) (@lem3395420 _88193 _88202 f s x)). Qed.
Lemma lem3395422 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : (term107 _88193 _88202 f s x) = (term133 _88193 _88202 f s x).
Proof. exact (EQ_MP (@lem3395421 _88193 _88202 f s x) (@lem3395396 _88193 _88202 f s x)). Qed.
Lemma lem3395423 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term65 _88193 _88202 x f s) = (term65 _88193 _88202 x f s).
Proof. exact (eq_refl (term65 _88193 _88202 x f s)). Qed.
Lemma lem3395424 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (x : _88202) : ((term63 _88193 _88202 x f s) = (term107 _88193 _88202 f s x)) = ((term63 _88193 _88202 x f s) = (term133 _88193 _88202 f s x)).
Proof. exact (MK_COMB (@lem3395423 _88193 _88202 x f s) (@lem3395422 _88193 _88202 f s x)). Qed.
Lemma lem3395425 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) : (term108 _88193 _88202 f s) = (term134 _88193 _88202 f s).
Proof. exact (fun_ext (fun x : _88202 => @lem3395424 _88193 _88202 f s x)). Qed.
Lemma lem3395426 {_88202 : Type'} : (@all _88202) = (@all _88202).
Proof. exact (eq_refl (@all _88202)). Qed.
Lemma lem3395427 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) : (term109 _88193 _88202 f s) = (term135 _88193 _88202 f s).
Proof. exact (MK_COMB (@lem3395426 _88202) (@lem3395425 _88193 _88202 f s)). Qed.
Lemma lem3395428 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term110 _88193 _88202 f) = (term136 _88193 _88202 f).
Proof. exact (fun_ext (fun s : type686 _88193 => @lem3395427 _88193 _88202 f s)). Qed.
Lemma lem3395429 {_88193 : Type'} : (@all ((_88193 -> Prop) -> Prop)) = (@all ((_88193 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_88193 -> Prop) -> Prop))). Qed.
Lemma lem3395430 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term111 _88193 _88202 f) = (term137 _88193 _88202 f).
Proof. exact (MK_COMB (@lem3395429 _88193) (@lem3395428 _88193 _88202 f)). Qed.
Lemma lem3395431 {_88193 _88202 : Type'} : (term112 _88193 _88202) = (term138 _88193 _88202).
Proof. exact (fun_ext (fun f : _88193 -> _88202 => @lem3395430 _88193 _88202 f)). Qed.
Lemma lem3395432 {_88193 _88202 : Type'} : (@all (_88193 -> _88202)) = (@all (_88193 -> _88202)).
Proof. exact (eq_refl (@all (_88193 -> _88202))). Qed.
Lemma lem3395433 {_88193 _88202 : Type'} : (term113 _88193 _88202) = (term139 _88193 _88202).
Proof. exact (MK_COMB (@lem3395432 _88193 _88202) (@lem3395431 _88193 _88202)). Qed.
Lemma lem3395434 {_88193 _88202 : Type'} : (term139 _88193 _88202) = (term113 _88193 _88202).
Proof. exact (SYM (@lem3395433 _88193 _88202)). Qed.
Lemma lem3395474 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term1 t1 t2 t3) = (term0 t1 t2 t3).
Proof. exact (EQ_MP (@lem3395103 t1 t2 t3) (@lem3395102 t1 t2 t3)). Qed.
Lemma lem3395475 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term102 _88193 _88202 f x s x' t) = (term140 _88193 _88202 f x s x' t).
Proof. exact (@lem3395474 (t = (@IMAGE _88193 _88202 f x)) (@IN (_88193 -> Prop) x s) (@IN _88202 x' t)). Qed.
Lemma lem3395482 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) : (term128 _88193 _88202 f x s x') = (term141 _88193 _88202 f x s x').
Proof. exact (fun_ext (fun t : _88202 -> Prop => @lem3395475 _88193 _88202 f x s x' t)). Qed.
Lemma lem3395483 {_88202 : Type'} : (@ex (_88202 -> Prop)) = (@ex (_88202 -> Prop)).
Proof. exact (eq_refl (@ex (_88202 -> Prop))). Qed.
Lemma lem3395484 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) : (term130 _88193 _88202 f x s x') = (term142 _88193 _88202 f x s x').
Proof. exact (MK_COMB (@lem3395483 _88202) (@lem3395482 _88193 _88202 f x s x')). Qed.
Lemma lem3395486 {A : Type'} (P : A -> Prop) (a : A) : (term24 A a P) = (P a).
Proof. exact (EQ_MP (@lem3395094 A P a) (@lem3395093 A P a)). Qed.
Lemma lem3395487 {_88202 : Type'} (P : type686 _88202) (a : _88202 -> Prop) : (term143 _88202 a P) = (P a).
Proof. exact (@lem3395486 (_88202 -> Prop) P a). Qed.
Lemma lem3395488 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term144 _88193 _88202 f x' s x) = (term145 _88193 _88202 s x f x').
Proof. exact (@lem3395487 _88202 (term146 _88193 _88202 x' s x) (@IMAGE _88193 _88202 f x')). Qed.
Lemma lem3395489 {_88193 _88202 : Type'} (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term147 _88193 _88202 x s x' t) = (term148 _88193 _88202 x s x' t).
Proof. exact (eq_refl (term147 _88193 _88202 x s x' t)). Qed.
Lemma lem3395490 {_88193 _88202 : Type'} (t : _88202 -> Prop) (f : _88193 -> _88202) (x : _88193 -> Prop) : (term149 _88193 _88202 t f x) = (term149 _88193 _88202 t f x).
Proof. exact (eq_refl (term149 _88193 _88202 t f x)). Qed.
Lemma lem3395491 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (t : _88202 -> Prop) : (term150 _88193 _88202 f x s x' t) = (term140 _88193 _88202 f x s x' t).
Proof. exact (MK_COMB (@lem3395490 _88193 _88202 t f x) (@lem3395489 _88193 _88202 x s x' t)). Qed.
Lemma lem3395492 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) : (term151 _88193 _88202 f x s x') = (term141 _88193 _88202 f x s x').
Proof. exact (fun_ext (fun t : _88202 -> Prop => @lem3395491 _88193 _88202 f x s x' t)). Qed.
Lemma lem3395493 {_88202 : Type'} : (@ex (_88202 -> Prop)) = (@ex (_88202 -> Prop)).
Proof. exact (eq_refl (@ex (_88202 -> Prop))). Qed.
Lemma lem3395494 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) : (term144 _88193 _88202 f x s x') = (term142 _88193 _88202 f x s x').
Proof. exact (MK_COMB (@lem3395493 _88202) (@lem3395492 _88193 _88202 f x s x')). Qed.
Lemma lem3395495 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3395496 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x : _88193 -> Prop) (s : type686 _88193) (x' : _88202) : (term152 _88193 _88202 f x s x') = (term153 _88193 _88202 f x s x').
Proof. exact (MK_COMB (@lem3395495) (@lem3395494 _88193 _88202 f x s x')). Qed.
Lemma lem3395497 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term145 _88193 _88202 s x f x') = (term154 _88193 _88202 s x f x').
Proof. exact (eq_refl (term145 _88193 _88202 s x f x')). Qed.
Lemma lem3395498 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : ((term144 _88193 _88202 f x' s x) = (term145 _88193 _88202 s x f x')) = ((term142 _88193 _88202 f x' s x) = (term154 _88193 _88202 s x f x')).
Proof. exact (MK_COMB (@lem3395496 _88193 _88202 f x' s x) (@lem3395497 _88193 _88202 s x f x')). Qed.
Lemma lem3395499 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term142 _88193 _88202 f x' s x) = (term154 _88193 _88202 s x f x').
Proof. exact (EQ_MP (@lem3395498 _88193 _88202 s x f x') (@lem3395488 _88193 _88202 s x f x')). Qed.
Lemma lem3395503 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term19 A B y f s) = (term20 A B y f s).
Proof. exact (EQ_MP (@lem3395088 A B y f s) (@lem3395087 A B y s f)). Qed.
Lemma lem3395504 {_88193 _88202 : Type'} (y : _88202) (f : _88193 -> _88202) (s : _88193 -> Prop) : (term19 _88193 _88202 y f s) = (term20 _88193 _88202 y f s).
Proof. exact (@lem3395503 _88193 _88202 y f s). Qed.
Lemma lem3395505 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term19 _88193 _88202 x f x') = (term20 _88193 _88202 x f x').
Proof. exact (@lem3395504 _88193 _88202 x f x'). Qed.
Lemma lem3395516 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term155 _88193 x s) = (term155 _88193 x s).
Proof. exact (eq_refl (term155 _88193 x s)). Qed.
Lemma lem3395517 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term154 _88193 _88202 s x f x') = (term156 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3395516 _88193 x' s) (@lem3395505 _88193 _88202 x f x')). Qed.
Lemma lem3395520 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term142 _88193 _88202 f x' s x) = (term156 _88193 _88202 s x f x').
Proof. exact (TRANS (@lem3395499 _88193 _88202 s x f x') (@lem3395517 _88193 _88202 s x f x')). Qed.
Lemma lem3395521 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term130 _88193 _88202 f x' s x) = (term156 _88193 _88202 s x f x').
Proof. exact (TRANS (@lem3395484 _88193 _88202 f x' s x) (@lem3395520 _88193 _88202 s x f x')). Qed.
Lemma lem3395522 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term132 _88193 _88202 f s x) = (term157 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3395521 _88193 _88202 s x f x')). Qed.
Lemma lem3395523 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395524 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term133 _88193 _88202 f s x) = (term158 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3395523 _88193) (@lem3395522 _88193 _88202 s x f)). Qed.
Lemma lem3395529 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term65 _88193 _88202 x f s) = (term65 _88193 _88202 x f s).
Proof. exact (eq_refl (term65 _88193 _88202 x f s)). Qed.
Lemma lem3395530 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : ((term63 _88193 _88202 x f s) = (term133 _88193 _88202 f s x)) = ((term63 _88193 _88202 x f s) = (term158 _88193 _88202 s x f)).
Proof. exact (MK_COMB (@lem3395529 _88193 _88202 x f s) (@lem3395524 _88193 _88202 s x f)). Qed.
Lemma lem3395533 {_88193 _88202 : Type'} (s : type686 _88193) (f : _88193 -> _88202) : (term134 _88193 _88202 f s) = (term159 _88193 _88202 s f).
Proof. exact (fun_ext (fun x : _88202 => @lem3395530 _88193 _88202 s x f)). Qed.
Lemma lem3395534 {_88202 : Type'} : (@all _88202) = (@all _88202).
Proof. exact (eq_refl (@all _88202)). Qed.
Lemma lem3395535 {_88193 _88202 : Type'} (s : type686 _88193) (f : _88193 -> _88202) : (term135 _88193 _88202 f s) = (term160 _88193 _88202 s f).
Proof. exact (MK_COMB (@lem3395534 _88202) (@lem3395533 _88193 _88202 s f)). Qed.
Lemma lem3395540 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term136 _88193 _88202 f) = (term161 _88193 _88202 f).
Proof. exact (fun_ext (fun s : type686 _88193 => @lem3395535 _88193 _88202 s f)). Qed.
Lemma lem3395541 {_88193 : Type'} : (@all ((_88193 -> Prop) -> Prop)) = (@all ((_88193 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_88193 -> Prop) -> Prop))). Qed.
Lemma lem3395542 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term137 _88193 _88202 f) = (term162 _88193 _88202 f).
Proof. exact (MK_COMB (@lem3395541 _88193) (@lem3395540 _88193 _88202 f)). Qed.
Lemma lem3395547 {_88193 _88202 : Type'} : (term138 _88193 _88202) = (term163 _88193 _88202).
Proof. exact (fun_ext (fun f : _88193 -> _88202 => @lem3395542 _88193 _88202 f)). Qed.
Lemma lem3395548 {_88193 _88202 : Type'} : (@all (_88193 -> _88202)) = (@all (_88193 -> _88202)).
Proof. exact (eq_refl (@all (_88193 -> _88202))). Qed.
Lemma lem3395549 {_88193 _88202 : Type'} : (term139 _88193 _88202) = (term164 _88193 _88202).
Proof. exact (MK_COMB (@lem3395548 _88193 _88202) (@lem3395547 _88193 _88202)). Qed.
Lemma lem3395554 {_88193 _88202 : Type'} : (term164 _88193 _88202) = (term139 _88193 _88202).
Proof. exact (SYM (@lem3395549 _88193 _88202)). Qed.
Lemma lem3395556 (p : Prop) : p = (term165 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3395557 {_88193 _88202 : Type'} : (term164 _88193 _88202) = (term166 _88193 _88202).
Proof. exact (@lem3395556 (term164 _88193 _88202)). Qed.
Lemma lem3395558 {_88193 _88202 : Type'} : (term166 _88193 _88202) = (term164 _88193 _88202).
Proof. exact (SYM (@lem3395557 _88193 _88202)). Qed.
Lemma lem3395559 {_88193 _88202 : Type'} (h1 : term167 _88193 _88202) : term167 _88193 _88202.
Proof. exact (h1). Qed.
Lemma lem3395562 {_88193 _88202 : Type'} (h1 : term166 _88193 _88202) : term166 _88193 _88202.
Proof. exact (h1). Qed.
Lemma lem3395563 {_88193 _88202 : Type'} : term168 _88193 _88202.
Proof. exact (fun h0 : term166 _88193 _88202 => @lem3395562 _88193 _88202 h0). Qed.
Lemma lem3395564 {_88193 _88202 : Type'} (h1 : term168 _88193 _88202) : term168 _88193 _88202.
Proof. exact (h1). Qed.
Lemma lem3395565 {_88193 _88202 : Type'} (h1 : term166 _88193 _88202) : term166 _88193 _88202.
Proof. exact (h1). Qed.
Lemma lem3395566 {_88193 _88202 : Type'} (h1 : term166 _88193 _88202) (h2 : term168 _88193 _88202) : term166 _88193 _88202.
Proof. exact (@lem3395564 _88193 _88202 h2 (@lem3395565 _88193 _88202 h1)). Qed.
Lemma lem3395567 {_88193 _88202 : Type'} (h1 : term166 _88193 _88202) : term169 _88193 _88202.
Proof. exact (fun h0 : term168 _88193 _88202 => @lem3395566 _88193 _88202 h1 h0). Qed.
Lemma lem3395568 {_88193 _88202 : Type'} (h1 : term168 _88193 _88202) : term168 _88193 _88202.
Proof. exact (h1). Qed.
Lemma lem3395569 {_88193 _88202 : Type'} (h1 : term166 _88193 _88202) (h2 : term168 _88193 _88202) : term166 _88193 _88202.
Proof. exact (@lem3395567 _88193 _88202 h1 (@lem3395568 _88193 _88202 h2)). Qed.
Lemma lem3395570 {_88193 _88202 : Type'} (h1 : term168 _88193 _88202) : term168 _88193 _88202.
Proof. exact (fun h0 : term166 _88193 _88202 => @lem3395569 _88193 _88202 h0 h1). Qed.
Lemma lem3395571 {_88193 _88202 : Type'} : term170 _88193 _88202.
Proof. exact (fun h0 : term168 _88193 _88202 => @lem3395570 _88193 _88202 h0). Qed.
Lemma lem3395574 {_88193 _88202 : Type'} : term168 _88193 _88202.
Proof. exact (@lem3395571 _88193 _88202 (@lem3395563 _88193 _88202)). Qed.
Lemma lem3395575 {_88193 _88202 : Type'} : term168 _88193 _88202.
Proof. exact (@lem3395574 _88193 _88202). Qed.
Lemma lem3395577 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3395578 {_88193 _88202 : Type'} : (term166 _88193 _88202) = (term171 _88193 _88202).
Proof. exact (@lem3395577 (term167 _88193 _88202)). Qed.
Lemma lem3395580 (t : Prop) : (term172 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3395581 {_88193 _88202 : Type'} : (term171 _88193 _88202) = (term164 _88193 _88202).
Proof. exact (@lem3395580 (term164 _88193 _88202)). Qed.
Lemma lem3395798 {_88193 _88202 : Type'} : (term166 _88193 _88202) = (term164 _88193 _88202).
Proof. exact (TRANS (@lem3395578 _88193 _88202) (@lem3395581 _88193 _88202)). Qed.
Lemma lem3395803 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term173 _88193 _88202 x f x' x'') = (term173 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term173 _88193 _88202 x f x' x'')). Qed.
Lemma lem3395804 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term174 _88193 _88202 x f x') = (term174 _88193 _88202 x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3395803 _88193 _88202 x f x'' x')). Qed.
Lemma lem3395805 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3395806 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term20 _88193 _88202 x f x') = (term20 _88193 _88202 x f x').
Proof. exact (MK_COMB (@lem3395805 _88193) (@lem3395804 _88193 _88202 x f x')). Qed.
Lemma lem3395809 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term155 _88193 x s) = (term155 _88193 x s).
Proof. exact (eq_refl (term155 _88193 x s)). Qed.
Lemma lem3395810 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term156 _88193 _88202 s x f x') = (term156 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3395809 _88193 x' s) (@lem3395806 _88193 _88202 x f x')). Qed.
Lemma lem3395811 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term157 _88193 _88202 s x f) = (term157 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3395810 _88193 _88202 s x f x')). Qed.
Lemma lem3395812 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395813 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term158 _88193 _88202 s x f) = (term158 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3395812 _88193) (@lem3395811 _88193 _88202 s x f)). Qed.
Lemma lem3395818 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term175 _88193 s x t) = (term175 _88193 s x t).
Proof. exact (eq_refl (term175 _88193 s x t)). Qed.
Lemma lem3395819 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term176 _88193 s x) = (term176 _88193 s x).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3395818 _88193 s x t)). Qed.
Lemma lem3395820 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395821 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term40 _88193 s x) = (term40 _88193 s x).
Proof. exact (MK_COMB (@lem3395820 _88193) (@lem3395819 _88193 s x)). Qed.
Lemma lem3395824 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term58 _88193 _88202 x f x') = (term58 _88193 _88202 x f x').
Proof. exact (eq_refl (term58 _88193 _88202 x f x')). Qed.
Lemma lem3395825 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term60 _88193 _88202 x f s x') = (term60 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3395824 _88193 _88202 x f x') (@lem3395821 _88193 s x')). Qed.
Lemma lem3395826 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term62 _88193 _88202 x f s) = (term62 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3395825 _88193 _88202 x f s x')). Qed.
Lemma lem3395827 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3395828 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term63 _88193 _88202 x f s) = (term63 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395827 _88193) (@lem3395826 _88193 _88202 x f s)). Qed.
Lemma lem3395829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3395830 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term65 _88193 _88202 x f s) = (term65 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395829) (@lem3395828 _88193 _88202 x f s)). Qed.
Lemma lem3395831 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : ((term63 _88193 _88202 x f s) = (term158 _88193 _88202 s x f)) = ((term63 _88193 _88202 x f s) = (term158 _88193 _88202 s x f)).
Proof. exact (MK_COMB (@lem3395830 _88193 _88202 x f s) (@lem3395813 _88193 _88202 s x f)). Qed.
Lemma lem3395832 {_88193 _88202 : Type'} (s : type686 _88193) (f : _88193 -> _88202) : (term159 _88193 _88202 s f) = (term159 _88193 _88202 s f).
Proof. exact (fun_ext (fun x : _88202 => @lem3395831 _88193 _88202 s x f)). Qed.
Lemma lem3395833 {_88202 : Type'} : (@all _88202) = (@all _88202).
Proof. exact (eq_refl (@all _88202)). Qed.
Lemma lem3395834 {_88193 _88202 : Type'} (s : type686 _88193) (f : _88193 -> _88202) : (term160 _88193 _88202 s f) = (term160 _88193 _88202 s f).
Proof. exact (MK_COMB (@lem3395833 _88202) (@lem3395832 _88193 _88202 s f)). Qed.
Lemma lem3395835 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term161 _88193 _88202 f) = (term161 _88193 _88202 f).
Proof. exact (fun_ext (fun s : type686 _88193 => @lem3395834 _88193 _88202 s f)). Qed.
Lemma lem3395836 {_88193 : Type'} : (@all ((_88193 -> Prop) -> Prop)) = (@all ((_88193 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_88193 -> Prop) -> Prop))). Qed.
Lemma lem3395837 {_88193 _88202 : Type'} (f : _88193 -> _88202) : (term162 _88193 _88202 f) = (term162 _88193 _88202 f).
Proof. exact (MK_COMB (@lem3395836 _88193) (@lem3395835 _88193 _88202 f)). Qed.
Lemma lem3395838 {_88193 _88202 : Type'} : (term163 _88193 _88202) = (term163 _88193 _88202).
Proof. exact (fun_ext (fun f : _88193 -> _88202 => @lem3395837 _88193 _88202 f)). Qed.
Lemma lem3395839 {_88193 _88202 : Type'} : (@all (_88193 -> _88202)) = (@all (_88193 -> _88202)).
Proof. exact (eq_refl (@all (_88193 -> _88202))). Qed.
Lemma lem3395840 {_88193 _88202 : Type'} : (term164 _88193 _88202) = (term164 _88193 _88202).
Proof. exact (MK_COMB (@lem3395839 _88193 _88202) (@lem3395838 _88193 _88202)). Qed.
Lemma lem3395893 {_88193 _88202 : Type'} : (term166 _88193 _88202) = (term164 _88193 _88202).
Proof. exact (TRANS (@lem3395798 _88193 _88202) (@lem3395840 _88193 _88202)). Qed.
Lemma lem3395894 {_88193 _88202 : Type'} : (term164 _88193 _88202) = (term166 _88193 _88202).
Proof. exact (SYM (@lem3395893 _88193 _88202)). Qed.
Lemma lem3395896 (p : Prop) : p = (term165 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3395897 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : ((term63 _88193 _88202 x f s) = (term158 _88193 _88202 s x f)) = (term177 _88193 _88202 s x f).
Proof. exact (@lem3395896 ((term63 _88193 _88202 x f s) = (term158 _88193 _88202 s x f))). Qed.
Lemma lem3395898 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term177 _88193 _88202 s x f) = ((term63 _88193 _88202 x f s) = (term158 _88193 _88202 s x f)).
Proof. exact (SYM (@lem3395897 _88193 _88202 s x f)). Qed.
Lemma lem3395899 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term178 _88193 _88202 s x f) : term178 _88193 _88202 s x f.
Proof. exact (h1). Qed.
Lemma lem3395910 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term179 _88193 s x t) = (term180 _88193 s x t).
Proof. exact (@lem17045 (@IN (_88193 -> Prop) t s) (@IN _88193 x t)). Qed.
Lemma lem3395913 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term175 _88193 s x t) = (term175 _88193 s x t).
Proof. exact (eq_refl (term175 _88193 s x t)). Qed.
Lemma lem3395914 {_88193 : Type'} (P : type686 _88193) : (term181 _88193 P) = (term182 _88193 P).
Proof. exact (@lem18394 (_88193 -> Prop) P). Qed.
Lemma lem3395915 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term183 _88193 s x) = (term184 _88193 s x).
Proof. exact (@lem3395914 _88193 (term176 _88193 s x)). Qed.
Lemma lem3395916 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term185 _88193 s x t) = (term175 _88193 s x t).
Proof. exact (eq_refl (term185 _88193 s x t)). Qed.
Lemma lem3395917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3395918 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term186 _88193 s x t) = (term179 _88193 s x t).
Proof. exact (MK_COMB (@lem3395917) (@lem3395916 _88193 s x t)). Qed.
Lemma lem3395919 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term186 _88193 s x t) = (term180 _88193 s x t).
Proof. exact (TRANS (@lem3395918 _88193 s x t) (@lem3395910 _88193 s x t)). Qed.
Lemma lem3395920 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term187 _88193 s x) = (term188 _88193 s x).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3395919 _88193 s x t)). Qed.
Lemma lem3395921 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3395922 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term184 _88193 s x) = (term189 _88193 s x).
Proof. exact (MK_COMB (@lem3395921 _88193) (@lem3395920 _88193 s x)). Qed.
Lemma lem3395923 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term183 _88193 s x) = (term189 _88193 s x).
Proof. exact (TRANS (@lem3395915 _88193 s x) (@lem3395922 _88193 s x)). Qed.
Lemma lem3395924 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term176 _88193 s x) = (term176 _88193 s x).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3395913 _88193 s x t)). Qed.
Lemma lem3395925 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395926 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term40 _88193 s x) = (term40 _88193 s x).
Proof. exact (MK_COMB (@lem3395925 _88193) (@lem3395924 _88193 s x)). Qed.
Lemma lem3395928 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term190 _88193 _88202 x f x') = (term190 _88193 _88202 x f x').
Proof. exact (eq_refl (term190 _88193 _88202 x f x')). Qed.
Lemma lem3395929 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term191 _88193 _88202 x f s x') = (term192 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3395928 _88193 _88202 x f x') (@lem3395923 _88193 s x')). Qed.
Lemma lem3395930 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term193 _88193 _88202 x f s x') = (term191 _88193 _88202 x f s x').
Proof. exact (@lem17045 (x = (f x')) (term40 _88193 s x')). Qed.
Lemma lem3395931 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term193 _88193 _88202 x f s x') = (term192 _88193 _88202 x f s x').
Proof. exact (TRANS (@lem3395930 _88193 _88202 x f s x') (@lem3395929 _88193 _88202 x f s x')). Qed.
Lemma lem3395933 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term58 _88193 _88202 x f x') = (term58 _88193 _88202 x f x').
Proof. exact (eq_refl (term58 _88193 _88202 x f x')). Qed.
Lemma lem3395934 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term60 _88193 _88202 x f s x') = (term60 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3395933 _88193 _88202 x f x') (@lem3395926 _88193 s x')). Qed.
Lemma lem3395935 {_88193 : Type'} (P : _88193 -> Prop) : (term194 _88193 P) = (term195 _88193 P).
Proof. exact (@lem18394 _88193 P). Qed.
Lemma lem3395936 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term196 _88193 _88202 x f s) = (term197 _88193 _88202 x f s).
Proof. exact (@lem3395935 _88193 (term62 _88193 _88202 x f s)). Qed.
Lemma lem3395937 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term198 _88193 _88202 x f s x') = (term60 _88193 _88202 x f s x').
Proof. exact (eq_refl (term198 _88193 _88202 x f s x')). Qed.
Lemma lem3395938 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3395939 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term199 _88193 _88202 x f s x') = (term193 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3395938) (@lem3395937 _88193 _88202 x f s x')). Qed.
Lemma lem3395940 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term199 _88193 _88202 x f s x') = (term192 _88193 _88202 x f s x').
Proof. exact (TRANS (@lem3395939 _88193 _88202 x f s x') (@lem3395931 _88193 _88202 x f s x')). Qed.
Lemma lem3395941 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term200 _88193 _88202 x f s) = (term201 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3395940 _88193 _88202 x f s x')). Qed.
Lemma lem3395942 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3395943 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term197 _88193 _88202 x f s) = (term202 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395942 _88193) (@lem3395941 _88193 _88202 x f s)). Qed.
Lemma lem3395944 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term196 _88193 _88202 x f s) = (term202 _88193 _88202 x f s).
Proof. exact (TRANS (@lem3395936 _88193 _88202 x f s) (@lem3395943 _88193 _88202 x f s)). Qed.
Lemma lem3395945 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term62 _88193 _88202 x f s) = (term62 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3395934 _88193 _88202 x f s x')). Qed.
Lemma lem3395946 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3395947 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term63 _88193 _88202 x f s) = (term63 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395946 _88193) (@lem3395945 _88193 _88202 x f s)). Qed.
Lemma lem3395958 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term203 _88193 _88202 x f x' x'') = (term204 _88193 _88202 x f x' x'').
Proof. exact (@lem17045 (x = (f x')) (@IN _88193 x' x'')). Qed.
Lemma lem3395961 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term173 _88193 _88202 x f x' x'') = (term173 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term173 _88193 _88202 x f x' x'')). Qed.
Lemma lem3395962 {_88193 : Type'} (P : _88193 -> Prop) : (term194 _88193 P) = (term195 _88193 P).
Proof. exact (@lem18394 _88193 P). Qed.
Lemma lem3395963 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term205 _88193 _88202 x f x') = (term206 _88193 _88202 x f x').
Proof. exact (@lem3395962 _88193 (term174 _88193 _88202 x f x')). Qed.
Lemma lem3395964 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term207 _88193 _88202 x f x'' x') = (term173 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term207 _88193 _88202 x f x'' x')). Qed.
Lemma lem3395965 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3395966 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term208 _88193 _88202 x f x'' x') = (term203 _88193 _88202 x f x' x'').
Proof. exact (MK_COMB (@lem3395965) (@lem3395964 _88193 _88202 x f x' x'')). Qed.
Lemma lem3395967 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term208 _88193 _88202 x f x'' x') = (term204 _88193 _88202 x f x' x'').
Proof. exact (TRANS (@lem3395966 _88193 _88202 x f x' x'') (@lem3395958 _88193 _88202 x f x' x'')). Qed.
Lemma lem3395968 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term209 _88193 _88202 x f x') = (term210 _88193 _88202 x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3395967 _88193 _88202 x f x'' x')). Qed.
Lemma lem3395969 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3395970 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term206 _88193 _88202 x f x') = (term211 _88193 _88202 x f x').
Proof. exact (MK_COMB (@lem3395969 _88193) (@lem3395968 _88193 _88202 x f x')). Qed.
Lemma lem3395971 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term205 _88193 _88202 x f x') = (term211 _88193 _88202 x f x').
Proof. exact (TRANS (@lem3395963 _88193 _88202 x f x') (@lem3395970 _88193 _88202 x f x')). Qed.
Lemma lem3395972 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term174 _88193 _88202 x f x') = (term174 _88193 _88202 x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3395961 _88193 _88202 x f x'' x')). Qed.
Lemma lem3395973 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3395974 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term20 _88193 _88202 x f x') = (term20 _88193 _88202 x f x').
Proof. exact (MK_COMB (@lem3395973 _88193) (@lem3395972 _88193 _88202 x f x')). Qed.
Lemma lem3395976 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term212 _88193 x s) = (term212 _88193 x s).
Proof. exact (eq_refl (term212 _88193 x s)). Qed.
Lemma lem3395977 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term213 _88193 _88202 s x f x') = (term214 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3395976 _88193 x' s) (@lem3395971 _88193 _88202 x f x')). Qed.
Lemma lem3395978 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term215 _88193 _88202 s x f x') = (term213 _88193 _88202 s x f x').
Proof. exact (@lem17045 (@IN (_88193 -> Prop) x' s) (term20 _88193 _88202 x f x')). Qed.
Lemma lem3395979 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term215 _88193 _88202 s x f x') = (term214 _88193 _88202 s x f x').
Proof. exact (TRANS (@lem3395978 _88193 _88202 s x f x') (@lem3395977 _88193 _88202 s x f x')). Qed.
Lemma lem3395981 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term155 _88193 x s) = (term155 _88193 x s).
Proof. exact (eq_refl (term155 _88193 x s)). Qed.
Lemma lem3395982 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term156 _88193 _88202 s x f x') = (term156 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3395981 _88193 x' s) (@lem3395974 _88193 _88202 x f x')). Qed.
Lemma lem3395983 {_88193 : Type'} (P : type686 _88193) : (term181 _88193 P) = (term182 _88193 P).
Proof. exact (@lem18394 (_88193 -> Prop) P). Qed.
Lemma lem3395984 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term216 _88193 _88202 s x f) = (term217 _88193 _88202 s x f).
Proof. exact (@lem3395983 _88193 (term157 _88193 _88202 s x f)). Qed.
Lemma lem3395985 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term218 _88193 _88202 s x f x') = (term156 _88193 _88202 s x f x').
Proof. exact (eq_refl (term218 _88193 _88202 s x f x')). Qed.
Lemma lem3395986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3395987 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term219 _88193 _88202 s x f x') = (term215 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3395986) (@lem3395985 _88193 _88202 s x f x')). Qed.
Lemma lem3395988 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term219 _88193 _88202 s x f x') = (term214 _88193 _88202 s x f x').
Proof. exact (TRANS (@lem3395987 _88193 _88202 s x f x') (@lem3395979 _88193 _88202 s x f x')). Qed.
Lemma lem3395989 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term220 _88193 _88202 s x f) = (term221 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3395988 _88193 _88202 s x f x')). Qed.
Lemma lem3395990 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3395991 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term217 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3395990 _88193) (@lem3395989 _88193 _88202 s x f)). Qed.
Lemma lem3395992 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term216 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3395984 _88193 _88202 s x f) (@lem3395991 _88193 _88202 s x f)). Qed.
Lemma lem3395993 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term157 _88193 _88202 s x f) = (term157 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3395982 _88193 _88202 s x f x')). Qed.
Lemma lem3395994 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3395995 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term158 _88193 _88202 s x f) = (term158 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3395994 _88193) (@lem3395993 _88193 _88202 s x f)). Qed.
Lemma lem3395996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3395997 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term223 _88193 _88202 x f s) = (term224 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395996) (@lem3395944 _88193 _88202 x f s)). Qed.
Lemma lem3395998 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term225 _88193 _88202 s x f) = (term226 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3395997 _88193 _88202 x f s) (@lem3395995 _88193 _88202 s x f)). Qed.
Lemma lem3395999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3396000 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term227 _88193 _88202 x f s) = (term227 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3395999) (@lem3395947 _88193 _88202 x f s)). Qed.
Lemma lem3396001 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term228 _88193 _88202 s x f) = (term229 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396000 _88193 _88202 x f s) (@lem3395992 _88193 _88202 s x f)). Qed.
Lemma lem3396002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3396003 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term230 _88193 _88202 s x f) = (term231 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396002) (@lem3396001 _88193 _88202 s x f)). Qed.
Lemma lem3396004 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term232 _88193 _88202 s x f) = (term233 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396003 _88193 _88202 s x f) (@lem3395998 _88193 _88202 s x f)). Qed.
Lemma lem3396005 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term178 _88193 _88202 s x f) = (term232 _88193 _88202 s x f).
Proof. exact (@lem17646 (term63 _88193 _88202 x f s) (term158 _88193 _88202 s x f)). Qed.
Lemma lem3396006 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term178 _88193 _88202 s x f) = (term233 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396005 _88193 _88202 s x f) (@lem3396004 _88193 _88202 s x f)). Qed.
Lemma lem3396393 {A : Type'} (P : Prop) (Q : A -> Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3396394 {_88193 : Type'} (P : Prop) (Q : type686 _88193) : (term236 _88193 P Q) = (term237 _88193 P Q).
Proof. exact (@lem3396393 (_88193 -> Prop) P Q). Qed.
Lemma lem3396395 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term238 _88193 _88202 x f s x') = (term239 _88193 _88202 x f s x').
Proof. exact (@lem3396394 _88193 (x = (f x')) (term176 _88193 s x')). Qed.
Lemma lem3396396 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term185 _88193 s x t) = (term175 _88193 s x t).
Proof. exact (eq_refl (term185 _88193 s x t)). Qed.
Lemma lem3396397 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term240 _88193 s x) = (term176 _88193 s x).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396396 _88193 s x t)). Qed.
Lemma lem3396398 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396399 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term241 _88193 s x) = (term40 _88193 s x).
Proof. exact (MK_COMB (@lem3396398 _88193) (@lem3396397 _88193 s x)). Qed.
Lemma lem3396400 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term58 _88193 _88202 x f x') = (term58 _88193 _88202 x f x').
Proof. exact (eq_refl (term58 _88193 _88202 x f x')). Qed.
Lemma lem3396401 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term238 _88193 _88202 x f s x') = (term60 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396400 _88193 _88202 x f x') (@lem3396399 _88193 s x')). Qed.
Lemma lem3396402 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396403 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term242 _88193 _88202 x f s x') = (term243 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396402) (@lem3396401 _88193 _88202 x f s x')). Qed.
Lemma lem3396404 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term185 _88193 s x t) = (term175 _88193 s x t).
Proof. exact (eq_refl (term185 _88193 s x t)). Qed.
Lemma lem3396405 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term58 _88193 _88202 x f x') = (term58 _88193 _88202 x f x').
Proof. exact (eq_refl (term58 _88193 _88202 x f x')). Qed.
Lemma lem3396406 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) (t : _88193 -> Prop) : (term244 _88193 _88202 x f s x' t) = (term245 _88193 _88202 x f s x' t).
Proof. exact (MK_COMB (@lem3396405 _88193 _88202 x f x') (@lem3396404 _88193 s x' t)). Qed.
Lemma lem3396407 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term246 _88193 _88202 x f s x') = (term247 _88193 _88202 x f s x').
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396406 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396408 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396409 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term239 _88193 _88202 x f s x') = (term248 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396408 _88193) (@lem3396407 _88193 _88202 x f s x')). Qed.
Lemma lem3396410 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : ((term238 _88193 _88202 x f s x') = (term239 _88193 _88202 x f s x')) = ((term60 _88193 _88202 x f s x') = (term248 _88193 _88202 x f s x')).
Proof. exact (MK_COMB (@lem3396403 _88193 _88202 x f s x') (@lem3396409 _88193 _88202 x f s x')). Qed.
Lemma lem3396411 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term60 _88193 _88202 x f s x') = (term248 _88193 _88202 x f s x').
Proof. exact (EQ_MP (@lem3396410 _88193 _88202 x f s x') (@lem3396395 _88193 _88202 x f s x')). Qed.
Lemma lem3396412 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term62 _88193 _88202 x f s) = (term249 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396411 _88193 _88202 x f s x')). Qed.
Lemma lem3396413 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396414 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term63 _88193 _88202 x f s) = (term250 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396413 _88193) (@lem3396412 _88193 _88202 x f s)). Qed.
Lemma lem3396415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3396416 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term227 _88193 _88202 x f s) = (term251 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396415) (@lem3396414 _88193 _88202 x f s)). Qed.
Lemma lem3396417 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (eq_refl (term222 _88193 _88202 s x f)). Qed.
Lemma lem3396418 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term229 _88193 _88202 s x f) = (term252 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396416 _88193 _88202 x f s) (@lem3396417 _88193 _88202 s x f)). Qed.
Lemma lem3396420 {A : Type'} (P : A -> Prop) (Q : Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3396421 {_88193 : Type'} (P : _88193 -> Prop) (Q : Prop) : (term34 _88193 P Q) = (term35 _88193 P Q).
Proof. exact (@lem3396420 _88193 P Q). Qed.
Lemma lem3396422 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term253 _88193 _88202 s x f) = (term254 _88193 _88202 s x f).
Proof. exact (@lem3396421 _88193 (term249 _88193 _88202 x f s) (term222 _88193 _88202 s x f)). Qed.
Lemma lem3396423 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term255 _88193 _88202 x f s x') = (term248 _88193 _88202 x f s x').
Proof. exact (eq_refl (term255 _88193 _88202 x f s x')). Qed.
Lemma lem3396424 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term256 _88193 _88202 x f s) = (term249 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396423 _88193 _88202 x f s x')). Qed.
Lemma lem3396425 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396426 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term257 _88193 _88202 x f s) = (term250 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396425 _88193) (@lem3396424 _88193 _88202 x f s)). Qed.
Lemma lem3396427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3396428 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term258 _88193 _88202 x f s) = (term251 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396427) (@lem3396426 _88193 _88202 x f s)). Qed.
Lemma lem3396429 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (eq_refl (term222 _88193 _88202 s x f)). Qed.
Lemma lem3396430 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term253 _88193 _88202 s x f) = (term252 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396428 _88193 _88202 x f s) (@lem3396429 _88193 _88202 s x f)). Qed.
Lemma lem3396431 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396432 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term259 _88193 _88202 s x f) = (term260 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396431) (@lem3396430 _88193 _88202 s x f)). Qed.
Lemma lem3396433 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term255 _88193 _88202 x f s x') = (term248 _88193 _88202 x f s x').
Proof. exact (eq_refl (term255 _88193 _88202 x f s x')). Qed.
Lemma lem3396434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3396435 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term261 _88193 _88202 x f s x') = (term262 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396434) (@lem3396433 _88193 _88202 x f s x')). Qed.
Lemma lem3396436 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (eq_refl (term222 _88193 _88202 s x f)). Qed.
Lemma lem3396437 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term263 _88193 _88202 x s x' f) = (term264 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396435 _88193 _88202 x' f s x) (@lem3396436 _88193 _88202 s x' f)). Qed.
Lemma lem3396438 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term265 _88193 _88202 s x f) = (term266 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396437 _88193 _88202 x' s x f)). Qed.
Lemma lem3396439 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396440 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term254 _88193 _88202 s x f) = (term267 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396439 _88193) (@lem3396438 _88193 _88202 s x f)). Qed.
Lemma lem3396441 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : ((term253 _88193 _88202 s x f) = (term254 _88193 _88202 s x f)) = ((term252 _88193 _88202 s x f) = (term267 _88193 _88202 s x f)).
Proof. exact (MK_COMB (@lem3396432 _88193 _88202 s x f) (@lem3396440 _88193 _88202 s x f)). Qed.
Lemma lem3396442 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term252 _88193 _88202 s x f) = (term267 _88193 _88202 s x f).
Proof. exact (EQ_MP (@lem3396441 _88193 _88202 s x f) (@lem3396422 _88193 _88202 s x f)). Qed.
Lemma lem3396444 {A : Type'} (P : A -> Prop) (Q : Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3396445 {_88193 : Type'} (P : type686 _88193) (Q : Prop) : (term87 _88193 P Q) = (term88 _88193 P Q).
Proof. exact (@lem3396444 (_88193 -> Prop) P Q). Qed.
Lemma lem3396446 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term268 _88193 _88202 x s x' f) = (term269 _88193 _88202 x s x' f).
Proof. exact (@lem3396445 _88193 (term247 _88193 _88202 x' f s x) (term222 _88193 _88202 s x' f)). Qed.
Lemma lem3396447 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) (t : _88193 -> Prop) : (term270 _88193 _88202 x f s x' t) = (term245 _88193 _88202 x f s x' t).
Proof. exact (eq_refl (term270 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396448 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term271 _88193 _88202 x f s x') = (term247 _88193 _88202 x f s x').
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396447 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396449 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396450 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term272 _88193 _88202 x f s x') = (term248 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396449 _88193) (@lem3396448 _88193 _88202 x f s x')). Qed.
Lemma lem3396451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3396452 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term273 _88193 _88202 x f s x') = (term262 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396451) (@lem3396450 _88193 _88202 x f s x')). Qed.
Lemma lem3396453 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (eq_refl (term222 _88193 _88202 s x f)). Qed.
Lemma lem3396454 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term268 _88193 _88202 x s x' f) = (term264 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396452 _88193 _88202 x' f s x) (@lem3396453 _88193 _88202 s x' f)). Qed.
Lemma lem3396455 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396456 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term274 _88193 _88202 x s x' f) = (term275 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396455) (@lem3396454 _88193 _88202 x s x' f)). Qed.
Lemma lem3396457 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) (t : _88193 -> Prop) : (term270 _88193 _88202 x f s x' t) = (term245 _88193 _88202 x f s x' t).
Proof. exact (eq_refl (term270 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396458 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3396459 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) (t : _88193 -> Prop) : (term276 _88193 _88202 x f s x' t) = (term277 _88193 _88202 x f s x' t).
Proof. exact (MK_COMB (@lem3396458) (@lem3396457 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396460 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (eq_refl (term222 _88193 _88202 s x f)). Qed.
Lemma lem3396461 {_88193 _88202 : Type'} (x : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term278 _88193 _88202 x t s x' f) = (term279 _88193 _88202 x t s x' f).
Proof. exact (MK_COMB (@lem3396459 _88193 _88202 x' f s x t) (@lem3396460 _88193 _88202 s x' f)). Qed.
Lemma lem3396462 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term280 _88193 _88202 x s x' f) = (term281 _88193 _88202 x s x' f).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396461 _88193 _88202 x t s x' f)). Qed.
Lemma lem3396463 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396464 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term269 _88193 _88202 x s x' f) = (term282 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396463 _88193) (@lem3396462 _88193 _88202 x s x' f)). Qed.
Lemma lem3396465 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : ((term268 _88193 _88202 x s x' f) = (term269 _88193 _88202 x s x' f)) = ((term264 _88193 _88202 x s x' f) = (term282 _88193 _88202 x s x' f)).
Proof. exact (MK_COMB (@lem3396456 _88193 _88202 x s x' f) (@lem3396464 _88193 _88202 x s x' f)). Qed.
Lemma lem3396466 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term264 _88193 _88202 x s x' f) = (term282 _88193 _88202 x s x' f).
Proof. exact (EQ_MP (@lem3396465 _88193 _88202 x s x' f) (@lem3396446 _88193 _88202 x s x' f)). Qed.
Lemma lem3396467 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term266 _88193 _88202 s x f) = (term283 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396466 _88193 _88202 x' s x f)). Qed.
Lemma lem3396468 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396469 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term267 _88193 _88202 s x f) = (term284 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396468 _88193) (@lem3396467 _88193 _88202 s x f)). Qed.
Lemma lem3396470 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term252 _88193 _88202 s x f) = (term284 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396442 _88193 _88202 s x f) (@lem3396469 _88193 _88202 s x f)). Qed.
Lemma lem3396471 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term229 _88193 _88202 s x f) = (term284 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396418 _88193 _88202 s x f) (@lem3396470 _88193 _88202 s x f)). Qed.
Lemma lem3396472 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3396473 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term231 _88193 _88202 s x f) = (term285 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396472) (@lem3396471 _88193 _88202 s x f)). Qed.
Lemma lem3396475 {A : Type'} (P : Prop) (Q : A -> Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3396476 {_88193 : Type'} (P : Prop) (Q : _88193 -> Prop) : (term234 _88193 P Q) = (term235 _88193 P Q).
Proof. exact (@lem3396475 _88193 P Q). Qed.
Lemma lem3396477 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term286 _88193 _88202 s x f x') = (term287 _88193 _88202 s x f x').
Proof. exact (@lem3396476 _88193 (@IN (_88193 -> Prop) x' s) (term174 _88193 _88202 x f x')). Qed.
Lemma lem3396478 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term207 _88193 _88202 x f x'' x') = (term173 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term207 _88193 _88202 x f x'' x')). Qed.
Lemma lem3396479 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term288 _88193 _88202 x f x') = (term174 _88193 _88202 x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396478 _88193 _88202 x f x'' x')). Qed.
Lemma lem3396480 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396481 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term289 _88193 _88202 x f x') = (term20 _88193 _88202 x f x').
Proof. exact (MK_COMB (@lem3396480 _88193) (@lem3396479 _88193 _88202 x f x')). Qed.
Lemma lem3396482 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term155 _88193 x s) = (term155 _88193 x s).
Proof. exact (eq_refl (term155 _88193 x s)). Qed.
Lemma lem3396483 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term286 _88193 _88202 s x f x') = (term156 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396482 _88193 x' s) (@lem3396481 _88193 _88202 x f x')). Qed.
Lemma lem3396484 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396485 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term290 _88193 _88202 s x f x') = (term291 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396484) (@lem3396483 _88193 _88202 s x f x')). Qed.
Lemma lem3396486 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term207 _88193 _88202 x f x'' x') = (term173 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term207 _88193 _88202 x f x'' x')). Qed.
Lemma lem3396487 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term155 _88193 x s) = (term155 _88193 x s).
Proof. exact (eq_refl (term155 _88193 x s)). Qed.
Lemma lem3396488 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term292 _88193 _88202 s x f x'' x') = (term293 _88193 _88202 s x f x' x'').
Proof. exact (MK_COMB (@lem3396487 _88193 x'' s) (@lem3396486 _88193 _88202 x f x' x'')). Qed.
Lemma lem3396489 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term294 _88193 _88202 s x f x') = (term295 _88193 _88202 s x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396488 _88193 _88202 s x f x'' x')). Qed.
Lemma lem3396490 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396491 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term287 _88193 _88202 s x f x') = (term296 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396490 _88193) (@lem3396489 _88193 _88202 s x f x')). Qed.
Lemma lem3396492 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : ((term286 _88193 _88202 s x f x') = (term287 _88193 _88202 s x f x')) = ((term156 _88193 _88202 s x f x') = (term296 _88193 _88202 s x f x')).
Proof. exact (MK_COMB (@lem3396485 _88193 _88202 s x f x') (@lem3396491 _88193 _88202 s x f x')). Qed.
Lemma lem3396493 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term156 _88193 _88202 s x f x') = (term296 _88193 _88202 s x f x').
Proof. exact (EQ_MP (@lem3396492 _88193 _88202 s x f x') (@lem3396477 _88193 _88202 s x f x')). Qed.
Lemma lem3396494 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term157 _88193 _88202 s x f) = (term297 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3396493 _88193 _88202 s x f x')). Qed.
Lemma lem3396495 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396496 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term158 _88193 _88202 s x f) = (term298 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396495 _88193) (@lem3396494 _88193 _88202 s x f)). Qed.
Lemma lem3396497 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term224 _88193 _88202 x f s) = (term224 _88193 _88202 x f s).
Proof. exact (eq_refl (term224 _88193 _88202 x f s)). Qed.
Lemma lem3396498 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term226 _88193 _88202 s x f) = (term299 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396497 _88193 _88202 x f s) (@lem3396496 _88193 _88202 s x f)). Qed.
Lemma lem3396500 {A : Type'} (P : Prop) (Q : A -> Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3396501 {_88193 : Type'} (P : Prop) (Q : type686 _88193) : (term236 _88193 P Q) = (term237 _88193 P Q).
Proof. exact (@lem3396500 (_88193 -> Prop) P Q). Qed.
Lemma lem3396502 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term300 _88193 _88202 s x f) = (term301 _88193 _88202 s x f).
Proof. exact (@lem3396501 _88193 (term202 _88193 _88202 x f s) (term297 _88193 _88202 s x f)). Qed.
Lemma lem3396503 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term302 _88193 _88202 s x f x') = (term296 _88193 _88202 s x f x').
Proof. exact (eq_refl (term302 _88193 _88202 s x f x')). Qed.
Lemma lem3396504 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term303 _88193 _88202 s x f) = (term297 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3396503 _88193 _88202 s x f x')). Qed.
Lemma lem3396505 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396506 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term304 _88193 _88202 s x f) = (term298 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396505 _88193) (@lem3396504 _88193 _88202 s x f)). Qed.
Lemma lem3396507 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term224 _88193 _88202 x f s) = (term224 _88193 _88202 x f s).
Proof. exact (eq_refl (term224 _88193 _88202 x f s)). Qed.
Lemma lem3396508 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term300 _88193 _88202 s x f) = (term299 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396507 _88193 _88202 x f s) (@lem3396506 _88193 _88202 s x f)). Qed.
Lemma lem3396509 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396510 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term305 _88193 _88202 s x f) = (term306 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396509) (@lem3396508 _88193 _88202 s x f)). Qed.
Lemma lem3396511 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term302 _88193 _88202 s x f x') = (term296 _88193 _88202 s x f x').
Proof. exact (eq_refl (term302 _88193 _88202 s x f x')). Qed.
Lemma lem3396512 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term224 _88193 _88202 x f s) = (term224 _88193 _88202 x f s).
Proof. exact (eq_refl (term224 _88193 _88202 x f s)). Qed.
Lemma lem3396513 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term307 _88193 _88202 s x f x') = (term308 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396512 _88193 _88202 x f s) (@lem3396511 _88193 _88202 s x f x')). Qed.
Lemma lem3396514 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term309 _88193 _88202 s x f) = (term310 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3396513 _88193 _88202 s x f x')). Qed.
Lemma lem3396515 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396516 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term301 _88193 _88202 s x f) = (term311 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396515 _88193) (@lem3396514 _88193 _88202 s x f)). Qed.
Lemma lem3396517 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : ((term300 _88193 _88202 s x f) = (term301 _88193 _88202 s x f)) = ((term299 _88193 _88202 s x f) = (term311 _88193 _88202 s x f)).
Proof. exact (MK_COMB (@lem3396510 _88193 _88202 s x f) (@lem3396516 _88193 _88202 s x f)). Qed.
Lemma lem3396518 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term299 _88193 _88202 s x f) = (term311 _88193 _88202 s x f).
Proof. exact (EQ_MP (@lem3396517 _88193 _88202 s x f) (@lem3396502 _88193 _88202 s x f)). Qed.
Lemma lem3396520 {A : Type'} (P : Prop) (Q : A -> Prop) : (term234 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3396521 {_88193 : Type'} (P : Prop) (Q : _88193 -> Prop) : (term234 _88193 P Q) = (term235 _88193 P Q).
Proof. exact (@lem3396520 _88193 P Q). Qed.
Lemma lem3396522 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term312 _88193 _88202 s x f x') = (term313 _88193 _88202 s x f x').
Proof. exact (@lem3396521 _88193 (term202 _88193 _88202 x f s) (term295 _88193 _88202 s x f x')). Qed.
Lemma lem3396523 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term314 _88193 _88202 s x f x'' x') = (term293 _88193 _88202 s x f x' x'').
Proof. exact (eq_refl (term314 _88193 _88202 s x f x'' x')). Qed.
Lemma lem3396524 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term315 _88193 _88202 s x f x') = (term295 _88193 _88202 s x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396523 _88193 _88202 s x f x'' x')). Qed.
Lemma lem3396525 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396526 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term316 _88193 _88202 s x f x') = (term296 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396525 _88193) (@lem3396524 _88193 _88202 s x f x')). Qed.
Lemma lem3396527 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term224 _88193 _88202 x f s) = (term224 _88193 _88202 x f s).
Proof. exact (eq_refl (term224 _88193 _88202 x f s)). Qed.
Lemma lem3396528 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term312 _88193 _88202 s x f x') = (term308 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396527 _88193 _88202 x f s) (@lem3396526 _88193 _88202 s x f x')). Qed.
Lemma lem3396529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396530 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term317 _88193 _88202 s x f x') = (term318 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396529) (@lem3396528 _88193 _88202 s x f x')). Qed.
Lemma lem3396531 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term314 _88193 _88202 s x f x'' x') = (term293 _88193 _88202 s x f x' x'').
Proof. exact (eq_refl (term314 _88193 _88202 s x f x'' x')). Qed.
Lemma lem3396532 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term224 _88193 _88202 x f s) = (term224 _88193 _88202 x f s).
Proof. exact (eq_refl (term224 _88193 _88202 x f s)). Qed.
Lemma lem3396533 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term319 _88193 _88202 s x f x'' x') = (term320 _88193 _88202 s x f x' x'').
Proof. exact (MK_COMB (@lem3396532 _88193 _88202 x f s) (@lem3396531 _88193 _88202 s x f x' x'')). Qed.
Lemma lem3396534 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term321 _88193 _88202 s x f x') = (term322 _88193 _88202 s x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396533 _88193 _88202 s x f x'' x')). Qed.
Lemma lem3396535 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396536 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term313 _88193 _88202 s x f x') = (term323 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396535 _88193) (@lem3396534 _88193 _88202 s x f x')). Qed.
Lemma lem3396537 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : ((term312 _88193 _88202 s x f x') = (term313 _88193 _88202 s x f x')) = ((term308 _88193 _88202 s x f x') = (term323 _88193 _88202 s x f x')).
Proof. exact (MK_COMB (@lem3396530 _88193 _88202 s x f x') (@lem3396536 _88193 _88202 s x f x')). Qed.
Lemma lem3396538 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term308 _88193 _88202 s x f x') = (term323 _88193 _88202 s x f x').
Proof. exact (EQ_MP (@lem3396537 _88193 _88202 s x f x') (@lem3396522 _88193 _88202 s x f x')). Qed.
Lemma lem3396539 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term310 _88193 _88202 s x f) = (term324 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3396538 _88193 _88202 s x f x')). Qed.
Lemma lem3396540 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396541 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term311 _88193 _88202 s x f) = (term325 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396540 _88193) (@lem3396539 _88193 _88202 s x f)). Qed.
Lemma lem3396542 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term299 _88193 _88202 s x f) = (term325 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396518 _88193 _88202 s x f) (@lem3396541 _88193 _88202 s x f)). Qed.
Lemma lem3396543 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term226 _88193 _88202 s x f) = (term325 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396498 _88193 _88202 s x f) (@lem3396542 _88193 _88202 s x f)). Qed.
Lemma lem3396544 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term233 _88193 _88202 s x f) = (term326 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396473 _88193 _88202 s x f) (@lem3396543 _88193 _88202 s x f)). Qed.
Lemma lem3396548 {A : Type'} (P : A -> Prop) (Q : Prop) : (term327 A P Q) = (term328 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3396549 {_88193 : Type'} (P : _88193 -> Prop) (Q : Prop) : (term327 _88193 P Q) = (term328 _88193 P Q).
Proof. exact (@lem3396548 _88193 P Q). Qed.
Lemma lem3396550 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term329 _88193 _88202 s x f) = (term330 _88193 _88202 s x f).
Proof. exact (@lem3396549 _88193 (term283 _88193 _88202 s x f) (term325 _88193 _88202 s x f)). Qed.
Lemma lem3396551 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term331 _88193 _88202 s x' f x) = (term282 _88193 _88202 x s x' f).
Proof. exact (eq_refl (term331 _88193 _88202 s x' f x)). Qed.
Lemma lem3396552 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term332 _88193 _88202 s x f) = (term283 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396551 _88193 _88202 x' s x f)). Qed.
Lemma lem3396553 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396554 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term333 _88193 _88202 s x f) = (term284 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396553 _88193) (@lem3396552 _88193 _88202 s x f)). Qed.
Lemma lem3396555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3396556 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term334 _88193 _88202 s x f) = (term285 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396555) (@lem3396554 _88193 _88202 s x f)). Qed.
Lemma lem3396557 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term325 _88193 _88202 s x f) = (term325 _88193 _88202 s x f).
Proof. exact (eq_refl (term325 _88193 _88202 s x f)). Qed.
Lemma lem3396558 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term329 _88193 _88202 s x f) = (term326 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396556 _88193 _88202 s x f) (@lem3396557 _88193 _88202 s x f)). Qed.
Lemma lem3396559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396560 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term335 _88193 _88202 s x f) = (term336 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396559) (@lem3396558 _88193 _88202 s x f)). Qed.
Lemma lem3396561 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term331 _88193 _88202 s x' f x) = (term282 _88193 _88202 x s x' f).
Proof. exact (eq_refl (term331 _88193 _88202 s x' f x)). Qed.
Lemma lem3396562 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3396563 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term337 _88193 _88202 s x' f x) = (term338 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396562) (@lem3396561 _88193 _88202 x s x' f)). Qed.
Lemma lem3396564 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term325 _88193 _88202 s x f) = (term325 _88193 _88202 s x f).
Proof. exact (eq_refl (term325 _88193 _88202 s x f)). Qed.
Lemma lem3396565 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term339 _88193 _88202 x s x' f) = (term340 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396563 _88193 _88202 x s x' f) (@lem3396564 _88193 _88202 s x' f)). Qed.
Lemma lem3396566 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term341 _88193 _88202 s x f) = (term342 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396565 _88193 _88202 x' s x f)). Qed.
Lemma lem3396567 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396568 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term330 _88193 _88202 s x f) = (term343 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396567 _88193) (@lem3396566 _88193 _88202 s x f)). Qed.
Lemma lem3396569 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : ((term329 _88193 _88202 s x f) = (term330 _88193 _88202 s x f)) = ((term326 _88193 _88202 s x f) = (term343 _88193 _88202 s x f)).
Proof. exact (MK_COMB (@lem3396560 _88193 _88202 s x f) (@lem3396568 _88193 _88202 s x f)). Qed.
Lemma lem3396570 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term326 _88193 _88202 s x f) = (term343 _88193 _88202 s x f).
Proof. exact (EQ_MP (@lem3396569 _88193 _88202 s x f) (@lem3396550 _88193 _88202 s x f)). Qed.
Lemma lem3396572 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term344 A P Q) = (term345 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3396573 {_88193 : Type'} (P : type686 _88193) (Q : type686 _88193) : (term346 _88193 P Q) = (term347 _88193 P Q).
Proof. exact (@lem3396572 (_88193 -> Prop) P Q). Qed.
Lemma lem3396574 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term348 _88193 _88202 x s x' f) = (term349 _88193 _88202 x s x' f).
Proof. exact (@lem3396573 _88193 (term281 _88193 _88202 x s x' f) (term324 _88193 _88202 s x' f)). Qed.
Lemma lem3396575 {_88193 _88202 : Type'} (x : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term350 _88193 _88202 x s x' f t) = (term279 _88193 _88202 x t s x' f).
Proof. exact (eq_refl (term350 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396576 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term351 _88193 _88202 x s x' f) = (term281 _88193 _88202 x s x' f).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396575 _88193 _88202 x t s x' f)). Qed.
Lemma lem3396577 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396578 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term352 _88193 _88202 x s x' f) = (term282 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396577 _88193) (@lem3396576 _88193 _88202 x s x' f)). Qed.
Lemma lem3396579 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3396580 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term353 _88193 _88202 x s x' f) = (term338 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396579) (@lem3396578 _88193 _88202 x s x' f)). Qed.
Lemma lem3396581 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term354 _88193 _88202 s x f t) = (term323 _88193 _88202 s x f t).
Proof. exact (eq_refl (term354 _88193 _88202 s x f t)). Qed.
Lemma lem3396582 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term355 _88193 _88202 s x f) = (term324 _88193 _88202 s x f).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396581 _88193 _88202 s x f t)). Qed.
Lemma lem3396583 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396584 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term356 _88193 _88202 s x f) = (term325 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396583 _88193) (@lem3396582 _88193 _88202 s x f)). Qed.
Lemma lem3396585 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term348 _88193 _88202 x s x' f) = (term340 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396580 _88193 _88202 x s x' f) (@lem3396584 _88193 _88202 s x' f)). Qed.
Lemma lem3396586 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396587 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term357 _88193 _88202 x s x' f) = (term358 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396586) (@lem3396585 _88193 _88202 x s x' f)). Qed.
Lemma lem3396588 {_88193 _88202 : Type'} (x : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term350 _88193 _88202 x s x' f t) = (term279 _88193 _88202 x t s x' f).
Proof. exact (eq_refl (term350 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3396590 {_88193 _88202 : Type'} (x : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term359 _88193 _88202 x s x' f t) = (term360 _88193 _88202 x t s x' f).
Proof. exact (MK_COMB (@lem3396589) (@lem3396588 _88193 _88202 x t s x' f)). Qed.
Lemma lem3396591 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term354 _88193 _88202 s x f t) = (term323 _88193 _88202 s x f t).
Proof. exact (eq_refl (term354 _88193 _88202 s x f t)). Qed.
Lemma lem3396592 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term361 _88193 _88202 x s x' f t) = (term362 _88193 _88202 x s x' f t).
Proof. exact (MK_COMB (@lem3396590 _88193 _88202 x t s x' f) (@lem3396591 _88193 _88202 s x' f t)). Qed.
Lemma lem3396593 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term363 _88193 _88202 x s x' f) = (term364 _88193 _88202 x s x' f).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396592 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396594 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396595 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term349 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396594 _88193) (@lem3396593 _88193 _88202 x s x' f)). Qed.
Lemma lem3396596 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : ((term348 _88193 _88202 x s x' f) = (term349 _88193 _88202 x s x' f)) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)).
Proof. exact (MK_COMB (@lem3396587 _88193 _88202 x s x' f) (@lem3396595 _88193 _88202 x s x' f)). Qed.
Lemma lem3396597 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f).
Proof. exact (EQ_MP (@lem3396596 _88193 _88202 x s x' f) (@lem3396574 _88193 _88202 x s x' f)). Qed.
Lemma lem3396600 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term366 _88193 _88202 x s x' f) = (term366 _88193 _88202 x s x' f).
Proof. exact (eq_refl (term366 _88193 _88202 x s x' f)). Qed.
Lemma lem3396601 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term366 _88193 _88202 x s x' f) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)).
Proof. exact (eq_refl (term366 _88193 _88202 x s x' f)). Qed.
Lemma lem3396602 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term367 _88193 _88202 x s x' f) = (term367 _88193 _88202 x s x' f).
Proof. exact (eq_refl (term367 _88193 _88202 x s x' f)). Qed.
Lemma lem3396603 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : ((term366 _88193 _88202 x s x' f) = (term366 _88193 _88202 x s x' f)) = ((term366 _88193 _88202 x s x' f) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f))).
Proof. exact (MK_COMB (@lem3396602 _88193 _88202 x s x' f) (@lem3396601 _88193 _88202 x s x' f)). Qed.
Lemma lem3396604 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term366 _88193 _88202 x s x' f) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)).
Proof. exact (eq_refl (term366 _88193 _88202 x s x' f)). Qed.
Lemma lem3396605 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396606 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term367 _88193 _88202 x s x' f) = (term368 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396605) (@lem3396604 _88193 _88202 x s x' f)). Qed.
Lemma lem3396607 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)).
Proof. exact (eq_refl ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f))). Qed.
Lemma lem3396608 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : ((term366 _88193 _88202 x s x' f) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f))) = (((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f))).
Proof. exact (MK_COMB (@lem3396606 _88193 _88202 x s x' f) (@lem3396607 _88193 _88202 x s x' f)). Qed.
Lemma lem3396609 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : ((term366 _88193 _88202 x s x' f) = (term366 _88193 _88202 x s x' f)) = (((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f))).
Proof. exact (TRANS (@lem3396603 _88193 _88202 x s x' f) (@lem3396608 _88193 _88202 x s x' f)). Qed.
Lemma lem3396610 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)) = ((term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f)).
Proof. exact (EQ_MP (@lem3396609 _88193 _88202 x s x' f) (@lem3396600 _88193 _88202 x s x' f)). Qed.
Lemma lem3396611 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term340 _88193 _88202 x s x' f) = (term365 _88193 _88202 x s x' f).
Proof. exact (EQ_MP (@lem3396610 _88193 _88202 x s x' f) (@lem3396597 _88193 _88202 x s x' f)). Qed.
Lemma lem3396613 {A : Type'} (P : Prop) (Q : A -> Prop) : (term369 A P Q) = (term370 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3396614 {_88193 : Type'} (P : Prop) (Q : _88193 -> Prop) : (term369 _88193 P Q) = (term370 _88193 P Q).
Proof. exact (@lem3396613 _88193 P Q). Qed.
Lemma lem3396615 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term371 _88193 _88202 x s x' f t) = (term372 _88193 _88202 x s x' f t).
Proof. exact (@lem3396614 _88193 (term279 _88193 _88202 x t s x' f) (term322 _88193 _88202 s x' f t)). Qed.
Lemma lem3396616 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (t : _88193 -> Prop) : (term373 _88193 _88202 s x f t x') = (term320 _88193 _88202 s x f x' t).
Proof. exact (eq_refl (term373 _88193 _88202 s x f t x')). Qed.
Lemma lem3396617 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term374 _88193 _88202 s x f t) = (term322 _88193 _88202 s x f t).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396616 _88193 _88202 s x f x' t)). Qed.
Lemma lem3396618 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396619 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term375 _88193 _88202 s x f t) = (term323 _88193 _88202 s x f t).
Proof. exact (MK_COMB (@lem3396618 _88193) (@lem3396617 _88193 _88202 s x f t)). Qed.
Lemma lem3396620 {_88193 _88202 : Type'} (x : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term360 _88193 _88202 x t s x' f) = (term360 _88193 _88202 x t s x' f).
Proof. exact (eq_refl (term360 _88193 _88202 x t s x' f)). Qed.
Lemma lem3396621 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term371 _88193 _88202 x s x' f t) = (term362 _88193 _88202 x s x' f t).
Proof. exact (MK_COMB (@lem3396620 _88193 _88202 x t s x' f) (@lem3396619 _88193 _88202 s x' f t)). Qed.
Lemma lem3396622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396623 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term376 _88193 _88202 x s x' f t) = (term377 _88193 _88202 x s x' f t).
Proof. exact (MK_COMB (@lem3396622) (@lem3396621 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396624 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (t : _88193 -> Prop) : (term373 _88193 _88202 s x f t x') = (term320 _88193 _88202 s x f x' t).
Proof. exact (eq_refl (term373 _88193 _88202 s x f t x')). Qed.
Lemma lem3396625 {_88193 _88202 : Type'} (x : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term360 _88193 _88202 x t s x' f) = (term360 _88193 _88202 x t s x' f).
Proof. exact (eq_refl (term360 _88193 _88202 x t s x' f)). Qed.
Lemma lem3396626 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) : (term378 _88193 _88202 x s x' f t x'') = (term379 _88193 _88202 x s x' f x'' t).
Proof. exact (MK_COMB (@lem3396625 _88193 _88202 x t s x' f) (@lem3396624 _88193 _88202 s x' f x'' t)). Qed.
Lemma lem3396627 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term380 _88193 _88202 x s x' f t) = (term381 _88193 _88202 x s x' f t).
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396626 _88193 _88202 x s x' f x'' t)). Qed.
Lemma lem3396628 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396629 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term372 _88193 _88202 x s x' f t) = (term382 _88193 _88202 x s x' f t).
Proof. exact (MK_COMB (@lem3396628 _88193) (@lem3396627 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396630 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : ((term371 _88193 _88202 x s x' f t) = (term372 _88193 _88202 x s x' f t)) = ((term362 _88193 _88202 x s x' f t) = (term382 _88193 _88202 x s x' f t)).
Proof. exact (MK_COMB (@lem3396623 _88193 _88202 x s x' f t) (@lem3396629 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396631 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) : (term362 _88193 _88202 x s x' f t) = (term382 _88193 _88202 x s x' f t).
Proof. exact (EQ_MP (@lem3396630 _88193 _88202 x s x' f t) (@lem3396615 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396632 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term364 _88193 _88202 x s x' f) = (term383 _88193 _88202 x s x' f).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396631 _88193 _88202 x s x' f t)). Qed.
Lemma lem3396633 {_88193 : Type'} : (@ex (_88193 -> Prop)) = (@ex (_88193 -> Prop)).
Proof. exact (eq_refl (@ex (_88193 -> Prop))). Qed.
Lemma lem3396634 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term365 _88193 _88202 x s x' f) = (term384 _88193 _88202 x s x' f).
Proof. exact (MK_COMB (@lem3396633 _88193) (@lem3396632 _88193 _88202 x s x' f)). Qed.
Lemma lem3396635 {_88193 _88202 : Type'} (x : _88193) (s : type686 _88193) (x' : _88202) (f : _88193 -> _88202) : (term340 _88193 _88202 x s x' f) = (term384 _88193 _88202 x s x' f).
Proof. exact (TRANS (@lem3396611 _88193 _88202 x s x' f) (@lem3396634 _88193 _88202 x s x' f)). Qed.
Lemma lem3396636 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term342 _88193 _88202 s x f) = (term385 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396635 _88193 _88202 x' s x f)). Qed.
Lemma lem3396637 {_88193 : Type'} : (@ex _88193) = (@ex _88193).
Proof. exact (eq_refl (@ex _88193)). Qed.
Lemma lem3396638 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term343 _88193 _88202 s x f) = (term386 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396637 _88193) (@lem3396636 _88193 _88202 s x f)). Qed.
Lemma lem3396639 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term326 _88193 _88202 s x f) = (term386 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396570 _88193 _88202 s x f) (@lem3396638 _88193 _88202 s x f)). Qed.
Lemma lem3396641 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term233 _88193 _88202 s x f) = (term386 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396544 _88193 _88202 s x f) (@lem3396639 _88193 _88202 s x f)). Qed.
Lemma lem3396642 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term178 _88193 _88202 s x f) = (term386 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396006 _88193 _88202 s x f) (@lem3396641 _88193 _88202 s x f)). Qed.
Lemma lem3396643 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term178 _88193 _88202 s x f) : term386 _88193 _88202 s x f.
Proof. exact (EQ_MP (@lem3396642 _88193 _88202 s x f) (@lem3395899 _88193 _88202 s x f h1)). Qed.
Lemma lem3396644 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term384 _88193 _88202 x' s x f) : term384 _88193 _88202 x' s x f.
Proof. exact (h1). Qed.
Lemma lem3396645 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) (h1 : term382 _88193 _88202 x' s x f t) : term382 _88193 _88202 x' s x f t.
Proof. exact (h1). Qed.
Lemma lem3396646 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term379 _88193 _88202 x' s x f x'' t) : term379 _88193 _88202 x' s x f x'' t.
Proof. exact (h1). Qed.
Lemma lem3396669 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) : (term293 _88193 _88202 s x f x'' t) = (term293 _88193 _88202 s x f x'' t).
Proof. exact (eq_refl (term293 _88193 _88202 s x f x'' t)). Qed.
Lemma lem3396686 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term180 _88193 s x t) = (term180 _88193 s x t).
Proof. exact (eq_refl (term180 _88193 s x t)). Qed.
Lemma lem3396687 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term188 _88193 s x) = (term188 _88193 s x).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396686 _88193 s x t)). Qed.
Lemma lem3396688 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3396689 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term189 _88193 s x) = (term189 _88193 s x).
Proof. exact (MK_COMB (@lem3396688 _88193) (@lem3396687 _88193 s x)). Qed.
Lemma lem3396700 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term190 _88193 _88202 x f x') = (term190 _88193 _88202 x f x').
Proof. exact (eq_refl (term190 _88193 _88202 x f x')). Qed.
Lemma lem3396701 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term192 _88193 _88202 x f s x') = (term192 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396700 _88193 _88202 x f x') (@lem3396689 _88193 s x')). Qed.
Lemma lem3396702 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term201 _88193 _88202 x f s) = (term201 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396701 _88193 _88202 x f s x')). Qed.
Lemma lem3396703 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3396704 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term202 _88193 _88202 x f s) = (term202 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396703 _88193) (@lem3396702 _88193 _88202 x f s)). Qed.
Lemma lem3396705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3396706 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term224 _88193 _88202 x f s) = (term224 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396705) (@lem3396704 _88193 _88202 x f s)). Qed.
Lemma lem3396707 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) : (term320 _88193 _88202 s x f x'' t) = (term320 _88193 _88202 s x f x'' t).
Proof. exact (MK_COMB (@lem3396706 _88193 _88202 x f s) (@lem3396669 _88193 _88202 s x f x'' t)). Qed.
Lemma lem3396726 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term204 _88193 _88202 x f x' x'') = (term204 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term204 _88193 _88202 x f x' x'')). Qed.
Lemma lem3396727 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term210 _88193 _88202 x f x') = (term210 _88193 _88202 x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396726 _88193 _88202 x f x'' x')). Qed.
Lemma lem3396728 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3396729 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term211 _88193 _88202 x f x') = (term211 _88193 _88202 x f x').
Proof. exact (MK_COMB (@lem3396728 _88193) (@lem3396727 _88193 _88202 x f x')). Qed.
Lemma lem3396738 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term212 _88193 x s) = (term212 _88193 x s).
Proof. exact (eq_refl (term212 _88193 x s)). Qed.
Lemma lem3396739 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term214 _88193 _88202 s x f x') = (term214 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396738 _88193 x' s) (@lem3396729 _88193 _88202 x f x')). Qed.
Lemma lem3396740 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term221 _88193 _88202 s x f) = (term221 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3396739 _88193 _88202 s x f x')). Qed.
Lemma lem3396741 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3396742 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term222 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396741 _88193) (@lem3396740 _88193 _88202 s x f)). Qed.
Lemma lem3396767 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) (t : _88193 -> Prop) : (term277 _88193 _88202 x f s x' t) = (term277 _88193 _88202 x f s x' t).
Proof. exact (eq_refl (term277 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396768 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term279 _88193 _88202 x' t s x f) = (term279 _88193 _88202 x' t s x f).
Proof. exact (MK_COMB (@lem3396767 _88193 _88202 x f s x' t) (@lem3396742 _88193 _88202 s x f)). Qed.
Lemma lem3396769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3396770 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term360 _88193 _88202 x' t s x f) = (term360 _88193 _88202 x' t s x f).
Proof. exact (MK_COMB (@lem3396769) (@lem3396768 _88193 _88202 x' t s x f)). Qed.
Lemma lem3396771 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) : (term379 _88193 _88202 x' s x f x'' t) = (term379 _88193 _88202 x' s x f x'' t).
Proof. exact (MK_COMB (@lem3396770 _88193 _88202 x' t s x f) (@lem3396707 _88193 _88202 s x f x'' t)). Qed.
Lemma lem3396772 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term379 _88193 _88202 x' s x f x'' t) : term379 _88193 _88202 x' s x f x'' t.
Proof. exact (EQ_MP (@lem3396771 _88193 _88202 x' s x f x'' t) (@lem3396646 _88193 _88202 x' s x f x'' t h1)). Qed.
Lemma lem3396773 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term279 _88193 _88202 x' t s x f.
Proof. exact (h1). Qed.
Lemma lem3396774 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term320 _88193 _88202 s x f x'' t.
Proof. exact (h1). Qed.
Lemma lem3396775 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term222 _88193 _88202 s x f.
Proof. exact (proj2 (@lem3396773 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3396776 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term245 _88193 _88202 x f s x' t.
Proof. exact (proj1 (@lem3396773 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3396777 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term175 _88193 s x' t.
Proof. exact (proj2 (@lem3396776 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3396781 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term293 _88193 _88202 s x f x'' t.
Proof. exact (proj2 (@lem3396774 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3396782 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term202 _88193 _88202 x f s.
Proof. exact (proj1 (@lem3396774 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3396783 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term173 _88193 _88202 x f x'' t.
Proof. exact (proj2 (@lem3396781 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3396788 {A : Type'} (P : Prop) (Q : A -> Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3396789 {_88193 : Type'} (P : Prop) (Q : _88193 -> Prop) : (term387 _88193 P Q) = (term388 _88193 P Q).
Proof. exact (@lem3396788 _88193 P Q). Qed.
Lemma lem3396790 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term389 _88193 _88202 s x f x') = (term390 _88193 _88202 s x f x').
Proof. exact (@lem3396789 _88193 (term391 _88193 x' s) (term210 _88193 _88202 x f x')). Qed.
Lemma lem3396791 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term392 _88193 _88202 x f x'' x') = (term204 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term392 _88193 _88202 x f x'' x')). Qed.
Lemma lem3396792 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term393 _88193 _88202 x f x') = (term210 _88193 _88202 x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396791 _88193 _88202 x f x'' x')). Qed.
Lemma lem3396793 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3396794 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term394 _88193 _88202 x f x') = (term211 _88193 _88202 x f x').
Proof. exact (MK_COMB (@lem3396793 _88193) (@lem3396792 _88193 _88202 x f x')). Qed.
Lemma lem3396795 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term212 _88193 x s) = (term212 _88193 x s).
Proof. exact (eq_refl (term212 _88193 x s)). Qed.
Lemma lem3396796 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term389 _88193 _88202 s x f x') = (term214 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396795 _88193 x' s) (@lem3396794 _88193 _88202 x f x')). Qed.
Lemma lem3396797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396798 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term395 _88193 _88202 s x f x') = (term396 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396797) (@lem3396796 _88193 _88202 s x f x')). Qed.
Lemma lem3396799 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term392 _88193 _88202 x f x'' x') = (term204 _88193 _88202 x f x' x'').
Proof. exact (eq_refl (term392 _88193 _88202 x f x'' x')). Qed.
Lemma lem3396800 {_88193 : Type'} (x : _88193 -> Prop) (s : type686 _88193) : (term212 _88193 x s) = (term212 _88193 x s).
Proof. exact (eq_refl (term212 _88193 x s)). Qed.
Lemma lem3396801 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term397 _88193 _88202 s x f x'' x') = (term398 _88193 _88202 s x f x' x'').
Proof. exact (MK_COMB (@lem3396800 _88193 x'' s) (@lem3396799 _88193 _88202 x f x' x'')). Qed.
Lemma lem3396802 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term399 _88193 _88202 s x f x') = (term400 _88193 _88202 s x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396801 _88193 _88202 s x f x'' x')). Qed.
Lemma lem3396803 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3396804 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term390 _88193 _88202 s x f x') = (term401 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396803 _88193) (@lem3396802 _88193 _88202 s x f x')). Qed.
Lemma lem3396805 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : ((term389 _88193 _88202 s x f x') = (term390 _88193 _88202 s x f x')) = ((term214 _88193 _88202 s x f x') = (term401 _88193 _88202 s x f x')).
Proof. exact (MK_COMB (@lem3396798 _88193 _88202 s x f x') (@lem3396804 _88193 _88202 s x f x')). Qed.
Lemma lem3396806 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term214 _88193 _88202 s x f x') = (term401 _88193 _88202 s x f x').
Proof. exact (EQ_MP (@lem3396805 _88193 _88202 s x f x') (@lem3396790 _88193 _88202 s x f x')). Qed.
Lemma lem3396807 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term221 _88193 _88202 s x f) = (term402 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3396806 _88193 _88202 s x f x')). Qed.
Lemma lem3396808 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3396809 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term403 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396808 _88193) (@lem3396807 _88193 _88202 s x f)). Qed.
Lemma lem3396822 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193) (x'' : _88193 -> Prop) : (term398 _88193 _88202 s x f x' x'') = (term398 _88193 _88202 s x f x' x'').
Proof. exact (eq_refl (term398 _88193 _88202 s x f x' x'')). Qed.
Lemma lem3396823 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term400 _88193 _88202 s x f x') = (term400 _88193 _88202 s x f x').
Proof. exact (fun_ext (fun x'' : _88193 => @lem3396822 _88193 _88202 s x f x'' x')). Qed.
Lemma lem3396824 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3396825 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x' : _88193 -> Prop) : (term401 _88193 _88202 s x f x') = (term401 _88193 _88202 s x f x').
Proof. exact (MK_COMB (@lem3396824 _88193) (@lem3396823 _88193 _88202 s x f x')). Qed.
Lemma lem3396826 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term402 _88193 _88202 s x f) = (term402 _88193 _88202 s x f).
Proof. exact (fun_ext (fun x' : _88193 -> Prop => @lem3396825 _88193 _88202 s x f x')). Qed.
Lemma lem3396827 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3396828 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term403 _88193 _88202 s x f) = (term403 _88193 _88202 s x f).
Proof. exact (MK_COMB (@lem3396827 _88193) (@lem3396826 _88193 _88202 s x f)). Qed.
Lemma lem3396829 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term222 _88193 _88202 s x f) = (term403 _88193 _88202 s x f).
Proof. exact (TRANS (@lem3396809 _88193 _88202 s x f) (@lem3396828 _88193 _88202 s x f)). Qed.
Lemma lem3396830 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term403 _88193 _88202 s x f.
Proof. exact (EQ_MP (@lem3396829 _88193 _88202 s x f) (@lem3396775 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3396844 {A : Type'} (P : Prop) (Q : A -> Prop) : (term387 A P Q) = (term388 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem3396845 {_88193 : Type'} (P : Prop) (Q : type686 _88193) : (term404 _88193 P Q) = (term405 _88193 P Q).
Proof. exact (@lem3396844 (_88193 -> Prop) P Q). Qed.
Lemma lem3396846 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term406 _88193 _88202 x f s x') = (term407 _88193 _88202 x f s x').
Proof. exact (@lem3396845 _88193 (term408 _88193 _88202 x f x') (term188 _88193 s x')). Qed.
Lemma lem3396847 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term409 _88193 s x t) = (term180 _88193 s x t).
Proof. exact (eq_refl (term409 _88193 s x t)). Qed.
Lemma lem3396848 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term410 _88193 s x) = (term188 _88193 s x).
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396847 _88193 s x t)). Qed.
Lemma lem3396849 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3396850 {_88193 : Type'} (s : type686 _88193) (x : _88193) : (term411 _88193 s x) = (term189 _88193 s x).
Proof. exact (MK_COMB (@lem3396849 _88193) (@lem3396848 _88193 s x)). Qed.
Lemma lem3396851 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term190 _88193 _88202 x f x') = (term190 _88193 _88202 x f x').
Proof. exact (eq_refl (term190 _88193 _88202 x f x')). Qed.
Lemma lem3396852 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term406 _88193 _88202 x f s x') = (term192 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396851 _88193 _88202 x f x') (@lem3396850 _88193 s x')). Qed.
Lemma lem3396853 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396854 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term412 _88193 _88202 x f s x') = (term413 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396853) (@lem3396852 _88193 _88202 x f s x')). Qed.
Lemma lem3396855 {_88193 : Type'} (s : type686 _88193) (x : _88193) (t : _88193 -> Prop) : (term409 _88193 s x t) = (term180 _88193 s x t).
Proof. exact (eq_refl (term409 _88193 s x t)). Qed.
Lemma lem3396856 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (x' : _88193) : (term190 _88193 _88202 x f x') = (term190 _88193 _88202 x f x').
Proof. exact (eq_refl (term190 _88193 _88202 x f x')). Qed.
Lemma lem3396857 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) (t : _88193 -> Prop) : (term414 _88193 _88202 x f s x' t) = (term415 _88193 _88202 x f s x' t).
Proof. exact (MK_COMB (@lem3396856 _88193 _88202 x f x') (@lem3396855 _88193 s x' t)). Qed.
Lemma lem3396858 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term416 _88193 _88202 x f s x') = (term417 _88193 _88202 x f s x').
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396857 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396859 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3396860 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term407 _88193 _88202 x f s x') = (term418 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396859 _88193) (@lem3396858 _88193 _88202 x f s x')). Qed.
Lemma lem3396861 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : ((term406 _88193 _88202 x f s x') = (term407 _88193 _88202 x f s x')) = ((term192 _88193 _88202 x f s x') = (term418 _88193 _88202 x f s x')).
Proof. exact (MK_COMB (@lem3396854 _88193 _88202 x f s x') (@lem3396860 _88193 _88202 x f s x')). Qed.
Lemma lem3396862 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term192 _88193 _88202 x f s x') = (term418 _88193 _88202 x f s x').
Proof. exact (EQ_MP (@lem3396861 _88193 _88202 x f s x') (@lem3396846 _88193 _88202 x f s x')). Qed.
Lemma lem3396863 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term201 _88193 _88202 x f s) = (term419 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396862 _88193 _88202 x f s x')). Qed.
Lemma lem3396864 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3396865 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term202 _88193 _88202 x f s) = (term420 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396864 _88193) (@lem3396863 _88193 _88202 x f s)). Qed.
Lemma lem3396878 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) (t : _88193 -> Prop) : (term415 _88193 _88202 x f s x' t) = (term415 _88193 _88202 x f s x' t).
Proof. exact (eq_refl (term415 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396879 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term417 _88193 _88202 x f s x') = (term417 _88193 _88202 x f s x').
Proof. exact (fun_ext (fun t : _88193 -> Prop => @lem3396878 _88193 _88202 x f s x' t)). Qed.
Lemma lem3396880 {_88193 : Type'} : (@all (_88193 -> Prop)) = (@all (_88193 -> Prop)).
Proof. exact (eq_refl (@all (_88193 -> Prop))). Qed.
Lemma lem3396881 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (x' : _88193) : (term418 _88193 _88202 x f s x') = (term418 _88193 _88202 x f s x').
Proof. exact (MK_COMB (@lem3396880 _88193) (@lem3396879 _88193 _88202 x f s x')). Qed.
Lemma lem3396882 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term419 _88193 _88202 x f s) = (term419 _88193 _88202 x f s).
Proof. exact (fun_ext (fun x' : _88193 => @lem3396881 _88193 _88202 x f s x')). Qed.
Lemma lem3396883 {_88193 : Type'} : (@all _88193) = (@all _88193).
Proof. exact (eq_refl (@all _88193)). Qed.
Lemma lem3396884 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term420 _88193 _88202 x f s) = (term420 _88193 _88202 x f s).
Proof. exact (MK_COMB (@lem3396883 _88193) (@lem3396882 _88193 _88202 x f s)). Qed.
Lemma lem3396885 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) : (term202 _88193 _88202 x f s) = (term420 _88193 _88202 x f s).
Proof. exact (TRANS (@lem3396865 _88193 _88202 x f s) (@lem3396884 _88193 _88202 x f s)). Qed.
Lemma lem3396886 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term420 _88193 _88202 x f s.
Proof. exact (EQ_MP (@lem3396885 _88193 _88202 x f s) (@lem3396782 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3396899 {_88193 _88202 : Type'} (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term421 _88193 _88202 s x f _35758.
Proof. exact (@lem3396830 _88193 _88202 x' t s x f h1 _35758). Qed.
Lemma lem3396900 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (_35758 : _88193 -> Prop) : (term421 _88193 _88202 s x f _35758) = (term401 _88193 _88202 s x f _35758).
Proof. exact (eq_refl (term421 _88193 _88202 s x f _35758)). Qed.
Lemma lem3396901 {_88193 _88202 : Type'} (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term401 _88193 _88202 s x f _35758.
Proof. exact (EQ_MP (@lem3396900 _88193 _88202 s x f _35758) (@lem3396899 _88193 _88202 _35758 x' t s x f h1)). Qed.
Lemma lem3396902 {_88193 _88202 : Type'} (_35758 : _88193 -> Prop) (_35759 : _88193) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term422 _88193 _88202 s x f _35758 _35759.
Proof. exact (@lem3396901 _88193 _88202 _35758 x' t s x f h1 _35759). Qed.
Lemma lem3396903 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term422 _88193 _88202 s x f _35758 _35759) = (term398 _88193 _88202 s x f _35759 _35758).
Proof. exact (eq_refl (term422 _88193 _88202 s x f _35758 _35759)). Qed.
Lemma lem3396905 {_88193 _88202 : Type'} (_35760 : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term423 _88193 _88202 x f s _35760.
Proof. exact (@lem3396886 _88193 _88202 s x f x'' t h1 _35760). Qed.
Lemma lem3396906 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) : (term423 _88193 _88202 x f s _35760) = (term418 _88193 _88202 x f s _35760).
Proof. exact (eq_refl (term423 _88193 _88202 x f s _35760)). Qed.
Lemma lem3396907 {_88193 _88202 : Type'} (_35760 : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term418 _88193 _88202 x f s _35760.
Proof. exact (EQ_MP (@lem3396906 _88193 _88202 x f s _35760) (@lem3396905 _88193 _88202 _35760 s x f x'' t h1)). Qed.
Lemma lem3396908 {_88193 _88202 : Type'} (_35760 : _88193) (_35761 : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term424 _88193 _88202 x f s _35760 _35761.
Proof. exact (@lem3396907 _88193 _88202 _35760 s x f x'' t h1 _35761). Qed.
Lemma lem3396909 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term424 _88193 _88202 x f s _35760 _35761) = (term415 _88193 _88202 x f s _35760 _35761).
Proof. exact (eq_refl (term424 _88193 _88202 x f s _35760 _35761)). Qed.
Lemma lem3396920 {_88193 _88202 : Type'} (_35759 : _88193) (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term398 _88193 _88202 s x f _35759 _35758.
Proof. exact (EQ_MP (@lem3396903 _88193 _88202 s x f _35759 _35758) (@lem3396902 _88193 _88202 _35758 _35759 x' t s x f h1)). Qed.
Lemma lem3396922 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : x = (f x').
Proof. exact (proj1 (@lem3396776 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3396936 {_88193 _88202 : Type'} (_35760 : _88193) (_35761 : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term415 _88193 _88202 x f s _35760 _35761.
Proof. exact (EQ_MP (@lem3396909 _88193 _88202 x f s _35760 _35761) (@lem3396908 _88193 _88202 _35760 _35761 s x f x'' t h1)). Qed.
Lemma lem3396940 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : x = (f x'').
Proof. exact (proj1 (@lem3396783 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3396957 {_88193 _88202 : Type'} (s : type686 _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term425 _88193 _88202 s f _35759 _35758) = (term425 _88193 _88202 s f _35759 _35758).
Proof. exact (eq_refl (term425 _88193 _88202 s f _35759 _35758)). Qed.
Lemma lem3396958 {_88193 _88202 : Type'} (_35759 : _88193) (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : (term426 _88193 _88202 s f _35759 _35758 x) = (term427 _88193 _88202 s _35759 _35758 f x').
Proof. exact (MK_COMB (@lem3396957 _88193 _88202 s f _35759 _35758) (@lem3396922 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3396959 {_88193 _88202 : Type'} (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term427 _88193 _88202 s _35759 _35758 f x') = (term428 _88193 _88202 s x' f _35759 _35758).
Proof. exact (eq_refl (term427 _88193 _88202 s _35759 _35758 f x')). Qed.
Lemma lem3396960 {_88193 _88202 : Type'} (s : type686 _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) (x : _88202) : (term429 _88193 _88202 s f _35759 _35758 x) = (term429 _88193 _88202 s f _35759 _35758 x).
Proof. exact (eq_refl (term429 _88193 _88202 s f _35759 _35758 x)). Qed.
Lemma lem3396961 {_88193 _88202 : Type'} (x : _88202) (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : ((term426 _88193 _88202 s f _35759 _35758 x) = (term427 _88193 _88202 s _35759 _35758 f x')) = ((term426 _88193 _88202 s f _35759 _35758 x) = (term428 _88193 _88202 s x' f _35759 _35758)).
Proof. exact (MK_COMB (@lem3396960 _88193 _88202 s f _35759 _35758 x) (@lem3396959 _88193 _88202 s x' f _35759 _35758)). Qed.
Lemma lem3396962 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term426 _88193 _88202 s f _35759 _35758 x) = (term398 _88193 _88202 s x f _35759 _35758).
Proof. exact (eq_refl (term426 _88193 _88202 s f _35759 _35758 x)). Qed.
Lemma lem3396963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3396964 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term429 _88193 _88202 s f _35759 _35758 x) = (term430 _88193 _88202 s x f _35759 _35758).
Proof. exact (MK_COMB (@lem3396963) (@lem3396962 _88193 _88202 s x f _35759 _35758)). Qed.
Lemma lem3396965 {_88193 _88202 : Type'} (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term428 _88193 _88202 s x' f _35759 _35758) = (term428 _88193 _88202 s x' f _35759 _35758).
Proof. exact (eq_refl (term428 _88193 _88202 s x' f _35759 _35758)). Qed.
Lemma lem3396966 {_88193 _88202 : Type'} (x : _88202) (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : ((term426 _88193 _88202 s f _35759 _35758 x) = (term428 _88193 _88202 s x' f _35759 _35758)) = ((term398 _88193 _88202 s x f _35759 _35758) = (term428 _88193 _88202 s x' f _35759 _35758)).
Proof. exact (MK_COMB (@lem3396964 _88193 _88202 s x f _35759 _35758) (@lem3396965 _88193 _88202 s x' f _35759 _35758)). Qed.
Lemma lem3396967 {_88193 _88202 : Type'} (x : _88202) (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : ((term426 _88193 _88202 s f _35759 _35758 x) = (term427 _88193 _88202 s _35759 _35758 f x')) = ((term398 _88193 _88202 s x f _35759 _35758) = (term428 _88193 _88202 s x' f _35759 _35758)).
Proof. exact (TRANS (@lem3396961 _88193 _88202 x s x' f _35759 _35758) (@lem3396966 _88193 _88202 x s x' f _35759 _35758)). Qed.
Lemma lem3396968 {_88193 _88202 : Type'} (_35759 : _88193) (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : (term398 _88193 _88202 s x f _35759 _35758) = (term428 _88193 _88202 s x' f _35759 _35758).
Proof. exact (EQ_MP (@lem3396967 _88193 _88202 x s x' f _35759 _35758) (@lem3396958 _88193 _88202 _35759 _35758 x' t s x f h1)). Qed.
Lemma lem3396969 {_88193 _88202 : Type'} (_35759 : _88193) (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term428 _88193 _88202 s x' f _35759 _35758.
Proof. exact (EQ_MP (@lem3396968 _88193 _88202 _35759 _35758 x' t s x f h1) (@lem3396920 _88193 _88202 _35759 _35758 x' t s x f h1)). Qed.
Lemma lem3397012 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term431 _88193 _88202 f s _35760 _35761) = (term431 _88193 _88202 f s _35760 _35761).
Proof. exact (eq_refl (term431 _88193 _88202 f s _35760 _35761)). Qed.
Lemma lem3397013 {_88193 _88202 : Type'} (_35760 : _88193) (_35761 : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : (term432 _88193 _88202 f s _35760 _35761 x) = (term433 _88193 _88202 s _35760 _35761 f x'').
Proof. exact (MK_COMB (@lem3397012 _88193 _88202 f s _35760 _35761) (@lem3396940 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397014 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term433 _88193 _88202 s _35760 _35761 f x'') = (term434 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (eq_refl (term433 _88193 _88202 s _35760 _35761 f x'')). Qed.
Lemma lem3397015 {_88193 _88202 : Type'} (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) (x : _88202) : (term435 _88193 _88202 f s _35760 _35761 x) = (term435 _88193 _88202 f s _35760 _35761 x).
Proof. exact (eq_refl (term435 _88193 _88202 f s _35760 _35761 x)). Qed.
Lemma lem3397016 {_88193 _88202 : Type'} (x : _88202) (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : ((term432 _88193 _88202 f s _35760 _35761 x) = (term433 _88193 _88202 s _35760 _35761 f x'')) = ((term432 _88193 _88202 f s _35760 _35761 x) = (term434 _88193 _88202 x'' f s _35760 _35761)).
Proof. exact (MK_COMB (@lem3397015 _88193 _88202 f s _35760 _35761 x) (@lem3397014 _88193 _88202 x'' f s _35760 _35761)). Qed.
Lemma lem3397017 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term432 _88193 _88202 f s _35760 _35761 x) = (term415 _88193 _88202 x f s _35760 _35761).
Proof. exact (eq_refl (term432 _88193 _88202 f s _35760 _35761 x)). Qed.
Lemma lem3397018 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3397019 {_88193 _88202 : Type'} (x : _88202) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term435 _88193 _88202 f s _35760 _35761 x) = (term436 _88193 _88202 x f s _35760 _35761).
Proof. exact (MK_COMB (@lem3397018) (@lem3397017 _88193 _88202 x f s _35760 _35761)). Qed.
Lemma lem3397020 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term434 _88193 _88202 x'' f s _35760 _35761) = (term434 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (eq_refl (term434 _88193 _88202 x'' f s _35760 _35761)). Qed.
Lemma lem3397021 {_88193 _88202 : Type'} (x : _88202) (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : ((term432 _88193 _88202 f s _35760 _35761 x) = (term434 _88193 _88202 x'' f s _35760 _35761)) = ((term415 _88193 _88202 x f s _35760 _35761) = (term434 _88193 _88202 x'' f s _35760 _35761)).
Proof. exact (MK_COMB (@lem3397019 _88193 _88202 x f s _35760 _35761) (@lem3397020 _88193 _88202 x'' f s _35760 _35761)). Qed.
Lemma lem3397022 {_88193 _88202 : Type'} (x : _88202) (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : ((term432 _88193 _88202 f s _35760 _35761 x) = (term433 _88193 _88202 s _35760 _35761 f x'')) = ((term415 _88193 _88202 x f s _35760 _35761) = (term434 _88193 _88202 x'' f s _35760 _35761)).
Proof. exact (TRANS (@lem3397016 _88193 _88202 x x'' f s _35760 _35761) (@lem3397021 _88193 _88202 x x'' f s _35760 _35761)). Qed.
Lemma lem3397023 {_88193 _88202 : Type'} (_35760 : _88193) (_35761 : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : (term415 _88193 _88202 x f s _35760 _35761) = (term434 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (EQ_MP (@lem3397022 _88193 _88202 x x'' f s _35760 _35761) (@lem3397013 _88193 _88202 _35760 _35761 s x f x'' t h1)). Qed.
Lemma lem3397024 {_88193 _88202 : Type'} (_35760 : _88193) (_35761 : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term434 _88193 _88202 x'' f s _35760 _35761.
Proof. exact (EQ_MP (@lem3397023 _88193 _88202 _35760 _35761 s x f x'' t h1) (@lem3396936 _88193 _88202 _35760 _35761 s x f x'' t h1)). Qed.
Lemma lem3397108 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : @IN (_88193 -> Prop) t s.
Proof. exact (proj1 (@lem3396777 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397109 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term437 _88193 t s.
Proof. exact (fun h0 : term391 _88193 t s => @lem3397108 _88193 _88202 x' t s x f h1). Qed.
Lemma lem3397111 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397112 {_88193 : Type'} (t : _88193 -> Prop) (s : type686 _88193) : (term437 _88193 t s) = (@IN (_88193 -> Prop) t s).
Proof. exact (@lem3397111 (@IN (_88193 -> Prop) t s)). Qed.
Lemma lem3397113 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : @IN (_88193 -> Prop) t s.
Proof. exact (EQ_MP (@lem3397112 _88193 t s) (@lem3397109 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397115 {_88202 : Type'} (x : _88202) : x = x.
Proof. exact (@lem21386 _88202 x). Qed.
Lemma lem3397116 {_88202 : Type'} (x : _88202) : x = x.
Proof. exact (@lem3397115 _88202 x). Qed.
Lemma lem3397117 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x' : _88193) : (f x') = (f x').
Proof. exact (@lem3397116 _88202 (f x')). Qed.
Lemma lem3397118 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x' : _88193) : term439 _88193 _88202 f x'.
Proof. exact (fun h0 : term440 _88193 _88202 f x' => @lem3397117 _88193 _88202 f x'). Qed.
Lemma lem3397120 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397121 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x' : _88193) : (term439 _88193 _88202 f x') = ((f x') = (f x')).
Proof. exact (@lem3397120 ((f x') = (f x'))). Qed.
Lemma lem3397122 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x' : _88193) : (f x') = (f x').
Proof. exact (EQ_MP (@lem3397121 _88193 _88202 f x') (@lem3397118 _88193 _88202 f x')). Qed.
Lemma lem3397124 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : @IN _88193 x' t.
Proof. exact (proj2 (@lem3396777 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397125 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term441 _88193 x' t.
Proof. exact (fun h0 : term442 _88193 x' t => @lem3397124 _88193 _88202 x' t s x f h1). Qed.
Lemma lem3397127 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397128 {_88193 : Type'} (x' : _88193) (t : _88193 -> Prop) : (term441 _88193 x' t) = (@IN _88193 x' t).
Proof. exact (@lem3397127 (@IN _88193 x' t)). Qed.
Lemma lem3397129 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : @IN _88193 x' t.
Proof. exact (EQ_MP (@lem3397128 _88193 x' t) (@lem3397125 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397131 (a : Prop) (b : Prop) : (term443 a b) = (term444 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3397132 {_88193 _88202 : Type'} (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term445 _88193 _88202 x' f _35759 _35758) = (term446 _88193 _88202 x' f _35759 _35758).
Proof. exact (@lem3397131 ((f x') = (f _35759)) (@IN _88193 _35759 _35758)). Qed.
Lemma lem3397133 {_88193 : Type'} (_35758 : _88193 -> Prop) (s : type686 _88193) : (term212 _88193 _35758 s) = (term212 _88193 _35758 s).
Proof. exact (eq_refl (term212 _88193 _35758 s)). Qed.
Lemma lem3397134 {_88193 _88202 : Type'} (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term428 _88193 _88202 s x' f _35759 _35758) = (term447 _88193 _88202 s x' f _35759 _35758).
Proof. exact (MK_COMB (@lem3397133 _88193 _35758 s) (@lem3397132 _88193 _88202 x' f _35759 _35758)). Qed.
Lemma lem3397136 (a : Prop) (b : Prop) : (term443 a b) = (term444 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3397137 {_88193 _88202 : Type'} (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term447 _88193 _88202 s x' f _35759 _35758) = (term448 _88193 _88202 s x' f _35759 _35758).
Proof. exact (@lem3397136 (@IN (_88193 -> Prop) _35758 s) (term449 _88193 _88202 x' f _35759 _35758)). Qed.
Lemma lem3397138 {_88193 _88202 : Type'} (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term428 _88193 _88202 s x' f _35759 _35758) = (term448 _88193 _88202 s x' f _35759 _35758).
Proof. exact (TRANS (@lem3397134 _88193 _88202 s x' f _35759 _35758) (@lem3397137 _88193 _88202 s x' f _35759 _35758)). Qed.
Lemma lem3397140 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3397141 {_88193 _88202 : Type'} (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term448 _88193 _88202 s x' f _35759 _35758) = (term450 _88193 _88202 s x' f _35759 _35758).
Proof. exact (@lem3397140 (term451 _88193 _88202 s x' f _35759 _35758)). Qed.
Lemma lem3397142 {_88193 _88202 : Type'} (s : type686 _88193) (x' : _88193) (f : _88193 -> _88202) (_35759 : _88193) (_35758 : _88193 -> Prop) : (term428 _88193 _88202 s x' f _35759 _35758) = (term450 _88193 _88202 s x' f _35759 _35758).
Proof. exact (TRANS (@lem3397138 _88193 _88202 s x' f _35759 _35758) (@lem3397141 _88193 _88202 s x' f _35759 _35758)). Qed.
Lemma lem3397144 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term452 _88193 _88202 f x' t.
Proof. exact (conj (@lem3397122 _88193 _88202 f x') (@lem3397129 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397145 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term453 _88193 _88202 s f x' t.
Proof. exact (conj (@lem3397113 _88193 _88202 x' t s x f h1) (@lem3397144 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397147 {_88193 _88202 : Type'} (_35759 : _88193) (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term450 _88193 _88202 s x' f _35759 _35758.
Proof. exact (EQ_MP (@lem3397142 _88193 _88202 s x' f _35759 _35758) (@lem3396969 _88193 _88202 _35759 _35758 x' t s x f h1)). Qed.
Lemma lem3397148 {_88193 _88202 : Type'} (_35759 : _88193) (_35758 : _88193 -> Prop) (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term450 _88193 _88202 s x' f _35759 _35758.
Proof. exact (@lem3397147 _88193 _88202 _35759 _35758 x' t s x f h1). Qed.
Lemma lem3397149 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term454 _88193 _88202 s f x' t.
Proof. exact (@lem3397148 _88193 _88202 x' t x' t s x f h1). Qed.
Lemma lem3397152 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : False.
Proof. exact (@lem3397149 _88193 _88202 x' t s x f h1 (@lem3397145 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397153 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : term455.
Proof. exact (fun h0 : ~ False => @lem3397152 _88193 _88202 x' t s x f h1). Qed.
Lemma lem3397155 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397156 : term455 = False.
Proof. exact (@lem3397155 False). Qed.
Lemma lem3397213 {_88202 : Type'} (x : _88202) : x = x.
Proof. exact (@lem21386 _88202 x). Qed.
Lemma lem3397214 {_88202 : Type'} (x : _88202) : x = x.
Proof. exact (@lem3397213 _88202 x). Qed.
Lemma lem3397215 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x'' : _88193) : (f x'') = (f x'').
Proof. exact (@lem3397214 _88202 (f x'')). Qed.
Lemma lem3397216 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x'' : _88193) : term439 _88193 _88202 f x''.
Proof. exact (fun h0 : term440 _88193 _88202 f x'' => @lem3397215 _88193 _88202 f x''). Qed.
Lemma lem3397218 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397219 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x'' : _88193) : (term439 _88193 _88202 f x'') = ((f x'') = (f x'')).
Proof. exact (@lem3397218 ((f x'') = (f x''))). Qed.
Lemma lem3397220 {_88193 _88202 : Type'} (f : _88193 -> _88202) (x'' : _88193) : (f x'') = (f x'').
Proof. exact (EQ_MP (@lem3397219 _88193 _88202 f x'') (@lem3397216 _88193 _88202 f x'')). Qed.
Lemma lem3397222 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : @IN (_88193 -> Prop) t s.
Proof. exact (proj1 (@lem3396781 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397223 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term437 _88193 t s.
Proof. exact (fun h0 : term391 _88193 t s => @lem3397222 _88193 _88202 s x f x'' t h1). Qed.
Lemma lem3397225 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397226 {_88193 : Type'} (t : _88193 -> Prop) (s : type686 _88193) : (term437 _88193 t s) = (@IN (_88193 -> Prop) t s).
Proof. exact (@lem3397225 (@IN (_88193 -> Prop) t s)). Qed.
Lemma lem3397227 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : @IN (_88193 -> Prop) t s.
Proof. exact (EQ_MP (@lem3397226 _88193 t s) (@lem3397223 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397229 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : @IN _88193 x'' t.
Proof. exact (proj2 (@lem3396783 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397230 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term441 _88193 x'' t.
Proof. exact (fun h0 : term442 _88193 x'' t => @lem3397229 _88193 _88202 s x f x'' t h1). Qed.
Lemma lem3397232 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397233 {_88193 : Type'} (x'' : _88193) (t : _88193 -> Prop) : (term441 _88193 x'' t) = (@IN _88193 x'' t).
Proof. exact (@lem3397232 (@IN _88193 x'' t)). Qed.
Lemma lem3397234 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : @IN _88193 x'' t.
Proof. exact (EQ_MP (@lem3397233 _88193 x'' t) (@lem3397230 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397236 (a : Prop) (b : Prop) : (term443 a b) = (term444 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3397237 {_88193 : Type'} (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term180 _88193 s _35760 _35761) = (term179 _88193 s _35760 _35761).
Proof. exact (@lem3397236 (@IN (_88193 -> Prop) _35761 s) (@IN _88193 _35760 _35761)). Qed.
Lemma lem3397238 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (_35760 : _88193) : (term456 _88193 _88202 x'' f _35760) = (term456 _88193 _88202 x'' f _35760).
Proof. exact (eq_refl (term456 _88193 _88202 x'' f _35760)). Qed.
Lemma lem3397239 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term434 _88193 _88202 x'' f s _35760 _35761) = (term457 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (MK_COMB (@lem3397238 _88193 _88202 x'' f _35760) (@lem3397237 _88193 s _35760 _35761)). Qed.
Lemma lem3397241 (a : Prop) (b : Prop) : (term443 a b) = (term444 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3397242 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term457 _88193 _88202 x'' f s _35760 _35761) = (term458 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (@lem3397241 ((f x'') = (f _35760)) (term175 _88193 s _35760 _35761)). Qed.
Lemma lem3397243 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term434 _88193 _88202 x'' f s _35760 _35761) = (term458 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (TRANS (@lem3397239 _88193 _88202 x'' f s _35760 _35761) (@lem3397242 _88193 _88202 x'' f s _35760 _35761)). Qed.
Lemma lem3397245 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3397246 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term458 _88193 _88202 x'' f s _35760 _35761) = (term459 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (@lem3397245 (term460 _88193 _88202 x'' f s _35760 _35761)). Qed.
Lemma lem3397247 {_88193 _88202 : Type'} (x'' : _88193) (f : _88193 -> _88202) (s : type686 _88193) (_35760 : _88193) (_35761 : _88193 -> Prop) : (term434 _88193 _88202 x'' f s _35760 _35761) = (term459 _88193 _88202 x'' f s _35760 _35761).
Proof. exact (TRANS (@lem3397243 _88193 _88202 x'' f s _35760 _35761) (@lem3397246 _88193 _88202 x'' f s _35760 _35761)). Qed.
Lemma lem3397249 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term175 _88193 s x'' t.
Proof. exact (conj (@lem3397227 _88193 _88202 s x f x'' t h1) (@lem3397234 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397250 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term461 _88193 _88202 f s x'' t.
Proof. exact (conj (@lem3397220 _88193 _88202 f x'') (@lem3397249 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397252 {_88193 _88202 : Type'} (_35760 : _88193) (_35761 : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term459 _88193 _88202 x'' f s _35760 _35761.
Proof. exact (EQ_MP (@lem3397247 _88193 _88202 x'' f s _35760 _35761) (@lem3397024 _88193 _88202 _35760 _35761 s x f x'' t h1)). Qed.
Lemma lem3397253 {_88193 _88202 : Type'} (_35760 : _88193) (_35761 : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term459 _88193 _88202 x'' f s _35760 _35761.
Proof. exact (@lem3397252 _88193 _88202 _35760 _35761 s x f x'' t h1). Qed.
Lemma lem3397254 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term462 _88193 _88202 f s x'' t.
Proof. exact (@lem3397253 _88193 _88202 x'' t s x f x'' t h1). Qed.
Lemma lem3397257 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : False.
Proof. exact (@lem3397254 _88193 _88202 s x f x'' t h1 (@lem3397250 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397258 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : term455.
Proof. exact (fun h0 : ~ False => @lem3397257 _88193 _88202 s x f x'' t h1). Qed.
Lemma lem3397260 (p : Prop) : (term438 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3397261 : term455 = False.
Proof. exact (@lem3397260 False). Qed.
Lemma lem3397263 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term320 _88193 _88202 s x f x'' t) : False.
Proof. exact (EQ_MP (@lem3397261) (@lem3397258 _88193 _88202 s x f x'' t h1)). Qed.
Lemma lem3397264 {_88193 _88202 : Type'} (x' : _88193) (t : _88193 -> Prop) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term279 _88193 _88202 x' t s x f) : False.
Proof. exact (EQ_MP (@lem3397156) (@lem3397153 _88193 _88202 x' t s x f h1)). Qed.
Lemma lem3397265 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term379 _88193 _88202 x' s x f x'' t) : False.
Proof. exact (or_elim (@lem3396772 _88193 _88202 x' s x f x'' t h1) (fun h0 : term279 _88193 _88202 x' t s x f => @lem3397264 _88193 _88202 x' t s x f h0) (fun h0 : term320 _88193 _88202 s x f x'' t => @lem3397263 _88193 _88202 s x f x'' t h0)). Qed.
Lemma lem3397266 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term379 _88193 _88202 x' s x f x'' t) : (term379 _88193 _88202 x' s x f x'' t) = False.
Proof. exact (prop_ext (fun h2 : term379 _88193 _88202 x' s x f x'' t => @lem3397265 _88193 _88202 x' s x f x'' t h1) (fun h2 : False => @lem3396772 _88193 _88202 x' s x f x'' t h1)). Qed.
Lemma lem3397267 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (x'' : _88193) (t : _88193 -> Prop) (h1 : term379 _88193 _88202 x' s x f x'' t) : False.
Proof. exact (EQ_MP (@lem3397266 _88193 _88202 x' s x f x'' t h1) (@lem3396772 _88193 _88202 x' s x f x'' t h1)). Qed.
Lemma lem3397268 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (t : _88193 -> Prop) (h1 : term382 _88193 _88202 x' s x f t) : False.
Proof. exact (ex_elim (@lem3396645 _88193 _88202 x' s x f t h1) (fun x'' : _88193 => fun h0 : term381 _88193 _88202 x' s x f t x'' => @lem3397267 _88193 _88202 x' s x f x'' t h0)). Qed.
Lemma lem3397269 {_88193 _88202 : Type'} (x' : _88193) (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term384 _88193 _88202 x' s x f) : False.
Proof. exact (ex_elim (@lem3396644 _88193 _88202 x' s x f h1) (fun t : _88193 -> Prop => fun h0 : term383 _88193 _88202 x' s x f t => @lem3397268 _88193 _88202 x' s x f t h0)). Qed.
Lemma lem3397270 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term178 _88193 _88202 s x f) : False.
Proof. exact (ex_elim (@lem3396643 _88193 _88202 s x f h1) (fun x' : _88193 => fun h0 : term385 _88193 _88202 s x f x' => @lem3397269 _88193 _88202 x' s x f h0)). Qed.
Lemma lem3397271 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term178 _88193 _88202 s x f) : (term178 _88193 _88202 s x f) = False.
Proof. exact (prop_ext (fun h2 : term178 _88193 _88202 s x f => @lem3397270 _88193 _88202 s x f h1) (fun h2 : False => @lem3395899 _88193 _88202 s x f h1)). Qed.
Lemma lem3397272 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) (h1 : term178 _88193 _88202 s x f) : False.
Proof. exact (EQ_MP (@lem3397271 _88193 _88202 s x f h1) (@lem3395899 _88193 _88202 s x f h1)). Qed.
Lemma lem3397273 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : term177 _88193 _88202 s x f.
Proof. exact (fun h0 : term178 _88193 _88202 s x f => @lem3397272 _88193 _88202 s x f h0). Qed.
Lemma lem3397274 {_88193 _88202 : Type'} (s : type686 _88193) (x : _88202) (f : _88193 -> _88202) : (term63 _88193 _88202 x f s) = (term158 _88193 _88202 s x f).
Proof. exact (EQ_MP (@lem3395898 _88193 _88202 s x f) (@lem3397273 _88193 _88202 s x f)). Qed.
Lemma lem3397279 {_88193 _88202 : Type'} (s : type686 _88193) (f : _88193 -> _88202) : term160 _88193 _88202 s f.
Proof. exact (fun x : _88202 => @lem3397274 _88193 _88202 s x f). Qed.
Lemma lem3397284 {_88193 _88202 : Type'} (f : _88193 -> _88202) : term162 _88193 _88202 f.
Proof. exact (fun s : type686 _88193 => @lem3397279 _88193 _88202 s f). Qed.
Lemma lem3397289 {_88193 _88202 : Type'} : term164 _88193 _88202.
Proof. exact (fun f : _88193 -> _88202 => @lem3397284 _88193 _88202 f). Qed.
Lemma lem3397290 {_88193 _88202 : Type'} : term166 _88193 _88202.
Proof. exact (EQ_MP (@lem3395894 _88193 _88202) (@lem3397289 _88193 _88202)). Qed.
Lemma lem3397292 {_88193 _88202 : Type'} : term166 _88193 _88202.
Proof. exact (@lem3395575 _88193 _88202 (@lem3397290 _88193 _88202)). Qed.
Lemma lem3397293 {_88193 _88202 : Type'} (h1 : term167 _88193 _88202) : False.
Proof. exact (@lem3397292 _88193 _88202 (@lem3395559 _88193 _88202 h1)). Qed.
Lemma lem3397294 {_88193 _88202 : Type'} (h1 : term167 _88193 _88202) : (term167 _88193 _88202) = False.
Proof. exact (prop_ext (fun h2 : term167 _88193 _88202 => @lem3397293 _88193 _88202 h1) (fun h2 : False => @lem3395559 _88193 _88202 h1)). Qed.
Lemma lem3397295 {_88193 _88202 : Type'} (h1 : term167 _88193 _88202) : False.
Proof. exact (EQ_MP (@lem3397294 _88193 _88202 h1) (@lem3395559 _88193 _88202 h1)). Qed.
Lemma lem3397296 {_88193 _88202 : Type'} : term166 _88193 _88202.
Proof. exact (fun h0 : term167 _88193 _88202 => @lem3397295 _88193 _88202 h0). Qed.
Lemma lem3397297 {_88193 _88202 : Type'} : term164 _88193 _88202.
Proof. exact (EQ_MP (@lem3395558 _88193 _88202) (@lem3397296 _88193 _88202)). Qed.
Lemma lem3397298 {_88193 _88202 : Type'} : term139 _88193 _88202.
Proof. exact (EQ_MP (@lem3395554 _88193 _88202) (@lem3397297 _88193 _88202)). Qed.
Lemma lem3397299 {_88193 _88202 : Type'} : term113 _88193 _88202.
Proof. exact (EQ_MP (@lem3395434 _88193 _88202) (@lem3397298 _88193 _88202)). Qed.
Lemma lem3397300 {_88193 _88202 : Type'} : term86 _88193 _88202.
Proof. exact (EQ_MP (@lem3395364 _88193 _88202) (@lem3397299 _88193 _88202)). Qed.
Lemma lem3397301 {_88193 _88202 : Type'} : term55 _88193 _88202.
Proof. exact (EQ_MP (@lem3395265 _88193 _88202) (@lem3397300 _88193 _88202)). Qed.
Lemma lem3397302 {_88193 _88202 : Type'} : term54 _88193 _88202.
Proof. exact (EQ_MP (@lem3395155 _88193 _88202) (@lem3397301 _88193 _88202)). Qed.
