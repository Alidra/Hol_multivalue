Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_ADD_term_abbrevs.
Require Import COND_RAND_spec.
Require Import COND_RATOR_spec.
Require Import EXTENSION_spec.
Require Import INT_POS_spec.
Require Import IN_NUMSEG_spec.
Require Import LEFT_IMP_EXISTS_THM_spec.
Require Import REAL_ADD_RDISTRIB_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import SUM_ADD_NUMSEG_spec.
Require Import SUM_RESTRICT_SET_spec.
Require Import polynomial_function_spec.
Require Import thm0_spec.
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
Require Import thm1386578_spec.
Require Import thm1482687_spec.
Require Import thm1483205_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
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
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988289_spec.
Require Import thm1988291_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318511_spec.
Require Import thm2318512_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841374_spec.
Require Import thm2841375_spec.
Require Import thm2841407_spec.
Require Import thm2841408_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm7_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem7555025 (m : nat) : term0 m.
Proof. exact (@lem5371273 m). Qed.
Lemma lem7555026 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem7555027 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem7555026 m) (@lem7555025 m)). Qed.
Lemma lem7555028 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem7555027 m n). Qed.
Lemma lem7555029 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem7555030 (m : nat) (n : nat) : term3 m n.
Proof. exact (EQ_MP (@lem7555029 m n) (@lem7555028 m n)). Qed.
Lemma lem7555031 (m : nat) (n : nat) (p : nat) : term4 m n p.
Proof. exact (@lem7555030 m n p). Qed.
Lemma lem7555032 (m : nat) (p : nat) (n : nat) : (term4 m n p) = ((term5 p m n) = (term6 m p n)).
Proof. exact (eq_refl (term4 m n p)). Qed.
Lemma lem7555058 {_83095 : Type'} : term7 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem7555059 {_83095 : Type'} (p : _83095 -> Prop) : term8 _83095 p.
Proof. exact (@lem7555058 _83095 p). Qed.
Lemma lem7555060 {_83095 : Type'} (p : _83095 -> Prop) : (term8 _83095 p) = (term9 _83095 p).
Proof. exact (eq_refl (term8 _83095 p)). Qed.
Lemma lem7555061 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (EQ_MP (@lem7555060 _83095 p) (@lem7555059 _83095 p)). Qed.
Lemma lem7555062 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term10 _83095 p x.
Proof. exact (@lem7555061 _83095 p x). Qed.
Lemma lem7555063 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 p x) = ((term11 _83095 x p) = (p x)).
Proof. exact (eq_refl (term10 _83095 p x)). Qed.
Lemma lem7555072 {A : Type'} (s : A -> Prop) : term12 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem7555073 {A : Type'} (s : A -> Prop) : (term12 A s) = (term13 A s).
Proof. exact (eq_refl (term12 A s)). Qed.
Lemma lem7555074 {A : Type'} (s : A -> Prop) : term13 A s.
Proof. exact (EQ_MP (@lem7555073 A s) (@lem7555072 A s)). Qed.
Lemma lem7555075 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term14 A s t.
Proof. exact (@lem7555074 A s t). Qed.
Lemma lem7555076 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term14 A s t) = ((s = t) = (term15 A s t)).
Proof. exact (eq_refl (term14 A s t)). Qed.
Lemma lem7555081 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) (h1 : (term16 _133899 s P f) = (term17 _133899 s P f)) : (term16 _133899 s P f) = (term17 _133899 s P f).
Proof. exact (h1). Qed.
Lemma lem7555082 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) (h1 : (term16 _133899 s P f) = (term17 _133899 s P f)) : (term17 _133899 s P f) = (term16 _133899 s P f).
Proof. exact (SYM (@lem7555081 _133899 s P f h1)). Qed.
Lemma lem7555083 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) (h1 : (term17 _133899 s P f) = (term16 _133899 s P f)) : (term17 _133899 s P f) = (term16 _133899 s P f).
Proof. exact (h1). Qed.
Lemma lem7555084 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) (h1 : (term17 _133899 s P f) = (term16 _133899 s P f)) : (term16 _133899 s P f) = (term17 _133899 s P f).
Proof. exact (SYM (@lem7555083 _133899 s P f h1)). Qed.
Lemma lem7555085 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : ((term16 _133899 s P f) = (term17 _133899 s P f)) = ((term17 _133899 s P f) = (term16 _133899 s P f)).
Proof. exact (prop_ext (fun h1 : (term16 _133899 s P f) = (term17 _133899 s P f) => @lem7555082 _133899 s P f h1) (fun h1 : (term17 _133899 s P f) = (term16 _133899 s P f) => @lem7555084 _133899 s P f h1)). Qed.
Lemma lem7555086 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term18 _133899 s P) = (term19 _133899 s P).
Proof. exact (fun_ext (fun f : _133899 -> real => @lem7555085 _133899 s P f)). Qed.
Lemma lem7555087 {_133899 : Type'} : (@all (_133899 -> real)) = (@all (_133899 -> real)).
Proof. exact (eq_refl (@all (_133899 -> real))). Qed.
Lemma lem7555088 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term20 _133899 s P) = (term21 _133899 s P).
Proof. exact (MK_COMB (@lem7555087 _133899) (@lem7555086 _133899 s P)). Qed.
Lemma lem7555089 {_133899 : Type'} (P : _133899 -> Prop) : (term22 _133899 P) = (term23 _133899 P).
Proof. exact (fun_ext (fun s : _133899 -> Prop => @lem7555088 _133899 s P)). Qed.
Lemma lem7555090 {_133899 : Type'} : (@all (_133899 -> Prop)) = (@all (_133899 -> Prop)).
Proof. exact (eq_refl (@all (_133899 -> Prop))). Qed.
Lemma lem7555091 {_133899 : Type'} (P : _133899 -> Prop) : (term24 _133899 P) = (term25 _133899 P).
Proof. exact (MK_COMB (@lem7555090 _133899) (@lem7555089 _133899 P)). Qed.
Lemma lem7555092 {_133899 : Type'} : (term26 _133899) = (term27 _133899).
Proof. exact (fun_ext (fun P : _133899 -> Prop => @lem7555091 _133899 P)). Qed.
Lemma lem7555093 {_133899 : Type'} : (@all (_133899 -> Prop)) = (@all (_133899 -> Prop)).
Proof. exact (eq_refl (@all (_133899 -> Prop))). Qed.
Lemma lem7555094 {_133899 : Type'} : (term28 _133899) = (term29 _133899).
Proof. exact (MK_COMB (@lem7555093 _133899) (@lem7555092 _133899)). Qed.
Lemma lem7555095 {_133899 : Type'} : term29 _133899.
Proof. exact (EQ_MP (@lem7555094 _133899) (@lem7157061 _133899)). Qed.
Lemma lem7555096 {_133899 : Type'} (P : _133899 -> Prop) : term30 _133899 P.
Proof. exact (@lem7555095 _133899 P). Qed.
Lemma lem7555097 {_133899 : Type'} (P : _133899 -> Prop) : (term30 _133899 P) = (term25 _133899 P).
Proof. exact (eq_refl (term30 _133899 P)). Qed.
Lemma lem7555098 {_133899 : Type'} (P : _133899 -> Prop) : term25 _133899 P.
Proof. exact (EQ_MP (@lem7555097 _133899 P) (@lem7555096 _133899 P)). Qed.
Lemma lem7555099 {_133899 : Type'} (P : _133899 -> Prop) (s : _133899 -> Prop) : term31 _133899 P s.
Proof. exact (@lem7555098 _133899 P s). Qed.
Lemma lem7555100 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : (term31 _133899 P s) = (term21 _133899 s P).
Proof. exact (eq_refl (term31 _133899 P s)). Qed.
Lemma lem7555101 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) : term21 _133899 s P.
Proof. exact (EQ_MP (@lem7555100 _133899 s P) (@lem7555099 _133899 P s)). Qed.
Lemma lem7555102 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : term32 _133899 s P f.
Proof. exact (@lem7555101 _133899 s P f). Qed.
Lemma lem7555103 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term32 _133899 s P f) = ((term17 _133899 s P f) = (term16 _133899 s P f)).
Proof. exact (eq_refl (term32 _133899 s P f)). Qed.
Lemma lem7555105 (x : real) : term33 x.
Proof. exact (@lem1357243 x). Qed.
Lemma lem7555106 (x : real) : (term33 x) = ((term34 x) = term35).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem7555108 {A B : Type'} (b : Prop) : term36 A B b.
Proof. exact (@lem13056 A B b). Qed.
Lemma lem7555109 {A B : Type'} (b : Prop) : (term36 A B b) = (term37 A B b).
Proof. exact (eq_refl (term36 A B b)). Qed.
Lemma lem7555110 {A B : Type'} (b : Prop) : term37 A B b.
Proof. exact (EQ_MP (@lem7555109 A B b) (@lem7555108 A B b)). Qed.
Lemma lem7555111 {A B : Type'} (b : Prop) (f : A -> B) : term38 A B b f.
Proof. exact (@lem7555110 A B b f). Qed.
Lemma lem7555112 {A B : Type'} (b : Prop) (f : A -> B) : (term38 A B b f) = (term39 A B b f).
Proof. exact (eq_refl (term38 A B b f)). Qed.
Lemma lem7555113 {A B : Type'} (b : Prop) (f : A -> B) : term39 A B b f.
Proof. exact (EQ_MP (@lem7555112 A B b f) (@lem7555111 A B b f)). Qed.
Lemma lem7555114 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : term40 A B b f g.
Proof. exact (@lem7555113 A B b f g). Qed.
Lemma lem7555115 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : (term40 A B b f g) = (term41 A B b f g).
Proof. exact (eq_refl (term40 A B b f g)). Qed.
Lemma lem7555116 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : term41 A B b f g.
Proof. exact (EQ_MP (@lem7555115 A B b f g) (@lem7555114 A B b f g)). Qed.
Lemma lem7555117 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : term42 A B b f g x.
Proof. exact (@lem7555116 A B b f g x). Qed.
Lemma lem7555118 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (term42 A B b f g x) = ((@COND (A -> B) b f g x) = (term43 A B b f g x)).
Proof. exact (eq_refl (term42 A B b f g x)). Qed.
Lemma lem7555120 {A B : Type'} (b : Prop) : term44 A B b.
Proof. exact (@lem12958 A B b). Qed.
Lemma lem7555121 {A B : Type'} (b : Prop) : (term44 A B b) = (term45 A B b).
Proof. exact (eq_refl (term44 A B b)). Qed.
Lemma lem7555122 {A B : Type'} (b : Prop) : term45 A B b.
Proof. exact (EQ_MP (@lem7555121 A B b) (@lem7555120 A B b)). Qed.
Lemma lem7555123 {A B : Type'} (b : Prop) (f : A -> B) : term46 A B b f.
Proof. exact (@lem7555122 A B b f). Qed.
Lemma lem7555124 {A B : Type'} (b : Prop) (f : A -> B) : (term46 A B b f) = (term47 A B b f).
Proof. exact (eq_refl (term46 A B b f)). Qed.
Lemma lem7555125 {A B : Type'} (b : Prop) (f : A -> B) : term47 A B b f.
Proof. exact (EQ_MP (@lem7555124 A B b f) (@lem7555123 A B b f)). Qed.
Lemma lem7555126 {A B : Type'} (b : Prop) (f : A -> B) (x : A) : term48 A B b f x.
Proof. exact (@lem7555125 A B b f x). Qed.
Lemma lem7555127 {A B : Type'} (b : Prop) (x : A) (f : A -> B) : (term48 A B b f x) = (term49 A B b x f).
Proof. exact (eq_refl (term48 A B b f x)). Qed.
Lemma lem7555128 {A B : Type'} (b : Prop) (x : A) (f : A -> B) : term49 A B b x f.
Proof. exact (EQ_MP (@lem7555127 A B b x f) (@lem7555126 A B b f x)). Qed.
Lemma lem7555129 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : term50 A B b x f y.
Proof. exact (@lem7555128 A B b x f y). Qed.
Lemma lem7555130 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term50 A B b x f y) = ((term51 A B f b x y) = (term52 A B b x f y)).
Proof. exact (eq_refl (term50 A B b x f y)). Qed.
Lemma lem7555132 (f : nat -> real) : term53 f.
Proof. exact (@lem7210115 f). Qed.
Lemma lem7555133 (f : nat -> real) : (term53 f) = (term54 f).
Proof. exact (eq_refl (term53 f)). Qed.
Lemma lem7555134 (f : nat -> real) : term54 f.
Proof. exact (EQ_MP (@lem7555133 f) (@lem7555132 f)). Qed.
Lemma lem7555135 (f : nat -> real) (g : nat -> real) : term55 f g.
Proof. exact (@lem7555134 f g). Qed.
Lemma lem7555136 (f : nat -> real) (g : nat -> real) : (term55 f g) = (term56 f g).
Proof. exact (eq_refl (term55 f g)). Qed.
Lemma lem7555137 (f : nat -> real) (g : nat -> real) : term56 f g.
Proof. exact (EQ_MP (@lem7555136 f g) (@lem7555135 f g)). Qed.
Lemma lem7555138 (f : nat -> real) (g : nat -> real) (m : nat) : term57 f g m.
Proof. exact (@lem7555137 f g m). Qed.
Lemma lem7555139 (f : nat -> real) (m : nat) (g : nat -> real) : (term57 f g m) = (term58 f m g).
Proof. exact (eq_refl (term57 f g m)). Qed.
Lemma lem7555140 (f : nat -> real) (m : nat) (g : nat -> real) : term58 f m g.
Proof. exact (EQ_MP (@lem7555139 f m g) (@lem7555138 f g m)). Qed.
Lemma lem7555141 (f : nat -> real) (m : nat) (g : nat -> real) (n : nat) : term59 f m g n.
Proof. exact (@lem7555140 f m g n). Qed.
Lemma lem7555142 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term59 f m g n) = ((term60 m n f g) = (term61 f m n g)).
Proof. exact (eq_refl (term59 f m g n)). Qed.
Lemma lem7555144 (x : real) : term62 x.
Proof. exact (@lem1487144 x). Qed.
Lemma lem7555145 (x : real) : (term62 x) = (term63 x).
Proof. exact (eq_refl (term62 x)). Qed.
Lemma lem7555146 (x : real) : term63 x.
Proof. exact (EQ_MP (@lem7555145 x) (@lem7555144 x)). Qed.
Lemma lem7555147 (x : real) (y : real) : term64 x y.
Proof. exact (@lem7555146 x y). Qed.
Lemma lem7555148 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (eq_refl (term64 x y)). Qed.
Lemma lem7555149 (x : real) (y : real) : term65 x y.
Proof. exact (EQ_MP (@lem7555148 x y) (@lem7555147 x y)). Qed.
Lemma lem7555150 (x : real) (y : real) (z : real) : term66 x y z.
Proof. exact (@lem7555149 x y z). Qed.
Lemma lem7555151 (x : real) (y : real) (z : real) : (term66 x y z) = ((term67 x y z) = (term68 x y z)).
Proof. exact (eq_refl (term66 x y z)). Qed.
Lemma lem7555153 {A : Type'} (P : A -> Prop) : term69 A P.
Proof. exact (@lem6644 A P). Qed.
Lemma lem7555154 {A : Type'} (P : A -> Prop) : (term69 A P) = (term70 A P).
Proof. exact (eq_refl (term69 A P)). Qed.
Lemma lem7555155 {A : Type'} (P : A -> Prop) : term70 A P.
Proof. exact (EQ_MP (@lem7555154 A P) (@lem7555153 A P)). Qed.
Lemma lem7555156 {A : Type'} (P : A -> Prop) (Q : Prop) : term71 A P Q.
Proof. exact (@lem7555155 A P Q). Qed.
Lemma lem7555157 {A : Type'} (P : A -> Prop) (Q : Prop) : (term71 A P Q) = ((term72 A P Q) = (term73 A P Q)).
Proof. exact (eq_refl (term71 A P Q)). Qed.
Lemma lem7555159 (p : real -> real) : term74 p.
Proof. exact (@lem7553488 p). Qed.
Lemma lem7555160 (p : real -> real) : (term74 p) = ((polynomial_function p) = (term75 p)).
Proof. exact (eq_refl (term74 p)). Qed.
Lemma lem7555163 (p : Prop) (q : Prop) (r : Prop) : (term76 p q r) = (term77 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7555164 (p : real -> real) (q : real -> real) : (term78 p q) = (term79 p q).
Proof. exact (@lem7555163 (polynomial_function p) (polynomial_function q) (term80 p q)). Qed.
Lemma lem7555168 (p : real -> real) : (polynomial_function p) = (term75 p).
Proof. exact (EQ_MP (@lem7555160 p) (@lem7555159 p)). Qed.
Lemma lem7555183 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555184 (p : real -> real) : (term81 p) = (term82 p).
Proof. exact (MK_COMB (@lem7555183) (@lem7555168 p)). Qed.
Lemma lem7555188 (p : real -> real) : (polynomial_function p) = (term75 p).
Proof. exact (EQ_MP (@lem7555160 p) (@lem7555159 p)). Qed.
Lemma lem7555189 (q : real -> real) : (polynomial_function q) = (term75 q).
Proof. exact (@lem7555188 q). Qed.
Lemma lem7555204 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555205 (q : real -> real) : (term81 q) = (term82 q).
Proof. exact (MK_COMB (@lem7555204) (@lem7555189 q)). Qed.
Lemma lem7555207 (p : real -> real) : (polynomial_function p) = (term75 p).
Proof. exact (EQ_MP (@lem7555160 p) (@lem7555159 p)). Qed.
Lemma lem7555208 (p : real -> real) (q : real -> real) : (term80 p q) = (term83 p q).
Proof. exact (@lem7555207 (term84 p q)). Qed.
Lemma lem7555224 {A B : Type'} (f : A -> B) (y : A) : (term85 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7555225 (f : real -> real) (y : real) : (term86 f y) = (f y).
Proof. exact (@lem7555224 real real f y). Qed.
Lemma lem7555226 (p : real -> real) (q : real -> real) (x : real) : (term87 p q x) = (term88 p q x).
Proof. exact (@lem7555225 (term84 p q) x). Qed.
Lemma lem7555227 (p : real -> real) (q : real -> real) (x : real) : (term88 p q x) = (term89 p q x).
Proof. exact (eq_refl (term88 p q x)). Qed.
Lemma lem7555228 (p : real -> real) (q : real -> real) : (term90 p q) = (term84 p q).
Proof. exact (fun_ext (fun x : real => @lem7555227 p q x)). Qed.
Lemma lem7555229 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7555230 (p : real -> real) (q : real -> real) (x : real) : (term87 p q x) = (term88 p q x).
Proof. exact (MK_COMB (@lem7555228 p q) (@lem7555229 x)). Qed.
Lemma lem7555231 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7555232 (p : real -> real) (q : real -> real) (x : real) : (term91 p q x) = (term92 p q x).
Proof. exact (MK_COMB (@lem7555231) (@lem7555230 p q x)). Qed.
Lemma lem7555233 (p : real -> real) (q : real -> real) (x : real) : (term88 p q x) = (term89 p q x).
Proof. exact (eq_refl (term88 p q x)). Qed.
Lemma lem7555234 (p : real -> real) (q : real -> real) (x : real) : ((term87 p q x) = (term88 p q x)) = ((term88 p q x) = (term89 p q x)).
Proof. exact (MK_COMB (@lem7555232 p q x) (@lem7555233 p q x)). Qed.
Lemma lem7555235 (p : real -> real) (q : real -> real) (x : real) : (term88 p q x) = (term89 p q x).
Proof. exact (EQ_MP (@lem7555234 p q x) (@lem7555226 p q x)). Qed.
Lemma lem7555236 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7555237 (p : real -> real) (q : real -> real) (x : real) : (term92 p q x) = (term93 p q x).
Proof. exact (MK_COMB (@lem7555236) (@lem7555235 p q x)). Qed.
Lemma lem7555238 (m : nat) (c : nat -> real) (x : real) : (term94 m c x) = (term94 m c x).
Proof. exact (eq_refl (term94 m c x)). Qed.
Lemma lem7555239 (p : real -> real) (q : real -> real) (m : nat) (c : nat -> real) (x : real) : ((term88 p q x) = (term94 m c x)) = ((term89 p q x) = (term94 m c x)).
Proof. exact (MK_COMB (@lem7555237 p q x) (@lem7555238 m c x)). Qed.
Lemma lem7555242 (p : real -> real) (q : real -> real) (m : nat) (c : nat -> real) : (term95 p q m c) = (term96 p q m c).
Proof. exact (fun_ext (fun x : real => @lem7555239 p q m c x)). Qed.
Lemma lem7555243 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7555244 (p : real -> real) (q : real -> real) (m : nat) (c : nat -> real) : (term97 p q m c) = (term98 p q m c).
Proof. exact (MK_COMB (@lem7555243) (@lem7555242 p q m c)). Qed.
Lemma lem7555249 (p : real -> real) (q : real -> real) (m : nat) : (term99 p q m) = (term100 p q m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7555244 p q m c)). Qed.
Lemma lem7555250 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7555251 (p : real -> real) (q : real -> real) (m : nat) : (term101 p q m) = (term102 p q m).
Proof. exact (MK_COMB (@lem7555250) (@lem7555249 p q m)). Qed.
Lemma lem7555256 (p : real -> real) (q : real -> real) : (term103 p q) = (term104 p q).
Proof. exact (fun_ext (fun m : nat => @lem7555251 p q m)). Qed.
Lemma lem7555257 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7555258 (p : real -> real) (q : real -> real) : (term83 p q) = (term105 p q).
Proof. exact (MK_COMB (@lem7555257) (@lem7555256 p q)). Qed.
Lemma lem7555263 (p : real -> real) (q : real -> real) : (term80 p q) = (term105 p q).
Proof. exact (TRANS (@lem7555208 p q) (@lem7555258 p q)). Qed.
Lemma lem7555264 (p : real -> real) (q : real -> real) : (term106 p q) = (term107 p q).
Proof. exact (MK_COMB (@lem7555205 q) (@lem7555263 p q)). Qed.
Lemma lem7555266 {A : Type'} (P : A -> Prop) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem7555157 A P Q) (@lem7555156 A P Q)). Qed.
Lemma lem7555267 (P : nat -> Prop) (Q : Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem7555266 nat P Q). Qed.
Lemma lem7555268 (p : real -> real) (q : real -> real) : (term110 p q) = (term111 p q).
Proof. exact (@lem7555267 (term112 q) (term105 p q)). Qed.
Lemma lem7555269 (q : real -> real) (m : nat) : (term113 q m) = (term114 q m).
Proof. exact (eq_refl (term113 q m)). Qed.
Lemma lem7555270 (q : real -> real) : (term115 q) = (term112 q).
Proof. exact (fun_ext (fun m : nat => @lem7555269 q m)). Qed.
Lemma lem7555271 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7555272 (q : real -> real) : (term116 q) = (term75 q).
Proof. exact (MK_COMB (@lem7555271) (@lem7555270 q)). Qed.
Lemma lem7555273 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555274 (q : real -> real) : (term117 q) = (term82 q).
Proof. exact (MK_COMB (@lem7555273) (@lem7555272 q)). Qed.
Lemma lem7555275 (p : real -> real) (q : real -> real) : (term105 p q) = (term105 p q).
Proof. exact (eq_refl (term105 p q)). Qed.
Lemma lem7555276 (p : real -> real) (q : real -> real) : (term110 p q) = (term107 p q).
Proof. exact (MK_COMB (@lem7555274 q) (@lem7555275 p q)). Qed.
Lemma lem7555277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7555278 (p : real -> real) (q : real -> real) : (term118 p q) = (term119 p q).
Proof. exact (MK_COMB (@lem7555277) (@lem7555276 p q)). Qed.
Lemma lem7555279 (q : real -> real) (m : nat) : (term113 q m) = (term114 q m).
Proof. exact (eq_refl (term113 q m)). Qed.
Lemma lem7555280 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555281 (q : real -> real) (m : nat) : (term120 q m) = (term121 q m).
Proof. exact (MK_COMB (@lem7555280) (@lem7555279 q m)). Qed.
Lemma lem7555282 (p : real -> real) (q : real -> real) : (term105 p q) = (term105 p q).
Proof. exact (eq_refl (term105 p q)). Qed.
Lemma lem7555283 (m : nat) (p : real -> real) (q : real -> real) : (term122 m p q) = (term123 m p q).
Proof. exact (MK_COMB (@lem7555281 q m) (@lem7555282 p q)). Qed.
Lemma lem7555284 (p : real -> real) (q : real -> real) : (term124 p q) = (term125 p q).
Proof. exact (fun_ext (fun m : nat => @lem7555283 m p q)). Qed.
Lemma lem7555285 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7555286 (p : real -> real) (q : real -> real) : (term111 p q) = (term126 p q).
Proof. exact (MK_COMB (@lem7555285) (@lem7555284 p q)). Qed.
Lemma lem7555287 (p : real -> real) (q : real -> real) : ((term110 p q) = (term111 p q)) = ((term107 p q) = (term126 p q)).
Proof. exact (MK_COMB (@lem7555278 p q) (@lem7555286 p q)). Qed.
Lemma lem7555288 (p : real -> real) (q : real -> real) : (term107 p q) = (term126 p q).
Proof. exact (EQ_MP (@lem7555287 p q) (@lem7555268 p q)). Qed.
Lemma lem7555294 {A : Type'} (P : A -> Prop) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem7555157 A P Q) (@lem7555156 A P Q)). Qed.
Lemma lem7555295 (P : type1010) (Q : Prop) : (term127 P Q) = (term128 P Q).
Proof. exact (@lem7555294 (nat -> real) P Q). Qed.
Lemma lem7555296 (m : nat) (p : real -> real) (q : real -> real) : (term129 m p q) = (term130 m p q).
Proof. exact (@lem7555295 (term131 q m) (term105 p q)). Qed.
Lemma lem7555297 (q : real -> real) (m : nat) (c : nat -> real) : (term132 q m c) = (term133 q m c).
Proof. exact (eq_refl (term132 q m c)). Qed.
Lemma lem7555298 (q : real -> real) (m : nat) : (term134 q m) = (term131 q m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7555297 q m c)). Qed.
Lemma lem7555299 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7555300 (q : real -> real) (m : nat) : (term135 q m) = (term114 q m).
Proof. exact (MK_COMB (@lem7555299) (@lem7555298 q m)). Qed.
Lemma lem7555301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555302 (q : real -> real) (m : nat) : (term136 q m) = (term121 q m).
Proof. exact (MK_COMB (@lem7555301) (@lem7555300 q m)). Qed.
Lemma lem7555303 (p : real -> real) (q : real -> real) : (term105 p q) = (term105 p q).
Proof. exact (eq_refl (term105 p q)). Qed.
Lemma lem7555304 (m : nat) (p : real -> real) (q : real -> real) : (term129 m p q) = (term123 m p q).
Proof. exact (MK_COMB (@lem7555302 q m) (@lem7555303 p q)). Qed.
Lemma lem7555305 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7555306 (m : nat) (p : real -> real) (q : real -> real) : (term137 m p q) = (term138 m p q).
Proof. exact (MK_COMB (@lem7555305) (@lem7555304 m p q)). Qed.
Lemma lem7555307 (q : real -> real) (m : nat) (c : nat -> real) : (term132 q m c) = (term133 q m c).
Proof. exact (eq_refl (term132 q m c)). Qed.
Lemma lem7555308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555309 (q : real -> real) (m : nat) (c : nat -> real) : (term139 q m c) = (term140 q m c).
Proof. exact (MK_COMB (@lem7555308) (@lem7555307 q m c)). Qed.
Lemma lem7555310 (p : real -> real) (q : real -> real) : (term105 p q) = (term105 p q).
Proof. exact (eq_refl (term105 p q)). Qed.
Lemma lem7555311 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) : (term141 m c p q) = (term142 m c p q).
Proof. exact (MK_COMB (@lem7555309 q m c) (@lem7555310 p q)). Qed.
Lemma lem7555312 (m : nat) (p : real -> real) (q : real -> real) : (term143 m p q) = (term144 m p q).
Proof. exact (fun_ext (fun c : nat -> real => @lem7555311 m c p q)). Qed.
Lemma lem7555313 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7555314 (m : nat) (p : real -> real) (q : real -> real) : (term130 m p q) = (term145 m p q).
Proof. exact (MK_COMB (@lem7555313) (@lem7555312 m p q)). Qed.
Lemma lem7555315 (m : nat) (p : real -> real) (q : real -> real) : ((term129 m p q) = (term130 m p q)) = ((term123 m p q) = (term145 m p q)).
Proof. exact (MK_COMB (@lem7555306 m p q) (@lem7555314 m p q)). Qed.
Lemma lem7555316 (m : nat) (p : real -> real) (q : real -> real) : (term123 m p q) = (term145 m p q).
Proof. exact (EQ_MP (@lem7555315 m p q) (@lem7555296 m p q)). Qed.
Lemma lem7555343 (p : real -> real) (q : real -> real) : (term125 p q) = (term146 p q).
Proof. exact (fun_ext (fun m : nat => @lem7555316 m p q)). Qed.
Lemma lem7555344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7555345 (p : real -> real) (q : real -> real) : (term126 p q) = (term147 p q).
Proof. exact (MK_COMB (@lem7555344) (@lem7555343 p q)). Qed.
Lemma lem7555350 (p : real -> real) (q : real -> real) : (term107 p q) = (term147 p q).
Proof. exact (TRANS (@lem7555288 p q) (@lem7555345 p q)). Qed.
Lemma lem7555351 (p : real -> real) (q : real -> real) : (term106 p q) = (term147 p q).
Proof. exact (TRANS (@lem7555264 p q) (@lem7555350 p q)). Qed.
Lemma lem7555352 (p : real -> real) (q : real -> real) : (term79 p q) = (term148 p q).
Proof. exact (MK_COMB (@lem7555184 p) (@lem7555351 p q)). Qed.
Lemma lem7555354 {A : Type'} (P : A -> Prop) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem7555157 A P Q) (@lem7555156 A P Q)). Qed.
Lemma lem7555355 (P : nat -> Prop) (Q : Prop) : (term108 P Q) = (term109 P Q).
Proof. exact (@lem7555354 nat P Q). Qed.
Lemma lem7555356 (p : real -> real) (q : real -> real) : (term149 p q) = (term150 p q).
Proof. exact (@lem7555355 (term112 p) (term147 p q)). Qed.
Lemma lem7555357 (p : real -> real) (m : nat) : (term113 p m) = (term114 p m).
Proof. exact (eq_refl (term113 p m)). Qed.
Lemma lem7555358 (p : real -> real) : (term115 p) = (term112 p).
Proof. exact (fun_ext (fun m : nat => @lem7555357 p m)). Qed.
Lemma lem7555359 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7555360 (p : real -> real) : (term116 p) = (term75 p).
Proof. exact (MK_COMB (@lem7555359) (@lem7555358 p)). Qed.
Lemma lem7555361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555362 (p : real -> real) : (term117 p) = (term82 p).
Proof. exact (MK_COMB (@lem7555361) (@lem7555360 p)). Qed.
Lemma lem7555363 (p : real -> real) (q : real -> real) : (term147 p q) = (term147 p q).
Proof. exact (eq_refl (term147 p q)). Qed.
Lemma lem7555364 (p : real -> real) (q : real -> real) : (term149 p q) = (term148 p q).
Proof. exact (MK_COMB (@lem7555362 p) (@lem7555363 p q)). Qed.
Lemma lem7555365 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7555366 (p : real -> real) (q : real -> real) : (term151 p q) = (term152 p q).
Proof. exact (MK_COMB (@lem7555365) (@lem7555364 p q)). Qed.
Lemma lem7555367 (p : real -> real) (m : nat) : (term113 p m) = (term114 p m).
Proof. exact (eq_refl (term113 p m)). Qed.
Lemma lem7555368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555369 (p : real -> real) (m : nat) : (term120 p m) = (term121 p m).
Proof. exact (MK_COMB (@lem7555368) (@lem7555367 p m)). Qed.
Lemma lem7555370 (p : real -> real) (q : real -> real) : (term147 p q) = (term147 p q).
Proof. exact (eq_refl (term147 p q)). Qed.
Lemma lem7555371 (m : nat) (p : real -> real) (q : real -> real) : (term153 m p q) = (term154 m p q).
Proof. exact (MK_COMB (@lem7555369 p m) (@lem7555370 p q)). Qed.
Lemma lem7555372 (p : real -> real) (q : real -> real) : (term155 p q) = (term156 p q).
Proof. exact (fun_ext (fun m : nat => @lem7555371 m p q)). Qed.
Lemma lem7555373 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7555374 (p : real -> real) (q : real -> real) : (term150 p q) = (term157 p q).
Proof. exact (MK_COMB (@lem7555373) (@lem7555372 p q)). Qed.
Lemma lem7555375 (p : real -> real) (q : real -> real) : ((term149 p q) = (term150 p q)) = ((term148 p q) = (term157 p q)).
Proof. exact (MK_COMB (@lem7555366 p q) (@lem7555374 p q)). Qed.
Lemma lem7555376 (p : real -> real) (q : real -> real) : (term148 p q) = (term157 p q).
Proof. exact (EQ_MP (@lem7555375 p q) (@lem7555356 p q)). Qed.
Lemma lem7555382 {A : Type'} (P : A -> Prop) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem7555157 A P Q) (@lem7555156 A P Q)). Qed.
Lemma lem7555383 (P : type1010) (Q : Prop) : (term127 P Q) = (term128 P Q).
Proof. exact (@lem7555382 (nat -> real) P Q). Qed.
Lemma lem7555384 (m : nat) (p : real -> real) (q : real -> real) : (term158 m p q) = (term159 m p q).
Proof. exact (@lem7555383 (term131 p m) (term147 p q)). Qed.
Lemma lem7555385 (p : real -> real) (m : nat) (c : nat -> real) : (term132 p m c) = (term133 p m c).
Proof. exact (eq_refl (term132 p m c)). Qed.
Lemma lem7555386 (p : real -> real) (m : nat) : (term134 p m) = (term131 p m).
Proof. exact (fun_ext (fun c : nat -> real => @lem7555385 p m c)). Qed.
Lemma lem7555387 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7555388 (p : real -> real) (m : nat) : (term135 p m) = (term114 p m).
Proof. exact (MK_COMB (@lem7555387) (@lem7555386 p m)). Qed.
Lemma lem7555389 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555390 (p : real -> real) (m : nat) : (term136 p m) = (term121 p m).
Proof. exact (MK_COMB (@lem7555389) (@lem7555388 p m)). Qed.
Lemma lem7555391 (p : real -> real) (q : real -> real) : (term147 p q) = (term147 p q).
Proof. exact (eq_refl (term147 p q)). Qed.
Lemma lem7555392 (m : nat) (p : real -> real) (q : real -> real) : (term158 m p q) = (term154 m p q).
Proof. exact (MK_COMB (@lem7555390 p m) (@lem7555391 p q)). Qed.
Lemma lem7555393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7555394 (m : nat) (p : real -> real) (q : real -> real) : (term160 m p q) = (term161 m p q).
Proof. exact (MK_COMB (@lem7555393) (@lem7555392 m p q)). Qed.
Lemma lem7555395 (p : real -> real) (m : nat) (c : nat -> real) : (term132 p m c) = (term133 p m c).
Proof. exact (eq_refl (term132 p m c)). Qed.
Lemma lem7555396 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7555397 (p : real -> real) (m : nat) (c : nat -> real) : (term139 p m c) = (term140 p m c).
Proof. exact (MK_COMB (@lem7555396) (@lem7555395 p m c)). Qed.
Lemma lem7555398 (p : real -> real) (q : real -> real) : (term147 p q) = (term147 p q).
Proof. exact (eq_refl (term147 p q)). Qed.
Lemma lem7555399 (m : nat) (c : nat -> real) (p : real -> real) (q : real -> real) : (term162 m c p q) = (term163 m c p q).
Proof. exact (MK_COMB (@lem7555397 p m c) (@lem7555398 p q)). Qed.
Lemma lem7555400 (m : nat) (p : real -> real) (q : real -> real) : (term164 m p q) = (term165 m p q).
Proof. exact (fun_ext (fun c : nat -> real => @lem7555399 m c p q)). Qed.
Lemma lem7555401 : (@all (nat -> real)) = (@all (nat -> real)).
Proof. exact (eq_refl (@all (nat -> real))). Qed.
Lemma lem7555402 (m : nat) (p : real -> real) (q : real -> real) : (term159 m p q) = (term166 m p q).
Proof. exact (MK_COMB (@lem7555401) (@lem7555400 m p q)). Qed.
Lemma lem7555403 (m : nat) (p : real -> real) (q : real -> real) : ((term158 m p q) = (term159 m p q)) = ((term154 m p q) = (term166 m p q)).
Proof. exact (MK_COMB (@lem7555394 m p q) (@lem7555402 m p q)). Qed.
Lemma lem7555404 (m : nat) (p : real -> real) (q : real -> real) : (term154 m p q) = (term166 m p q).
Proof. exact (EQ_MP (@lem7555403 m p q) (@lem7555384 m p q)). Qed.
Lemma lem7555447 (p : real -> real) (q : real -> real) : (term156 p q) = (term167 p q).
Proof. exact (fun_ext (fun m : nat => @lem7555404 m p q)). Qed.
Lemma lem7555448 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7555449 (p : real -> real) (q : real -> real) : (term157 p q) = (term168 p q).
Proof. exact (MK_COMB (@lem7555448) (@lem7555447 p q)). Qed.
Lemma lem7555454 (p : real -> real) (q : real -> real) : (term148 p q) = (term168 p q).
Proof. exact (TRANS (@lem7555376 p q) (@lem7555449 p q)). Qed.
Lemma lem7555455 (p : real -> real) (q : real -> real) : (term79 p q) = (term168 p q).
Proof. exact (TRANS (@lem7555352 p q) (@lem7555454 p q)). Qed.
Lemma lem7555456 (p : real -> real) (q : real -> real) : (term78 p q) = (term168 p q).
Proof. exact (TRANS (@lem7555164 p q) (@lem7555455 p q)). Qed.
Lemma lem7555457 (p : real -> real) (q : real -> real) : (term168 p q) = (term78 p q).
Proof. exact (SYM (@lem7555456 p q)). Qed.
Lemma lem7555458 (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : term133 p m a.
Proof. exact (h1). Qed.
Lemma lem7555459 (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 q n b) : term133 q n b.
Proof. exact (h1). Qed.
Lemma lem7555460 (x : real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : term169 p m a x.
Proof. exact (@lem7555458 p m a h1 x). Qed.
Lemma lem7555461 (p : real -> real) (m : nat) (a : nat -> real) (x : real) : (term169 p m a x) = ((p x) = (term94 m a x)).
Proof. exact (eq_refl (term169 p m a x)). Qed.
Lemma lem7555463 (x : real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 q n b) : term169 q n b x.
Proof. exact (@lem7555459 q n b h1 x). Qed.
Lemma lem7555464 (q : real -> real) (n : nat) (b : nat -> real) (x : real) : (term169 q n b x) = ((q x) = (term94 n b x)).
Proof. exact (eq_refl (term169 q n b x)). Qed.
Lemma lem7555518 (x : real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : (p x) = (term94 m a x).
Proof. exact (EQ_MP (@lem7555461 p m a x) (@lem7555460 x p m a h1)). Qed.
Lemma lem7555519 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7555520 (x : real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : (term170 p x) = (term171 m a x).
Proof. exact (MK_COMB (@lem7555519) (@lem7555518 x p m a h1)). Qed.
Lemma lem7555522 (x : real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 q n b) : (q x) = (term94 n b x).
Proof. exact (EQ_MP (@lem7555464 q n b x) (@lem7555463 x q n b h1)). Qed.
Lemma lem7555523 (x : real) (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term89 p q x) = (term172 m a n b x).
Proof. exact (MK_COMB (@lem7555520 x p m a h1) (@lem7555522 x q n b h2)). Qed.
Lemma lem7555524 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7555525 (x : real) (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term93 p q x) = (term173 m a n b x).
Proof. exact (MK_COMB (@lem7555524) (@lem7555523 x p m a q n b h1 h2)). Qed.
Lemma lem7555526 (_97558 : nat) (c : nat -> real) (x : real) : (term94 _97558 c x) = (term94 _97558 c x).
Proof. exact (eq_refl (term94 _97558 c x)). Qed.
Lemma lem7555527 (_97558 : nat) (c : nat -> real) (x : real) (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : ((term89 p q x) = (term94 _97558 c x)) = ((term172 m a n b x) = (term94 _97558 c x)).
Proof. exact (MK_COMB (@lem7555525 x p m a q n b h1 h2) (@lem7555526 _97558 c x)). Qed.
Lemma lem7555530 (_97558 : nat) (c : nat -> real) (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term96 p q _97558 c) = (term174 m a n b _97558 c).
Proof. exact (fun_ext (fun x : real => @lem7555527 _97558 c x p m a q n b h1 h2)). Qed.
Lemma lem7555531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7555532 (_97558 : nat) (c : nat -> real) (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term98 p q _97558 c) = (term175 m a n b _97558 c).
Proof. exact (MK_COMB (@lem7555531) (@lem7555530 _97558 c p m a q n b h1 h2)). Qed.
Lemma lem7555537 (_97558 : nat) (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term100 p q _97558) = (term176 m a n b _97558).
Proof. exact (fun_ext (fun c : nat -> real => @lem7555532 _97558 c p m a q n b h1 h2)). Qed.
Lemma lem7555538 : (@ex (nat -> real)) = (@ex (nat -> real)).
Proof. exact (eq_refl (@ex (nat -> real))). Qed.
Lemma lem7555539 (_97558 : nat) (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term102 p q _97558) = (term177 m a n b _97558).
Proof. exact (MK_COMB (@lem7555538) (@lem7555537 _97558 p m a q n b h1 h2)). Qed.
Lemma lem7555546 (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term104 p q) = (term178 m a n b).
Proof. exact (fun_ext (fun _97558 : nat => @lem7555539 _97558 p m a q n b h1 h2)). Qed.
Lemma lem7555547 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7555548 (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term105 p q) = (term179 m a n b).
Proof. exact (MK_COMB (@lem7555547) (@lem7555546 p m a q n b h1 h2)). Qed.
Lemma lem7555553 (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term179 m a n b) = (term105 p q).
Proof. exact (SYM (@lem7555548 p m a q n b h1 h2)). Qed.
Lemma lem7555557 {A B : Type'} (f : A -> B) (y : A) : (term85 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7555558 (f : nat -> real) (y : nat) : (term180 f y) = (f y).
Proof. exact (@lem7555557 nat real f y). Qed.
Lemma lem7555559 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : (term181 m a n b i) = (term182 m a n b i).
Proof. exact (@lem7555558 (term183 m a n b) i). Qed.
Lemma lem7555560 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : (term182 m a n b i) = (term184 m a n b i).
Proof. exact (eq_refl (term182 m a n b i)). Qed.
Lemma lem7555561 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) : (term185 m a n b) = (term183 m a n b).
Proof. exact (fun_ext (fun i : nat => @lem7555560 m a n b i)). Qed.
Lemma lem7555562 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7555563 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : (term181 m a n b i) = (term182 m a n b i).
Proof. exact (MK_COMB (@lem7555561 m a n b) (@lem7555562 i)). Qed.
Lemma lem7555564 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7555565 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : (term186 m a n b i) = (term187 m a n b i).
Proof. exact (MK_COMB (@lem7555564) (@lem7555563 m a n b i)). Qed.
Lemma lem7555566 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : (term182 m a n b i) = (term184 m a n b i).
Proof. exact (eq_refl (term182 m a n b i)). Qed.
Lemma lem7555567 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : ((term181 m a n b i) = (term182 m a n b i)) = ((term182 m a n b i) = (term184 m a n b i)).
Proof. exact (MK_COMB (@lem7555565 m a n b i) (@lem7555566 m a n b i)). Qed.
Lemma lem7555568 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : (term182 m a n b i) = (term184 m a n b i).
Proof. exact (EQ_MP (@lem7555567 m a n b i) (@lem7555559 m a n b i)). Qed.
Lemma lem7555569 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7555570 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (i : nat) : (term188 m a n b i) = (term189 m a n b i).
Proof. exact (MK_COMB (@lem7555569) (@lem7555568 m a n b i)). Qed.
Lemma lem7555571 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7555572 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) (i : nat) : (term190 m a n b x i) = (term191 m a n b x i).
Proof. exact (MK_COMB (@lem7555570 m a n b i) (@lem7555571 x i)). Qed.
Lemma lem7555574 (x : real) (y : real) (z : real) : (term67 x y z) = (term68 x y z).
Proof. exact (EQ_MP (@lem7555151 x y z) (@lem7555150 x y z)). Qed.
Lemma lem7555575 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) (i : nat) : (term191 m a n b x i) = (term192 m a n b x i).
Proof. exact (@lem7555574 (term193 m a i) (term193 n b i) (real_pow x i)). Qed.
Lemma lem7555576 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) (i : nat) : (term190 m a n b x i) = (term192 m a n b x i).
Proof. exact (TRANS (@lem7555572 m a n b x i) (@lem7555575 m a n b x i)). Qed.
Lemma lem7555577 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term194 m a n b x) = (term195 m a n b x).
Proof. exact (fun_ext (fun i : nat => @lem7555576 m a n b x i)). Qed.
Lemma lem7555578 (m : nat) (n : nat) : (term196 m n) = (term196 m n).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem7555579 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term197 m a n b x) = (term198 m a n b x).
Proof. exact (MK_COMB (@lem7555578 m n) (@lem7555577 m a n b x)). Qed.
Lemma lem7555581 (f : nat -> real) (m : nat) (n : nat) (g : nat -> real) : (term60 m n f g) = (term61 f m n g).
Proof. exact (EQ_MP (@lem7555142 f m n g) (@lem7555141 f m g n)). Qed.
Lemma lem7555582 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term199 m a n b x) = (term200 a m n b x).
Proof. exact (@lem7555581 (term201 m a x) (NUMERAL 0) (Nat.max m n) (term201 n b x)). Qed.
Lemma lem7555583 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term202 m a x i) = (term203 m a x i).
Proof. exact (eq_refl (term202 m a x i)). Qed.
Lemma lem7555584 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7555585 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term204 m a x i) = (term205 m a x i).
Proof. exact (MK_COMB (@lem7555584) (@lem7555583 m a x i)). Qed.
Lemma lem7555586 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term202 n b x i) = (term203 n b x i).
Proof. exact (eq_refl (term202 n b x i)). Qed.
Lemma lem7555587 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) (i : nat) : (term206 m a n b x i) = (term192 m a n b x i).
Proof. exact (MK_COMB (@lem7555585 m a x i) (@lem7555586 n b x i)). Qed.
Lemma lem7555588 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term207 m a n b x) = (term195 m a n b x).
Proof. exact (fun_ext (fun i : nat => @lem7555587 m a n b x i)). Qed.
Lemma lem7555589 (m : nat) (n : nat) : (term196 m n) = (term196 m n).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem7555590 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term199 m a n b x) = (term198 m a n b x).
Proof. exact (MK_COMB (@lem7555589 m n) (@lem7555588 m a n b x)). Qed.
Lemma lem7555591 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7555592 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term208 m a n b x) = (term209 m a n b x).
Proof. exact (MK_COMB (@lem7555591) (@lem7555590 m a n b x)). Qed.
Lemma lem7555593 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term200 a m n b x) = (term200 a m n b x).
Proof. exact (eq_refl (term200 a m n b x)). Qed.
Lemma lem7555594 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : ((term199 m a n b x) = (term200 a m n b x)) = ((term198 m a n b x) = (term200 a m n b x)).
Proof. exact (MK_COMB (@lem7555592 m a n b x) (@lem7555593 a m n b x)). Qed.
Lemma lem7555595 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term198 m a n b x) = (term200 a m n b x).
Proof. exact (EQ_MP (@lem7555594 a m n b x) (@lem7555582 a m n b x)). Qed.
Lemma lem7555596 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term197 m a n b x) = (term200 a m n b x).
Proof. exact (TRANS (@lem7555579 m a n b x) (@lem7555595 a m n b x)). Qed.
Lemma lem7555597 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term173 m a n b x) = (term173 m a n b x).
Proof. exact (eq_refl (term173 m a n b x)). Qed.
Lemma lem7555598 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : ((term172 m a n b x) = (term197 m a n b x)) = ((term172 m a n b x) = (term200 a m n b x)).
Proof. exact (MK_COMB (@lem7555597 m a n b x) (@lem7555596 a m n b x)). Qed.
Lemma lem7555601 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : ((term172 m a n b x) = (term200 a m n b x)) = ((term172 m a n b x) = (term197 m a n b x)).
Proof. exact (SYM (@lem7555598 a m n b x)). Qed.
Lemma lem7555743 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term51 A B f b x y) = (term52 A B b x f y).
Proof. exact (EQ_MP (@lem7555130 A B b x f y) (@lem7555129 A B b x f y)). Qed.
Lemma lem7555744 (b : Prop) (x : real) (f : type1627) (y : real) : (term210 f b x y) = (term211 b x f y).
Proof. exact (@lem7555743 real (real -> real) b x f y). Qed.
Lemma lem7555745 (m : nat) (a : nat -> real) (i : nat) : (term212 m a i) = (term213 m a i).
Proof. exact (@lem7555744 (Peano.le i m) (a i) real_mul term35). Qed.
Lemma lem7555798 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7555799 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term203 m a x i) = (term214 m a x i).
Proof. exact (MK_COMB (@lem7555745 m a i) (@lem7555798 x i)). Qed.
Lemma lem7555801 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (@COND (A -> B) b f g x) = (term43 A B b f g x).
Proof. exact (EQ_MP (@lem7555118 A B b f g x) (@lem7555117 A B b f g x)). Qed.
Lemma lem7555802 (b : Prop) (f : real -> real) (g : real -> real) (x : real) : (@COND (real -> real) b f g x) = (term215 b f g x).
Proof. exact (@lem7555801 real real b f g x). Qed.
Lemma lem7555803 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term214 m a x i) = (term216 m a x i).
Proof. exact (@lem7555802 (Peano.le i m) (term217 a i) term218 (real_pow x i)). Qed.
Lemma lem7555845 (x : real) : (term34 x) = term35.
Proof. exact (EQ_MP (@lem7555106 x) (@lem7555105 x)). Qed.
Lemma lem7555846 (x : real) (i : nat) : (term219 x i) = term35.
Proof. exact (@lem7555845 (real_pow x i)). Qed.
Lemma lem7555857 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term220 m a x i) = (term220 m a x i).
Proof. exact (eq_refl (term220 m a x i)). Qed.
Lemma lem7555858 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term216 m a x i) = (term221 m a x i).
Proof. exact (MK_COMB (@lem7555857 m a x i) (@lem7555846 x i)). Qed.
Lemma lem7555861 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term214 m a x i) = (term221 m a x i).
Proof. exact (TRANS (@lem7555803 m a x i) (@lem7555858 m a x i)). Qed.
Lemma lem7555862 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term203 m a x i) = (term221 m a x i).
Proof. exact (TRANS (@lem7555799 m a x i) (@lem7555861 m a x i)). Qed.
Lemma lem7555863 (m : nat) (a : nat -> real) (x : real) : (term201 m a x) = (term222 m a x).
Proof. exact (fun_ext (fun i : nat => @lem7555862 m a x i)). Qed.
Lemma lem7555866 (m : nat) (n : nat) : (term196 m n) = (term196 m n).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem7555867 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term223 n m a x) = (term224 n m a x).
Proof. exact (MK_COMB (@lem7555866 m n) (@lem7555863 m a x)). Qed.
Lemma lem7555870 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7555871 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term225 n m a x) = (term226 n m a x).
Proof. exact (MK_COMB (@lem7555870) (@lem7555867 n m a x)). Qed.
Lemma lem7555907 {A B : Type'} (b : Prop) (x : A) (f : A -> B) (y : A) : (term51 A B f b x y) = (term52 A B b x f y).
Proof. exact (EQ_MP (@lem7555130 A B b x f y) (@lem7555129 A B b x f y)). Qed.
Lemma lem7555908 (b : Prop) (x : real) (f : type1627) (y : real) : (term210 f b x y) = (term211 b x f y).
Proof. exact (@lem7555907 real (real -> real) b x f y). Qed.
Lemma lem7555909 (n : nat) (b : nat -> real) (i : nat) : (term212 n b i) = (term213 n b i).
Proof. exact (@lem7555908 (Peano.le i n) (b i) real_mul term35). Qed.
Lemma lem7555962 (x : real) (i : nat) : (real_pow x i) = (real_pow x i).
Proof. exact (eq_refl (real_pow x i)). Qed.
Lemma lem7555963 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term203 n b x i) = (term214 n b x i).
Proof. exact (MK_COMB (@lem7555909 n b i) (@lem7555962 x i)). Qed.
Lemma lem7555965 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) (x : A) : (@COND (A -> B) b f g x) = (term43 A B b f g x).
Proof. exact (EQ_MP (@lem7555118 A B b f g x) (@lem7555117 A B b f g x)). Qed.
Lemma lem7555966 (b : Prop) (f : real -> real) (g : real -> real) (x : real) : (@COND (real -> real) b f g x) = (term215 b f g x).
Proof. exact (@lem7555965 real real b f g x). Qed.
Lemma lem7555967 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term214 n b x i) = (term216 n b x i).
Proof. exact (@lem7555966 (Peano.le i n) (term217 b i) term218 (real_pow x i)). Qed.
Lemma lem7556009 (x : real) : (term34 x) = term35.
Proof. exact (EQ_MP (@lem7555106 x) (@lem7555105 x)). Qed.
Lemma lem7556010 (x : real) (i : nat) : (term219 x i) = term35.
Proof. exact (@lem7556009 (real_pow x i)). Qed.
Lemma lem7556021 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term220 n b x i) = (term220 n b x i).
Proof. exact (eq_refl (term220 n b x i)). Qed.
Lemma lem7556022 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term216 n b x i) = (term221 n b x i).
Proof. exact (MK_COMB (@lem7556021 n b x i) (@lem7556010 x i)). Qed.
Lemma lem7556025 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term214 n b x i) = (term221 n b x i).
Proof. exact (TRANS (@lem7555967 n b x i) (@lem7556022 n b x i)). Qed.
Lemma lem7556026 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term203 n b x i) = (term221 n b x i).
Proof. exact (TRANS (@lem7555963 n b x i) (@lem7556025 n b x i)). Qed.
Lemma lem7556027 (n : nat) (b : nat -> real) (x : real) : (term201 n b x) = (term222 n b x).
Proof. exact (fun_ext (fun i : nat => @lem7556026 n b x i)). Qed.
Lemma lem7556030 (m : nat) (n : nat) : (term196 m n) = (term196 m n).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem7556031 (m : nat) (n : nat) (b : nat -> real) (x : real) : (term227 m n b x) = (term228 m n b x).
Proof. exact (MK_COMB (@lem7556030 m n) (@lem7556027 n b x)). Qed.
Lemma lem7556034 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term200 a m n b x) = (term229 a m n b x).
Proof. exact (MK_COMB (@lem7555871 n m a x) (@lem7556031 m n b x)). Qed.
Lemma lem7556037 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term173 m a n b x) = (term173 m a n b x).
Proof. exact (eq_refl (term173 m a n b x)). Qed.
Lemma lem7556038 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : ((term172 m a n b x) = (term200 a m n b x)) = ((term172 m a n b x) = (term229 a m n b x)).
Proof. exact (MK_COMB (@lem7556037 m a n b x) (@lem7556034 a m n b x)). Qed.
Lemma lem7556043 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : ((term172 m a n b x) = (term229 a m n b x)) = ((term172 m a n b x) = (term200 a m n b x)).
Proof. exact (SYM (@lem7556038 a m n b x)). Qed.
Lemma lem7556047 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term17 _133899 s P f) = (term16 _133899 s P f).
Proof. exact (EQ_MP (@lem7555103 _133899 s P f) (@lem7555102 _133899 s P f)). Qed.
Lemma lem7556048 (s : nat -> Prop) (P : nat -> Prop) (f : nat -> real) : (term230 s P f) = (term231 s P f).
Proof. exact (@lem7556047 nat s P f). Qed.
Lemma lem7556049 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term232 n m a x) = (term233 n m a x).
Proof. exact (@lem7556048 (term234 m n) (term235 m) (term236 a x)). Qed.
Lemma lem7556050 (i : nat) (m : nat) : (term237 m i) = (Peano.le i m).
Proof. exact (eq_refl (term237 m i)). Qed.
Lemma lem7556051 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7556052 (i : nat) (m : nat) : (term238 m i) = (term239 i m).
Proof. exact (MK_COMB (@lem7556051) (@lem7556050 i m)). Qed.
Lemma lem7556053 (a : nat -> real) (x : real) (i : nat) : (term240 a x i) = (term241 a x i).
Proof. exact (eq_refl (term240 a x i)). Qed.
Lemma lem7556054 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term242 m a x i) = (term220 m a x i).
Proof. exact (MK_COMB (@lem7556052 i m) (@lem7556053 a x i)). Qed.
Lemma lem7556055 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7556056 (m : nat) (a : nat -> real) (x : real) (i : nat) : (term243 m a x i) = (term221 m a x i).
Proof. exact (MK_COMB (@lem7556054 m a x i) (@lem7556055)). Qed.
Lemma lem7556057 (m : nat) (a : nat -> real) (x : real) : (term244 m a x) = (term222 m a x).
Proof. exact (fun_ext (fun i : nat => @lem7556056 m a x i)). Qed.
Lemma lem7556058 (m : nat) (n : nat) : (term196 m n) = (term196 m n).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem7556059 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term232 n m a x) = (term224 n m a x).
Proof. exact (MK_COMB (@lem7556058 m n) (@lem7556057 m a x)). Qed.
Lemma lem7556060 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7556061 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term245 n m a x) = (term246 n m a x).
Proof. exact (MK_COMB (@lem7556060) (@lem7556059 n m a x)). Qed.
Lemma lem7556062 (i : nat) (m : nat) : (term237 m i) = (Peano.le i m).
Proof. exact (eq_refl (term237 m i)). Qed.
Lemma lem7556063 (i : nat) (m : nat) (n : nat) : (term247 i m n) = (term247 i m n).
Proof. exact (eq_refl (term247 i m n)). Qed.
Lemma lem7556064 (n : nat) (i : nat) (m : nat) : (term248 n m i) = (term249 n i m).
Proof. exact (MK_COMB (@lem7556063 i m n) (@lem7556062 i m)). Qed.
Lemma lem7556065 (GEN_PVAR_316 : nat) : (@SETSPEC nat GEN_PVAR_316) = (@SETSPEC nat GEN_PVAR_316).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_316)). Qed.
Lemma lem7556066 (GEN_PVAR_316 : nat) (n : nat) (i : nat) (m : nat) : (term250 GEN_PVAR_316 n m i) = (term251 GEN_PVAR_316 n i m).
Proof. exact (MK_COMB (@lem7556065 GEN_PVAR_316) (@lem7556064 n i m)). Qed.
Lemma lem7556067 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7556068 (GEN_PVAR_316 : nat) (n : nat) (m : nat) (i : nat) : (term252 GEN_PVAR_316 n m i) = (term253 GEN_PVAR_316 n m i).
Proof. exact (MK_COMB (@lem7556066 GEN_PVAR_316 n i m) (@lem7556067 i)). Qed.
Lemma lem7556069 (GEN_PVAR_316 : nat) (n : nat) (m : nat) : (term254 GEN_PVAR_316 n m) = (term255 GEN_PVAR_316 n m).
Proof. exact (fun_ext (fun i : nat => @lem7556068 GEN_PVAR_316 n m i)). Qed.
Lemma lem7556070 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7556071 (GEN_PVAR_316 : nat) (n : nat) (m : nat) : (term256 GEN_PVAR_316 n m) = (term257 GEN_PVAR_316 n m).
Proof. exact (MK_COMB (@lem7556070) (@lem7556069 GEN_PVAR_316 n m)). Qed.
Lemma lem7556072 (n : nat) (m : nat) : (term258 n m) = (term259 n m).
Proof. exact (fun_ext (fun GEN_PVAR_316 : nat => @lem7556071 GEN_PVAR_316 n m)). Qed.
Lemma lem7556073 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem7556074 (n : nat) (m : nat) : (term260 n m) = (term261 n m).
Proof. exact (MK_COMB (@lem7556073) (@lem7556072 n m)). Qed.
Lemma lem7556075 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7556076 (n : nat) (m : nat) : (term262 n m) = (term263 n m).
Proof. exact (MK_COMB (@lem7556075) (@lem7556074 n m)). Qed.
Lemma lem7556077 (a : nat -> real) (x : real) : (term236 a x) = (term236 a x).
Proof. exact (eq_refl (term236 a x)). Qed.
Lemma lem7556078 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term233 n m a x) = (term264 n m a x).
Proof. exact (MK_COMB (@lem7556076 n m) (@lem7556077 a x)). Qed.
Lemma lem7556079 (n : nat) (m : nat) (a : nat -> real) (x : real) : ((term232 n m a x) = (term233 n m a x)) = ((term224 n m a x) = (term264 n m a x)).
Proof. exact (MK_COMB (@lem7556061 n m a x) (@lem7556078 n m a x)). Qed.
Lemma lem7556080 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term224 n m a x) = (term264 n m a x).
Proof. exact (EQ_MP (@lem7556079 n m a x) (@lem7556049 n m a x)). Qed.
Lemma lem7556087 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7556088 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term226 n m a x) = (term265 n m a x).
Proof. exact (MK_COMB (@lem7556087) (@lem7556080 n m a x)). Qed.
Lemma lem7556090 {_133899 : Type'} (s : _133899 -> Prop) (P : _133899 -> Prop) (f : _133899 -> real) : (term17 _133899 s P f) = (term16 _133899 s P f).
Proof. exact (EQ_MP (@lem7555103 _133899 s P f) (@lem7555102 _133899 s P f)). Qed.
Lemma lem7556091 (s : nat -> Prop) (P : nat -> Prop) (f : nat -> real) : (term230 s P f) = (term231 s P f).
Proof. exact (@lem7556090 nat s P f). Qed.
Lemma lem7556092 (m : nat) (n : nat) (b : nat -> real) (x : real) : (term266 m n b x) = (term267 m n b x).
Proof. exact (@lem7556091 (term234 m n) (term235 n) (term236 b x)). Qed.
Lemma lem7556093 (i : nat) (n : nat) : (term237 n i) = (Peano.le i n).
Proof. exact (eq_refl (term237 n i)). Qed.
Lemma lem7556094 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem7556095 (i : nat) (n : nat) : (term238 n i) = (term239 i n).
Proof. exact (MK_COMB (@lem7556094) (@lem7556093 i n)). Qed.
Lemma lem7556096 (b : nat -> real) (x : real) (i : nat) : (term240 b x i) = (term241 b x i).
Proof. exact (eq_refl (term240 b x i)). Qed.
Lemma lem7556097 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term242 n b x i) = (term220 n b x i).
Proof. exact (MK_COMB (@lem7556095 i n) (@lem7556096 b x i)). Qed.
Lemma lem7556098 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7556099 (n : nat) (b : nat -> real) (x : real) (i : nat) : (term243 n b x i) = (term221 n b x i).
Proof. exact (MK_COMB (@lem7556097 n b x i) (@lem7556098)). Qed.
Lemma lem7556100 (n : nat) (b : nat -> real) (x : real) : (term244 n b x) = (term222 n b x).
Proof. exact (fun_ext (fun i : nat => @lem7556099 n b x i)). Qed.
Lemma lem7556101 (m : nat) (n : nat) : (term196 m n) = (term196 m n).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem7556102 (m : nat) (n : nat) (b : nat -> real) (x : real) : (term266 m n b x) = (term228 m n b x).
Proof. exact (MK_COMB (@lem7556101 m n) (@lem7556100 n b x)). Qed.
Lemma lem7556103 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7556104 (m : nat) (n : nat) (b : nat -> real) (x : real) : (term268 m n b x) = (term269 m n b x).
Proof. exact (MK_COMB (@lem7556103) (@lem7556102 m n b x)). Qed.
Lemma lem7556105 (i : nat) (n : nat) : (term237 n i) = (Peano.le i n).
Proof. exact (eq_refl (term237 n i)). Qed.
Lemma lem7556106 (i : nat) (m : nat) (n : nat) : (term247 i m n) = (term247 i m n).
Proof. exact (eq_refl (term247 i m n)). Qed.
Lemma lem7556107 (m : nat) (i : nat) (n : nat) : (term270 m n i) = (term271 m i n).
Proof. exact (MK_COMB (@lem7556106 i m n) (@lem7556105 i n)). Qed.
Lemma lem7556108 (GEN_PVAR_316 : nat) : (@SETSPEC nat GEN_PVAR_316) = (@SETSPEC nat GEN_PVAR_316).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_316)). Qed.
Lemma lem7556109 (GEN_PVAR_316 : nat) (m : nat) (i : nat) (n : nat) : (term272 GEN_PVAR_316 m n i) = (term273 GEN_PVAR_316 m i n).
Proof. exact (MK_COMB (@lem7556108 GEN_PVAR_316) (@lem7556107 m i n)). Qed.
Lemma lem7556110 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7556111 (GEN_PVAR_316 : nat) (m : nat) (n : nat) (i : nat) : (term274 GEN_PVAR_316 m n i) = (term275 GEN_PVAR_316 m n i).
Proof. exact (MK_COMB (@lem7556109 GEN_PVAR_316 m i n) (@lem7556110 i)). Qed.
Lemma lem7556112 (GEN_PVAR_316 : nat) (m : nat) (n : nat) : (term276 GEN_PVAR_316 m n) = (term277 GEN_PVAR_316 m n).
Proof. exact (fun_ext (fun i : nat => @lem7556111 GEN_PVAR_316 m n i)). Qed.
Lemma lem7556113 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7556114 (GEN_PVAR_316 : nat) (m : nat) (n : nat) : (term278 GEN_PVAR_316 m n) = (term279 GEN_PVAR_316 m n).
Proof. exact (MK_COMB (@lem7556113) (@lem7556112 GEN_PVAR_316 m n)). Qed.
Lemma lem7556115 (m : nat) (n : nat) : (term280 m n) = (term281 m n).
Proof. exact (fun_ext (fun GEN_PVAR_316 : nat => @lem7556114 GEN_PVAR_316 m n)). Qed.
Lemma lem7556116 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem7556117 (m : nat) (n : nat) : (term282 m n) = (term283 m n).
Proof. exact (MK_COMB (@lem7556116) (@lem7556115 m n)). Qed.
Lemma lem7556118 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7556119 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (MK_COMB (@lem7556118) (@lem7556117 m n)). Qed.
Lemma lem7556120 (b : nat -> real) (x : real) : (term236 b x) = (term236 b x).
Proof. exact (eq_refl (term236 b x)). Qed.
Lemma lem7556121 (m : nat) (n : nat) (b : nat -> real) (x : real) : (term267 m n b x) = (term286 m n b x).
Proof. exact (MK_COMB (@lem7556119 m n) (@lem7556120 b x)). Qed.
Lemma lem7556122 (m : nat) (n : nat) (b : nat -> real) (x : real) : ((term266 m n b x) = (term267 m n b x)) = ((term228 m n b x) = (term286 m n b x)).
Proof. exact (MK_COMB (@lem7556104 m n b x) (@lem7556121 m n b x)). Qed.
Lemma lem7556123 (m : nat) (n : nat) (b : nat -> real) (x : real) : (term228 m n b x) = (term286 m n b x).
Proof. exact (EQ_MP (@lem7556122 m n b x) (@lem7556092 m n b x)). Qed.
Lemma lem7556130 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term229 a m n b x) = (term287 a m n b x).
Proof. exact (MK_COMB (@lem7556088 n m a x) (@lem7556123 m n b x)). Qed.
Lemma lem7556131 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term173 m a n b x) = (term173 m a n b x).
Proof. exact (eq_refl (term173 m a n b x)). Qed.
Lemma lem7556132 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : ((term172 m a n b x) = (term229 a m n b x)) = ((term172 m a n b x) = (term287 a m n b x)).
Proof. exact (MK_COMB (@lem7556131 m a n b x) (@lem7556130 a m n b x)). Qed.
Lemma lem7556135 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : ((term172 m a n b x) = (term287 a m n b x)) = ((term172 m a n b x) = (term229 a m n b x)).
Proof. exact (SYM (@lem7556132 a m n b x)). Qed.
Lemma lem7556136 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7556137 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7556138 : (@sum nat) = (@sum nat).
Proof. exact (eq_refl (@sum nat)). Qed.
Lemma lem7556150 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7556151 (x : nat -> real) : (x = x) = True.
Proof. exact (@lem7556150 (nat -> real) x). Qed.
Lemma lem7556152 (a : nat -> real) (x : real) : ((term236 a x) = (term236 a x)) = True.
Proof. exact (@lem7556151 (term236 a x)). Qed.
Lemma lem7556153 (a : nat -> real) (x : real) : True = ((term236 a x) = (term236 a x)).
Proof. exact (SYM (@lem7556152 a x)). Qed.
Lemma lem7556154 (a : nat -> real) (x : real) : (term236 a x) = (term236 a x).
Proof. exact (EQ_MP (@lem7556153 a x) (@lem0)). Qed.
Lemma lem7556166 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7556167 (x : nat -> real) : (x = x) = True.
Proof. exact (@lem7556166 (nat -> real) x). Qed.
Lemma lem7556168 (b : nat -> real) (x : real) : ((term236 b x) = (term236 b x)) = True.
Proof. exact (@lem7556167 (term236 b x)). Qed.
Lemma lem7556169 (b : nat -> real) (x : real) : True = ((term236 b x) = (term236 b x)).
Proof. exact (SYM (@lem7556168 b x)). Qed.
Lemma lem7556170 (b : nat -> real) (x : real) : (term236 b x) = (term236 b x).
Proof. exact (EQ_MP (@lem7556169 b x) (@lem0)). Qed.
Lemma lem7556174 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem7555076 A s t) (@lem7555075 A s t)). Qed.
Lemma lem7556175 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term288 s t).
Proof. exact (@lem7556174 nat s t). Qed.
Lemma lem7556176 (n : nat) (m : nat) : ((term289 m) = (term261 n m)) = (term290 n m).
Proof. exact (@lem7556175 (term289 m) (term261 n m)). Qed.
Lemma lem7556186 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7555032 m p n) (@lem7555031 m n p)). Qed.
Lemma lem7556187 (x : nat) (m : nat) : (term291 x m) = (term292 x m).
Proof. exact (@lem7556186 (NUMERAL 0) x m). Qed.
Lemma lem7556190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7556191 (x : nat) (m : nat) : (term293 x m) = (term294 x m).
Proof. exact (MK_COMB (@lem7556190) (@lem7556187 x m)). Qed.
Lemma lem7556193 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7555063 _83095 p x) (@lem7555062 _83095 p x)). Qed.
Lemma lem7556194 (p : nat -> Prop) (x : nat) : (term295 x p) = (p x).
Proof. exact (@lem7556193 nat p x). Qed.
Lemma lem7556195 (n : nat) (m : nat) (x : nat) : (term296 x n m) = (term297 n m x).
Proof. exact (@lem7556194 (term298 n m) x). Qed.
Lemma lem7556196 (n : nat) (i : nat) (m : nat) : (term297 n m i) = (term249 n i m).
Proof. exact (eq_refl (term297 n m i)). Qed.
Lemma lem7556197 (GEN_PVAR_316 : nat) : (@SETSPEC nat GEN_PVAR_316) = (@SETSPEC nat GEN_PVAR_316).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_316)). Qed.
Lemma lem7556198 (GEN_PVAR_316 : nat) (n : nat) (i : nat) (m : nat) : (term299 GEN_PVAR_316 n m i) = (term251 GEN_PVAR_316 n i m).
Proof. exact (MK_COMB (@lem7556197 GEN_PVAR_316) (@lem7556196 n i m)). Qed.
Lemma lem7556199 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7556200 (GEN_PVAR_316 : nat) (n : nat) (m : nat) (i : nat) : (term300 GEN_PVAR_316 n m i) = (term253 GEN_PVAR_316 n m i).
Proof. exact (MK_COMB (@lem7556198 GEN_PVAR_316 n i m) (@lem7556199 i)). Qed.
Lemma lem7556201 (GEN_PVAR_316 : nat) (n : nat) (m : nat) : (term301 GEN_PVAR_316 n m) = (term255 GEN_PVAR_316 n m).
Proof. exact (fun_ext (fun i : nat => @lem7556200 GEN_PVAR_316 n m i)). Qed.
Lemma lem7556202 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7556203 (GEN_PVAR_316 : nat) (n : nat) (m : nat) : (term302 GEN_PVAR_316 n m) = (term257 GEN_PVAR_316 n m).
Proof. exact (MK_COMB (@lem7556202) (@lem7556201 GEN_PVAR_316 n m)). Qed.
Lemma lem7556204 (n : nat) (m : nat) : (term303 n m) = (term259 n m).
Proof. exact (fun_ext (fun GEN_PVAR_316 : nat => @lem7556203 GEN_PVAR_316 n m)). Qed.
Lemma lem7556205 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem7556206 (n : nat) (m : nat) : (term304 n m) = (term261 n m).
Proof. exact (MK_COMB (@lem7556205) (@lem7556204 n m)). Qed.
Lemma lem7556207 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem7556208 (x : nat) (n : nat) (m : nat) : (term296 x n m) = (term305 x n m).
Proof. exact (MK_COMB (@lem7556207 x) (@lem7556206 n m)). Qed.
Lemma lem7556209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7556210 (x : nat) (n : nat) (m : nat) : (term306 x n m) = (term307 x n m).
Proof. exact (MK_COMB (@lem7556209) (@lem7556208 x n m)). Qed.
Lemma lem7556211 (n : nat) (x : nat) (m : nat) : (term297 n m x) = (term249 n x m).
Proof. exact (eq_refl (term297 n m x)). Qed.
Lemma lem7556212 (n : nat) (x : nat) (m : nat) : ((term296 x n m) = (term297 n m x)) = ((term305 x n m) = (term249 n x m)).
Proof. exact (MK_COMB (@lem7556210 x n m) (@lem7556211 n x m)). Qed.
Lemma lem7556213 (n : nat) (x : nat) (m : nat) : (term305 x n m) = (term249 n x m).
Proof. exact (EQ_MP (@lem7556212 n x m) (@lem7556195 n m x)). Qed.
Lemma lem7556217 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7555032 m p n) (@lem7555031 m n p)). Qed.
Lemma lem7556218 (x : nat) (m : nat) (n : nat) : (term308 x m n) = (term309 x m n).
Proof. exact (@lem7556217 (NUMERAL 0) x (Nat.max m n)). Qed.
Lemma lem7556221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556222 (x : nat) (m : nat) (n : nat) : (term247 x m n) = (term310 x m n).
Proof. exact (MK_COMB (@lem7556221) (@lem7556218 x m n)). Qed.
Lemma lem7556223 (x : nat) (m : nat) : (Peano.le x m) = (Peano.le x m).
Proof. exact (eq_refl (Peano.le x m)). Qed.
Lemma lem7556224 (n : nat) (x : nat) (m : nat) : (term249 n x m) = (term311 n x m).
Proof. exact (MK_COMB (@lem7556222 x m n) (@lem7556223 x m)). Qed.
Lemma lem7556227 (n : nat) (x : nat) (m : nat) : (term305 x n m) = (term311 n x m).
Proof. exact (TRANS (@lem7556213 n x m) (@lem7556224 n x m)). Qed.
Lemma lem7556228 (n : nat) (x : nat) (m : nat) : ((term291 x m) = (term305 x n m)) = ((term292 x m) = (term311 n x m)).
Proof. exact (MK_COMB (@lem7556191 x m) (@lem7556227 n x m)). Qed.
Lemma lem7556233 (n : nat) (m : nat) : (term312 n m) = (term313 n m).
Proof. exact (fun_ext (fun x : nat => @lem7556228 n x m)). Qed.
Lemma lem7556234 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7556235 (n : nat) (m : nat) : (term290 n m) = (term314 n m).
Proof. exact (MK_COMB (@lem7556234) (@lem7556233 n m)). Qed.
Lemma lem7556240 (n : nat) (m : nat) : ((term289 m) = (term261 n m)) = (term314 n m).
Proof. exact (TRANS (@lem7556176 n m) (@lem7556235 n m)). Qed.
Lemma lem7556241 (n : nat) (m : nat) : (term314 n m) = ((term289 m) = (term261 n m)).
Proof. exact (SYM (@lem7556240 n m)). Qed.
Lemma lem7556245 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term15 A s t).
Proof. exact (EQ_MP (@lem7555076 A s t) (@lem7555075 A s t)). Qed.
Lemma lem7556246 (s : nat -> Prop) (t : nat -> Prop) : (s = t) = (term288 s t).
Proof. exact (@lem7556245 nat s t). Qed.
Lemma lem7556247 (m : nat) (n : nat) : ((term289 n) = (term283 m n)) = (term315 m n).
Proof. exact (@lem7556246 (term289 n) (term283 m n)). Qed.
Lemma lem7556257 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7555032 m p n) (@lem7555031 m n p)). Qed.
Lemma lem7556258 (x : nat) (n : nat) : (term291 x n) = (term292 x n).
Proof. exact (@lem7556257 (NUMERAL 0) x n). Qed.
Lemma lem7556261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7556262 (x : nat) (n : nat) : (term293 x n) = (term294 x n).
Proof. exact (MK_COMB (@lem7556261) (@lem7556258 x n)). Qed.
Lemma lem7556264 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem7555063 _83095 p x) (@lem7555062 _83095 p x)). Qed.
Lemma lem7556265 (p : nat -> Prop) (x : nat) : (term295 x p) = (p x).
Proof. exact (@lem7556264 nat p x). Qed.
Lemma lem7556266 (m : nat) (n : nat) (x : nat) : (term316 x m n) = (term317 m n x).
Proof. exact (@lem7556265 (term318 m n) x). Qed.
Lemma lem7556267 (m : nat) (i : nat) (n : nat) : (term317 m n i) = (term271 m i n).
Proof. exact (eq_refl (term317 m n i)). Qed.
Lemma lem7556268 (GEN_PVAR_316 : nat) : (@SETSPEC nat GEN_PVAR_316) = (@SETSPEC nat GEN_PVAR_316).
Proof. exact (eq_refl (@SETSPEC nat GEN_PVAR_316)). Qed.
Lemma lem7556269 (GEN_PVAR_316 : nat) (m : nat) (i : nat) (n : nat) : (term319 GEN_PVAR_316 m n i) = (term273 GEN_PVAR_316 m i n).
Proof. exact (MK_COMB (@lem7556268 GEN_PVAR_316) (@lem7556267 m i n)). Qed.
Lemma lem7556270 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7556271 (GEN_PVAR_316 : nat) (m : nat) (n : nat) (i : nat) : (term320 GEN_PVAR_316 m n i) = (term275 GEN_PVAR_316 m n i).
Proof. exact (MK_COMB (@lem7556269 GEN_PVAR_316 m i n) (@lem7556270 i)). Qed.
Lemma lem7556272 (GEN_PVAR_316 : nat) (m : nat) (n : nat) : (term321 GEN_PVAR_316 m n) = (term277 GEN_PVAR_316 m n).
Proof. exact (fun_ext (fun i : nat => @lem7556271 GEN_PVAR_316 m n i)). Qed.
Lemma lem7556273 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem7556274 (GEN_PVAR_316 : nat) (m : nat) (n : nat) : (term322 GEN_PVAR_316 m n) = (term279 GEN_PVAR_316 m n).
Proof. exact (MK_COMB (@lem7556273) (@lem7556272 GEN_PVAR_316 m n)). Qed.
Lemma lem7556275 (m : nat) (n : nat) : (term323 m n) = (term281 m n).
Proof. exact (fun_ext (fun GEN_PVAR_316 : nat => @lem7556274 GEN_PVAR_316 m n)). Qed.
Lemma lem7556276 : (@GSPEC nat) = (@GSPEC nat).
Proof. exact (eq_refl (@GSPEC nat)). Qed.
Lemma lem7556277 (m : nat) (n : nat) : (term324 m n) = (term283 m n).
Proof. exact (MK_COMB (@lem7556276) (@lem7556275 m n)). Qed.
Lemma lem7556278 (x : nat) : (@IN nat x) = (@IN nat x).
Proof. exact (eq_refl (@IN nat x)). Qed.
Lemma lem7556279 (x : nat) (m : nat) (n : nat) : (term316 x m n) = (term325 x m n).
Proof. exact (MK_COMB (@lem7556278 x) (@lem7556277 m n)). Qed.
Lemma lem7556280 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7556281 (x : nat) (m : nat) (n : nat) : (term326 x m n) = (term327 x m n).
Proof. exact (MK_COMB (@lem7556280) (@lem7556279 x m n)). Qed.
Lemma lem7556282 (m : nat) (x : nat) (n : nat) : (term317 m n x) = (term271 m x n).
Proof. exact (eq_refl (term317 m n x)). Qed.
Lemma lem7556283 (m : nat) (x : nat) (n : nat) : ((term316 x m n) = (term317 m n x)) = ((term325 x m n) = (term271 m x n)).
Proof. exact (MK_COMB (@lem7556281 x m n) (@lem7556282 m x n)). Qed.
Lemma lem7556284 (m : nat) (x : nat) (n : nat) : (term325 x m n) = (term271 m x n).
Proof. exact (EQ_MP (@lem7556283 m x n) (@lem7556266 m n x)). Qed.
Lemma lem7556288 (m : nat) (p : nat) (n : nat) : (term5 p m n) = (term6 m p n).
Proof. exact (EQ_MP (@lem7555032 m p n) (@lem7555031 m n p)). Qed.
Lemma lem7556289 (x : nat) (m : nat) (n : nat) : (term308 x m n) = (term309 x m n).
Proof. exact (@lem7556288 (NUMERAL 0) x (Nat.max m n)). Qed.
Lemma lem7556292 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556293 (x : nat) (m : nat) (n : nat) : (term247 x m n) = (term310 x m n).
Proof. exact (MK_COMB (@lem7556292) (@lem7556289 x m n)). Qed.
Lemma lem7556294 (x : nat) (n : nat) : (Peano.le x n) = (Peano.le x n).
Proof. exact (eq_refl (Peano.le x n)). Qed.
Lemma lem7556295 (m : nat) (x : nat) (n : nat) : (term271 m x n) = (term328 m x n).
Proof. exact (MK_COMB (@lem7556293 x m n) (@lem7556294 x n)). Qed.
Lemma lem7556298 (m : nat) (x : nat) (n : nat) : (term325 x m n) = (term328 m x n).
Proof. exact (TRANS (@lem7556284 m x n) (@lem7556295 m x n)). Qed.
Lemma lem7556299 (m : nat) (x : nat) (n : nat) : ((term291 x n) = (term325 x m n)) = ((term292 x n) = (term328 m x n)).
Proof. exact (MK_COMB (@lem7556262 x n) (@lem7556298 m x n)). Qed.
Lemma lem7556304 (m : nat) (n : nat) : (term329 m n) = (term330 m n).
Proof. exact (fun_ext (fun x : nat => @lem7556299 m x n)). Qed.
Lemma lem7556305 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7556306 (m : nat) (n : nat) : (term315 m n) = (term331 m n).
Proof. exact (MK_COMB (@lem7556305) (@lem7556304 m n)). Qed.
Lemma lem7556311 (m : nat) (n : nat) : ((term289 n) = (term283 m n)) = (term331 m n).
Proof. exact (TRANS (@lem7556247 m n) (@lem7556306 m n)). Qed.
Lemma lem7556312 (m : nat) (n : nat) : (term331 m n) = ((term289 n) = (term283 m n)).
Proof. exact (SYM (@lem7556311 m n)). Qed.
Lemma lem7556342 (n : nat) (x : nat) (m : nat) : ((term292 x m) = (term311 n x m)) = ((term292 x m) = (term311 n x m)).
Proof. exact (eq_refl ((term292 x m) = (term311 n x m))). Qed.
Lemma lem7556343 (n : nat) (m : nat) : (term313 n m) = (term313 n m).
Proof. exact (fun_ext (fun x : nat => @lem7556342 n x m)). Qed.
Lemma lem7556344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7556346 (n : nat) (m : nat) : (term314 n m) = (term314 n m).
Proof. exact (MK_COMB (@lem7556344) (@lem7556343 n m)). Qed.
Lemma lem7556355 (x : nat) (m : nat) : (term332 x m) = (term333 x m).
Proof. exact (@lem17045 (term334 x) (Peano.le x m)). Qed.
Lemma lem7556367 (x : nat) (m : nat) (n : nat) : (term335 x m n) = (term336 x m n).
Proof. exact (@lem17045 (term334 x) (term337 x m n)). Qed.
Lemma lem7556371 (x : nat) (m : nat) : (term338 x m) = (term338 x m).
Proof. exact (eq_refl (term338 x m)). Qed.
Lemma lem7556373 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556374 (x : nat) (m : nat) (n : nat) : (term339 x m n) = (term340 x m n).
Proof. exact (MK_COMB (@lem7556373) (@lem7556367 x m n)). Qed.
Lemma lem7556375 (n : nat) (x : nat) (m : nat) : (term341 n x m) = (term342 n x m).
Proof. exact (MK_COMB (@lem7556374 x m n) (@lem7556371 x m)). Qed.
Lemma lem7556376 (n : nat) (x : nat) (m : nat) : (term343 n x m) = (term341 n x m).
Proof. exact (@lem17045 (term309 x m n) (Peano.le x m)). Qed.
Lemma lem7556377 (n : nat) (x : nat) (m : nat) : (term343 n x m) = (term342 n x m).
Proof. exact (TRANS (@lem7556376 n x m) (@lem7556375 n x m)). Qed.
Lemma lem7556380 (n : nat) (x : nat) (m : nat) : (term311 n x m) = (term311 n x m).
Proof. exact (eq_refl (term311 n x m)). Qed.
Lemma lem7556381 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556382 (x : nat) (m : nat) : (term344 x m) = (term345 x m).
Proof. exact (MK_COMB (@lem7556381) (@lem7556355 x m)). Qed.
Lemma lem7556383 (n : nat) (x : nat) (m : nat) : (term346 n x m) = (term347 n x m).
Proof. exact (MK_COMB (@lem7556382 x m) (@lem7556380 n x m)). Qed.
Lemma lem7556385 (x : nat) (m : nat) : (term348 x m) = (term348 x m).
Proof. exact (eq_refl (term348 x m)). Qed.
Lemma lem7556386 (n : nat) (x : nat) (m : nat) : (term349 n x m) = (term350 n x m).
Proof. exact (MK_COMB (@lem7556385 x m) (@lem7556377 n x m)). Qed.
Lemma lem7556387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556388 (n : nat) (x : nat) (m : nat) : (term351 n x m) = (term352 n x m).
Proof. exact (MK_COMB (@lem7556387) (@lem7556386 n x m)). Qed.
Lemma lem7556389 (n : nat) (x : nat) (m : nat) : (term353 n x m) = (term354 n x m).
Proof. exact (MK_COMB (@lem7556388 n x m) (@lem7556383 n x m)). Qed.
Lemma lem7556390 (n : nat) (x : nat) (m : nat) : ((term292 x m) = (term311 n x m)) = (term353 n x m).
Proof. exact (@lem17784 (term292 x m) (term311 n x m)). Qed.
Lemma lem7556391 (n : nat) (x : nat) (m : nat) : ((term292 x m) = (term311 n x m)) = (term354 n x m).
Proof. exact (TRANS (@lem7556390 n x m) (@lem7556389 n x m)). Qed.
Lemma lem7556392 (n : nat) (m : nat) : (term313 n m) = (term355 n m).
Proof. exact (fun_ext (fun x : nat => @lem7556391 n x m)). Qed.
Lemma lem7556393 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7556394 (n : nat) (m : nat) : (term314 n m) = (term356 n m).
Proof. exact (MK_COMB (@lem7556393) (@lem7556392 n m)). Qed.
Lemma lem7556395 (n : nat) (m : nat) : (term314 n m) = (term356 n m).
Proof. exact (TRANS (@lem7556346 n m) (@lem7556394 n m)). Qed.
Lemma lem7556396 (n : nat) (x : nat) (m : nat) : (term354 n x m) = (term354 n x m).
Proof. exact (eq_refl (term354 n x m)). Qed.
Lemma lem7556397 (n : nat) (m : nat) : (term355 n m) = (term355 n m).
Proof. exact (fun_ext (fun x : nat => @lem7556396 n x m)). Qed.
Lemma lem7556398 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7556399 (n : nat) (m : nat) : (term356 n m) = (term356 n m).
Proof. exact (MK_COMB (@lem7556398) (@lem7556397 n m)). Qed.
Lemma lem7556428 (n : nat) (m : nat) : (term314 n m) = (term356 n m).
Proof. exact (TRANS (@lem7556395 n m) (@lem7556399 n m)). Qed.
Lemma lem7556515 (n : nat) (x : nat) (m : nat) : (term354 n x m) = (term354 n x m).
Proof. exact (eq_refl (term354 n x m)). Qed.
Lemma lem7556516 (n : nat) (m : nat) : (term355 n m) = (term355 n m).
Proof. exact (fun_ext (fun x : nat => @lem7556515 n x m)). Qed.
Lemma lem7556517 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7556518 (n : nat) (m : nat) : (term356 n m) = (term356 n m).
Proof. exact (MK_COMB (@lem7556517) (@lem7556516 n m)). Qed.
Lemma lem7556521 (n : nat) (m : nat) : (term314 n m) = (term356 n m).
Proof. exact (TRANS (@lem7556428 n m) (@lem7556518 n m)). Qed.
Lemma lem7556523 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556524 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7556523 (NUMERAL 0) x). Qed.
Lemma lem7556525 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556526 (x : nat) : (term359 x) = (term360 x).
Proof. exact (MK_COMB (@lem7556525) (@lem7556524 x)). Qed.
Lemma lem7556528 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556529 (x : nat) (m : nat) : (Peano.le x m) = (term357 x m).
Proof. exact (@lem7556528 x m). Qed.
Lemma lem7556530 (x : nat) (m : nat) : (term292 x m) = (term361 x m).
Proof. exact (MK_COMB (@lem7556526 x) (@lem7556529 x m)). Qed.
Lemma lem7556531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556532 (x : nat) (m : nat) : (term348 x m) = (term362 x m).
Proof. exact (MK_COMB (@lem7556531) (@lem7556530 x m)). Qed.
Lemma lem7556534 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556535 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7556534 (NUMERAL 0) x). Qed.
Lemma lem7556536 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7556537 (x : nat) : (term363 x) = (term364 x).
Proof. exact (MK_COMB (@lem7556536) (@lem7556535 x)). Qed.
Lemma lem7556538 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556539 (x : nat) : (term365 x) = (term366 x).
Proof. exact (MK_COMB (@lem7556538) (@lem7556537 x)). Qed.
Lemma lem7556541 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556542 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term367 x m n).
Proof. exact (@lem7556541 x (Nat.max m n)). Qed.
Lemma lem7556544 (m : nat) (n : nat) : (term368 m n) = (term369 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem7556545 (x : nat) : (term370 x) = (term370 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem7556546 (x : nat) (m : nat) (n : nat) : (term367 x m n) = (term371 x m n).
Proof. exact (MK_COMB (@lem7556545 x) (@lem7556544 m n)). Qed.
Lemma lem7556547 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term371 x m n).
Proof. exact (TRANS (@lem7556542 x m n) (@lem7556546 x m n)). Qed.
Lemma lem7556548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7556549 (x : nat) (m : nat) (n : nat) : (term372 x m n) = (term373 x m n).
Proof. exact (MK_COMB (@lem7556548) (@lem7556547 x m n)). Qed.
Lemma lem7556550 (x : nat) (m : nat) (n : nat) : (term336 x m n) = (term374 x m n).
Proof. exact (MK_COMB (@lem7556539 x) (@lem7556549 x m n)). Qed.
Lemma lem7556551 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556552 (x : nat) (m : nat) (n : nat) : (term340 x m n) = (term375 x m n).
Proof. exact (MK_COMB (@lem7556551) (@lem7556550 x m n)). Qed.
Lemma lem7556554 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556555 (x : nat) (m : nat) : (Peano.le x m) = (term357 x m).
Proof. exact (@lem7556554 x m). Qed.
Lemma lem7556556 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7556557 (x : nat) (m : nat) : (term338 x m) = (term376 x m).
Proof. exact (MK_COMB (@lem7556556) (@lem7556555 x m)). Qed.
Lemma lem7556558 (n : nat) (x : nat) (m : nat) : (term342 n x m) = (term377 n x m).
Proof. exact (MK_COMB (@lem7556552 x m n) (@lem7556557 x m)). Qed.
Lemma lem7556559 (n : nat) (x : nat) (m : nat) : (term350 n x m) = (term378 n x m).
Proof. exact (MK_COMB (@lem7556532 x m) (@lem7556558 n x m)). Qed.
Lemma lem7556560 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556561 (n : nat) (x : nat) (m : nat) : (term352 n x m) = (term379 n x m).
Proof. exact (MK_COMB (@lem7556560) (@lem7556559 n x m)). Qed.
Lemma lem7556563 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556564 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7556563 (NUMERAL 0) x). Qed.
Lemma lem7556565 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7556566 (x : nat) : (term363 x) = (term364 x).
Proof. exact (MK_COMB (@lem7556565) (@lem7556564 x)). Qed.
Lemma lem7556567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556568 (x : nat) : (term365 x) = (term366 x).
Proof. exact (MK_COMB (@lem7556567) (@lem7556566 x)). Qed.
Lemma lem7556570 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556571 (x : nat) (m : nat) : (Peano.le x m) = (term357 x m).
Proof. exact (@lem7556570 x m). Qed.
Lemma lem7556572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7556573 (x : nat) (m : nat) : (term338 x m) = (term376 x m).
Proof. exact (MK_COMB (@lem7556572) (@lem7556571 x m)). Qed.
Lemma lem7556574 (x : nat) (m : nat) : (term333 x m) = (term380 x m).
Proof. exact (MK_COMB (@lem7556568 x) (@lem7556573 x m)). Qed.
Lemma lem7556575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556576 (x : nat) (m : nat) : (term345 x m) = (term381 x m).
Proof. exact (MK_COMB (@lem7556575) (@lem7556574 x m)). Qed.
Lemma lem7556578 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556579 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7556578 (NUMERAL 0) x). Qed.
Lemma lem7556580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556581 (x : nat) : (term359 x) = (term360 x).
Proof. exact (MK_COMB (@lem7556580) (@lem7556579 x)). Qed.
Lemma lem7556583 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556584 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term367 x m n).
Proof. exact (@lem7556583 x (Nat.max m n)). Qed.
Lemma lem7556586 (m : nat) (n : nat) : (term368 m n) = (term369 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem7556587 (x : nat) : (term370 x) = (term370 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem7556588 (x : nat) (m : nat) (n : nat) : (term367 x m n) = (term371 x m n).
Proof. exact (MK_COMB (@lem7556587 x) (@lem7556586 m n)). Qed.
Lemma lem7556589 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term371 x m n).
Proof. exact (TRANS (@lem7556584 x m n) (@lem7556588 x m n)). Qed.
Lemma lem7556590 (x : nat) (m : nat) (n : nat) : (term309 x m n) = (term382 x m n).
Proof. exact (MK_COMB (@lem7556581 x) (@lem7556589 x m n)). Qed.
Lemma lem7556591 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556592 (x : nat) (m : nat) (n : nat) : (term310 x m n) = (term383 x m n).
Proof. exact (MK_COMB (@lem7556591) (@lem7556590 x m n)). Qed.
Lemma lem7556594 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7556595 (x : nat) (m : nat) : (Peano.le x m) = (term357 x m).
Proof. exact (@lem7556594 x m). Qed.
Lemma lem7556596 (n : nat) (x : nat) (m : nat) : (term311 n x m) = (term384 n x m).
Proof. exact (MK_COMB (@lem7556592 x m n) (@lem7556595 x m)). Qed.
Lemma lem7556597 (n : nat) (x : nat) (m : nat) : (term347 n x m) = (term385 n x m).
Proof. exact (MK_COMB (@lem7556576 x m) (@lem7556596 n x m)). Qed.
Lemma lem7556598 (n : nat) (x : nat) (m : nat) : (term354 n x m) = (term386 n x m).
Proof. exact (MK_COMB (@lem7556561 n x m) (@lem7556597 n x m)). Qed.
Lemma lem7556599 (n : nat) (m : nat) : (term355 n m) = (term387 n m).
Proof. exact (fun_ext (fun x : nat => @lem7556598 n x m)). Qed.
Lemma lem7556600 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7556601 (n : nat) (m : nat) : (term356 n m) = (term388 n m).
Proof. exact (MK_COMB (@lem7556600) (@lem7556599 n m)). Qed.
Lemma lem7556602 (n : nat) (m : nat) : (term314 n m) = (term388 n m).
Proof. exact (TRANS (@lem7556521 n m) (@lem7556601 n m)). Qed.
Lemma lem7556603 (m : nat) : term389 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem7556604 (m : nat) : (term389 m) = (term358 m).
Proof. exact (eq_refl (term389 m)). Qed.
Lemma lem7556605 (m : nat) : term358 m.
Proof. exact (EQ_MP (@lem7556604 m) (@lem7556603 m)). Qed.
Lemma lem7556606 (n : nat) : term389 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem7556607 (n : nat) : (term389 n) = (term358 n).
Proof. exact (eq_refl (term389 n)). Qed.
Lemma lem7556608 (n : nat) : term358 n.
Proof. exact (EQ_MP (@lem7556607 n) (@lem7556606 n)). Qed.
Lemma lem7556609 (x : nat) : term389 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem7556610 (x : nat) : (term389 x) = (term358 x).
Proof. exact (eq_refl (term389 x)). Qed.
Lemma lem7556611 (x : nat) : term358 x.
Proof. exact (EQ_MP (@lem7556610 x) (@lem7556609 x)). Qed.
Lemma lem7556612 (_97560 : int) (_97561 : int) (_97559 : int) : (term390 _97560 _97561 _97559) = (term391 _97560 _97561 _97559).
Proof. exact (@lem2318604 (term391 _97560 _97561 _97559)). Qed.
Lemma lem7556651 (_97561 : int) (_97559 : int) : (term392 _97561 _97559) = (term393 _97561 _97559).
Proof. exact (@lem17045 (term394 _97561) (int_le _97561 _97559)). Qed.
Lemma lem7556654 (_97561 : int) : (term395 _97561) = (term394 _97561).
Proof. exact (@lem16933 (term394 _97561)). Qed.
Lemma lem7556657 (_97561 : int) (_97559 : int) (_97560 : int) : (term396 _97561 _97559 _97560) = (term397 _97561 _97559 _97560).
Proof. exact (@lem16933 (term397 _97561 _97559 _97560)). Qed.
Lemma lem7556658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556659 (_97561 : int) : (term398 _97561) = (term399 _97561).
Proof. exact (MK_COMB (@lem7556658) (@lem7556654 _97561)). Qed.
Lemma lem7556660 (_97561 : int) (_97559 : int) (_97560 : int) : (term400 _97561 _97559 _97560) = (term401 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7556659 _97561) (@lem7556657 _97561 _97559 _97560)). Qed.
Lemma lem7556661 (_97561 : int) (_97559 : int) (_97560 : int) : (term402 _97561 _97559 _97560) = (term400 _97561 _97559 _97560).
Proof. exact (@lem17160 (term403 _97561) (term404 _97561 _97559 _97560)). Qed.
Lemma lem7556662 (_97561 : int) (_97559 : int) (_97560 : int) : (term402 _97561 _97559 _97560) = (term401 _97561 _97559 _97560).
Proof. exact (TRANS (@lem7556661 _97561 _97559 _97560) (@lem7556660 _97561 _97559 _97560)). Qed.
Lemma lem7556665 (_97561 : int) (_97559 : int) : (term405 _97561 _97559) = (int_le _97561 _97559).
Proof. exact (@lem16933 (int_le _97561 _97559)). Qed.
Lemma lem7556666 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556667 (_97561 : int) (_97559 : int) (_97560 : int) : (term406 _97561 _97559 _97560) = (term407 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7556666) (@lem7556662 _97561 _97559 _97560)). Qed.
Lemma lem7556668 (_97560 : int) (_97561 : int) (_97559 : int) : (term408 _97560 _97561 _97559) = (term409 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556667 _97561 _97559 _97560) (@lem7556665 _97561 _97559)). Qed.
Lemma lem7556669 (_97560 : int) (_97561 : int) (_97559 : int) : (term410 _97560 _97561 _97559) = (term408 _97560 _97561 _97559).
Proof. exact (@lem17160 (term411 _97561 _97559 _97560) (term412 _97561 _97559)). Qed.
Lemma lem7556670 (_97560 : int) (_97561 : int) (_97559 : int) : (term410 _97560 _97561 _97559) = (term409 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556669 _97560 _97561 _97559) (@lem7556668 _97560 _97561 _97559)). Qed.
Lemma lem7556671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556672 (_97561 : int) (_97559 : int) : (term413 _97561 _97559) = (term414 _97561 _97559).
Proof. exact (MK_COMB (@lem7556671) (@lem7556651 _97561 _97559)). Qed.
Lemma lem7556673 (_97560 : int) (_97561 : int) (_97559 : int) : (term415 _97560 _97561 _97559) = (term416 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556672 _97561 _97559) (@lem7556670 _97560 _97561 _97559)). Qed.
Lemma lem7556674 (_97560 : int) (_97561 : int) (_97559 : int) : (term417 _97560 _97561 _97559) = (term415 _97560 _97561 _97559).
Proof. exact (@lem17160 (term418 _97561 _97559) (term419 _97560 _97561 _97559)). Qed.
Lemma lem7556675 (_97560 : int) (_97561 : int) (_97559 : int) : (term417 _97560 _97561 _97559) = (term416 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556674 _97560 _97561 _97559) (@lem7556673 _97560 _97561 _97559)). Qed.
Lemma lem7556678 (_97561 : int) : (term395 _97561) = (term394 _97561).
Proof. exact (@lem16933 (term394 _97561)). Qed.
Lemma lem7556681 (_97561 : int) (_97559 : int) : (term405 _97561 _97559) = (int_le _97561 _97559).
Proof. exact (@lem16933 (int_le _97561 _97559)). Qed.
Lemma lem7556682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556683 (_97561 : int) : (term398 _97561) = (term399 _97561).
Proof. exact (MK_COMB (@lem7556682) (@lem7556678 _97561)). Qed.
Lemma lem7556684 (_97561 : int) (_97559 : int) : (term420 _97561 _97559) = (term418 _97561 _97559).
Proof. exact (MK_COMB (@lem7556683 _97561) (@lem7556681 _97561 _97559)). Qed.
Lemma lem7556685 (_97561 : int) (_97559 : int) : (term421 _97561 _97559) = (term420 _97561 _97559).
Proof. exact (@lem17160 (term403 _97561) (term412 _97561 _97559)). Qed.
Lemma lem7556686 (_97561 : int) (_97559 : int) : (term421 _97561 _97559) = (term418 _97561 _97559).
Proof. exact (TRANS (@lem7556685 _97561 _97559) (@lem7556684 _97561 _97559)). Qed.
Lemma lem7556693 (_97561 : int) (_97559 : int) (_97560 : int) : (term422 _97561 _97559 _97560) = (term411 _97561 _97559 _97560).
Proof. exact (@lem17045 (term394 _97561) (term397 _97561 _97559 _97560)). Qed.
Lemma lem7556694 (_97561 : int) (_97559 : int) : (term412 _97561 _97559) = (term412 _97561 _97559).
Proof. exact (eq_refl (term412 _97561 _97559)). Qed.
Lemma lem7556695 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556696 (_97561 : int) (_97559 : int) (_97560 : int) : (term423 _97561 _97559 _97560) = (term424 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7556695) (@lem7556693 _97561 _97559 _97560)). Qed.
Lemma lem7556697 (_97560 : int) (_97561 : int) (_97559 : int) : (term425 _97560 _97561 _97559) = (term419 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556696 _97561 _97559 _97560) (@lem7556694 _97561 _97559)). Qed.
Lemma lem7556698 (_97560 : int) (_97561 : int) (_97559 : int) : (term426 _97560 _97561 _97559) = (term425 _97560 _97561 _97559).
Proof. exact (@lem17045 (term401 _97561 _97559 _97560) (int_le _97561 _97559)). Qed.
Lemma lem7556699 (_97560 : int) (_97561 : int) (_97559 : int) : (term426 _97560 _97561 _97559) = (term419 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556698 _97560 _97561 _97559) (@lem7556697 _97560 _97561 _97559)). Qed.
Lemma lem7556700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556701 (_97561 : int) (_97559 : int) : (term427 _97561 _97559) = (term428 _97561 _97559).
Proof. exact (MK_COMB (@lem7556700) (@lem7556686 _97561 _97559)). Qed.
Lemma lem7556702 (_97560 : int) (_97561 : int) (_97559 : int) : (term429 _97560 _97561 _97559) = (term430 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556701 _97561 _97559) (@lem7556699 _97560 _97561 _97559)). Qed.
Lemma lem7556703 (_97560 : int) (_97561 : int) (_97559 : int) : (term431 _97560 _97561 _97559) = (term429 _97560 _97561 _97559).
Proof. exact (@lem17160 (term393 _97561 _97559) (term409 _97560 _97561 _97559)). Qed.
Lemma lem7556704 (_97560 : int) (_97561 : int) (_97559 : int) : (term431 _97560 _97561 _97559) = (term430 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556703 _97560 _97561 _97559) (@lem7556702 _97560 _97561 _97559)). Qed.
Lemma lem7556705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556706 (_97560 : int) (_97561 : int) (_97559 : int) : (term432 _97560 _97561 _97559) = (term433 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556705) (@lem7556675 _97560 _97561 _97559)). Qed.
Lemma lem7556707 (_97560 : int) (_97561 : int) (_97559 : int) : (term434 _97560 _97561 _97559) = (term435 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556706 _97560 _97561 _97559) (@lem7556704 _97560 _97561 _97559)). Qed.
Lemma lem7556708 (_97560 : int) (_97561 : int) (_97559 : int) : (term436 _97560 _97561 _97559) = (term434 _97560 _97561 _97559).
Proof. exact (@lem17045 (term437 _97560 _97561 _97559) (term438 _97560 _97561 _97559)). Qed.
Lemma lem7556709 (_97560 : int) (_97561 : int) (_97559 : int) : (term436 _97560 _97561 _97559) = (term435 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556708 _97560 _97561 _97559) (@lem7556707 _97560 _97561 _97559)). Qed.
Lemma lem7556711 (_97561 : int) : (term399 _97561) = (term399 _97561).
Proof. exact (eq_refl (term399 _97561)). Qed.
Lemma lem7556712 (_97560 : int) (_97561 : int) (_97559 : int) : (term439 _97560 _97561 _97559) = (term440 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556711 _97561) (@lem7556709 _97560 _97561 _97559)). Qed.
Lemma lem7556713 (_97560 : int) (_97561 : int) (_97559 : int) : (term441 _97560 _97561 _97559) = (term439 _97560 _97561 _97559).
Proof. exact (@lem17362 (term394 _97561) (term442 _97560 _97561 _97559)). Qed.
Lemma lem7556714 (_97560 : int) (_97561 : int) (_97559 : int) : (term441 _97560 _97561 _97559) = (term440 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556713 _97560 _97561 _97559) (@lem7556712 _97560 _97561 _97559)). Qed.
Lemma lem7556716 (_97560 : int) : (term399 _97560) = (term399 _97560).
Proof. exact (eq_refl (term399 _97560)). Qed.
Lemma lem7556717 (_97560 : int) (_97561 : int) (_97559 : int) : (term443 _97560 _97561 _97559) = (term444 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556716 _97560) (@lem7556714 _97560 _97561 _97559)). Qed.
Lemma lem7556718 (_97560 : int) (_97561 : int) (_97559 : int) : (term445 _97560 _97561 _97559) = (term443 _97560 _97561 _97559).
Proof. exact (@lem17362 (term394 _97560) (term446 _97560 _97561 _97559)). Qed.
Lemma lem7556719 (_97560 : int) (_97561 : int) (_97559 : int) : (term445 _97560 _97561 _97559) = (term444 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556718 _97560 _97561 _97559) (@lem7556717 _97560 _97561 _97559)). Qed.
Lemma lem7556721 (_97559 : int) : (term399 _97559) = (term399 _97559).
Proof. exact (eq_refl (term399 _97559)). Qed.
Lemma lem7556722 (_97560 : int) (_97561 : int) (_97559 : int) : (term447 _97560 _97561 _97559) = (term448 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556721 _97559) (@lem7556719 _97560 _97561 _97559)). Qed.
Lemma lem7556723 (_97560 : int) (_97561 : int) (_97559 : int) : (term449 _97560 _97561 _97559) = (term447 _97560 _97561 _97559).
Proof. exact (@lem17362 (term394 _97559) (term450 _97560 _97561 _97559)). Qed.
Lemma lem7556785 (_97560 : int) (_97561 : int) (_97559 : int) : (term449 _97560 _97561 _97559) = (term448 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7556723 _97560 _97561 _97559) (@lem7556722 _97560 _97561 _97559)). Qed.
Lemma lem7556788 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556789 (_97559 : int) : (term394 _97559) = (term452 _97559).
Proof. exact (@lem7556788 term453 _97559). Qed.
Lemma lem7556791 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556792 : term455 = term35.
Proof. exact (@lem7556791 (NUMERAL 0)). Qed.
Lemma lem7556793 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556794 : term456 = term457.
Proof. exact (MK_COMB (@lem7556793) (@lem7556792)). Qed.
Lemma lem7556795 (_97559 : int) : (real_of_int _97559) = (real_of_int _97559).
Proof. exact (eq_refl (real_of_int _97559)). Qed.
Lemma lem7556796 (_97559 : int) : (term452 _97559) = (term458 _97559).
Proof. exact (MK_COMB (@lem7556794) (@lem7556795 _97559)). Qed.
Lemma lem7556798 (_97559 : int) : (term394 _97559) = (term458 _97559).
Proof. exact (TRANS (@lem7556789 _97559) (@lem7556796 _97559)). Qed.
Lemma lem7556801 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556802 (_97560 : int) : (term394 _97560) = (term452 _97560).
Proof. exact (@lem7556801 term453 _97560). Qed.
Lemma lem7556804 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556805 : term455 = term35.
Proof. exact (@lem7556804 (NUMERAL 0)). Qed.
Lemma lem7556806 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556807 : term456 = term457.
Proof. exact (MK_COMB (@lem7556806) (@lem7556805)). Qed.
Lemma lem7556808 (_97560 : int) : (real_of_int _97560) = (real_of_int _97560).
Proof. exact (eq_refl (real_of_int _97560)). Qed.
Lemma lem7556809 (_97560 : int) : (term452 _97560) = (term458 _97560).
Proof. exact (MK_COMB (@lem7556807) (@lem7556808 _97560)). Qed.
Lemma lem7556811 (_97560 : int) : (term394 _97560) = (term458 _97560).
Proof. exact (TRANS (@lem7556802 _97560) (@lem7556809 _97560)). Qed.
Lemma lem7556814 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556815 (_97561 : int) : (term394 _97561) = (term452 _97561).
Proof. exact (@lem7556814 term453 _97561). Qed.
Lemma lem7556817 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556818 : term455 = term35.
Proof. exact (@lem7556817 (NUMERAL 0)). Qed.
Lemma lem7556819 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556820 : term456 = term457.
Proof. exact (MK_COMB (@lem7556819) (@lem7556818)). Qed.
Lemma lem7556821 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7556822 (_97561 : int) : (term452 _97561) = (term458 _97561).
Proof. exact (MK_COMB (@lem7556820) (@lem7556821 _97561)). Qed.
Lemma lem7556824 (_97561 : int) : (term394 _97561) = (term458 _97561).
Proof. exact (TRANS (@lem7556815 _97561) (@lem7556822 _97561)). Qed.
Lemma lem7556826 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7556827 (_97561 : int) : (term403 _97561) = (term460 _97561).
Proof. exact (@lem7556826 _97561 term453). Qed.
Lemma lem7556829 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556830 (_97561 : int) : (term460 _97561) = (term461 _97561).
Proof. exact (@lem7556829 (term462 _97561) term453). Qed.
Lemma lem7556832 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7556833 (_97561 : int) : (term465 _97561) = (term466 _97561).
Proof. exact (@lem7556832 _97561 term467). Qed.
Lemma lem7556835 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556836 : term468 = term469.
Proof. exact (@lem7556835 term470). Qed.
Lemma lem7556837 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7556838 (_97561 : int) : (term466 _97561) = (term472 _97561).
Proof. exact (MK_COMB (@lem7556837 _97561) (@lem7556836)). Qed.
Lemma lem7556839 (_97561 : int) : (term465 _97561) = (term472 _97561).
Proof. exact (TRANS (@lem7556833 _97561) (@lem7556838 _97561)). Qed.
Lemma lem7556840 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556841 (_97561 : int) : (term473 _97561) = (term474 _97561).
Proof. exact (MK_COMB (@lem7556840) (@lem7556839 _97561)). Qed.
Lemma lem7556843 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556844 : term455 = term35.
Proof. exact (@lem7556843 (NUMERAL 0)). Qed.
Lemma lem7556845 (_97561 : int) : (term461 _97561) = (term475 _97561).
Proof. exact (MK_COMB (@lem7556841 _97561) (@lem7556844)). Qed.
Lemma lem7556846 (_97561 : int) : (term460 _97561) = (term475 _97561).
Proof. exact (TRANS (@lem7556830 _97561) (@lem7556845 _97561)). Qed.
Lemma lem7556847 (_97561 : int) : (term403 _97561) = (term475 _97561).
Proof. exact (TRANS (@lem7556827 _97561) (@lem7556846 _97561)). Qed.
Lemma lem7556849 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7556850 (_97559 : int) (_97561 : int) : (term412 _97561 _97559) = (term459 _97559 _97561).
Proof. exact (@lem7556849 _97559 _97561). Qed.
Lemma lem7556852 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556853 (_97559 : int) (_97561 : int) : (term459 _97559 _97561) = (term476 _97559 _97561).
Proof. exact (@lem7556852 (term462 _97559) _97561). Qed.
Lemma lem7556855 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7556856 (_97559 : int) : (term465 _97559) = (term466 _97559).
Proof. exact (@lem7556855 _97559 term467). Qed.
Lemma lem7556858 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556859 : term468 = term469.
Proof. exact (@lem7556858 term470). Qed.
Lemma lem7556860 (_97559 : int) : (term471 _97559) = (term471 _97559).
Proof. exact (eq_refl (term471 _97559)). Qed.
Lemma lem7556861 (_97559 : int) : (term466 _97559) = (term472 _97559).
Proof. exact (MK_COMB (@lem7556860 _97559) (@lem7556859)). Qed.
Lemma lem7556862 (_97559 : int) : (term465 _97559) = (term472 _97559).
Proof. exact (TRANS (@lem7556856 _97559) (@lem7556861 _97559)). Qed.
Lemma lem7556863 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556864 (_97559 : int) : (term473 _97559) = (term474 _97559).
Proof. exact (MK_COMB (@lem7556863) (@lem7556862 _97559)). Qed.
Lemma lem7556865 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7556866 (_97559 : int) (_97561 : int) : (term476 _97559 _97561) = (term477 _97559 _97561).
Proof. exact (MK_COMB (@lem7556864 _97559) (@lem7556865 _97561)). Qed.
Lemma lem7556867 (_97559 : int) (_97561 : int) : (term459 _97559 _97561) = (term477 _97559 _97561).
Proof. exact (TRANS (@lem7556853 _97559 _97561) (@lem7556866 _97559 _97561)). Qed.
Lemma lem7556868 (_97559 : int) (_97561 : int) : (term412 _97561 _97559) = (term477 _97559 _97561).
Proof. exact (TRANS (@lem7556850 _97559 _97561) (@lem7556867 _97559 _97561)). Qed.
Lemma lem7556869 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556870 (_97561 : int) : (term478 _97561) = (term479 _97561).
Proof. exact (MK_COMB (@lem7556869) (@lem7556847 _97561)). Qed.
Lemma lem7556871 (_97559 : int) (_97561 : int) : (term393 _97561 _97559) = (term480 _97559 _97561).
Proof. exact (MK_COMB (@lem7556870 _97561) (@lem7556868 _97559 _97561)). Qed.
Lemma lem7556874 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556875 (_97561 : int) : (term394 _97561) = (term452 _97561).
Proof. exact (@lem7556874 term453 _97561). Qed.
Lemma lem7556877 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556878 : term455 = term35.
Proof. exact (@lem7556877 (NUMERAL 0)). Qed.
Lemma lem7556879 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556880 : term456 = term457.
Proof. exact (MK_COMB (@lem7556879) (@lem7556878)). Qed.
Lemma lem7556881 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7556882 (_97561 : int) : (term452 _97561) = (term458 _97561).
Proof. exact (MK_COMB (@lem7556880) (@lem7556881 _97561)). Qed.
Lemma lem7556884 (_97561 : int) : (term394 _97561) = (term458 _97561).
Proof. exact (TRANS (@lem7556875 _97561) (@lem7556882 _97561)). Qed.
Lemma lem7556887 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556888 (_97561 : int) (_97559 : int) (_97560 : int) : (term397 _97561 _97559 _97560) = (term481 _97561 _97559 _97560).
Proof. exact (@lem7556887 _97561 (int_max _97559 _97560)). Qed.
Lemma lem7556890 (x : int) (y : int) : (term482 x y) = (term483 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem7556891 (_97559 : int) (_97560 : int) : (term482 _97559 _97560) = (term483 _97559 _97560).
Proof. exact (@lem7556890 _97559 _97560). Qed.
Lemma lem7556892 (_97561 : int) : (term484 _97561) = (term484 _97561).
Proof. exact (eq_refl (term484 _97561)). Qed.
Lemma lem7556893 (_97561 : int) (_97559 : int) (_97560 : int) : (term481 _97561 _97559 _97560) = (term485 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7556892 _97561) (@lem7556891 _97559 _97560)). Qed.
Lemma lem7556895 (_97561 : int) (_97559 : int) (_97560 : int) : (term397 _97561 _97559 _97560) = (term485 _97561 _97559 _97560).
Proof. exact (TRANS (@lem7556888 _97561 _97559 _97560) (@lem7556893 _97561 _97559 _97560)). Qed.
Lemma lem7556896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556897 (_97561 : int) : (term399 _97561) = (term486 _97561).
Proof. exact (MK_COMB (@lem7556896) (@lem7556884 _97561)). Qed.
Lemma lem7556898 (_97561 : int) (_97559 : int) (_97560 : int) : (term401 _97561 _97559 _97560) = (term487 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7556897 _97561) (@lem7556895 _97561 _97559 _97560)). Qed.
Lemma lem7556901 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556903 (_97561 : int) (_97559 : int) : (int_le _97561 _97559) = (term451 _97561 _97559).
Proof. exact (@lem7556901 _97561 _97559). Qed.
Lemma lem7556904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556905 (_97561 : int) (_97559 : int) (_97560 : int) : (term407 _97561 _97559 _97560) = (term488 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7556904) (@lem7556898 _97561 _97559 _97560)). Qed.
Lemma lem7556906 (_97560 : int) (_97561 : int) (_97559 : int) : (term409 _97560 _97561 _97559) = (term489 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556905 _97561 _97559 _97560) (@lem7556903 _97561 _97559)). Qed.
Lemma lem7556907 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556908 (_97559 : int) (_97561 : int) : (term414 _97561 _97559) = (term490 _97559 _97561).
Proof. exact (MK_COMB (@lem7556907) (@lem7556871 _97559 _97561)). Qed.
Lemma lem7556909 (_97560 : int) (_97561 : int) (_97559 : int) : (term416 _97560 _97561 _97559) = (term491 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7556908 _97559 _97561) (@lem7556906 _97560 _97561 _97559)). Qed.
Lemma lem7556912 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556913 (_97561 : int) : (term394 _97561) = (term452 _97561).
Proof. exact (@lem7556912 term453 _97561). Qed.
Lemma lem7556915 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556916 : term455 = term35.
Proof. exact (@lem7556915 (NUMERAL 0)). Qed.
Lemma lem7556917 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556918 : term456 = term457.
Proof. exact (MK_COMB (@lem7556917) (@lem7556916)). Qed.
Lemma lem7556919 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7556920 (_97561 : int) : (term452 _97561) = (term458 _97561).
Proof. exact (MK_COMB (@lem7556918) (@lem7556919 _97561)). Qed.
Lemma lem7556922 (_97561 : int) : (term394 _97561) = (term458 _97561).
Proof. exact (TRANS (@lem7556913 _97561) (@lem7556920 _97561)). Qed.
Lemma lem7556925 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556927 (_97561 : int) (_97559 : int) : (int_le _97561 _97559) = (term451 _97561 _97559).
Proof. exact (@lem7556925 _97561 _97559). Qed.
Lemma lem7556928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7556929 (_97561 : int) : (term399 _97561) = (term486 _97561).
Proof. exact (MK_COMB (@lem7556928) (@lem7556922 _97561)). Qed.
Lemma lem7556930 (_97561 : int) (_97559 : int) : (term418 _97561 _97559) = (term492 _97561 _97559).
Proof. exact (MK_COMB (@lem7556929 _97561) (@lem7556927 _97561 _97559)). Qed.
Lemma lem7556932 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7556933 (_97561 : int) : (term403 _97561) = (term460 _97561).
Proof. exact (@lem7556932 _97561 term453). Qed.
Lemma lem7556935 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556936 (_97561 : int) : (term460 _97561) = (term461 _97561).
Proof. exact (@lem7556935 (term462 _97561) term453). Qed.
Lemma lem7556938 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7556939 (_97561 : int) : (term465 _97561) = (term466 _97561).
Proof. exact (@lem7556938 _97561 term467). Qed.
Lemma lem7556941 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556942 : term468 = term469.
Proof. exact (@lem7556941 term470). Qed.
Lemma lem7556943 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7556944 (_97561 : int) : (term466 _97561) = (term472 _97561).
Proof. exact (MK_COMB (@lem7556943 _97561) (@lem7556942)). Qed.
Lemma lem7556945 (_97561 : int) : (term465 _97561) = (term472 _97561).
Proof. exact (TRANS (@lem7556939 _97561) (@lem7556944 _97561)). Qed.
Lemma lem7556946 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556947 (_97561 : int) : (term473 _97561) = (term474 _97561).
Proof. exact (MK_COMB (@lem7556946) (@lem7556945 _97561)). Qed.
Lemma lem7556949 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556950 : term455 = term35.
Proof. exact (@lem7556949 (NUMERAL 0)). Qed.
Lemma lem7556951 (_97561 : int) : (term461 _97561) = (term475 _97561).
Proof. exact (MK_COMB (@lem7556947 _97561) (@lem7556950)). Qed.
Lemma lem7556952 (_97561 : int) : (term460 _97561) = (term475 _97561).
Proof. exact (TRANS (@lem7556936 _97561) (@lem7556951 _97561)). Qed.
Lemma lem7556953 (_97561 : int) : (term403 _97561) = (term475 _97561).
Proof. exact (TRANS (@lem7556933 _97561) (@lem7556952 _97561)). Qed.
Lemma lem7556955 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7556956 (_97559 : int) (_97560 : int) (_97561 : int) : (term404 _97561 _97559 _97560) = (term493 _97559 _97560 _97561).
Proof. exact (@lem7556955 (int_max _97559 _97560) _97561). Qed.
Lemma lem7556958 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556959 (_97559 : int) (_97560 : int) (_97561 : int) : (term493 _97559 _97560 _97561) = (term494 _97559 _97560 _97561).
Proof. exact (@lem7556958 (term495 _97559 _97560) _97561). Qed.
Lemma lem7556961 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7556962 (_97559 : int) (_97560 : int) : (term496 _97559 _97560) = (term497 _97559 _97560).
Proof. exact (@lem7556961 (int_max _97559 _97560) term467). Qed.
Lemma lem7556964 (x : int) (y : int) : (term482 x y) = (term483 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem7556965 (_97559 : int) (_97560 : int) : (term482 _97559 _97560) = (term483 _97559 _97560).
Proof. exact (@lem7556964 _97559 _97560). Qed.
Lemma lem7556966 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7556967 (_97559 : int) (_97560 : int) : (term498 _97559 _97560) = (term499 _97559 _97560).
Proof. exact (MK_COMB (@lem7556966) (@lem7556965 _97559 _97560)). Qed.
Lemma lem7556969 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556970 : term468 = term469.
Proof. exact (@lem7556969 term470). Qed.
Lemma lem7556971 (_97559 : int) (_97560 : int) : (term497 _97559 _97560) = (term500 _97559 _97560).
Proof. exact (MK_COMB (@lem7556967 _97559 _97560) (@lem7556970)). Qed.
Lemma lem7556972 (_97559 : int) (_97560 : int) : (term496 _97559 _97560) = (term500 _97559 _97560).
Proof. exact (TRANS (@lem7556962 _97559 _97560) (@lem7556971 _97559 _97560)). Qed.
Lemma lem7556973 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556974 (_97559 : int) (_97560 : int) : (term501 _97559 _97560) = (term502 _97559 _97560).
Proof. exact (MK_COMB (@lem7556973) (@lem7556972 _97559 _97560)). Qed.
Lemma lem7556975 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7556976 (_97559 : int) (_97560 : int) (_97561 : int) : (term494 _97559 _97560 _97561) = (term503 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7556974 _97559 _97560) (@lem7556975 _97561)). Qed.
Lemma lem7556977 (_97559 : int) (_97560 : int) (_97561 : int) : (term493 _97559 _97560 _97561) = (term503 _97559 _97560 _97561).
Proof. exact (TRANS (@lem7556959 _97559 _97560 _97561) (@lem7556976 _97559 _97560 _97561)). Qed.
Lemma lem7556978 (_97559 : int) (_97560 : int) (_97561 : int) : (term404 _97561 _97559 _97560) = (term503 _97559 _97560 _97561).
Proof. exact (TRANS (@lem7556956 _97559 _97560 _97561) (@lem7556977 _97559 _97560 _97561)). Qed.
Lemma lem7556979 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7556980 (_97561 : int) : (term478 _97561) = (term479 _97561).
Proof. exact (MK_COMB (@lem7556979) (@lem7556953 _97561)). Qed.
Lemma lem7556981 (_97559 : int) (_97560 : int) (_97561 : int) : (term411 _97561 _97559 _97560) = (term504 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7556980 _97561) (@lem7556978 _97559 _97560 _97561)). Qed.
Lemma lem7556983 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7556984 (_97559 : int) (_97561 : int) : (term412 _97561 _97559) = (term459 _97559 _97561).
Proof. exact (@lem7556983 _97559 _97561). Qed.
Lemma lem7556986 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7556987 (_97559 : int) (_97561 : int) : (term459 _97559 _97561) = (term476 _97559 _97561).
Proof. exact (@lem7556986 (term462 _97559) _97561). Qed.
Lemma lem7556989 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7556990 (_97559 : int) : (term465 _97559) = (term466 _97559).
Proof. exact (@lem7556989 _97559 term467). Qed.
Lemma lem7556992 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7556993 : term468 = term469.
Proof. exact (@lem7556992 term470). Qed.
Lemma lem7556994 (_97559 : int) : (term471 _97559) = (term471 _97559).
Proof. exact (eq_refl (term471 _97559)). Qed.
Lemma lem7556995 (_97559 : int) : (term466 _97559) = (term472 _97559).
Proof. exact (MK_COMB (@lem7556994 _97559) (@lem7556993)). Qed.
Lemma lem7556996 (_97559 : int) : (term465 _97559) = (term472 _97559).
Proof. exact (TRANS (@lem7556990 _97559) (@lem7556995 _97559)). Qed.
Lemma lem7556997 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7556998 (_97559 : int) : (term473 _97559) = (term474 _97559).
Proof. exact (MK_COMB (@lem7556997) (@lem7556996 _97559)). Qed.
Lemma lem7556999 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7557000 (_97559 : int) (_97561 : int) : (term476 _97559 _97561) = (term477 _97559 _97561).
Proof. exact (MK_COMB (@lem7556998 _97559) (@lem7556999 _97561)). Qed.
Lemma lem7557001 (_97559 : int) (_97561 : int) : (term459 _97559 _97561) = (term477 _97559 _97561).
Proof. exact (TRANS (@lem7556987 _97559 _97561) (@lem7557000 _97559 _97561)). Qed.
Lemma lem7557002 (_97559 : int) (_97561 : int) : (term412 _97561 _97559) = (term477 _97559 _97561).
Proof. exact (TRANS (@lem7556984 _97559 _97561) (@lem7557001 _97559 _97561)). Qed.
Lemma lem7557003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557004 (_97559 : int) (_97560 : int) (_97561 : int) : (term424 _97561 _97559 _97560) = (term505 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7557003) (@lem7556981 _97559 _97560 _97561)). Qed.
Lemma lem7557005 (_97560 : int) (_97559 : int) (_97561 : int) : (term419 _97560 _97561 _97559) = (term506 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557004 _97559 _97560 _97561) (@lem7557002 _97559 _97561)). Qed.
Lemma lem7557006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557007 (_97561 : int) (_97559 : int) : (term428 _97561 _97559) = (term507 _97561 _97559).
Proof. exact (MK_COMB (@lem7557006) (@lem7556930 _97561 _97559)). Qed.
Lemma lem7557008 (_97560 : int) (_97559 : int) (_97561 : int) : (term430 _97560 _97561 _97559) = (term508 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557007 _97561 _97559) (@lem7557005 _97560 _97559 _97561)). Qed.
Lemma lem7557009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557010 (_97560 : int) (_97561 : int) (_97559 : int) : (term433 _97560 _97561 _97559) = (term509 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7557009) (@lem7556909 _97560 _97561 _97559)). Qed.
Lemma lem7557011 (_97560 : int) (_97559 : int) (_97561 : int) : (term435 _97560 _97561 _97559) = (term510 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557010 _97560 _97561 _97559) (@lem7557008 _97560 _97559 _97561)). Qed.
Lemma lem7557012 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557013 (_97561 : int) : (term399 _97561) = (term486 _97561).
Proof. exact (MK_COMB (@lem7557012) (@lem7556824 _97561)). Qed.
Lemma lem7557014 (_97560 : int) (_97559 : int) (_97561 : int) : (term440 _97560 _97561 _97559) = (term511 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557013 _97561) (@lem7557011 _97560 _97559 _97561)). Qed.
Lemma lem7557015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557016 (_97560 : int) : (term399 _97560) = (term486 _97560).
Proof. exact (MK_COMB (@lem7557015) (@lem7556811 _97560)). Qed.
Lemma lem7557017 (_97560 : int) (_97559 : int) (_97561 : int) : (term444 _97560 _97561 _97559) = (term512 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557016 _97560) (@lem7557014 _97560 _97559 _97561)). Qed.
Lemma lem7557018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557019 (_97559 : int) : (term399 _97559) = (term486 _97559).
Proof. exact (MK_COMB (@lem7557018) (@lem7556798 _97559)). Qed.
Lemma lem7557020 (_97560 : int) (_97559 : int) (_97561 : int) : (term448 _97560 _97561 _97559) = (term513 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557019 _97559) (@lem7557017 _97560 _97559 _97561)). Qed.
Lemma lem7557021 (_97560 : int) (_97559 : int) (_97561 : int) : (term449 _97560 _97561 _97559) = (term513 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7556785 _97560 _97561 _97559) (@lem7557020 _97560 _97559 _97561)). Qed.
Lemma lem7557025 (t : Prop) : (term514 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7557151 (_97560 : int) (_97559 : int) (_97561 : int) : (term515 _97560 _97559 _97561) = (term513 _97560 _97559 _97561).
Proof. exact (@lem7557025 (term513 _97560 _97559 _97561)). Qed.
Lemma lem7557152 (_97559 : int) : (term458 _97559) = (term516 _97559).
Proof. exact (@lem1988287 (real_of_int _97559) term35). Qed.
Lemma lem7557158 (_97559 : int) : (term517 _97559) = (term518 _97559).
Proof. exact (@lem1982792 (real_of_int _97559) term35). Qed.
Lemma lem7557160 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557161 : term35 = term520.
Proof. exact (@lem7557160 (NUMERAL 0)). Qed.
Lemma lem7557163 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557164 : term523 = term524.
Proof. exact (@lem7557163 term470). Qed.
Lemma lem7557165 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557166 : term525 = term526.
Proof. exact (MK_COMB (@lem7557165) (@lem7557164)). Qed.
Lemma lem7557167 : term527 = term528.
Proof. exact (MK_COMB (@lem7557166) (@lem7557161)). Qed.
Lemma lem7557168 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7557170 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557171 : term532 = term533.
Proof. exact (@lem7557170 term470 term470). Qed.
Lemma lem7557172 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557173 : term535 = term470.
Proof. exact (EQ_MP (@lem7557172) (@lem940073)). Qed.
Lemma lem7557174 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557175 : term533 = term469.
Proof. exact (MK_COMB (@lem7557174) (@lem7557173)). Qed.
Lemma lem7557176 : term532 = term469.
Proof. exact (TRANS (@lem7557171) (@lem7557175)). Qed.
Lemma lem7557178 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7557179 : term527 = term35.
Proof. exact (@lem7557178 term470). Qed.
Lemma lem7557180 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557181 : term537 = term538.
Proof. exact (MK_COMB (@lem7557180) (@lem7557179)). Qed.
Lemma lem7557182 : term529 = term520.
Proof. exact (MK_COMB (@lem7557181) (@lem7557176)). Qed.
Lemma lem7557183 : term528 = term520.
Proof. exact (TRANS (@lem7557168) (@lem7557182)). Qed.
Lemma lem7557184 : term527 = term520.
Proof. exact (TRANS (@lem7557167) (@lem7557183)). Qed.
Lemma lem7557186 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557187 : term520 = term35.
Proof. exact (@lem7557186 term35). Qed.
Lemma lem7557188 : term527 = term35.
Proof. exact (TRANS (@lem7557184) (@lem7557187)). Qed.
Lemma lem7557189 (_97559 : int) : (term471 _97559) = (term471 _97559).
Proof. exact (eq_refl (term471 _97559)). Qed.
Lemma lem7557190 (_97559 : int) : (term518 _97559) = (term540 _97559).
Proof. exact (MK_COMB (@lem7557189 _97559) (@lem7557188)). Qed.
Lemma lem7557191 (_97559 : int) : (term540 _97559) = (real_of_int _97559).
Proof. exact (@lem1982723 (real_of_int _97559)). Qed.
Lemma lem7557192 (_97559 : int) : (term518 _97559) = (real_of_int _97559).
Proof. exact (TRANS (@lem7557190 _97559) (@lem7557191 _97559)). Qed.
Lemma lem7557194 (_97559 : int) : (term517 _97559) = (real_of_int _97559).
Proof. exact (TRANS (@lem7557158 _97559) (@lem7557192 _97559)). Qed.
Lemma lem7557195 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557196 (_97559 : int) : (term541 _97559) = (term542 _97559).
Proof. exact (MK_COMB (@lem7557195) (@lem7557194 _97559)). Qed.
Lemma lem7557197 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557198 (_97559 : int) : (term516 _97559) = (term543 _97559).
Proof. exact (MK_COMB (@lem7557196 _97559) (@lem7557197)). Qed.
Lemma lem7557199 (_97559 : int) : (term458 _97559) = (term543 _97559).
Proof. exact (TRANS (@lem7557152 _97559) (@lem7557198 _97559)). Qed.
Lemma lem7557200 (_97560 : int) : (term458 _97560) = (term516 _97560).
Proof. exact (@lem1988287 (real_of_int _97560) term35). Qed.
Lemma lem7557206 (_97560 : int) : (term517 _97560) = (term518 _97560).
Proof. exact (@lem1982792 (real_of_int _97560) term35). Qed.
Lemma lem7557208 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557209 : term35 = term520.
Proof. exact (@lem7557208 (NUMERAL 0)). Qed.
Lemma lem7557211 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557212 : term523 = term524.
Proof. exact (@lem7557211 term470). Qed.
Lemma lem7557213 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557214 : term525 = term526.
Proof. exact (MK_COMB (@lem7557213) (@lem7557212)). Qed.
Lemma lem7557215 : term527 = term528.
Proof. exact (MK_COMB (@lem7557214) (@lem7557209)). Qed.
Lemma lem7557216 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7557218 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557219 : term532 = term533.
Proof. exact (@lem7557218 term470 term470). Qed.
Lemma lem7557220 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557221 : term535 = term470.
Proof. exact (EQ_MP (@lem7557220) (@lem940073)). Qed.
Lemma lem7557222 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557223 : term533 = term469.
Proof. exact (MK_COMB (@lem7557222) (@lem7557221)). Qed.
Lemma lem7557224 : term532 = term469.
Proof. exact (TRANS (@lem7557219) (@lem7557223)). Qed.
Lemma lem7557226 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7557227 : term527 = term35.
Proof. exact (@lem7557226 term470). Qed.
Lemma lem7557228 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557229 : term537 = term538.
Proof. exact (MK_COMB (@lem7557228) (@lem7557227)). Qed.
Lemma lem7557230 : term529 = term520.
Proof. exact (MK_COMB (@lem7557229) (@lem7557224)). Qed.
Lemma lem7557231 : term528 = term520.
Proof. exact (TRANS (@lem7557216) (@lem7557230)). Qed.
Lemma lem7557232 : term527 = term520.
Proof. exact (TRANS (@lem7557215) (@lem7557231)). Qed.
Lemma lem7557234 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557235 : term520 = term35.
Proof. exact (@lem7557234 term35). Qed.
Lemma lem7557236 : term527 = term35.
Proof. exact (TRANS (@lem7557232) (@lem7557235)). Qed.
Lemma lem7557237 (_97560 : int) : (term471 _97560) = (term471 _97560).
Proof. exact (eq_refl (term471 _97560)). Qed.
Lemma lem7557238 (_97560 : int) : (term518 _97560) = (term540 _97560).
Proof. exact (MK_COMB (@lem7557237 _97560) (@lem7557236)). Qed.
Lemma lem7557239 (_97560 : int) : (term540 _97560) = (real_of_int _97560).
Proof. exact (@lem1982723 (real_of_int _97560)). Qed.
Lemma lem7557240 (_97560 : int) : (term518 _97560) = (real_of_int _97560).
Proof. exact (TRANS (@lem7557238 _97560) (@lem7557239 _97560)). Qed.
Lemma lem7557242 (_97560 : int) : (term517 _97560) = (real_of_int _97560).
Proof. exact (TRANS (@lem7557206 _97560) (@lem7557240 _97560)). Qed.
Lemma lem7557243 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557244 (_97560 : int) : (term541 _97560) = (term542 _97560).
Proof. exact (MK_COMB (@lem7557243) (@lem7557242 _97560)). Qed.
Lemma lem7557245 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557246 (_97560 : int) : (term516 _97560) = (term543 _97560).
Proof. exact (MK_COMB (@lem7557244 _97560) (@lem7557245)). Qed.
Lemma lem7557247 (_97560 : int) : (term458 _97560) = (term543 _97560).
Proof. exact (TRANS (@lem7557200 _97560) (@lem7557246 _97560)). Qed.
Lemma lem7557248 (_97561 : int) : (term458 _97561) = (term516 _97561).
Proof. exact (@lem1988287 (real_of_int _97561) term35). Qed.
Lemma lem7557254 (_97561 : int) : (term517 _97561) = (term518 _97561).
Proof. exact (@lem1982792 (real_of_int _97561) term35). Qed.
Lemma lem7557256 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557257 : term35 = term520.
Proof. exact (@lem7557256 (NUMERAL 0)). Qed.
Lemma lem7557259 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557260 : term523 = term524.
Proof. exact (@lem7557259 term470). Qed.
Lemma lem7557261 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557262 : term525 = term526.
Proof. exact (MK_COMB (@lem7557261) (@lem7557260)). Qed.
Lemma lem7557263 : term527 = term528.
Proof. exact (MK_COMB (@lem7557262) (@lem7557257)). Qed.
Lemma lem7557264 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7557266 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557267 : term532 = term533.
Proof. exact (@lem7557266 term470 term470). Qed.
Lemma lem7557268 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557269 : term535 = term470.
Proof. exact (EQ_MP (@lem7557268) (@lem940073)). Qed.
Lemma lem7557270 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557271 : term533 = term469.
Proof. exact (MK_COMB (@lem7557270) (@lem7557269)). Qed.
Lemma lem7557272 : term532 = term469.
Proof. exact (TRANS (@lem7557267) (@lem7557271)). Qed.
Lemma lem7557274 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7557275 : term527 = term35.
Proof. exact (@lem7557274 term470). Qed.
Lemma lem7557276 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557277 : term537 = term538.
Proof. exact (MK_COMB (@lem7557276) (@lem7557275)). Qed.
Lemma lem7557278 : term529 = term520.
Proof. exact (MK_COMB (@lem7557277) (@lem7557272)). Qed.
Lemma lem7557279 : term528 = term520.
Proof. exact (TRANS (@lem7557264) (@lem7557278)). Qed.
Lemma lem7557280 : term527 = term520.
Proof. exact (TRANS (@lem7557263) (@lem7557279)). Qed.
Lemma lem7557282 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557283 : term520 = term35.
Proof. exact (@lem7557282 term35). Qed.
Lemma lem7557284 : term527 = term35.
Proof. exact (TRANS (@lem7557280) (@lem7557283)). Qed.
Lemma lem7557285 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7557286 (_97561 : int) : (term518 _97561) = (term540 _97561).
Proof. exact (MK_COMB (@lem7557285 _97561) (@lem7557284)). Qed.
Lemma lem7557287 (_97561 : int) : (term540 _97561) = (real_of_int _97561).
Proof. exact (@lem1982723 (real_of_int _97561)). Qed.
Lemma lem7557288 (_97561 : int) : (term518 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7557286 _97561) (@lem7557287 _97561)). Qed.
Lemma lem7557290 (_97561 : int) : (term517 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7557254 _97561) (@lem7557288 _97561)). Qed.
Lemma lem7557291 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557292 (_97561 : int) : (term541 _97561) = (term542 _97561).
Proof. exact (MK_COMB (@lem7557291) (@lem7557290 _97561)). Qed.
Lemma lem7557293 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557294 (_97561 : int) : (term516 _97561) = (term543 _97561).
Proof. exact (MK_COMB (@lem7557292 _97561) (@lem7557293)). Qed.
Lemma lem7557295 (_97561 : int) : (term458 _97561) = (term543 _97561).
Proof. exact (TRANS (@lem7557248 _97561) (@lem7557294 _97561)). Qed.
Lemma lem7557296 (_97561 : int) : (term475 _97561) = (term544 _97561).
Proof. exact (@lem1988287 term35 (term472 _97561)). Qed.
Lemma lem7557308 (_97561 : int) : (term545 _97561) = (term546 _97561).
Proof. exact (@lem1982792 term35 (term472 _97561)). Qed.
Lemma lem7557309 (_97561 : int) : (term547 _97561) = (term548 _97561).
Proof. exact (@lem1982781 (real_of_int _97561) term523 term469). Qed.
Lemma lem7557311 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557312 : term469 = term549.
Proof. exact (@lem7557311 term470). Qed.
Lemma lem7557314 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557315 : term523 = term524.
Proof. exact (@lem7557314 term470). Qed.
Lemma lem7557316 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557317 : term525 = term526.
Proof. exact (MK_COMB (@lem7557316) (@lem7557315)). Qed.
Lemma lem7557318 : term550 = term551.
Proof. exact (MK_COMB (@lem7557317) (@lem7557312)). Qed.
Lemma lem7557319 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7557321 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557322 : term532 = term533.
Proof. exact (@lem7557321 term470 term470). Qed.
Lemma lem7557323 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557324 : term535 = term470.
Proof. exact (EQ_MP (@lem7557323) (@lem940073)). Qed.
Lemma lem7557325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557326 : term533 = term469.
Proof. exact (MK_COMB (@lem7557325) (@lem7557324)). Qed.
Lemma lem7557327 : term532 = term469.
Proof. exact (TRANS (@lem7557322) (@lem7557326)). Qed.
Lemma lem7557329 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7557330 : term550 = term555.
Proof. exact (@lem7557329 term470 term470). Qed.
Lemma lem7557331 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557332 : term535 = term470.
Proof. exact (EQ_MP (@lem7557331) (@lem940073)). Qed.
Lemma lem7557333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557334 : term533 = term469.
Proof. exact (MK_COMB (@lem7557333) (@lem7557332)). Qed.
Lemma lem7557335 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7557336 : term555 = term523.
Proof. exact (MK_COMB (@lem7557335) (@lem7557334)). Qed.
Lemma lem7557337 : term550 = term523.
Proof. exact (TRANS (@lem7557330) (@lem7557336)). Qed.
Lemma lem7557338 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557339 : term556 = term557.
Proof. exact (MK_COMB (@lem7557338) (@lem7557337)). Qed.
Lemma lem7557340 : term552 = term524.
Proof. exact (MK_COMB (@lem7557339) (@lem7557327)). Qed.
Lemma lem7557341 : term551 = term524.
Proof. exact (TRANS (@lem7557319) (@lem7557340)). Qed.
Lemma lem7557342 : term550 = term524.
Proof. exact (TRANS (@lem7557318) (@lem7557341)). Qed.
Lemma lem7557344 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557345 : term524 = term523.
Proof. exact (@lem7557344 term523). Qed.
Lemma lem7557346 : term550 = term523.
Proof. exact (TRANS (@lem7557342) (@lem7557345)). Qed.
Lemma lem7557349 (_97561 : int) : (term558 _97561) = (term558 _97561).
Proof. exact (eq_refl (term558 _97561)). Qed.
Lemma lem7557350 (_97561 : int) : (term548 _97561) = (term559 _97561).
Proof. exact (MK_COMB (@lem7557349 _97561) (@lem7557346)). Qed.
Lemma lem7557351 (_97561 : int) : (term547 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7557309 _97561) (@lem7557350 _97561)). Qed.
Lemma lem7557352 : term560 = term560.
Proof. exact (eq_refl term560). Qed.
Lemma lem7557353 (_97561 : int) : (term546 _97561) = (term561 _97561).
Proof. exact (MK_COMB (@lem7557352) (@lem7557351 _97561)). Qed.
Lemma lem7557354 (_97561 : int) : (term561 _97561) = (term559 _97561).
Proof. exact (@lem1982721 (term559 _97561)). Qed.
Lemma lem7557355 (_97561 : int) : (term546 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7557353 _97561) (@lem7557354 _97561)). Qed.
Lemma lem7557357 (_97561 : int) : (term545 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7557308 _97561) (@lem7557355 _97561)). Qed.
Lemma lem7557358 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557359 (_97561 : int) : (term562 _97561) = (term563 _97561).
Proof. exact (MK_COMB (@lem7557358) (@lem7557357 _97561)). Qed.
Lemma lem7557360 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557361 (_97561 : int) : (term544 _97561) = (term564 _97561).
Proof. exact (MK_COMB (@lem7557359 _97561) (@lem7557360)). Qed.
Lemma lem7557362 (_97561 : int) : (term475 _97561) = (term564 _97561).
Proof. exact (TRANS (@lem7557296 _97561) (@lem7557361 _97561)). Qed.
Lemma lem7557363 (_97561 : int) (_97559 : int) : (term477 _97559 _97561) = (term565 _97561 _97559).
Proof. exact (@lem1988287 (real_of_int _97561) (term472 _97559)). Qed.
Lemma lem7557375 (_97561 : int) (_97559 : int) : (term566 _97561 _97559) = (term567 _97561 _97559).
Proof. exact (@lem1982792 (real_of_int _97561) (term472 _97559)). Qed.
Lemma lem7557376 (_97559 : int) : (term547 _97559) = (term548 _97559).
Proof. exact (@lem1982781 (real_of_int _97559) term523 term469). Qed.
Lemma lem7557378 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557379 : term469 = term549.
Proof. exact (@lem7557378 term470). Qed.
Lemma lem7557381 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557382 : term523 = term524.
Proof. exact (@lem7557381 term470). Qed.
Lemma lem7557383 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557384 : term525 = term526.
Proof. exact (MK_COMB (@lem7557383) (@lem7557382)). Qed.
Lemma lem7557385 : term550 = term551.
Proof. exact (MK_COMB (@lem7557384) (@lem7557379)). Qed.
Lemma lem7557386 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7557388 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557389 : term532 = term533.
Proof. exact (@lem7557388 term470 term470). Qed.
Lemma lem7557390 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557391 : term535 = term470.
Proof. exact (EQ_MP (@lem7557390) (@lem940073)). Qed.
Lemma lem7557392 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557393 : term533 = term469.
Proof. exact (MK_COMB (@lem7557392) (@lem7557391)). Qed.
Lemma lem7557394 : term532 = term469.
Proof. exact (TRANS (@lem7557389) (@lem7557393)). Qed.
Lemma lem7557396 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7557397 : term550 = term555.
Proof. exact (@lem7557396 term470 term470). Qed.
Lemma lem7557398 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557399 : term535 = term470.
Proof. exact (EQ_MP (@lem7557398) (@lem940073)). Qed.
Lemma lem7557400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557401 : term533 = term469.
Proof. exact (MK_COMB (@lem7557400) (@lem7557399)). Qed.
Lemma lem7557402 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7557403 : term555 = term523.
Proof. exact (MK_COMB (@lem7557402) (@lem7557401)). Qed.
Lemma lem7557404 : term550 = term523.
Proof. exact (TRANS (@lem7557397) (@lem7557403)). Qed.
Lemma lem7557405 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557406 : term556 = term557.
Proof. exact (MK_COMB (@lem7557405) (@lem7557404)). Qed.
Lemma lem7557407 : term552 = term524.
Proof. exact (MK_COMB (@lem7557406) (@lem7557394)). Qed.
Lemma lem7557408 : term551 = term524.
Proof. exact (TRANS (@lem7557386) (@lem7557407)). Qed.
Lemma lem7557409 : term550 = term524.
Proof. exact (TRANS (@lem7557385) (@lem7557408)). Qed.
Lemma lem7557411 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557412 : term524 = term523.
Proof. exact (@lem7557411 term523). Qed.
Lemma lem7557413 : term550 = term523.
Proof. exact (TRANS (@lem7557409) (@lem7557412)). Qed.
Lemma lem7557416 (_97559 : int) : (term558 _97559) = (term558 _97559).
Proof. exact (eq_refl (term558 _97559)). Qed.
Lemma lem7557417 (_97559 : int) : (term548 _97559) = (term559 _97559).
Proof. exact (MK_COMB (@lem7557416 _97559) (@lem7557413)). Qed.
Lemma lem7557418 (_97559 : int) : (term547 _97559) = (term559 _97559).
Proof. exact (TRANS (@lem7557376 _97559) (@lem7557417 _97559)). Qed.
Lemma lem7557419 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7557420 (_97561 : int) (_97559 : int) : (term567 _97561 _97559) = (term568 _97561 _97559).
Proof. exact (MK_COMB (@lem7557419 _97561) (@lem7557418 _97559)). Qed.
Lemma lem7557425 (_97559 : int) (_97561 : int) : (term568 _97561 _97559) = (term569 _97559 _97561).
Proof. exact (@lem1982757 (term570 _97559) (real_of_int _97561) term523). Qed.
Lemma lem7557426 (_97559 : int) (_97561 : int) : (term567 _97561 _97559) = (term569 _97559 _97561).
Proof. exact (TRANS (@lem7557420 _97561 _97559) (@lem7557425 _97559 _97561)). Qed.
Lemma lem7557428 (_97559 : int) (_97561 : int) : (term566 _97561 _97559) = (term569 _97559 _97561).
Proof. exact (TRANS (@lem7557375 _97561 _97559) (@lem7557426 _97559 _97561)). Qed.
Lemma lem7557429 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557430 (_97559 : int) (_97561 : int) : (term571 _97561 _97559) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7557429) (@lem7557428 _97559 _97561)). Qed.
Lemma lem7557431 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557432 (_97559 : int) (_97561 : int) : (term565 _97561 _97559) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7557430 _97559 _97561) (@lem7557431)). Qed.
Lemma lem7557433 (_97559 : int) (_97561 : int) : (term477 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (TRANS (@lem7557363 _97561 _97559) (@lem7557432 _97559 _97561)). Qed.
Lemma lem7557434 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557435 (_97561 : int) : (term479 _97561) = (term574 _97561).
Proof. exact (MK_COMB (@lem7557434) (@lem7557362 _97561)). Qed.
Lemma lem7557436 (_97559 : int) (_97561 : int) : (term480 _97559 _97561) = (term575 _97559 _97561).
Proof. exact (MK_COMB (@lem7557435 _97561) (@lem7557433 _97559 _97561)). Qed.
Lemma lem7557437 (_97561 : int) : (term458 _97561) = (term516 _97561).
Proof. exact (@lem1988287 (real_of_int _97561) term35). Qed.
Lemma lem7557443 (_97561 : int) : (term517 _97561) = (term518 _97561).
Proof. exact (@lem1982792 (real_of_int _97561) term35). Qed.
Lemma lem7557445 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557446 : term35 = term520.
Proof. exact (@lem7557445 (NUMERAL 0)). Qed.
Lemma lem7557448 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557449 : term523 = term524.
Proof. exact (@lem7557448 term470). Qed.
Lemma lem7557450 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557451 : term525 = term526.
Proof. exact (MK_COMB (@lem7557450) (@lem7557449)). Qed.
Lemma lem7557452 : term527 = term528.
Proof. exact (MK_COMB (@lem7557451) (@lem7557446)). Qed.
Lemma lem7557453 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7557455 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557456 : term532 = term533.
Proof. exact (@lem7557455 term470 term470). Qed.
Lemma lem7557457 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557458 : term535 = term470.
Proof. exact (EQ_MP (@lem7557457) (@lem940073)). Qed.
Lemma lem7557459 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557460 : term533 = term469.
Proof. exact (MK_COMB (@lem7557459) (@lem7557458)). Qed.
Lemma lem7557461 : term532 = term469.
Proof. exact (TRANS (@lem7557456) (@lem7557460)). Qed.
Lemma lem7557463 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7557464 : term527 = term35.
Proof. exact (@lem7557463 term470). Qed.
Lemma lem7557465 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557466 : term537 = term538.
Proof. exact (MK_COMB (@lem7557465) (@lem7557464)). Qed.
Lemma lem7557467 : term529 = term520.
Proof. exact (MK_COMB (@lem7557466) (@lem7557461)). Qed.
Lemma lem7557468 : term528 = term520.
Proof. exact (TRANS (@lem7557453) (@lem7557467)). Qed.
Lemma lem7557469 : term527 = term520.
Proof. exact (TRANS (@lem7557452) (@lem7557468)). Qed.
Lemma lem7557471 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557472 : term520 = term35.
Proof. exact (@lem7557471 term35). Qed.
Lemma lem7557473 : term527 = term35.
Proof. exact (TRANS (@lem7557469) (@lem7557472)). Qed.
Lemma lem7557474 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7557475 (_97561 : int) : (term518 _97561) = (term540 _97561).
Proof. exact (MK_COMB (@lem7557474 _97561) (@lem7557473)). Qed.
Lemma lem7557476 (_97561 : int) : (term540 _97561) = (real_of_int _97561).
Proof. exact (@lem1982723 (real_of_int _97561)). Qed.
Lemma lem7557477 (_97561 : int) : (term518 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7557475 _97561) (@lem7557476 _97561)). Qed.
Lemma lem7557479 (_97561 : int) : (term517 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7557443 _97561) (@lem7557477 _97561)). Qed.
Lemma lem7557480 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557481 (_97561 : int) : (term541 _97561) = (term542 _97561).
Proof. exact (MK_COMB (@lem7557480) (@lem7557479 _97561)). Qed.
Lemma lem7557482 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557483 (_97561 : int) : (term516 _97561) = (term543 _97561).
Proof. exact (MK_COMB (@lem7557481 _97561) (@lem7557482)). Qed.
Lemma lem7557484 (_97561 : int) : (term458 _97561) = (term543 _97561).
Proof. exact (TRANS (@lem7557437 _97561) (@lem7557483 _97561)). Qed.
Lemma lem7557485 (_97559 : int) (_97560 : int) (_97561 : int) : (term485 _97561 _97559 _97560) = (term576 _97559 _97560 _97561).
Proof. exact (@lem1988287 (term483 _97559 _97560) (real_of_int _97561)). Qed.
Lemma lem7557495 (_97559 : int) (_97560 : int) (_97561 : int) : (term577 _97559 _97560 _97561) = (term578 _97559 _97560 _97561).
Proof. exact (@lem1982792 (term483 _97559 _97560) (real_of_int _97561)). Qed.
Lemma lem7557500 (_97561 : int) (_97559 : int) (_97560 : int) : (term578 _97559 _97560 _97561) = (term579 _97561 _97559 _97560).
Proof. exact (@lem1982761 (term570 _97561) (term483 _97559 _97560)). Qed.
Lemma lem7557502 (_97561 : int) (_97559 : int) (_97560 : int) : (term577 _97559 _97560 _97561) = (term579 _97561 _97559 _97560).
Proof. exact (TRANS (@lem7557495 _97559 _97560 _97561) (@lem7557500 _97561 _97559 _97560)). Qed.
Lemma lem7557503 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557504 (_97561 : int) (_97559 : int) (_97560 : int) : (term580 _97559 _97560 _97561) = (term581 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557503) (@lem7557502 _97561 _97559 _97560)). Qed.
Lemma lem7557505 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557506 (_97561 : int) (_97559 : int) (_97560 : int) : (term576 _97559 _97560 _97561) = (term582 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557504 _97561 _97559 _97560) (@lem7557505)). Qed.
Lemma lem7557507 (_97561 : int) (_97559 : int) (_97560 : int) : (term485 _97561 _97559 _97560) = (term582 _97561 _97559 _97560).
Proof. exact (TRANS (@lem7557485 _97559 _97560 _97561) (@lem7557506 _97561 _97559 _97560)). Qed.
Lemma lem7557508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557509 (_97561 : int) : (term486 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7557508) (@lem7557484 _97561)). Qed.
Lemma lem7557510 (_97561 : int) (_97559 : int) (_97560 : int) : (term487 _97561 _97559 _97560) = (term584 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557509 _97561) (@lem7557507 _97561 _97559 _97560)). Qed.
Lemma lem7557511 (_97559 : int) (_97561 : int) : (term451 _97561 _97559) = (term585 _97559 _97561).
Proof. exact (@lem1988287 (real_of_int _97559) (real_of_int _97561)). Qed.
Lemma lem7557524 (_97559 : int) (_97561 : int) : (term586 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982792 (real_of_int _97559) (real_of_int _97561)). Qed.
Lemma lem7557525 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557526 (_97559 : int) (_97561 : int) : (term588 _97559 _97561) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7557525) (@lem7557524 _97559 _97561)). Qed.
Lemma lem7557527 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557528 (_97559 : int) (_97561 : int) : (term585 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7557526 _97559 _97561) (@lem7557527)). Qed.
Lemma lem7557529 (_97559 : int) (_97561 : int) : (term451 _97561 _97559) = (term590 _97559 _97561).
Proof. exact (TRANS (@lem7557511 _97559 _97561) (@lem7557528 _97559 _97561)). Qed.
Lemma lem7557530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557531 (_97561 : int) (_97559 : int) (_97560 : int) : (term488 _97561 _97559 _97560) = (term591 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557530) (@lem7557510 _97561 _97559 _97560)). Qed.
Lemma lem7557532 (_97560 : int) (_97559 : int) (_97561 : int) : (term489 _97560 _97561 _97559) = (term592 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557531 _97561 _97559 _97560) (@lem7557529 _97559 _97561)). Qed.
Lemma lem7557533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557534 (_97559 : int) (_97561 : int) : (term490 _97559 _97561) = (term593 _97559 _97561).
Proof. exact (MK_COMB (@lem7557533) (@lem7557436 _97559 _97561)). Qed.
Lemma lem7557535 (_97560 : int) (_97559 : int) (_97561 : int) : (term491 _97560 _97561 _97559) = (term594 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557534 _97559 _97561) (@lem7557532 _97560 _97559 _97561)). Qed.
Lemma lem7557536 (_97561 : int) : (term458 _97561) = (term516 _97561).
Proof. exact (@lem1988287 (real_of_int _97561) term35). Qed.
Lemma lem7557542 (_97561 : int) : (term517 _97561) = (term518 _97561).
Proof. exact (@lem1982792 (real_of_int _97561) term35). Qed.
Lemma lem7557544 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557545 : term35 = term520.
Proof. exact (@lem7557544 (NUMERAL 0)). Qed.
Lemma lem7557547 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557548 : term523 = term524.
Proof. exact (@lem7557547 term470). Qed.
Lemma lem7557549 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557550 : term525 = term526.
Proof. exact (MK_COMB (@lem7557549) (@lem7557548)). Qed.
Lemma lem7557551 : term527 = term528.
Proof. exact (MK_COMB (@lem7557550) (@lem7557545)). Qed.
Lemma lem7557552 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7557554 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557555 : term532 = term533.
Proof. exact (@lem7557554 term470 term470). Qed.
Lemma lem7557556 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557557 : term535 = term470.
Proof. exact (EQ_MP (@lem7557556) (@lem940073)). Qed.
Lemma lem7557558 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557559 : term533 = term469.
Proof. exact (MK_COMB (@lem7557558) (@lem7557557)). Qed.
Lemma lem7557560 : term532 = term469.
Proof. exact (TRANS (@lem7557555) (@lem7557559)). Qed.
Lemma lem7557562 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7557563 : term527 = term35.
Proof. exact (@lem7557562 term470). Qed.
Lemma lem7557564 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557565 : term537 = term538.
Proof. exact (MK_COMB (@lem7557564) (@lem7557563)). Qed.
Lemma lem7557566 : term529 = term520.
Proof. exact (MK_COMB (@lem7557565) (@lem7557560)). Qed.
Lemma lem7557567 : term528 = term520.
Proof. exact (TRANS (@lem7557552) (@lem7557566)). Qed.
Lemma lem7557568 : term527 = term520.
Proof. exact (TRANS (@lem7557551) (@lem7557567)). Qed.
Lemma lem7557570 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557571 : term520 = term35.
Proof. exact (@lem7557570 term35). Qed.
Lemma lem7557572 : term527 = term35.
Proof. exact (TRANS (@lem7557568) (@lem7557571)). Qed.
Lemma lem7557573 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7557574 (_97561 : int) : (term518 _97561) = (term540 _97561).
Proof. exact (MK_COMB (@lem7557573 _97561) (@lem7557572)). Qed.
Lemma lem7557575 (_97561 : int) : (term540 _97561) = (real_of_int _97561).
Proof. exact (@lem1982723 (real_of_int _97561)). Qed.
Lemma lem7557576 (_97561 : int) : (term518 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7557574 _97561) (@lem7557575 _97561)). Qed.
Lemma lem7557578 (_97561 : int) : (term517 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7557542 _97561) (@lem7557576 _97561)). Qed.
Lemma lem7557579 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557580 (_97561 : int) : (term541 _97561) = (term542 _97561).
Proof. exact (MK_COMB (@lem7557579) (@lem7557578 _97561)). Qed.
Lemma lem7557581 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557582 (_97561 : int) : (term516 _97561) = (term543 _97561).
Proof. exact (MK_COMB (@lem7557580 _97561) (@lem7557581)). Qed.
Lemma lem7557583 (_97561 : int) : (term458 _97561) = (term543 _97561).
Proof. exact (TRANS (@lem7557536 _97561) (@lem7557582 _97561)). Qed.
Lemma lem7557584 (_97559 : int) (_97561 : int) : (term451 _97561 _97559) = (term585 _97559 _97561).
Proof. exact (@lem1988287 (real_of_int _97559) (real_of_int _97561)). Qed.
Lemma lem7557597 (_97559 : int) (_97561 : int) : (term586 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982792 (real_of_int _97559) (real_of_int _97561)). Qed.
Lemma lem7557598 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557599 (_97559 : int) (_97561 : int) : (term588 _97559 _97561) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7557598) (@lem7557597 _97559 _97561)). Qed.
Lemma lem7557600 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557601 (_97559 : int) (_97561 : int) : (term585 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7557599 _97559 _97561) (@lem7557600)). Qed.
Lemma lem7557602 (_97559 : int) (_97561 : int) : (term451 _97561 _97559) = (term590 _97559 _97561).
Proof. exact (TRANS (@lem7557584 _97559 _97561) (@lem7557601 _97559 _97561)). Qed.
Lemma lem7557603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557604 (_97561 : int) : (term486 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7557603) (@lem7557583 _97561)). Qed.
Lemma lem7557605 (_97559 : int) (_97561 : int) : (term492 _97561 _97559) = (term595 _97559 _97561).
Proof. exact (MK_COMB (@lem7557604 _97561) (@lem7557602 _97559 _97561)). Qed.
Lemma lem7557606 (_97561 : int) : (term475 _97561) = (term544 _97561).
Proof. exact (@lem1988287 term35 (term472 _97561)). Qed.
Lemma lem7557618 (_97561 : int) : (term545 _97561) = (term546 _97561).
Proof. exact (@lem1982792 term35 (term472 _97561)). Qed.
Lemma lem7557619 (_97561 : int) : (term547 _97561) = (term548 _97561).
Proof. exact (@lem1982781 (real_of_int _97561) term523 term469). Qed.
Lemma lem7557621 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557622 : term469 = term549.
Proof. exact (@lem7557621 term470). Qed.
Lemma lem7557624 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557625 : term523 = term524.
Proof. exact (@lem7557624 term470). Qed.
Lemma lem7557626 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557627 : term525 = term526.
Proof. exact (MK_COMB (@lem7557626) (@lem7557625)). Qed.
Lemma lem7557628 : term550 = term551.
Proof. exact (MK_COMB (@lem7557627) (@lem7557622)). Qed.
Lemma lem7557629 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7557631 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557632 : term532 = term533.
Proof. exact (@lem7557631 term470 term470). Qed.
Lemma lem7557633 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557634 : term535 = term470.
Proof. exact (EQ_MP (@lem7557633) (@lem940073)). Qed.
Lemma lem7557635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557636 : term533 = term469.
Proof. exact (MK_COMB (@lem7557635) (@lem7557634)). Qed.
Lemma lem7557637 : term532 = term469.
Proof. exact (TRANS (@lem7557632) (@lem7557636)). Qed.
Lemma lem7557639 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7557640 : term550 = term555.
Proof. exact (@lem7557639 term470 term470). Qed.
Lemma lem7557641 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557642 : term535 = term470.
Proof. exact (EQ_MP (@lem7557641) (@lem940073)). Qed.
Lemma lem7557643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557644 : term533 = term469.
Proof. exact (MK_COMB (@lem7557643) (@lem7557642)). Qed.
Lemma lem7557645 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7557646 : term555 = term523.
Proof. exact (MK_COMB (@lem7557645) (@lem7557644)). Qed.
Lemma lem7557647 : term550 = term523.
Proof. exact (TRANS (@lem7557640) (@lem7557646)). Qed.
Lemma lem7557648 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557649 : term556 = term557.
Proof. exact (MK_COMB (@lem7557648) (@lem7557647)). Qed.
Lemma lem7557650 : term552 = term524.
Proof. exact (MK_COMB (@lem7557649) (@lem7557637)). Qed.
Lemma lem7557651 : term551 = term524.
Proof. exact (TRANS (@lem7557629) (@lem7557650)). Qed.
Lemma lem7557652 : term550 = term524.
Proof. exact (TRANS (@lem7557628) (@lem7557651)). Qed.
Lemma lem7557654 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557655 : term524 = term523.
Proof. exact (@lem7557654 term523). Qed.
Lemma lem7557656 : term550 = term523.
Proof. exact (TRANS (@lem7557652) (@lem7557655)). Qed.
Lemma lem7557659 (_97561 : int) : (term558 _97561) = (term558 _97561).
Proof. exact (eq_refl (term558 _97561)). Qed.
Lemma lem7557660 (_97561 : int) : (term548 _97561) = (term559 _97561).
Proof. exact (MK_COMB (@lem7557659 _97561) (@lem7557656)). Qed.
Lemma lem7557661 (_97561 : int) : (term547 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7557619 _97561) (@lem7557660 _97561)). Qed.
Lemma lem7557662 : term560 = term560.
Proof. exact (eq_refl term560). Qed.
Lemma lem7557663 (_97561 : int) : (term546 _97561) = (term561 _97561).
Proof. exact (MK_COMB (@lem7557662) (@lem7557661 _97561)). Qed.
Lemma lem7557664 (_97561 : int) : (term561 _97561) = (term559 _97561).
Proof. exact (@lem1982721 (term559 _97561)). Qed.
Lemma lem7557665 (_97561 : int) : (term546 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7557663 _97561) (@lem7557664 _97561)). Qed.
Lemma lem7557667 (_97561 : int) : (term545 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7557618 _97561) (@lem7557665 _97561)). Qed.
Lemma lem7557668 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557669 (_97561 : int) : (term562 _97561) = (term563 _97561).
Proof. exact (MK_COMB (@lem7557668) (@lem7557667 _97561)). Qed.
Lemma lem7557670 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557671 (_97561 : int) : (term544 _97561) = (term564 _97561).
Proof. exact (MK_COMB (@lem7557669 _97561) (@lem7557670)). Qed.
Lemma lem7557672 (_97561 : int) : (term475 _97561) = (term564 _97561).
Proof. exact (TRANS (@lem7557606 _97561) (@lem7557671 _97561)). Qed.
Lemma lem7557673 (_97561 : int) (_97559 : int) (_97560 : int) : (term503 _97559 _97560 _97561) = (term596 _97561 _97559 _97560).
Proof. exact (@lem1988287 (real_of_int _97561) (term500 _97559 _97560)). Qed.
Lemma lem7557689 (_97561 : int) (_97559 : int) (_97560 : int) : (term597 _97561 _97559 _97560) = (term598 _97561 _97559 _97560).
Proof. exact (@lem1982792 (real_of_int _97561) (term500 _97559 _97560)). Qed.
Lemma lem7557690 (_97559 : int) (_97560 : int) : (term599 _97559 _97560) = (term600 _97559 _97560).
Proof. exact (@lem1982781 (term483 _97559 _97560) term523 term469). Qed.
Lemma lem7557692 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557693 : term469 = term549.
Proof. exact (@lem7557692 term470). Qed.
Lemma lem7557695 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557696 : term523 = term524.
Proof. exact (@lem7557695 term470). Qed.
Lemma lem7557697 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557698 : term525 = term526.
Proof. exact (MK_COMB (@lem7557697) (@lem7557696)). Qed.
Lemma lem7557699 : term550 = term551.
Proof. exact (MK_COMB (@lem7557698) (@lem7557693)). Qed.
Lemma lem7557700 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7557702 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557703 : term532 = term533.
Proof. exact (@lem7557702 term470 term470). Qed.
Lemma lem7557704 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557705 : term535 = term470.
Proof. exact (EQ_MP (@lem7557704) (@lem940073)). Qed.
Lemma lem7557706 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557707 : term533 = term469.
Proof. exact (MK_COMB (@lem7557706) (@lem7557705)). Qed.
Lemma lem7557708 : term532 = term469.
Proof. exact (TRANS (@lem7557703) (@lem7557707)). Qed.
Lemma lem7557710 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7557711 : term550 = term555.
Proof. exact (@lem7557710 term470 term470). Qed.
Lemma lem7557712 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557713 : term535 = term470.
Proof. exact (EQ_MP (@lem7557712) (@lem940073)). Qed.
Lemma lem7557714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557715 : term533 = term469.
Proof. exact (MK_COMB (@lem7557714) (@lem7557713)). Qed.
Lemma lem7557716 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7557717 : term555 = term523.
Proof. exact (MK_COMB (@lem7557716) (@lem7557715)). Qed.
Lemma lem7557718 : term550 = term523.
Proof. exact (TRANS (@lem7557711) (@lem7557717)). Qed.
Lemma lem7557719 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557720 : term556 = term557.
Proof. exact (MK_COMB (@lem7557719) (@lem7557718)). Qed.
Lemma lem7557721 : term552 = term524.
Proof. exact (MK_COMB (@lem7557720) (@lem7557708)). Qed.
Lemma lem7557722 : term551 = term524.
Proof. exact (TRANS (@lem7557700) (@lem7557721)). Qed.
Lemma lem7557723 : term550 = term524.
Proof. exact (TRANS (@lem7557699) (@lem7557722)). Qed.
Lemma lem7557725 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557726 : term524 = term523.
Proof. exact (@lem7557725 term523). Qed.
Lemma lem7557727 : term550 = term523.
Proof. exact (TRANS (@lem7557723) (@lem7557726)). Qed.
Lemma lem7557730 (_97559 : int) (_97560 : int) : (term601 _97559 _97560) = (term601 _97559 _97560).
Proof. exact (eq_refl (term601 _97559 _97560)). Qed.
Lemma lem7557731 (_97559 : int) (_97560 : int) : (term600 _97559 _97560) = (term602 _97559 _97560).
Proof. exact (MK_COMB (@lem7557730 _97559 _97560) (@lem7557727)). Qed.
Lemma lem7557732 (_97559 : int) (_97560 : int) : (term599 _97559 _97560) = (term602 _97559 _97560).
Proof. exact (TRANS (@lem7557690 _97559 _97560) (@lem7557731 _97559 _97560)). Qed.
Lemma lem7557733 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7557736 (_97561 : int) (_97559 : int) (_97560 : int) : (term598 _97561 _97559 _97560) = (term603 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557733 _97561) (@lem7557732 _97559 _97560)). Qed.
Lemma lem7557738 (_97561 : int) (_97559 : int) (_97560 : int) : (term597 _97561 _97559 _97560) = (term603 _97561 _97559 _97560).
Proof. exact (TRANS (@lem7557689 _97561 _97559 _97560) (@lem7557736 _97561 _97559 _97560)). Qed.
Lemma lem7557739 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557740 (_97561 : int) (_97559 : int) (_97560 : int) : (term604 _97561 _97559 _97560) = (term605 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557739) (@lem7557738 _97561 _97559 _97560)). Qed.
Lemma lem7557741 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557742 (_97561 : int) (_97559 : int) (_97560 : int) : (term596 _97561 _97559 _97560) = (term606 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557740 _97561 _97559 _97560) (@lem7557741)). Qed.
Lemma lem7557743 (_97561 : int) (_97559 : int) (_97560 : int) : (term503 _97559 _97560 _97561) = (term606 _97561 _97559 _97560).
Proof. exact (TRANS (@lem7557673 _97561 _97559 _97560) (@lem7557742 _97561 _97559 _97560)). Qed.
Lemma lem7557744 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557745 (_97561 : int) : (term479 _97561) = (term574 _97561).
Proof. exact (MK_COMB (@lem7557744) (@lem7557672 _97561)). Qed.
Lemma lem7557746 (_97561 : int) (_97559 : int) (_97560 : int) : (term504 _97559 _97560 _97561) = (term607 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557745 _97561) (@lem7557743 _97561 _97559 _97560)). Qed.
Lemma lem7557747 (_97561 : int) (_97559 : int) : (term477 _97559 _97561) = (term565 _97561 _97559).
Proof. exact (@lem1988287 (real_of_int _97561) (term472 _97559)). Qed.
Lemma lem7557759 (_97561 : int) (_97559 : int) : (term566 _97561 _97559) = (term567 _97561 _97559).
Proof. exact (@lem1982792 (real_of_int _97561) (term472 _97559)). Qed.
Lemma lem7557760 (_97559 : int) : (term547 _97559) = (term548 _97559).
Proof. exact (@lem1982781 (real_of_int _97559) term523 term469). Qed.
Lemma lem7557762 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7557763 : term469 = term549.
Proof. exact (@lem7557762 term470). Qed.
Lemma lem7557765 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7557766 : term523 = term524.
Proof. exact (@lem7557765 term470). Qed.
Lemma lem7557767 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7557768 : term525 = term526.
Proof. exact (MK_COMB (@lem7557767) (@lem7557766)). Qed.
Lemma lem7557769 : term550 = term551.
Proof. exact (MK_COMB (@lem7557768) (@lem7557763)). Qed.
Lemma lem7557770 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7557772 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7557773 : term532 = term533.
Proof. exact (@lem7557772 term470 term470). Qed.
Lemma lem7557774 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557775 : term535 = term470.
Proof. exact (EQ_MP (@lem7557774) (@lem940073)). Qed.
Lemma lem7557776 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557777 : term533 = term469.
Proof. exact (MK_COMB (@lem7557776) (@lem7557775)). Qed.
Lemma lem7557778 : term532 = term469.
Proof. exact (TRANS (@lem7557773) (@lem7557777)). Qed.
Lemma lem7557780 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7557781 : term550 = term555.
Proof. exact (@lem7557780 term470 term470). Qed.
Lemma lem7557782 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7557783 : term535 = term470.
Proof. exact (EQ_MP (@lem7557782) (@lem940073)). Qed.
Lemma lem7557784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7557785 : term533 = term469.
Proof. exact (MK_COMB (@lem7557784) (@lem7557783)). Qed.
Lemma lem7557786 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7557787 : term555 = term523.
Proof. exact (MK_COMB (@lem7557786) (@lem7557785)). Qed.
Lemma lem7557788 : term550 = term523.
Proof. exact (TRANS (@lem7557781) (@lem7557787)). Qed.
Lemma lem7557789 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7557790 : term556 = term557.
Proof. exact (MK_COMB (@lem7557789) (@lem7557788)). Qed.
Lemma lem7557791 : term552 = term524.
Proof. exact (MK_COMB (@lem7557790) (@lem7557778)). Qed.
Lemma lem7557792 : term551 = term524.
Proof. exact (TRANS (@lem7557770) (@lem7557791)). Qed.
Lemma lem7557793 : term550 = term524.
Proof. exact (TRANS (@lem7557769) (@lem7557792)). Qed.
Lemma lem7557795 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7557796 : term524 = term523.
Proof. exact (@lem7557795 term523). Qed.
Lemma lem7557797 : term550 = term523.
Proof. exact (TRANS (@lem7557793) (@lem7557796)). Qed.
Lemma lem7557800 (_97559 : int) : (term558 _97559) = (term558 _97559).
Proof. exact (eq_refl (term558 _97559)). Qed.
Lemma lem7557801 (_97559 : int) : (term548 _97559) = (term559 _97559).
Proof. exact (MK_COMB (@lem7557800 _97559) (@lem7557797)). Qed.
Lemma lem7557802 (_97559 : int) : (term547 _97559) = (term559 _97559).
Proof. exact (TRANS (@lem7557760 _97559) (@lem7557801 _97559)). Qed.
Lemma lem7557803 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7557804 (_97561 : int) (_97559 : int) : (term567 _97561 _97559) = (term568 _97561 _97559).
Proof. exact (MK_COMB (@lem7557803 _97561) (@lem7557802 _97559)). Qed.
Lemma lem7557809 (_97559 : int) (_97561 : int) : (term568 _97561 _97559) = (term569 _97559 _97561).
Proof. exact (@lem1982757 (term570 _97559) (real_of_int _97561) term523). Qed.
Lemma lem7557810 (_97559 : int) (_97561 : int) : (term567 _97561 _97559) = (term569 _97559 _97561).
Proof. exact (TRANS (@lem7557804 _97561 _97559) (@lem7557809 _97559 _97561)). Qed.
Lemma lem7557812 (_97559 : int) (_97561 : int) : (term566 _97561 _97559) = (term569 _97559 _97561).
Proof. exact (TRANS (@lem7557759 _97561 _97559) (@lem7557810 _97559 _97561)). Qed.
Lemma lem7557813 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7557814 (_97559 : int) (_97561 : int) : (term571 _97561 _97559) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7557813) (@lem7557812 _97559 _97561)). Qed.
Lemma lem7557815 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7557816 (_97559 : int) (_97561 : int) : (term565 _97561 _97559) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7557814 _97559 _97561) (@lem7557815)). Qed.
Lemma lem7557817 (_97559 : int) (_97561 : int) : (term477 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (TRANS (@lem7557747 _97561 _97559) (@lem7557816 _97559 _97561)). Qed.
Lemma lem7557818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557819 (_97561 : int) (_97559 : int) (_97560 : int) : (term505 _97559 _97560 _97561) = (term608 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557818) (@lem7557746 _97561 _97559 _97560)). Qed.
Lemma lem7557820 (_97560 : int) (_97559 : int) (_97561 : int) : (term506 _97560 _97559 _97561) = (term609 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557819 _97561 _97559 _97560) (@lem7557817 _97559 _97561)). Qed.
Lemma lem7557821 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557822 (_97559 : int) (_97561 : int) : (term507 _97561 _97559) = (term610 _97559 _97561).
Proof. exact (MK_COMB (@lem7557821) (@lem7557605 _97559 _97561)). Qed.
Lemma lem7557823 (_97560 : int) (_97559 : int) (_97561 : int) : (term508 _97560 _97559 _97561) = (term611 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557822 _97559 _97561) (@lem7557820 _97560 _97559 _97561)). Qed.
Lemma lem7557824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557825 (_97560 : int) (_97559 : int) (_97561 : int) : (term509 _97560 _97561 _97559) = (term612 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557824) (@lem7557535 _97560 _97559 _97561)). Qed.
Lemma lem7557826 (_97560 : int) (_97559 : int) (_97561 : int) : (term510 _97560 _97559 _97561) = (term613 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557825 _97560 _97559 _97561) (@lem7557823 _97560 _97559 _97561)). Qed.
Lemma lem7557827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557828 (_97561 : int) : (term486 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7557827) (@lem7557295 _97561)). Qed.
Lemma lem7557829 (_97560 : int) (_97559 : int) (_97561 : int) : (term511 _97560 _97559 _97561) = (term614 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557828 _97561) (@lem7557826 _97560 _97559 _97561)). Qed.
Lemma lem7557830 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557831 (_97560 : int) : (term486 _97560) = (term583 _97560).
Proof. exact (MK_COMB (@lem7557830) (@lem7557247 _97560)). Qed.
Lemma lem7557832 (_97560 : int) (_97559 : int) (_97561 : int) : (term512 _97560 _97559 _97561) = (term615 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557831 _97560) (@lem7557829 _97560 _97559 _97561)). Qed.
Lemma lem7557833 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7557834 (_97559 : int) : (term486 _97559) = (term583 _97559).
Proof. exact (MK_COMB (@lem7557833) (@lem7557199 _97559)). Qed.
Lemma lem7557835 (_97560 : int) (_97559 : int) (_97561 : int) : (term513 _97560 _97559 _97561) = (term616 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557834 _97559) (@lem7557832 _97560 _97559 _97561)). Qed.
Lemma lem7557842 (_97560 : int) (_97559 : int) (_97561 : int) : (term515 _97560 _97559 _97561) = (term616 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557151 _97560 _97559 _97561) (@lem7557835 _97560 _97559 _97561)). Qed.
Lemma lem7557862 (_97560 : int) (_97559 : int) (_97561 : int) : (term611 _97560 _97559 _97561) = (term617 _97560 _97559 _97561).
Proof. exact (@lem19158 (term607 _97561 _97559 _97560) (term595 _97559 _97561) (term573 _97559 _97561)). Qed.
Lemma lem7557863 (_97559 : int) (_97561 : int) : (term618 _97559 _97561) = (term618 _97559 _97561).
Proof. exact (eq_refl (term618 _97559 _97561)). Qed.
Lemma lem7557870 (_97561 : int) (_97559 : int) (_97560 : int) : (term619 _97561 _97559 _97560) = (term620 _97561 _97559 _97560).
Proof. exact (@lem19158 (term564 _97561) (term595 _97559 _97561) (term606 _97561 _97559 _97560)). Qed.
Lemma lem7557871 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557872 (_97561 : int) (_97559 : int) (_97560 : int) : (term621 _97561 _97559 _97560) = (term622 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557871) (@lem7557870 _97561 _97559 _97560)). Qed.
Lemma lem7557873 (_97560 : int) (_97559 : int) (_97561 : int) : (term617 _97560 _97559 _97561) = (term623 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557872 _97561 _97559 _97560) (@lem7557863 _97559 _97561)). Qed.
Lemma lem7557875 (_97560 : int) (_97559 : int) (_97561 : int) : (term611 _97560 _97559 _97561) = (term623 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557862 _97560 _97559 _97561) (@lem7557873 _97560 _97559 _97561)). Qed.
Lemma lem7557904 (_97560 : int) (_97559 : int) (_97561 : int) : (term594 _97560 _97559 _97561) = (term624 _97560 _97559 _97561).
Proof. exact (@lem19367 (term564 _97561) (term573 _97559 _97561) (term592 _97560 _97559 _97561)). Qed.
Lemma lem7557905 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557906 (_97560 : int) (_97559 : int) (_97561 : int) : (term612 _97560 _97559 _97561) = (term625 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557905) (@lem7557904 _97560 _97559 _97561)). Qed.
Lemma lem7557907 (_97560 : int) (_97559 : int) (_97561 : int) : (term613 _97560 _97559 _97561) = (term626 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557906 _97560 _97559 _97561) (@lem7557875 _97560 _97559 _97561)). Qed.
Lemma lem7557910 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (eq_refl (term583 _97561)). Qed.
Lemma lem7557911 (_97560 : int) (_97559 : int) (_97561 : int) : (term614 _97560 _97559 _97561) = (term627 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557910 _97561) (@lem7557907 _97560 _97559 _97561)). Qed.
Lemma lem7557912 (_97560 : int) (_97559 : int) (_97561 : int) : (term627 _97560 _97559 _97561) = (term628 _97560 _97559 _97561).
Proof. exact (@lem19158 (term624 _97560 _97559 _97561) (term543 _97561) (term623 _97560 _97559 _97561)). Qed.
Lemma lem7557913 (_97560 : int) (_97559 : int) (_97561 : int) : (term629 _97560 _97559 _97561) = (term630 _97560 _97559 _97561).
Proof. exact (@lem19158 (term620 _97561 _97559 _97560) (term543 _97561) (term618 _97559 _97561)). Qed.
Lemma lem7557914 (_97559 : int) (_97561 : int) : (term631 _97559 _97561) = (term631 _97559 _97561).
Proof. exact (eq_refl (term631 _97559 _97561)). Qed.
Lemma lem7557921 (_97561 : int) (_97559 : int) (_97560 : int) : (term632 _97561 _97559 _97560) = (term633 _97561 _97559 _97560).
Proof. exact (@lem19158 (term634 _97559 _97561) (term543 _97561) (term635 _97561 _97559 _97560)). Qed.
Lemma lem7557922 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557923 (_97561 : int) (_97559 : int) (_97560 : int) : (term636 _97561 _97559 _97560) = (term637 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557922) (@lem7557921 _97561 _97559 _97560)). Qed.
Lemma lem7557924 (_97560 : int) (_97559 : int) (_97561 : int) : (term630 _97560 _97559 _97561) = (term638 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557923 _97561 _97559 _97560) (@lem7557914 _97559 _97561)). Qed.
Lemma lem7557925 (_97560 : int) (_97559 : int) (_97561 : int) : (term629 _97560 _97559 _97561) = (term638 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557913 _97560 _97559 _97561) (@lem7557924 _97560 _97559 _97561)). Qed.
Lemma lem7557932 (_97560 : int) (_97559 : int) (_97561 : int) : (term639 _97560 _97559 _97561) = (term640 _97560 _97559 _97561).
Proof. exact (@lem19158 (term641 _97560 _97559 _97561) (term543 _97561) (term642 _97560 _97559 _97561)). Qed.
Lemma lem7557933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557934 (_97560 : int) (_97559 : int) (_97561 : int) : (term643 _97560 _97559 _97561) = (term644 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557933) (@lem7557932 _97560 _97559 _97561)). Qed.
Lemma lem7557935 (_97560 : int) (_97559 : int) (_97561 : int) : (term628 _97560 _97559 _97561) = (term645 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557934 _97560 _97559 _97561) (@lem7557925 _97560 _97559 _97561)). Qed.
Lemma lem7557936 (_97560 : int) (_97559 : int) (_97561 : int) : (term627 _97560 _97559 _97561) = (term645 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557912 _97560 _97559 _97561) (@lem7557935 _97560 _97559 _97561)). Qed.
Lemma lem7557937 (_97560 : int) (_97559 : int) (_97561 : int) : (term614 _97560 _97559 _97561) = (term645 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557911 _97560 _97559 _97561) (@lem7557936 _97560 _97559 _97561)). Qed.
Lemma lem7557940 (_97560 : int) : (term583 _97560) = (term583 _97560).
Proof. exact (eq_refl (term583 _97560)). Qed.
Lemma lem7557941 (_97560 : int) (_97559 : int) (_97561 : int) : (term615 _97560 _97559 _97561) = (term646 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557940 _97560) (@lem7557937 _97560 _97559 _97561)). Qed.
Lemma lem7557942 (_97560 : int) (_97559 : int) (_97561 : int) : (term646 _97560 _97559 _97561) = (term647 _97560 _97559 _97561).
Proof. exact (@lem19158 (term640 _97560 _97559 _97561) (term543 _97560) (term638 _97560 _97559 _97561)). Qed.
Lemma lem7557943 (_97560 : int) (_97559 : int) (_97561 : int) : (term648 _97560 _97559 _97561) = (term649 _97560 _97559 _97561).
Proof. exact (@lem19158 (term633 _97561 _97559 _97560) (term543 _97560) (term631 _97559 _97561)). Qed.
Lemma lem7557944 (_97560 : int) (_97559 : int) (_97561 : int) : (term650 _97560 _97559 _97561) = (term650 _97560 _97559 _97561).
Proof. exact (eq_refl (term650 _97560 _97559 _97561)). Qed.
Lemma lem7557951 (_97561 : int) (_97559 : int) (_97560 : int) : (term651 _97561 _97559 _97560) = (term652 _97561 _97559 _97560).
Proof. exact (@lem19158 (term653 _97559 _97561) (term543 _97560) (term654 _97561 _97559 _97560)). Qed.
Lemma lem7557952 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557953 (_97561 : int) (_97559 : int) (_97560 : int) : (term655 _97561 _97559 _97560) = (term656 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557952) (@lem7557951 _97561 _97559 _97560)). Qed.
Lemma lem7557954 (_97560 : int) (_97559 : int) (_97561 : int) : (term649 _97560 _97559 _97561) = (term657 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557953 _97561 _97559 _97560) (@lem7557944 _97560 _97559 _97561)). Qed.
Lemma lem7557955 (_97560 : int) (_97559 : int) (_97561 : int) : (term648 _97560 _97559 _97561) = (term657 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557943 _97560 _97559 _97561) (@lem7557954 _97560 _97559 _97561)). Qed.
Lemma lem7557962 (_97560 : int) (_97559 : int) (_97561 : int) : (term658 _97560 _97559 _97561) = (term659 _97560 _97559 _97561).
Proof. exact (@lem19158 (term660 _97560 _97559 _97561) (term543 _97560) (term661 _97560 _97559 _97561)). Qed.
Lemma lem7557963 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557964 (_97560 : int) (_97559 : int) (_97561 : int) : (term662 _97560 _97559 _97561) = (term663 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557963) (@lem7557962 _97560 _97559 _97561)). Qed.
Lemma lem7557965 (_97560 : int) (_97559 : int) (_97561 : int) : (term647 _97560 _97559 _97561) = (term664 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557964 _97560 _97559 _97561) (@lem7557955 _97560 _97559 _97561)). Qed.
Lemma lem7557966 (_97560 : int) (_97559 : int) (_97561 : int) : (term646 _97560 _97559 _97561) = (term664 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557942 _97560 _97559 _97561) (@lem7557965 _97560 _97559 _97561)). Qed.
Lemma lem7557967 (_97560 : int) (_97559 : int) (_97561 : int) : (term615 _97560 _97559 _97561) = (term664 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557941 _97560 _97559 _97561) (@lem7557966 _97560 _97559 _97561)). Qed.
Lemma lem7557970 (_97559 : int) : (term583 _97559) = (term583 _97559).
Proof. exact (eq_refl (term583 _97559)). Qed.
Lemma lem7557971 (_97560 : int) (_97559 : int) (_97561 : int) : (term616 _97560 _97559 _97561) = (term665 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557970 _97559) (@lem7557967 _97560 _97559 _97561)). Qed.
Lemma lem7557972 (_97560 : int) (_97559 : int) (_97561 : int) : (term665 _97560 _97559 _97561) = (term666 _97560 _97559 _97561).
Proof. exact (@lem19158 (term659 _97560 _97559 _97561) (term543 _97559) (term657 _97560 _97559 _97561)). Qed.
Lemma lem7557973 (_97560 : int) (_97559 : int) (_97561 : int) : (term667 _97560 _97559 _97561) = (term668 _97560 _97559 _97561).
Proof. exact (@lem19158 (term652 _97561 _97559 _97560) (term543 _97559) (term650 _97560 _97559 _97561)). Qed.
Lemma lem7557974 (_97560 : int) (_97559 : int) (_97561 : int) : (term669 _97560 _97559 _97561) = (term669 _97560 _97559 _97561).
Proof. exact (eq_refl (term669 _97560 _97559 _97561)). Qed.
Lemma lem7557981 (_97561 : int) (_97559 : int) (_97560 : int) : (term670 _97561 _97559 _97560) = (term671 _97561 _97559 _97560).
Proof. exact (@lem19158 (term672 _97560 _97559 _97561) (term543 _97559) (term673 _97561 _97559 _97560)). Qed.
Lemma lem7557982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557983 (_97561 : int) (_97559 : int) (_97560 : int) : (term674 _97561 _97559 _97560) = (term675 _97561 _97559 _97560).
Proof. exact (MK_COMB (@lem7557982) (@lem7557981 _97561 _97559 _97560)). Qed.
Lemma lem7557984 (_97560 : int) (_97559 : int) (_97561 : int) : (term668 _97560 _97559 _97561) = (term676 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557983 _97561 _97559 _97560) (@lem7557974 _97560 _97559 _97561)). Qed.
Lemma lem7557985 (_97560 : int) (_97559 : int) (_97561 : int) : (term667 _97560 _97559 _97561) = (term676 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557973 _97560 _97559 _97561) (@lem7557984 _97560 _97559 _97561)). Qed.
Lemma lem7557992 (_97560 : int) (_97559 : int) (_97561 : int) : (term677 _97560 _97559 _97561) = (term678 _97560 _97559 _97561).
Proof. exact (@lem19158 (term679 _97560 _97559 _97561) (term543 _97559) (term680 _97560 _97559 _97561)). Qed.
Lemma lem7557993 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7557994 (_97560 : int) (_97559 : int) (_97561 : int) : (term681 _97560 _97559 _97561) = (term682 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557993) (@lem7557992 _97560 _97559 _97561)). Qed.
Lemma lem7557995 (_97560 : int) (_97559 : int) (_97561 : int) : (term666 _97560 _97559 _97561) = (term683 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7557994 _97560 _97559 _97561) (@lem7557985 _97560 _97559 _97561)). Qed.
Lemma lem7557996 (_97560 : int) (_97559 : int) (_97561 : int) : (term665 _97560 _97559 _97561) = (term683 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557972 _97560 _97559 _97561) (@lem7557995 _97560 _97559 _97561)). Qed.
Lemma lem7557997 (_97560 : int) (_97559 : int) (_97561 : int) : (term616 _97560 _97559 _97561) = (term683 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557971 _97560 _97559 _97561) (@lem7557996 _97560 _97559 _97561)). Qed.
Lemma lem7557998 (_97560 : int) (_97559 : int) (_97561 : int) : (term515 _97560 _97559 _97561) = (term683 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7557842 _97560 _97559 _97561) (@lem7557997 _97560 _97559 _97561)). Qed.
Lemma lem7558000 (_97560 : int) (_97559 : int) (_97561 : int) : (term684 _97561 _97559 _97560) = (term685 _97560 _97559 _97561).
Proof. exact (eq_refl (term684 _97561 _97559 _97560)). Qed.
Lemma lem7558001 (_97561 : int) (_97559 : int) (_97560 : int) : (term685 _97560 _97559 _97561) = (term684 _97561 _97559 _97560).
Proof. exact (SYM (@lem7558000 _97560 _97559 _97561)). Qed.
Lemma lem7558002 (_97560 : int) (_97561 : int) (_97559 : int) : (term684 _97561 _97559 _97560) = (term686 _97560 _97561 _97559).
Proof. exact (@lem1483205 (real_of_int _97560) (term687 _97560 _97559 _97561) (real_of_int _97559)). Qed.
Lemma lem7558003 (_97560 : int) (_97561 : int) (_97559 : int) : (term685 _97560 _97559 _97561) = (term686 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7558001 _97561 _97559 _97560) (@lem7558002 _97560 _97561 _97559)). Qed.
Lemma lem7558004 (_97560 : int) (_97559 : int) (_97561 : int) : (term688 _97560 _97561 _97559) = (term689 _97560 _97559 _97561).
Proof. exact (eq_refl (term688 _97560 _97561 _97559)). Qed.
Lemma lem7558005 (_97559 : int) (_97560 : int) : (term690 _97559 _97560) = (term690 _97559 _97560).
Proof. exact (eq_refl (term690 _97559 _97560)). Qed.
Lemma lem7558006 (_97560 : int) (_97559 : int) (_97561 : int) : (term691 _97560 _97561 _97559) = (term692 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558005 _97559 _97560) (@lem7558004 _97560 _97559 _97561)). Qed.
Lemma lem7558007 (_97560 : int) (_97559 : int) (_97561 : int) : (term693 _97559 _97561 _97560) = (term694 _97560 _97559 _97561).
Proof. exact (eq_refl (term693 _97559 _97561 _97560)). Qed.
Lemma lem7558008 (_97560 : int) (_97559 : int) : (term695 _97560 _97559) = (term695 _97560 _97559).
Proof. exact (eq_refl (term695 _97560 _97559)). Qed.
Lemma lem7558009 (_97560 : int) (_97559 : int) (_97561 : int) : (term696 _97559 _97561 _97560) = (term697 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558008 _97560 _97559) (@lem7558007 _97560 _97559 _97561)). Qed.
Lemma lem7558010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7558011 (_97560 : int) (_97559 : int) (_97561 : int) : (term698 _97559 _97561 _97560) = (term699 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558010) (@lem7558009 _97560 _97559 _97561)). Qed.
Lemma lem7558012 (_97560 : int) (_97559 : int) (_97561 : int) : (term686 _97560 _97561 _97559) = (term700 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558011 _97560 _97559 _97561) (@lem7558006 _97560 _97559 _97561)). Qed.
Lemma lem7558013 (_97560 : int) (_97559 : int) (_97561 : int) : (term701 _97560 _97559 _97561) = (term701 _97560 _97559 _97561).
Proof. exact (eq_refl (term701 _97560 _97559 _97561)). Qed.
Lemma lem7558014 (_97560 : int) (_97559 : int) (_97561 : int) : ((term685 _97560 _97559 _97561) = (term686 _97560 _97561 _97559)) = ((term685 _97560 _97559 _97561) = (term700 _97560 _97559 _97561)).
Proof. exact (MK_COMB (@lem7558013 _97560 _97559 _97561) (@lem7558012 _97560 _97559 _97561)). Qed.
Lemma lem7558015 (_97560 : int) (_97559 : int) (_97561 : int) : (term685 _97560 _97559 _97561) = (term700 _97560 _97559 _97561).
Proof. exact (EQ_MP (@lem7558014 _97560 _97559 _97561) (@lem7558003 _97560 _97561 _97559)). Qed.
Lemma lem7558016 (_97560 : int) (_97559 : int) : (term702 _97560 _97559) = (term585 _97560 _97559).
Proof. exact (@lem1988291 (real_of_int _97560) (real_of_int _97559)). Qed.
Lemma lem7558022 (_97560 : int) (_97559 : int) : (term586 _97560 _97559) = (term587 _97560 _97559).
Proof. exact (@lem1982792 (real_of_int _97560) (real_of_int _97559)). Qed.
Lemma lem7558027 (_97559 : int) (_97560 : int) : (term587 _97560 _97559) = (term703 _97559 _97560).
Proof. exact (@lem1982761 (term570 _97559) (real_of_int _97560)). Qed.
Lemma lem7558029 (_97559 : int) (_97560 : int) : (term586 _97560 _97559) = (term703 _97559 _97560).
Proof. exact (TRANS (@lem7558022 _97560 _97559) (@lem7558027 _97559 _97560)). Qed.
Lemma lem7558030 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558031 (_97559 : int) (_97560 : int) : (term588 _97560 _97559) = (term704 _97559 _97560).
Proof. exact (MK_COMB (@lem7558030) (@lem7558029 _97559 _97560)). Qed.
Lemma lem7558032 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558033 (_97559 : int) (_97560 : int) : (term585 _97560 _97559) = (term705 _97559 _97560).
Proof. exact (MK_COMB (@lem7558031 _97559 _97560) (@lem7558032)). Qed.
Lemma lem7558034 (_97559 : int) (_97560 : int) : (term702 _97560 _97559) = (term705 _97559 _97560).
Proof. exact (TRANS (@lem7558016 _97560 _97559) (@lem7558033 _97559 _97560)). Qed.
Lemma lem7558035 (_97559 : int) : (term543 _97559) = (term516 _97559).
Proof. exact (@lem1988291 (real_of_int _97559) term35). Qed.
Lemma lem7558041 (_97559 : int) : (term517 _97559) = (term518 _97559).
Proof. exact (@lem1982792 (real_of_int _97559) term35). Qed.
Lemma lem7558043 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558044 : term35 = term520.
Proof. exact (@lem7558043 (NUMERAL 0)). Qed.
Lemma lem7558046 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558047 : term523 = term524.
Proof. exact (@lem7558046 term470). Qed.
Lemma lem7558048 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558049 : term525 = term526.
Proof. exact (MK_COMB (@lem7558048) (@lem7558047)). Qed.
Lemma lem7558050 : term527 = term528.
Proof. exact (MK_COMB (@lem7558049) (@lem7558044)). Qed.
Lemma lem7558051 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558053 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558054 : term532 = term533.
Proof. exact (@lem7558053 term470 term470). Qed.
Lemma lem7558055 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558056 : term535 = term470.
Proof. exact (EQ_MP (@lem7558055) (@lem940073)). Qed.
Lemma lem7558057 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558058 : term533 = term469.
Proof. exact (MK_COMB (@lem7558057) (@lem7558056)). Qed.
Lemma lem7558059 : term532 = term469.
Proof. exact (TRANS (@lem7558054) (@lem7558058)). Qed.
Lemma lem7558061 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558062 : term527 = term35.
Proof. exact (@lem7558061 term470). Qed.
Lemma lem7558063 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558064 : term537 = term538.
Proof. exact (MK_COMB (@lem7558063) (@lem7558062)). Qed.
Lemma lem7558065 : term529 = term520.
Proof. exact (MK_COMB (@lem7558064) (@lem7558059)). Qed.
Lemma lem7558066 : term528 = term520.
Proof. exact (TRANS (@lem7558051) (@lem7558065)). Qed.
Lemma lem7558067 : term527 = term520.
Proof. exact (TRANS (@lem7558050) (@lem7558066)). Qed.
Lemma lem7558069 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558070 : term520 = term35.
Proof. exact (@lem7558069 term35). Qed.
Lemma lem7558071 : term527 = term35.
Proof. exact (TRANS (@lem7558067) (@lem7558070)). Qed.
Lemma lem7558072 (_97559 : int) : (term471 _97559) = (term471 _97559).
Proof. exact (eq_refl (term471 _97559)). Qed.
Lemma lem7558073 (_97559 : int) : (term518 _97559) = (term540 _97559).
Proof. exact (MK_COMB (@lem7558072 _97559) (@lem7558071)). Qed.
Lemma lem7558074 (_97559 : int) : (term540 _97559) = (real_of_int _97559).
Proof. exact (@lem1982723 (real_of_int _97559)). Qed.
Lemma lem7558075 (_97559 : int) : (term518 _97559) = (real_of_int _97559).
Proof. exact (TRANS (@lem7558073 _97559) (@lem7558074 _97559)). Qed.
Lemma lem7558077 (_97559 : int) : (term517 _97559) = (real_of_int _97559).
Proof. exact (TRANS (@lem7558041 _97559) (@lem7558075 _97559)). Qed.
Lemma lem7558078 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558079 (_97559 : int) : (term541 _97559) = (term542 _97559).
Proof. exact (MK_COMB (@lem7558078) (@lem7558077 _97559)). Qed.
Lemma lem7558080 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558081 (_97559 : int) : (term516 _97559) = (term543 _97559).
Proof. exact (MK_COMB (@lem7558079 _97559) (@lem7558080)). Qed.
Lemma lem7558082 (_97559 : int) : (term543 _97559) = (term543 _97559).
Proof. exact (TRANS (@lem7558035 _97559) (@lem7558081 _97559)). Qed.
Lemma lem7558083 (_97560 : int) : (term543 _97560) = (term516 _97560).
Proof. exact (@lem1988291 (real_of_int _97560) term35). Qed.
Lemma lem7558089 (_97560 : int) : (term517 _97560) = (term518 _97560).
Proof. exact (@lem1982792 (real_of_int _97560) term35). Qed.
Lemma lem7558091 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558092 : term35 = term520.
Proof. exact (@lem7558091 (NUMERAL 0)). Qed.
Lemma lem7558094 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558095 : term523 = term524.
Proof. exact (@lem7558094 term470). Qed.
Lemma lem7558096 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558097 : term525 = term526.
Proof. exact (MK_COMB (@lem7558096) (@lem7558095)). Qed.
Lemma lem7558098 : term527 = term528.
Proof. exact (MK_COMB (@lem7558097) (@lem7558092)). Qed.
Lemma lem7558099 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558101 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558102 : term532 = term533.
Proof. exact (@lem7558101 term470 term470). Qed.
Lemma lem7558103 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558104 : term535 = term470.
Proof. exact (EQ_MP (@lem7558103) (@lem940073)). Qed.
Lemma lem7558105 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558106 : term533 = term469.
Proof. exact (MK_COMB (@lem7558105) (@lem7558104)). Qed.
Lemma lem7558107 : term532 = term469.
Proof. exact (TRANS (@lem7558102) (@lem7558106)). Qed.
Lemma lem7558109 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558110 : term527 = term35.
Proof. exact (@lem7558109 term470). Qed.
Lemma lem7558111 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558112 : term537 = term538.
Proof. exact (MK_COMB (@lem7558111) (@lem7558110)). Qed.
Lemma lem7558113 : term529 = term520.
Proof. exact (MK_COMB (@lem7558112) (@lem7558107)). Qed.
Lemma lem7558114 : term528 = term520.
Proof. exact (TRANS (@lem7558099) (@lem7558113)). Qed.
Lemma lem7558115 : term527 = term520.
Proof. exact (TRANS (@lem7558098) (@lem7558114)). Qed.
Lemma lem7558117 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558118 : term520 = term35.
Proof. exact (@lem7558117 term35). Qed.
Lemma lem7558119 : term527 = term35.
Proof. exact (TRANS (@lem7558115) (@lem7558118)). Qed.
Lemma lem7558120 (_97560 : int) : (term471 _97560) = (term471 _97560).
Proof. exact (eq_refl (term471 _97560)). Qed.
Lemma lem7558121 (_97560 : int) : (term518 _97560) = (term540 _97560).
Proof. exact (MK_COMB (@lem7558120 _97560) (@lem7558119)). Qed.
Lemma lem7558122 (_97560 : int) : (term540 _97560) = (real_of_int _97560).
Proof. exact (@lem1982723 (real_of_int _97560)). Qed.
Lemma lem7558123 (_97560 : int) : (term518 _97560) = (real_of_int _97560).
Proof. exact (TRANS (@lem7558121 _97560) (@lem7558122 _97560)). Qed.
Lemma lem7558125 (_97560 : int) : (term517 _97560) = (real_of_int _97560).
Proof. exact (TRANS (@lem7558089 _97560) (@lem7558123 _97560)). Qed.
Lemma lem7558126 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558127 (_97560 : int) : (term541 _97560) = (term542 _97560).
Proof. exact (MK_COMB (@lem7558126) (@lem7558125 _97560)). Qed.
Lemma lem7558128 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558129 (_97560 : int) : (term516 _97560) = (term543 _97560).
Proof. exact (MK_COMB (@lem7558127 _97560) (@lem7558128)). Qed.
Lemma lem7558130 (_97560 : int) : (term543 _97560) = (term543 _97560).
Proof. exact (TRANS (@lem7558083 _97560) (@lem7558129 _97560)). Qed.
Lemma lem7558131 (_97561 : int) : (term543 _97561) = (term516 _97561).
Proof. exact (@lem1988291 (real_of_int _97561) term35). Qed.
Lemma lem7558137 (_97561 : int) : (term517 _97561) = (term518 _97561).
Proof. exact (@lem1982792 (real_of_int _97561) term35). Qed.
Lemma lem7558139 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558140 : term35 = term520.
Proof. exact (@lem7558139 (NUMERAL 0)). Qed.
Lemma lem7558142 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558143 : term523 = term524.
Proof. exact (@lem7558142 term470). Qed.
Lemma lem7558144 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558145 : term525 = term526.
Proof. exact (MK_COMB (@lem7558144) (@lem7558143)). Qed.
Lemma lem7558146 : term527 = term528.
Proof. exact (MK_COMB (@lem7558145) (@lem7558140)). Qed.
Lemma lem7558147 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558149 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558150 : term532 = term533.
Proof. exact (@lem7558149 term470 term470). Qed.
Lemma lem7558151 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558152 : term535 = term470.
Proof. exact (EQ_MP (@lem7558151) (@lem940073)). Qed.
Lemma lem7558153 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558154 : term533 = term469.
Proof. exact (MK_COMB (@lem7558153) (@lem7558152)). Qed.
Lemma lem7558155 : term532 = term469.
Proof. exact (TRANS (@lem7558150) (@lem7558154)). Qed.
Lemma lem7558157 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558158 : term527 = term35.
Proof. exact (@lem7558157 term470). Qed.
Lemma lem7558159 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558160 : term537 = term538.
Proof. exact (MK_COMB (@lem7558159) (@lem7558158)). Qed.
Lemma lem7558161 : term529 = term520.
Proof. exact (MK_COMB (@lem7558160) (@lem7558155)). Qed.
Lemma lem7558162 : term528 = term520.
Proof. exact (TRANS (@lem7558147) (@lem7558161)). Qed.
Lemma lem7558163 : term527 = term520.
Proof. exact (TRANS (@lem7558146) (@lem7558162)). Qed.
Lemma lem7558165 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558166 : term520 = term35.
Proof. exact (@lem7558165 term35). Qed.
Lemma lem7558167 : term527 = term35.
Proof. exact (TRANS (@lem7558163) (@lem7558166)). Qed.
Lemma lem7558168 (_97561 : int) : (term471 _97561) = (term471 _97561).
Proof. exact (eq_refl (term471 _97561)). Qed.
Lemma lem7558169 (_97561 : int) : (term518 _97561) = (term540 _97561).
Proof. exact (MK_COMB (@lem7558168 _97561) (@lem7558167)). Qed.
Lemma lem7558170 (_97561 : int) : (term540 _97561) = (real_of_int _97561).
Proof. exact (@lem1982723 (real_of_int _97561)). Qed.
Lemma lem7558171 (_97561 : int) : (term518 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7558169 _97561) (@lem7558170 _97561)). Qed.
Lemma lem7558173 (_97561 : int) : (term517 _97561) = (real_of_int _97561).
Proof. exact (TRANS (@lem7558137 _97561) (@lem7558171 _97561)). Qed.
Lemma lem7558174 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558175 (_97561 : int) : (term541 _97561) = (term542 _97561).
Proof. exact (MK_COMB (@lem7558174) (@lem7558173 _97561)). Qed.
Lemma lem7558176 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558177 (_97561 : int) : (term516 _97561) = (term543 _97561).
Proof. exact (MK_COMB (@lem7558175 _97561) (@lem7558176)). Qed.
Lemma lem7558178 (_97561 : int) : (term543 _97561) = (term543 _97561).
Proof. exact (TRANS (@lem7558131 _97561) (@lem7558177 _97561)). Qed.
Lemma lem7558179 (_97561 : int) : (term564 _97561) = (term706 _97561).
Proof. exact (@lem1988291 (term559 _97561) term35). Qed.
Lemma lem7558197 (_97561 : int) : (term707 _97561) = (term708 _97561).
Proof. exact (@lem1982792 (term559 _97561) term35). Qed.
Lemma lem7558199 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558200 : term35 = term520.
Proof. exact (@lem7558199 (NUMERAL 0)). Qed.
Lemma lem7558202 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558203 : term523 = term524.
Proof. exact (@lem7558202 term470). Qed.
Lemma lem7558204 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558205 : term525 = term526.
Proof. exact (MK_COMB (@lem7558204) (@lem7558203)). Qed.
Lemma lem7558206 : term527 = term528.
Proof. exact (MK_COMB (@lem7558205) (@lem7558200)). Qed.
Lemma lem7558207 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558209 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558210 : term532 = term533.
Proof. exact (@lem7558209 term470 term470). Qed.
Lemma lem7558211 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558212 : term535 = term470.
Proof. exact (EQ_MP (@lem7558211) (@lem940073)). Qed.
Lemma lem7558213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558214 : term533 = term469.
Proof. exact (MK_COMB (@lem7558213) (@lem7558212)). Qed.
Lemma lem7558215 : term532 = term469.
Proof. exact (TRANS (@lem7558210) (@lem7558214)). Qed.
Lemma lem7558217 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558218 : term527 = term35.
Proof. exact (@lem7558217 term470). Qed.
Lemma lem7558219 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558220 : term537 = term538.
Proof. exact (MK_COMB (@lem7558219) (@lem7558218)). Qed.
Lemma lem7558221 : term529 = term520.
Proof. exact (MK_COMB (@lem7558220) (@lem7558215)). Qed.
Lemma lem7558222 : term528 = term520.
Proof. exact (TRANS (@lem7558207) (@lem7558221)). Qed.
Lemma lem7558223 : term527 = term520.
Proof. exact (TRANS (@lem7558206) (@lem7558222)). Qed.
Lemma lem7558225 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558226 : term520 = term35.
Proof. exact (@lem7558225 term35). Qed.
Lemma lem7558227 : term527 = term35.
Proof. exact (TRANS (@lem7558223) (@lem7558226)). Qed.
Lemma lem7558228 (_97561 : int) : (term709 _97561) = (term709 _97561).
Proof. exact (eq_refl (term709 _97561)). Qed.
Lemma lem7558229 (_97561 : int) : (term708 _97561) = (term710 _97561).
Proof. exact (MK_COMB (@lem7558228 _97561) (@lem7558227)). Qed.
Lemma lem7558230 (_97561 : int) : (term710 _97561) = (term559 _97561).
Proof. exact (@lem1982723 (term559 _97561)). Qed.
Lemma lem7558231 (_97561 : int) : (term708 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7558229 _97561) (@lem7558230 _97561)). Qed.
Lemma lem7558233 (_97561 : int) : (term707 _97561) = (term559 _97561).
Proof. exact (TRANS (@lem7558197 _97561) (@lem7558231 _97561)). Qed.
Lemma lem7558234 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558235 (_97561 : int) : (term711 _97561) = (term563 _97561).
Proof. exact (MK_COMB (@lem7558234) (@lem7558233 _97561)). Qed.
Lemma lem7558236 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558237 (_97561 : int) : (term706 _97561) = (term564 _97561).
Proof. exact (MK_COMB (@lem7558235 _97561) (@lem7558236)). Qed.
Lemma lem7558238 (_97561 : int) : (term564 _97561) = (term564 _97561).
Proof. exact (TRANS (@lem7558179 _97561) (@lem7558237 _97561)). Qed.
Lemma lem7558239 (_97561 : int) (_97560 : int) : (term705 _97561 _97560) = (term712 _97561 _97560).
Proof. exact (@lem1988291 (term703 _97561 _97560) term35). Qed.
Lemma lem7558240 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558253 (_97560 : int) (_97561 : int) : (term703 _97561 _97560) = (term587 _97560 _97561).
Proof. exact (@lem1982761 (real_of_int _97560) (term570 _97561)). Qed.
Lemma lem7558254 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7558255 (_97560 : int) (_97561 : int) : (term713 _97561 _97560) = (term714 _97560 _97561).
Proof. exact (MK_COMB (@lem7558254) (@lem7558253 _97560 _97561)). Qed.
Lemma lem7558256 (_97560 : int) (_97561 : int) : (term715 _97561 _97560) = (term716 _97560 _97561).
Proof. exact (MK_COMB (@lem7558255 _97560 _97561) (@lem7558240)). Qed.
Lemma lem7558257 (_97560 : int) (_97561 : int) : (term716 _97560 _97561) = (term717 _97560 _97561).
Proof. exact (@lem1982792 (term587 _97560 _97561) term35). Qed.
Lemma lem7558259 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558260 : term35 = term520.
Proof. exact (@lem7558259 (NUMERAL 0)). Qed.
Lemma lem7558262 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558263 : term523 = term524.
Proof. exact (@lem7558262 term470). Qed.
Lemma lem7558264 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558265 : term525 = term526.
Proof. exact (MK_COMB (@lem7558264) (@lem7558263)). Qed.
Lemma lem7558266 : term527 = term528.
Proof. exact (MK_COMB (@lem7558265) (@lem7558260)). Qed.
Lemma lem7558267 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558269 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558270 : term532 = term533.
Proof. exact (@lem7558269 term470 term470). Qed.
Lemma lem7558271 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558272 : term535 = term470.
Proof. exact (EQ_MP (@lem7558271) (@lem940073)). Qed.
Lemma lem7558273 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558274 : term533 = term469.
Proof. exact (MK_COMB (@lem7558273) (@lem7558272)). Qed.
Lemma lem7558275 : term532 = term469.
Proof. exact (TRANS (@lem7558270) (@lem7558274)). Qed.
Lemma lem7558277 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558278 : term527 = term35.
Proof. exact (@lem7558277 term470). Qed.
Lemma lem7558279 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558280 : term537 = term538.
Proof. exact (MK_COMB (@lem7558279) (@lem7558278)). Qed.
Lemma lem7558281 : term529 = term520.
Proof. exact (MK_COMB (@lem7558280) (@lem7558275)). Qed.
Lemma lem7558282 : term528 = term520.
Proof. exact (TRANS (@lem7558267) (@lem7558281)). Qed.
Lemma lem7558283 : term527 = term520.
Proof. exact (TRANS (@lem7558266) (@lem7558282)). Qed.
Lemma lem7558285 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558286 : term520 = term35.
Proof. exact (@lem7558285 term35). Qed.
Lemma lem7558287 : term527 = term35.
Proof. exact (TRANS (@lem7558283) (@lem7558286)). Qed.
Lemma lem7558288 (_97560 : int) (_97561 : int) : (term718 _97560 _97561) = (term718 _97560 _97561).
Proof. exact (eq_refl (term718 _97560 _97561)). Qed.
Lemma lem7558289 (_97560 : int) (_97561 : int) : (term717 _97560 _97561) = (term719 _97560 _97561).
Proof. exact (MK_COMB (@lem7558288 _97560 _97561) (@lem7558287)). Qed.
Lemma lem7558290 (_97560 : int) (_97561 : int) : (term719 _97560 _97561) = (term587 _97560 _97561).
Proof. exact (@lem1982723 (term587 _97560 _97561)). Qed.
Lemma lem7558291 (_97560 : int) (_97561 : int) : (term717 _97560 _97561) = (term587 _97560 _97561).
Proof. exact (TRANS (@lem7558289 _97560 _97561) (@lem7558290 _97560 _97561)). Qed.
Lemma lem7558292 (_97560 : int) (_97561 : int) : (term716 _97560 _97561) = (term587 _97560 _97561).
Proof. exact (TRANS (@lem7558257 _97560 _97561) (@lem7558291 _97560 _97561)). Qed.
Lemma lem7558293 (_97560 : int) (_97561 : int) : (term715 _97561 _97560) = (term587 _97560 _97561).
Proof. exact (TRANS (@lem7558256 _97560 _97561) (@lem7558292 _97560 _97561)). Qed.
Lemma lem7558294 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558295 (_97560 : int) (_97561 : int) : (term720 _97561 _97560) = (term589 _97560 _97561).
Proof. exact (MK_COMB (@lem7558294) (@lem7558293 _97560 _97561)). Qed.
Lemma lem7558296 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558297 (_97560 : int) (_97561 : int) : (term712 _97561 _97560) = (term590 _97560 _97561).
Proof. exact (MK_COMB (@lem7558295 _97560 _97561) (@lem7558296)). Qed.
Lemma lem7558298 (_97560 : int) (_97561 : int) : (term705 _97561 _97560) = (term590 _97560 _97561).
Proof. exact (TRANS (@lem7558239 _97561 _97560) (@lem7558297 _97560 _97561)). Qed.
Lemma lem7558299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558300 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558299) (@lem7558178 _97561)). Qed.
Lemma lem7558301 (_97560 : int) (_97561 : int) : (term721 _97561 _97560) = (term595 _97560 _97561).
Proof. exact (MK_COMB (@lem7558300 _97561) (@lem7558298 _97560 _97561)). Qed.
Lemma lem7558302 (_97559 : int) (_97561 : int) : (term590 _97559 _97561) = (term722 _97559 _97561).
Proof. exact (@lem1988291 (term587 _97559 _97561) term35). Qed.
Lemma lem7558320 (_97559 : int) (_97561 : int) : (term716 _97559 _97561) = (term717 _97559 _97561).
Proof. exact (@lem1982792 (term587 _97559 _97561) term35). Qed.
Lemma lem7558322 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558323 : term35 = term520.
Proof. exact (@lem7558322 (NUMERAL 0)). Qed.
Lemma lem7558325 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558326 : term523 = term524.
Proof. exact (@lem7558325 term470). Qed.
Lemma lem7558327 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558328 : term525 = term526.
Proof. exact (MK_COMB (@lem7558327) (@lem7558326)). Qed.
Lemma lem7558329 : term527 = term528.
Proof. exact (MK_COMB (@lem7558328) (@lem7558323)). Qed.
Lemma lem7558330 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558332 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558333 : term532 = term533.
Proof. exact (@lem7558332 term470 term470). Qed.
Lemma lem7558334 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558335 : term535 = term470.
Proof. exact (EQ_MP (@lem7558334) (@lem940073)). Qed.
Lemma lem7558336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558337 : term533 = term469.
Proof. exact (MK_COMB (@lem7558336) (@lem7558335)). Qed.
Lemma lem7558338 : term532 = term469.
Proof. exact (TRANS (@lem7558333) (@lem7558337)). Qed.
Lemma lem7558340 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558341 : term527 = term35.
Proof. exact (@lem7558340 term470). Qed.
Lemma lem7558342 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558343 : term537 = term538.
Proof. exact (MK_COMB (@lem7558342) (@lem7558341)). Qed.
Lemma lem7558344 : term529 = term520.
Proof. exact (MK_COMB (@lem7558343) (@lem7558338)). Qed.
Lemma lem7558345 : term528 = term520.
Proof. exact (TRANS (@lem7558330) (@lem7558344)). Qed.
Lemma lem7558346 : term527 = term520.
Proof. exact (TRANS (@lem7558329) (@lem7558345)). Qed.
Lemma lem7558348 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558349 : term520 = term35.
Proof. exact (@lem7558348 term35). Qed.
Lemma lem7558350 : term527 = term35.
Proof. exact (TRANS (@lem7558346) (@lem7558349)). Qed.
Lemma lem7558351 (_97559 : int) (_97561 : int) : (term718 _97559 _97561) = (term718 _97559 _97561).
Proof. exact (eq_refl (term718 _97559 _97561)). Qed.
Lemma lem7558352 (_97559 : int) (_97561 : int) : (term717 _97559 _97561) = (term719 _97559 _97561).
Proof. exact (MK_COMB (@lem7558351 _97559 _97561) (@lem7558350)). Qed.
Lemma lem7558353 (_97559 : int) (_97561 : int) : (term719 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982723 (term587 _97559 _97561)). Qed.
Lemma lem7558354 (_97559 : int) (_97561 : int) : (term717 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (TRANS (@lem7558352 _97559 _97561) (@lem7558353 _97559 _97561)). Qed.
Lemma lem7558356 (_97559 : int) (_97561 : int) : (term716 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (TRANS (@lem7558320 _97559 _97561) (@lem7558354 _97559 _97561)). Qed.
Lemma lem7558357 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558358 (_97559 : int) (_97561 : int) : (term723 _97559 _97561) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7558357) (@lem7558356 _97559 _97561)). Qed.
Lemma lem7558359 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558360 (_97559 : int) (_97561 : int) : (term722 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7558358 _97559 _97561) (@lem7558359)). Qed.
Lemma lem7558361 (_97559 : int) (_97561 : int) : (term590 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (TRANS (@lem7558302 _97559 _97561) (@lem7558360 _97559 _97561)). Qed.
Lemma lem7558362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558363 (_97560 : int) (_97561 : int) : (term724 _97561 _97560) = (term610 _97560 _97561).
Proof. exact (MK_COMB (@lem7558362) (@lem7558301 _97560 _97561)). Qed.
Lemma lem7558364 (_97560 : int) (_97559 : int) (_97561 : int) : (term725 _97560 _97559 _97561) = (term726 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558363 _97560 _97561) (@lem7558361 _97559 _97561)). Qed.
Lemma lem7558365 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558366 (_97561 : int) : (term727 _97561) = (term727 _97561).
Proof. exact (MK_COMB (@lem7558365) (@lem7558238 _97561)). Qed.
Lemma lem7558367 (_97560 : int) (_97559 : int) (_97561 : int) : (term728 _97560 _97559 _97561) = (term729 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558366 _97561) (@lem7558364 _97560 _97559 _97561)). Qed.
Lemma lem7558368 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558369 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558368) (@lem7558178 _97561)). Qed.
Lemma lem7558370 (_97560 : int) (_97559 : int) (_97561 : int) : (term730 _97560 _97559 _97561) = (term731 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558369 _97561) (@lem7558367 _97560 _97559 _97561)). Qed.
Lemma lem7558371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558372 (_97560 : int) : (term583 _97560) = (term583 _97560).
Proof. exact (MK_COMB (@lem7558371) (@lem7558130 _97560)). Qed.
Lemma lem7558373 (_97560 : int) (_97559 : int) (_97561 : int) : (term732 _97560 _97559 _97561) = (term733 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558372 _97560) (@lem7558370 _97560 _97559 _97561)). Qed.
Lemma lem7558374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558375 (_97559 : int) : (term583 _97559) = (term583 _97559).
Proof. exact (MK_COMB (@lem7558374) (@lem7558082 _97559)). Qed.
Lemma lem7558376 (_97560 : int) (_97559 : int) (_97561 : int) : (term694 _97560 _97559 _97561) = (term734 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558375 _97559) (@lem7558373 _97560 _97559 _97561)). Qed.
Lemma lem7558377 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558378 (_97559 : int) (_97560 : int) : (term695 _97560 _97559) = (term735 _97559 _97560).
Proof. exact (MK_COMB (@lem7558377) (@lem7558034 _97559 _97560)). Qed.
Lemma lem7558379 (_97560 : int) (_97559 : int) (_97561 : int) : (term697 _97560 _97559 _97561) = (term736 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558378 _97559 _97560) (@lem7558376 _97560 _97559 _97561)). Qed.
Lemma lem7558380 (_97559 : int) (_97560 : int) : (term737 _97559 _97560) = (term738 _97559 _97560).
Proof. exact (@lem1988289 (real_of_int _97559) (real_of_int _97560)). Qed.
Lemma lem7558393 (_97559 : int) (_97560 : int) : (term586 _97559 _97560) = (term587 _97559 _97560).
Proof. exact (@lem1982792 (real_of_int _97559) (real_of_int _97560)). Qed.
Lemma lem7558394 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7558395 (_97559 : int) (_97560 : int) : (term739 _97559 _97560) = (term740 _97559 _97560).
Proof. exact (MK_COMB (@lem7558394) (@lem7558393 _97559 _97560)). Qed.
Lemma lem7558396 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558397 (_97559 : int) (_97560 : int) : (term738 _97559 _97560) = (term741 _97559 _97560).
Proof. exact (MK_COMB (@lem7558395 _97559 _97560) (@lem7558396)). Qed.
Lemma lem7558398 (_97559 : int) (_97560 : int) : (term737 _97559 _97560) = (term741 _97559 _97560).
Proof. exact (TRANS (@lem7558380 _97559 _97560) (@lem7558397 _97559 _97560)). Qed.
Lemma lem7558399 (_97561 : int) (_97559 : int) : (term705 _97561 _97559) = (term712 _97561 _97559).
Proof. exact (@lem1988291 (term703 _97561 _97559) term35). Qed.
Lemma lem7558400 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558413 (_97559 : int) (_97561 : int) : (term703 _97561 _97559) = (term587 _97559 _97561).
Proof. exact (@lem1982761 (real_of_int _97559) (term570 _97561)). Qed.
Lemma lem7558414 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7558415 (_97559 : int) (_97561 : int) : (term713 _97561 _97559) = (term714 _97559 _97561).
Proof. exact (MK_COMB (@lem7558414) (@lem7558413 _97559 _97561)). Qed.
Lemma lem7558416 (_97559 : int) (_97561 : int) : (term715 _97561 _97559) = (term716 _97559 _97561).
Proof. exact (MK_COMB (@lem7558415 _97559 _97561) (@lem7558400)). Qed.
Lemma lem7558417 (_97559 : int) (_97561 : int) : (term716 _97559 _97561) = (term717 _97559 _97561).
Proof. exact (@lem1982792 (term587 _97559 _97561) term35). Qed.
Lemma lem7558419 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558420 : term35 = term520.
Proof. exact (@lem7558419 (NUMERAL 0)). Qed.
Lemma lem7558422 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558423 : term523 = term524.
Proof. exact (@lem7558422 term470). Qed.
Lemma lem7558424 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558425 : term525 = term526.
Proof. exact (MK_COMB (@lem7558424) (@lem7558423)). Qed.
Lemma lem7558426 : term527 = term528.
Proof. exact (MK_COMB (@lem7558425) (@lem7558420)). Qed.
Lemma lem7558427 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558429 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558430 : term532 = term533.
Proof. exact (@lem7558429 term470 term470). Qed.
Lemma lem7558431 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558432 : term535 = term470.
Proof. exact (EQ_MP (@lem7558431) (@lem940073)). Qed.
Lemma lem7558433 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558434 : term533 = term469.
Proof. exact (MK_COMB (@lem7558433) (@lem7558432)). Qed.
Lemma lem7558435 : term532 = term469.
Proof. exact (TRANS (@lem7558430) (@lem7558434)). Qed.
Lemma lem7558437 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558438 : term527 = term35.
Proof. exact (@lem7558437 term470). Qed.
Lemma lem7558439 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558440 : term537 = term538.
Proof. exact (MK_COMB (@lem7558439) (@lem7558438)). Qed.
Lemma lem7558441 : term529 = term520.
Proof. exact (MK_COMB (@lem7558440) (@lem7558435)). Qed.
Lemma lem7558442 : term528 = term520.
Proof. exact (TRANS (@lem7558427) (@lem7558441)). Qed.
Lemma lem7558443 : term527 = term520.
Proof. exact (TRANS (@lem7558426) (@lem7558442)). Qed.
Lemma lem7558445 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558446 : term520 = term35.
Proof. exact (@lem7558445 term35). Qed.
Lemma lem7558447 : term527 = term35.
Proof. exact (TRANS (@lem7558443) (@lem7558446)). Qed.
Lemma lem7558448 (_97559 : int) (_97561 : int) : (term718 _97559 _97561) = (term718 _97559 _97561).
Proof. exact (eq_refl (term718 _97559 _97561)). Qed.
Lemma lem7558449 (_97559 : int) (_97561 : int) : (term717 _97559 _97561) = (term719 _97559 _97561).
Proof. exact (MK_COMB (@lem7558448 _97559 _97561) (@lem7558447)). Qed.
Lemma lem7558450 (_97559 : int) (_97561 : int) : (term719 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982723 (term587 _97559 _97561)). Qed.
Lemma lem7558451 (_97559 : int) (_97561 : int) : (term717 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (TRANS (@lem7558449 _97559 _97561) (@lem7558450 _97559 _97561)). Qed.
Lemma lem7558452 (_97559 : int) (_97561 : int) : (term716 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (TRANS (@lem7558417 _97559 _97561) (@lem7558451 _97559 _97561)). Qed.
Lemma lem7558453 (_97559 : int) (_97561 : int) : (term715 _97561 _97559) = (term587 _97559 _97561).
Proof. exact (TRANS (@lem7558416 _97559 _97561) (@lem7558452 _97559 _97561)). Qed.
Lemma lem7558454 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558455 (_97559 : int) (_97561 : int) : (term720 _97561 _97559) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7558454) (@lem7558453 _97559 _97561)). Qed.
Lemma lem7558456 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558457 (_97559 : int) (_97561 : int) : (term712 _97561 _97559) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7558455 _97559 _97561) (@lem7558456)). Qed.
Lemma lem7558458 (_97559 : int) (_97561 : int) : (term705 _97561 _97559) = (term590 _97559 _97561).
Proof. exact (TRANS (@lem7558399 _97561 _97559) (@lem7558457 _97559 _97561)). Qed.
Lemma lem7558459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558460 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558459) (@lem7558178 _97561)). Qed.
Lemma lem7558461 (_97559 : int) (_97561 : int) : (term721 _97561 _97559) = (term595 _97559 _97561).
Proof. exact (MK_COMB (@lem7558460 _97561) (@lem7558458 _97559 _97561)). Qed.
Lemma lem7558462 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558463 (_97559 : int) (_97561 : int) : (term724 _97561 _97559) = (term610 _97559 _97561).
Proof. exact (MK_COMB (@lem7558462) (@lem7558461 _97559 _97561)). Qed.
Lemma lem7558464 (_97559 : int) (_97561 : int) : (term742 _97559 _97561) = (term743 _97559 _97561).
Proof. exact (MK_COMB (@lem7558463 _97559 _97561) (@lem7558361 _97559 _97561)). Qed.
Lemma lem7558465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558466 (_97561 : int) : (term727 _97561) = (term727 _97561).
Proof. exact (MK_COMB (@lem7558465) (@lem7558238 _97561)). Qed.
Lemma lem7558467 (_97559 : int) (_97561 : int) : (term744 _97559 _97561) = (term745 _97559 _97561).
Proof. exact (MK_COMB (@lem7558466 _97561) (@lem7558464 _97559 _97561)). Qed.
Lemma lem7558468 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558469 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558468) (@lem7558178 _97561)). Qed.
Lemma lem7558470 (_97559 : int) (_97561 : int) : (term746 _97559 _97561) = (term747 _97559 _97561).
Proof. exact (MK_COMB (@lem7558469 _97561) (@lem7558467 _97559 _97561)). Qed.
Lemma lem7558471 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558472 (_97560 : int) : (term583 _97560) = (term583 _97560).
Proof. exact (MK_COMB (@lem7558471) (@lem7558130 _97560)). Qed.
Lemma lem7558473 (_97560 : int) (_97559 : int) (_97561 : int) : (term748 _97560 _97559 _97561) = (term749 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558472 _97560) (@lem7558470 _97559 _97561)). Qed.
Lemma lem7558474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558475 (_97559 : int) : (term583 _97559) = (term583 _97559).
Proof. exact (MK_COMB (@lem7558474) (@lem7558082 _97559)). Qed.
Lemma lem7558476 (_97560 : int) (_97559 : int) (_97561 : int) : (term689 _97560 _97559 _97561) = (term750 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558475 _97559) (@lem7558473 _97560 _97559 _97561)). Qed.
Lemma lem7558477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558478 (_97559 : int) (_97560 : int) : (term690 _97559 _97560) = (term751 _97559 _97560).
Proof. exact (MK_COMB (@lem7558477) (@lem7558398 _97559 _97560)). Qed.
Lemma lem7558479 (_97560 : int) (_97559 : int) (_97561 : int) : (term692 _97560 _97559 _97561) = (term752 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558478 _97559 _97560) (@lem7558476 _97560 _97559 _97561)). Qed.
Lemma lem7558480 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7558481 (_97560 : int) (_97559 : int) (_97561 : int) : (term699 _97560 _97559 _97561) = (term753 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558480) (@lem7558379 _97560 _97559 _97561)). Qed.
Lemma lem7558482 (_97560 : int) (_97559 : int) (_97561 : int) : (term700 _97560 _97559 _97561) = (term754 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558481 _97560 _97559 _97561) (@lem7558479 _97560 _97559 _97561)). Qed.
Lemma lem7558494 (_97560 : int) (_97559 : int) (_97561 : int) : (term685 _97560 _97559 _97561) = (term754 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7558015 _97560 _97559 _97561) (@lem7558482 _97560 _97559 _97561)). Qed.
Lemma lem7558496 (_97560 : int) (_97559 : int) (_97561 : int) : (term755 _97561 _97559 _97560) = (term756 _97560 _97559 _97561).
Proof. exact (eq_refl (term755 _97561 _97559 _97560)). Qed.
Lemma lem7558497 (_97561 : int) (_97559 : int) (_97560 : int) : (term756 _97560 _97559 _97561) = (term755 _97561 _97559 _97560).
Proof. exact (SYM (@lem7558496 _97560 _97559 _97561)). Qed.
Lemma lem7558498 (_97560 : int) (_97561 : int) (_97559 : int) : (term755 _97561 _97559 _97560) = (term757 _97560 _97561 _97559).
Proof. exact (@lem1483205 (real_of_int _97560) (term758 _97560 _97559 _97561) (real_of_int _97559)). Qed.
Lemma lem7558499 (_97560 : int) (_97561 : int) (_97559 : int) : (term756 _97560 _97559 _97561) = (term757 _97560 _97561 _97559).
Proof. exact (TRANS (@lem7558497 _97561 _97559 _97560) (@lem7558498 _97560 _97561 _97559)). Qed.
Lemma lem7558500 (_97560 : int) (_97559 : int) (_97561 : int) : (term759 _97560 _97561 _97559) = (term760 _97560 _97559 _97561).
Proof. exact (eq_refl (term759 _97560 _97561 _97559)). Qed.
Lemma lem7558501 (_97559 : int) (_97560 : int) : (term690 _97559 _97560) = (term690 _97559 _97560).
Proof. exact (eq_refl (term690 _97559 _97560)). Qed.
Lemma lem7558502 (_97560 : int) (_97559 : int) (_97561 : int) : (term761 _97560 _97561 _97559) = (term762 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558501 _97559 _97560) (@lem7558500 _97560 _97559 _97561)). Qed.
Lemma lem7558503 (_97560 : int) (_97559 : int) (_97561 : int) : (term763 _97559 _97561 _97560) = (term764 _97560 _97559 _97561).
Proof. exact (eq_refl (term763 _97559 _97561 _97560)). Qed.
Lemma lem7558504 (_97560 : int) (_97559 : int) : (term695 _97560 _97559) = (term695 _97560 _97559).
Proof. exact (eq_refl (term695 _97560 _97559)). Qed.
Lemma lem7558505 (_97560 : int) (_97559 : int) (_97561 : int) : (term765 _97559 _97561 _97560) = (term766 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558504 _97560 _97559) (@lem7558503 _97560 _97559 _97561)). Qed.
Lemma lem7558506 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7558507 (_97560 : int) (_97559 : int) (_97561 : int) : (term767 _97559 _97561 _97560) = (term768 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558506) (@lem7558505 _97560 _97559 _97561)). Qed.
Lemma lem7558508 (_97560 : int) (_97559 : int) (_97561 : int) : (term757 _97560 _97561 _97559) = (term769 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558507 _97560 _97559 _97561) (@lem7558502 _97560 _97559 _97561)). Qed.
Lemma lem7558509 (_97560 : int) (_97559 : int) (_97561 : int) : (term770 _97560 _97559 _97561) = (term770 _97560 _97559 _97561).
Proof. exact (eq_refl (term770 _97560 _97559 _97561)). Qed.
Lemma lem7558510 (_97560 : int) (_97559 : int) (_97561 : int) : ((term756 _97560 _97559 _97561) = (term757 _97560 _97561 _97559)) = ((term756 _97560 _97559 _97561) = (term769 _97560 _97559 _97561)).
Proof. exact (MK_COMB (@lem7558509 _97560 _97559 _97561) (@lem7558508 _97560 _97559 _97561)). Qed.
Lemma lem7558511 (_97560 : int) (_97559 : int) (_97561 : int) : (term756 _97560 _97559 _97561) = (term769 _97560 _97559 _97561).
Proof. exact (EQ_MP (@lem7558510 _97560 _97559 _97561) (@lem7558499 _97560 _97561 _97559)). Qed.
Lemma lem7558512 (_97559 : int) (_97561 : int) : (term573 _97559 _97561) = (term771 _97559 _97561).
Proof. exact (@lem1988291 (term569 _97559 _97561) term35). Qed.
Lemma lem7558536 (_97559 : int) (_97561 : int) : (term772 _97559 _97561) = (term773 _97559 _97561).
Proof. exact (@lem1982792 (term569 _97559 _97561) term35). Qed.
Lemma lem7558538 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558539 : term35 = term520.
Proof. exact (@lem7558538 (NUMERAL 0)). Qed.
Lemma lem7558541 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558542 : term523 = term524.
Proof. exact (@lem7558541 term470). Qed.
Lemma lem7558543 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558544 : term525 = term526.
Proof. exact (MK_COMB (@lem7558543) (@lem7558542)). Qed.
Lemma lem7558545 : term527 = term528.
Proof. exact (MK_COMB (@lem7558544) (@lem7558539)). Qed.
Lemma lem7558546 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7558548 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558549 : term532 = term533.
Proof. exact (@lem7558548 term470 term470). Qed.
Lemma lem7558550 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558551 : term535 = term470.
Proof. exact (EQ_MP (@lem7558550) (@lem940073)). Qed.
Lemma lem7558552 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558553 : term533 = term469.
Proof. exact (MK_COMB (@lem7558552) (@lem7558551)). Qed.
Lemma lem7558554 : term532 = term469.
Proof. exact (TRANS (@lem7558549) (@lem7558553)). Qed.
Lemma lem7558556 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7558557 : term527 = term35.
Proof. exact (@lem7558556 term470). Qed.
Lemma lem7558558 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7558559 : term537 = term538.
Proof. exact (MK_COMB (@lem7558558) (@lem7558557)). Qed.
Lemma lem7558560 : term529 = term520.
Proof. exact (MK_COMB (@lem7558559) (@lem7558554)). Qed.
Lemma lem7558561 : term528 = term520.
Proof. exact (TRANS (@lem7558546) (@lem7558560)). Qed.
Lemma lem7558562 : term527 = term520.
Proof. exact (TRANS (@lem7558545) (@lem7558561)). Qed.
Lemma lem7558564 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7558565 : term520 = term35.
Proof. exact (@lem7558564 term35). Qed.
Lemma lem7558566 : term527 = term35.
Proof. exact (TRANS (@lem7558562) (@lem7558565)). Qed.
Lemma lem7558567 (_97559 : int) (_97561 : int) : (term774 _97559 _97561) = (term774 _97559 _97561).
Proof. exact (eq_refl (term774 _97559 _97561)). Qed.
Lemma lem7558568 (_97559 : int) (_97561 : int) : (term773 _97559 _97561) = (term775 _97559 _97561).
Proof. exact (MK_COMB (@lem7558567 _97559 _97561) (@lem7558566)). Qed.
Lemma lem7558569 (_97559 : int) (_97561 : int) : (term775 _97559 _97561) = (term569 _97559 _97561).
Proof. exact (@lem1982723 (term569 _97559 _97561)). Qed.
Lemma lem7558570 (_97559 : int) (_97561 : int) : (term773 _97559 _97561) = (term569 _97559 _97561).
Proof. exact (TRANS (@lem7558568 _97559 _97561) (@lem7558569 _97559 _97561)). Qed.
Lemma lem7558572 (_97559 : int) (_97561 : int) : (term772 _97559 _97561) = (term569 _97559 _97561).
Proof. exact (TRANS (@lem7558536 _97559 _97561) (@lem7558570 _97559 _97561)). Qed.
Lemma lem7558573 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558574 (_97559 : int) (_97561 : int) : (term776 _97559 _97561) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7558573) (@lem7558572 _97559 _97561)). Qed.
Lemma lem7558575 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558576 (_97559 : int) (_97561 : int) : (term771 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7558574 _97559 _97561) (@lem7558575)). Qed.
Lemma lem7558577 (_97559 : int) (_97561 : int) : (term573 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (TRANS (@lem7558512 _97559 _97561) (@lem7558576 _97559 _97561)). Qed.
Lemma lem7558578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558579 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558578) (@lem7558178 _97561)). Qed.
Lemma lem7558580 (_97560 : int) (_97561 : int) : (term721 _97561 _97560) = (term595 _97560 _97561).
Proof. exact (MK_COMB (@lem7558579 _97561) (@lem7558298 _97560 _97561)). Qed.
Lemma lem7558581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558582 (_97560 : int) (_97561 : int) : (term724 _97561 _97560) = (term610 _97560 _97561).
Proof. exact (MK_COMB (@lem7558581) (@lem7558580 _97560 _97561)). Qed.
Lemma lem7558583 (_97560 : int) (_97559 : int) (_97561 : int) : (term725 _97560 _97559 _97561) = (term726 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558582 _97560 _97561) (@lem7558361 _97559 _97561)). Qed.
Lemma lem7558584 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558585 (_97559 : int) (_97561 : int) : (term777 _97559 _97561) = (term777 _97559 _97561).
Proof. exact (MK_COMB (@lem7558584) (@lem7558577 _97559 _97561)). Qed.
Lemma lem7558586 (_97560 : int) (_97559 : int) (_97561 : int) : (term778 _97560 _97559 _97561) = (term779 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558585 _97559 _97561) (@lem7558583 _97560 _97559 _97561)). Qed.
Lemma lem7558587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558588 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558587) (@lem7558178 _97561)). Qed.
Lemma lem7558589 (_97560 : int) (_97559 : int) (_97561 : int) : (term780 _97560 _97559 _97561) = (term781 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558588 _97561) (@lem7558586 _97560 _97559 _97561)). Qed.
Lemma lem7558590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558591 (_97560 : int) : (term583 _97560) = (term583 _97560).
Proof. exact (MK_COMB (@lem7558590) (@lem7558130 _97560)). Qed.
Lemma lem7558592 (_97560 : int) (_97559 : int) (_97561 : int) : (term782 _97560 _97559 _97561) = (term783 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558591 _97560) (@lem7558589 _97560 _97559 _97561)). Qed.
Lemma lem7558593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558594 (_97559 : int) : (term583 _97559) = (term583 _97559).
Proof. exact (MK_COMB (@lem7558593) (@lem7558082 _97559)). Qed.
Lemma lem7558595 (_97560 : int) (_97559 : int) (_97561 : int) : (term764 _97560 _97559 _97561) = (term784 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558594 _97559) (@lem7558592 _97560 _97559 _97561)). Qed.
Lemma lem7558596 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558597 (_97559 : int) (_97560 : int) : (term695 _97560 _97559) = (term735 _97559 _97560).
Proof. exact (MK_COMB (@lem7558596) (@lem7558034 _97559 _97560)). Qed.
Lemma lem7558598 (_97560 : int) (_97559 : int) (_97561 : int) : (term766 _97560 _97559 _97561) = (term785 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558597 _97559 _97560) (@lem7558595 _97560 _97559 _97561)). Qed.
Lemma lem7558599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558600 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558599) (@lem7558178 _97561)). Qed.
Lemma lem7558601 (_97559 : int) (_97561 : int) : (term721 _97561 _97559) = (term595 _97559 _97561).
Proof. exact (MK_COMB (@lem7558600 _97561) (@lem7558458 _97559 _97561)). Qed.
Lemma lem7558602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558603 (_97559 : int) (_97561 : int) : (term724 _97561 _97559) = (term610 _97559 _97561).
Proof. exact (MK_COMB (@lem7558602) (@lem7558601 _97559 _97561)). Qed.
Lemma lem7558604 (_97559 : int) (_97561 : int) : (term742 _97559 _97561) = (term743 _97559 _97561).
Proof. exact (MK_COMB (@lem7558603 _97559 _97561) (@lem7558361 _97559 _97561)). Qed.
Lemma lem7558605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558606 (_97559 : int) (_97561 : int) : (term777 _97559 _97561) = (term777 _97559 _97561).
Proof. exact (MK_COMB (@lem7558605) (@lem7558577 _97559 _97561)). Qed.
Lemma lem7558607 (_97559 : int) (_97561 : int) : (term786 _97559 _97561) = (term787 _97559 _97561).
Proof. exact (MK_COMB (@lem7558606 _97559 _97561) (@lem7558604 _97559 _97561)). Qed.
Lemma lem7558608 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558609 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (MK_COMB (@lem7558608) (@lem7558178 _97561)). Qed.
Lemma lem7558610 (_97559 : int) (_97561 : int) : (term788 _97559 _97561) = (term789 _97559 _97561).
Proof. exact (MK_COMB (@lem7558609 _97561) (@lem7558607 _97559 _97561)). Qed.
Lemma lem7558611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558612 (_97560 : int) : (term583 _97560) = (term583 _97560).
Proof. exact (MK_COMB (@lem7558611) (@lem7558130 _97560)). Qed.
Lemma lem7558613 (_97560 : int) (_97559 : int) (_97561 : int) : (term790 _97560 _97559 _97561) = (term791 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558612 _97560) (@lem7558610 _97559 _97561)). Qed.
Lemma lem7558614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558615 (_97559 : int) : (term583 _97559) = (term583 _97559).
Proof. exact (MK_COMB (@lem7558614) (@lem7558082 _97559)). Qed.
Lemma lem7558616 (_97560 : int) (_97559 : int) (_97561 : int) : (term760 _97560 _97559 _97561) = (term792 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558615 _97559) (@lem7558613 _97560 _97559 _97561)). Qed.
Lemma lem7558617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558618 (_97559 : int) (_97560 : int) : (term690 _97559 _97560) = (term751 _97559 _97560).
Proof. exact (MK_COMB (@lem7558617) (@lem7558398 _97559 _97560)). Qed.
Lemma lem7558619 (_97560 : int) (_97559 : int) (_97561 : int) : (term762 _97560 _97559 _97561) = (term793 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558618 _97559 _97560) (@lem7558616 _97560 _97559 _97561)). Qed.
Lemma lem7558620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7558621 (_97560 : int) (_97559 : int) (_97561 : int) : (term768 _97560 _97559 _97561) = (term794 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558620) (@lem7558598 _97560 _97559 _97561)). Qed.
Lemma lem7558622 (_97560 : int) (_97559 : int) (_97561 : int) : (term769 _97560 _97559 _97561) = (term795 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558621 _97560 _97559 _97561) (@lem7558619 _97560 _97559 _97561)). Qed.
Lemma lem7558634 (_97560 : int) (_97559 : int) (_97561 : int) : (term756 _97560 _97559 _97561) = (term795 _97560 _97559 _97561).
Proof. exact (TRANS (@lem7558511 _97560 _97559 _97561) (@lem7558622 _97560 _97559 _97561)). Qed.
Lemma lem7558635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7558636 (_97560 : int) (_97559 : int) (_97561 : int) : (term796 _97560 _97559 _97561) = (term797 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558635) (@lem7558494 _97560 _97559 _97561)). Qed.
Lemma lem7558637 (_97560 : int) (_97559 : int) (_97561 : int) : (term678 _97560 _97559 _97561) = (term798 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558636 _97560 _97559 _97561) (@lem7558634 _97560 _97559 _97561)). Qed.
Lemma lem7558642 (x : real) (a : real) (y : real) (b : real) (r : real) : (term799 a x y b r) = (term800 x a y b r).
Proof. exact (proj1 (@lem1482687 x a b y (@el real) r)). Qed.
Lemma lem7558643 (_97559 : int) (_97561 : int) (_97560 : int) : (term606 _97561 _97559 _97560) = (term801 _97559 _97561 _97560).
Proof. exact (@lem7558642 (real_of_int _97559) (real_of_int _97561) (real_of_int _97560) term523 term35). Qed.
Lemma lem7558666 (_97560 : int) (_97561 : int) : (term568 _97561 _97560) = (term569 _97560 _97561).
Proof. exact (@lem1982757 (term570 _97560) (real_of_int _97561) term523). Qed.
Lemma lem7558667 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558668 (_97560 : int) (_97561 : int) : (term802 _97561 _97560) = (term572 _97560 _97561).
Proof. exact (MK_COMB (@lem7558667) (@lem7558666 _97560 _97561)). Qed.
Lemma lem7558669 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558670 (_97560 : int) (_97561 : int) : (term803 _97561 _97560) = (term573 _97560 _97561).
Proof. exact (MK_COMB (@lem7558668 _97560 _97561) (@lem7558669)). Qed.
Lemma lem7558693 (_97559 : int) (_97561 : int) : (term568 _97561 _97559) = (term569 _97559 _97561).
Proof. exact (@lem1982757 (term570 _97559) (real_of_int _97561) term523). Qed.
Lemma lem7558694 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558695 (_97559 : int) (_97561 : int) : (term802 _97561 _97559) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7558694) (@lem7558693 _97559 _97561)). Qed.
Lemma lem7558696 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558697 (_97559 : int) (_97561 : int) : (term803 _97561 _97559) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7558695 _97559 _97561) (@lem7558696)). Qed.
Lemma lem7558698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7558699 (_97559 : int) (_97561 : int) : (term804 _97561 _97559) = (term777 _97559 _97561).
Proof. exact (MK_COMB (@lem7558698) (@lem7558697 _97559 _97561)). Qed.
Lemma lem7558700 (_97559 : int) (_97560 : int) (_97561 : int) : (term801 _97559 _97561 _97560) = (term805 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7558699 _97559 _97561) (@lem7558670 _97560 _97561)). Qed.
Lemma lem7558701 (_97559 : int) (_97560 : int) (_97561 : int) : (term606 _97561 _97559 _97560) = (term805 _97559 _97560 _97561).
Proof. exact (TRANS (@lem7558643 _97559 _97561 _97560) (@lem7558700 _97559 _97560 _97561)). Qed.
Lemma lem7558702 (_97559 : int) (_97561 : int) : (term610 _97559 _97561) = (term610 _97559 _97561).
Proof. exact (eq_refl (term610 _97559 _97561)). Qed.
Lemma lem7558703 (_97559 : int) (_97560 : int) (_97561 : int) : (term635 _97561 _97559 _97560) = (term806 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7558702 _97559 _97561) (@lem7558701 _97559 _97560 _97561)). Qed.
Lemma lem7558704 (_97561 : int) : (term583 _97561) = (term583 _97561).
Proof. exact (eq_refl (term583 _97561)). Qed.
Lemma lem7558705 (_97559 : int) (_97560 : int) (_97561 : int) : (term654 _97561 _97559 _97560) = (term807 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7558704 _97561) (@lem7558703 _97559 _97560 _97561)). Qed.
Lemma lem7558706 (_97560 : int) : (term583 _97560) = (term583 _97560).
Proof. exact (eq_refl (term583 _97560)). Qed.
Lemma lem7558707 (_97559 : int) (_97560 : int) (_97561 : int) : (term673 _97561 _97559 _97560) = (term808 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7558706 _97560) (@lem7558705 _97559 _97560 _97561)). Qed.
Lemma lem7558708 (_97559 : int) : (term583 _97559) = (term583 _97559).
Proof. exact (eq_refl (term583 _97559)). Qed.
Lemma lem7558711 (_97559 : int) (_97560 : int) (_97561 : int) : (term809 _97561 _97559 _97560) = (term810 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7558708 _97559) (@lem7558707 _97559 _97560 _97561)). Qed.
Lemma lem7558713 (_97560 : int) (_97559 : int) (_97561 : int) : (term811 _97560 _97559 _97561) = (term811 _97560 _97559 _97561).
Proof. exact (eq_refl (term811 _97560 _97559 _97561)). Qed.
Lemma lem7558714 (_97559 : int) (_97560 : int) (_97561 : int) : (term671 _97561 _97559 _97560) = (term812 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7558713 _97560 _97559 _97561) (@lem7558711 _97559 _97560 _97561)). Qed.
Lemma lem7558717 (_97560 : int) (_97559 : int) (_97561 : int) : (term669 _97560 _97559 _97561) = (term669 _97560 _97559 _97561).
Proof. exact (eq_refl (term669 _97560 _97559 _97561)). Qed.
Lemma lem7558718 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7558719 (_97559 : int) (_97560 : int) (_97561 : int) : (term675 _97561 _97559 _97560) = (term813 _97559 _97560 _97561).
Proof. exact (MK_COMB (@lem7558718) (@lem7558714 _97559 _97560 _97561)). Qed.
Lemma lem7558720 (_97560 : int) (_97559 : int) (_97561 : int) : (term676 _97560 _97559 _97561) = (term814 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558719 _97559 _97560 _97561) (@lem7558717 _97560 _97559 _97561)). Qed.
Lemma lem7558721 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7558722 (_97560 : int) (_97559 : int) (_97561 : int) : (term682 _97560 _97559 _97561) = (term815 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558721) (@lem7558637 _97560 _97559 _97561)). Qed.
Lemma lem7558723 (_97560 : int) (_97559 : int) (_97561 : int) : (term683 _97560 _97559 _97561) = (term816 _97560 _97559 _97561).
Proof. exact (MK_COMB (@lem7558722 _97560 _97559 _97561) (@lem7558720 _97560 _97559 _97561)). Qed.
Lemma lem7558724 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term816 _97560 _97559 _97561) : term816 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7558725 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term798 _97560 _97559 _97561) : term798 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7558726 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term754 _97560 _97559 _97561) : term754 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7558727 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term736 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7558728 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term734 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7558727 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558730 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term733 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7558728 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558732 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term731 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7558730 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558734 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term729 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7558732 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558736 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term726 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7558734 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558737 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term564 _97561.
Proof. exact (proj1 (@lem7558734 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558739 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term595 _97560 _97561.
Proof. exact (proj1 (@lem7558736 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558741 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term543 _97561.
Proof. exact (proj1 (@lem7558739 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558743 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7558744 : term817 = term818.
Proof. exact (@lem7558743 term35 term469). Qed.
Lemma lem7558746 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558747 : term469 = term549.
Proof. exact (@lem7558746 term470). Qed.
Lemma lem7558749 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558750 : term35 = term520.
Proof. exact (@lem7558749 (NUMERAL 0)). Qed.
Lemma lem7558751 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7558752 : term819 = term820.
Proof. exact (MK_COMB (@lem7558751) (@lem7558750)). Qed.
Lemma lem7558753 : term818 = term821.
Proof. exact (MK_COMB (@lem7558752) (@lem7558747)). Qed.
Lemma lem7558754 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7558756 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558757 : term818 = term824.
Proof. exact (@lem7558756 (NUMERAL 0) term470). Qed.
Lemma lem7558758 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558759 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558760 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558759 h1) (fun h1 : term824 = True => @lem7558758)). Qed.
Lemma lem7558761 : term824 = True.
Proof. exact (EQ_MP (@lem7558760) (@lem7558758)). Qed.
Lemma lem7558762 : term818 = True.
Proof. exact (TRANS (@lem7558757) (@lem7558761)). Qed.
Lemma lem7558763 : True = term818.
Proof. exact (SYM (@lem7558762)). Qed.
Lemma lem7558764 : term818.
Proof. exact (EQ_MP (@lem7558763) (@lem0)). Qed.
Lemma lem7558765 : term826.
Proof. exact (@lem7558754 (@lem7558764)). Qed.
Lemma lem7558767 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558768 : term818 = term824.
Proof. exact (@lem7558767 (NUMERAL 0) term470). Qed.
Lemma lem7558769 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558770 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558771 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558770 h1) (fun h1 : term824 = True => @lem7558769)). Qed.
Lemma lem7558772 : term824 = True.
Proof. exact (EQ_MP (@lem7558771) (@lem7558769)). Qed.
Lemma lem7558773 : term818 = True.
Proof. exact (TRANS (@lem7558768) (@lem7558772)). Qed.
Lemma lem7558774 : True = term818.
Proof. exact (SYM (@lem7558773)). Qed.
Lemma lem7558775 : term818.
Proof. exact (EQ_MP (@lem7558774) (@lem0)). Qed.
Lemma lem7558776 : term821 = term827.
Proof. exact (@lem7558765 (@lem7558775)). Qed.
Lemma lem7558778 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558779 : term532 = term533.
Proof. exact (@lem7558778 term470 term470). Qed.
Lemma lem7558780 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558781 : term535 = term470.
Proof. exact (EQ_MP (@lem7558780) (@lem940073)). Qed.
Lemma lem7558782 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558783 : term533 = term469.
Proof. exact (MK_COMB (@lem7558782) (@lem7558781)). Qed.
Lemma lem7558784 : term532 = term469.
Proof. exact (TRANS (@lem7558779) (@lem7558783)). Qed.
Lemma lem7558786 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7558787 : term829 = term35.
Proof. exact (@lem7558786 term470). Qed.
Lemma lem7558788 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7558789 : term830 = term819.
Proof. exact (MK_COMB (@lem7558788) (@lem7558787)). Qed.
Lemma lem7558790 : term827 = term818.
Proof. exact (MK_COMB (@lem7558789) (@lem7558784)). Qed.
Lemma lem7558792 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558793 : term818 = term824.
Proof. exact (@lem7558792 (NUMERAL 0) term470). Qed.
Lemma lem7558794 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558795 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558796 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558795 h1) (fun h1 : term824 = True => @lem7558794)). Qed.
Lemma lem7558797 : term824 = True.
Proof. exact (EQ_MP (@lem7558796) (@lem7558794)). Qed.
Lemma lem7558798 : term818 = True.
Proof. exact (TRANS (@lem7558793) (@lem7558797)). Qed.
Lemma lem7558799 : term827 = True.
Proof. exact (TRANS (@lem7558790) (@lem7558798)). Qed.
Lemma lem7558800 : term821 = True.
Proof. exact (TRANS (@lem7558776) (@lem7558799)). Qed.
Lemma lem7558801 : term818 = True.
Proof. exact (TRANS (@lem7558753) (@lem7558800)). Qed.
Lemma lem7558802 : term817 = True.
Proof. exact (TRANS (@lem7558744) (@lem7558801)). Qed.
Lemma lem7558803 : True = term817.
Proof. exact (SYM (@lem7558802)). Qed.
Lemma lem7558804 : term817.
Proof. exact (EQ_MP (@lem7558803) (@lem0)). Qed.
Lemma lem7558805 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term831 _97561.
Proof. exact (conj (@lem7558804) (@lem7558741 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558807 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7558808 (_97561 : int) : term833 _97561.
Proof. exact (@lem7558807 term469 (real_of_int _97561)). Qed.
Lemma lem7558809 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term834 _97561.
Proof. exact (@lem7558808 _97561 (@lem7558805 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558810 (_97561 : int) : (term835 _97561) = (real_of_int _97561).
Proof. exact (@lem1982733 (real_of_int _97561)). Qed.
Lemma lem7558811 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558812 (_97561 : int) : (term836 _97561) = (term542 _97561).
Proof. exact (MK_COMB (@lem7558811) (@lem7558810 _97561)). Qed.
Lemma lem7558813 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558814 (_97561 : int) : (term834 _97561) = (term543 _97561).
Proof. exact (MK_COMB (@lem7558812 _97561) (@lem7558813)). Qed.
Lemma lem7558815 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term543 _97561.
Proof. exact (EQ_MP (@lem7558814 _97561) (@lem7558809 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558817 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7558818 : term817 = term818.
Proof. exact (@lem7558817 term35 term469). Qed.
Lemma lem7558820 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558821 : term469 = term549.
Proof. exact (@lem7558820 term470). Qed.
Lemma lem7558823 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558824 : term35 = term520.
Proof. exact (@lem7558823 (NUMERAL 0)). Qed.
Lemma lem7558825 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7558826 : term819 = term820.
Proof. exact (MK_COMB (@lem7558825) (@lem7558824)). Qed.
Lemma lem7558827 : term818 = term821.
Proof. exact (MK_COMB (@lem7558826) (@lem7558821)). Qed.
Lemma lem7558828 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7558830 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558831 : term818 = term824.
Proof. exact (@lem7558830 (NUMERAL 0) term470). Qed.
Lemma lem7558832 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558833 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558834 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558833 h1) (fun h1 : term824 = True => @lem7558832)). Qed.
Lemma lem7558835 : term824 = True.
Proof. exact (EQ_MP (@lem7558834) (@lem7558832)). Qed.
Lemma lem7558836 : term818 = True.
Proof. exact (TRANS (@lem7558831) (@lem7558835)). Qed.
Lemma lem7558837 : True = term818.
Proof. exact (SYM (@lem7558836)). Qed.
Lemma lem7558838 : term818.
Proof. exact (EQ_MP (@lem7558837) (@lem0)). Qed.
Lemma lem7558839 : term826.
Proof. exact (@lem7558828 (@lem7558838)). Qed.
Lemma lem7558841 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558842 : term818 = term824.
Proof. exact (@lem7558841 (NUMERAL 0) term470). Qed.
Lemma lem7558843 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558844 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558845 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558844 h1) (fun h1 : term824 = True => @lem7558843)). Qed.
Lemma lem7558846 : term824 = True.
Proof. exact (EQ_MP (@lem7558845) (@lem7558843)). Qed.
Lemma lem7558847 : term818 = True.
Proof. exact (TRANS (@lem7558842) (@lem7558846)). Qed.
Lemma lem7558848 : True = term818.
Proof. exact (SYM (@lem7558847)). Qed.
Lemma lem7558849 : term818.
Proof. exact (EQ_MP (@lem7558848) (@lem0)). Qed.
Lemma lem7558850 : term821 = term827.
Proof. exact (@lem7558839 (@lem7558849)). Qed.
Lemma lem7558852 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558853 : term532 = term533.
Proof. exact (@lem7558852 term470 term470). Qed.
Lemma lem7558854 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558855 : term535 = term470.
Proof. exact (EQ_MP (@lem7558854) (@lem940073)). Qed.
Lemma lem7558856 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558857 : term533 = term469.
Proof. exact (MK_COMB (@lem7558856) (@lem7558855)). Qed.
Lemma lem7558858 : term532 = term469.
Proof. exact (TRANS (@lem7558853) (@lem7558857)). Qed.
Lemma lem7558860 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7558861 : term829 = term35.
Proof. exact (@lem7558860 term470). Qed.
Lemma lem7558862 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7558863 : term830 = term819.
Proof. exact (MK_COMB (@lem7558862) (@lem7558861)). Qed.
Lemma lem7558864 : term827 = term818.
Proof. exact (MK_COMB (@lem7558863) (@lem7558858)). Qed.
Lemma lem7558866 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558867 : term818 = term824.
Proof. exact (@lem7558866 (NUMERAL 0) term470). Qed.
Lemma lem7558868 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558869 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558870 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558869 h1) (fun h1 : term824 = True => @lem7558868)). Qed.
Lemma lem7558871 : term824 = True.
Proof. exact (EQ_MP (@lem7558870) (@lem7558868)). Qed.
Lemma lem7558872 : term818 = True.
Proof. exact (TRANS (@lem7558867) (@lem7558871)). Qed.
Lemma lem7558873 : term827 = True.
Proof. exact (TRANS (@lem7558864) (@lem7558872)). Qed.
Lemma lem7558874 : term821 = True.
Proof. exact (TRANS (@lem7558850) (@lem7558873)). Qed.
Lemma lem7558875 : term818 = True.
Proof. exact (TRANS (@lem7558827) (@lem7558874)). Qed.
Lemma lem7558876 : term817 = True.
Proof. exact (TRANS (@lem7558818) (@lem7558875)). Qed.
Lemma lem7558877 : True = term817.
Proof. exact (SYM (@lem7558876)). Qed.
Lemma lem7558878 : term817.
Proof. exact (EQ_MP (@lem7558877) (@lem0)). Qed.
Lemma lem7558879 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term837 _97561.
Proof. exact (conj (@lem7558878) (@lem7558737 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558881 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7558882 (_97561 : int) : term838 _97561.
Proof. exact (@lem7558881 term469 (term559 _97561)). Qed.
Lemma lem7558883 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term839 _97561.
Proof. exact (@lem7558882 _97561 (@lem7558879 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558884 (_97561 : int) : (term840 _97561) = (term559 _97561).
Proof. exact (@lem1982733 (term559 _97561)). Qed.
Lemma lem7558885 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7558886 (_97561 : int) : (term841 _97561) = (term563 _97561).
Proof. exact (MK_COMB (@lem7558885) (@lem7558884 _97561)). Qed.
Lemma lem7558887 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7558888 (_97561 : int) : (term839 _97561) = (term564 _97561).
Proof. exact (MK_COMB (@lem7558886 _97561) (@lem7558887)). Qed.
Lemma lem7558889 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term564 _97561.
Proof. exact (EQ_MP (@lem7558888 _97561) (@lem7558883 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558890 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term842 _97561.
Proof. exact (conj (@lem7558889 _97560 _97559 _97561 h1) (@lem7558815 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558892 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7558893 (_97561 : int) : term844 _97561.
Proof. exact (@lem7558892 (term559 _97561) (real_of_int _97561)). Qed.
Lemma lem7558894 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term845 _97561.
Proof. exact (@lem7558893 _97561 (@lem7558890 _97560 _97559 _97561 h1)). Qed.
Lemma lem7558895 (_97561 : int) : (term846 _97561) = (term847 _97561).
Proof. exact (@lem1982759 (term570 _97561) (real_of_int _97561) term523). Qed.
Lemma lem7558896 (_97561 : int) : (term848 _97561) = (term849 _97561).
Proof. exact (@lem1982713 term523 (real_of_int _97561)). Qed.
Lemma lem7558898 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7558899 : term469 = term549.
Proof. exact (@lem7558898 term470). Qed.
Lemma lem7558901 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7558902 : term523 = term524.
Proof. exact (@lem7558901 term470). Qed.
Lemma lem7558903 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7558904 : term850 = term851.
Proof. exact (MK_COMB (@lem7558903) (@lem7558902)). Qed.
Lemma lem7558905 : term852 = term853.
Proof. exact (MK_COMB (@lem7558904) (@lem7558899)). Qed.
Lemma lem7558906 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7558908 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558909 : term818 = term824.
Proof. exact (@lem7558908 (NUMERAL 0) term470). Qed.
Lemma lem7558910 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558911 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558912 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558911 h1) (fun h1 : term824 = True => @lem7558910)). Qed.
Lemma lem7558913 : term824 = True.
Proof. exact (EQ_MP (@lem7558912) (@lem7558910)). Qed.
Lemma lem7558914 : term818 = True.
Proof. exact (TRANS (@lem7558909) (@lem7558913)). Qed.
Lemma lem7558915 : True = term818.
Proof. exact (SYM (@lem7558914)). Qed.
Lemma lem7558916 : term818.
Proof. exact (EQ_MP (@lem7558915) (@lem0)). Qed.
Lemma lem7558917 : term855.
Proof. exact (@lem7558906 (@lem7558916)). Qed.
Lemma lem7558919 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558920 : term818 = term824.
Proof. exact (@lem7558919 (NUMERAL 0) term470). Qed.
Lemma lem7558921 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558922 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558923 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558922 h1) (fun h1 : term824 = True => @lem7558921)). Qed.
Lemma lem7558924 : term824 = True.
Proof. exact (EQ_MP (@lem7558923) (@lem7558921)). Qed.
Lemma lem7558925 : term818 = True.
Proof. exact (TRANS (@lem7558920) (@lem7558924)). Qed.
Lemma lem7558926 : True = term818.
Proof. exact (SYM (@lem7558925)). Qed.
Lemma lem7558927 : term818.
Proof. exact (EQ_MP (@lem7558926) (@lem0)). Qed.
Lemma lem7558928 : term856.
Proof. exact (@lem7558917 (@lem7558927)). Qed.
Lemma lem7558930 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7558931 : term818 = term824.
Proof. exact (@lem7558930 (NUMERAL 0) term470). Qed.
Lemma lem7558932 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7558933 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7558934 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7558933 h1) (fun h1 : term824 = True => @lem7558932)). Qed.
Lemma lem7558935 : term824 = True.
Proof. exact (EQ_MP (@lem7558934) (@lem7558932)). Qed.
Lemma lem7558936 : term818 = True.
Proof. exact (TRANS (@lem7558931) (@lem7558935)). Qed.
Lemma lem7558937 : True = term818.
Proof. exact (SYM (@lem7558936)). Qed.
Lemma lem7558938 : term818.
Proof. exact (EQ_MP (@lem7558937) (@lem0)). Qed.
Lemma lem7558939 : term857.
Proof. exact (@lem7558928 (@lem7558938)). Qed.
Lemma lem7558941 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558942 : term532 = term533.
Proof. exact (@lem7558941 term470 term470). Qed.
Lemma lem7558943 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558944 : term535 = term470.
Proof. exact (EQ_MP (@lem7558943) (@lem940073)). Qed.
Lemma lem7558945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558946 : term533 = term469.
Proof. exact (MK_COMB (@lem7558945) (@lem7558944)). Qed.
Lemma lem7558947 : term532 = term469.
Proof. exact (TRANS (@lem7558942) (@lem7558946)). Qed.
Lemma lem7558949 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7558950 : term550 = term555.
Proof. exact (@lem7558949 term470 term470). Qed.
Lemma lem7558951 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558952 : term535 = term470.
Proof. exact (EQ_MP (@lem7558951) (@lem940073)). Qed.
Lemma lem7558953 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558954 : term533 = term469.
Proof. exact (MK_COMB (@lem7558953) (@lem7558952)). Qed.
Lemma lem7558955 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7558956 : term555 = term523.
Proof. exact (MK_COMB (@lem7558955) (@lem7558954)). Qed.
Lemma lem7558957 : term550 = term523.
Proof. exact (TRANS (@lem7558950) (@lem7558956)). Qed.
Lemma lem7558958 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7558959 : term858 = term850.
Proof. exact (MK_COMB (@lem7558958) (@lem7558957)). Qed.
Lemma lem7558960 : term859 = term852.
Proof. exact (MK_COMB (@lem7558959) (@lem7558947)). Qed.
Lemma lem7558962 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7558963 : term852 = term35.
Proof. exact (@lem7558962 term470). Qed.
Lemma lem7558964 : term859 = term35.
Proof. exact (TRANS (@lem7558960) (@lem7558963)). Qed.
Lemma lem7558965 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558966 : term861 = term218.
Proof. exact (MK_COMB (@lem7558965) (@lem7558964)). Qed.
Lemma lem7558967 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7558968 : term862 = term829.
Proof. exact (MK_COMB (@lem7558966) (@lem7558967)). Qed.
Lemma lem7558970 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7558971 : term829 = term35.
Proof. exact (@lem7558970 term470). Qed.
Lemma lem7558972 : term862 = term35.
Proof. exact (TRANS (@lem7558968) (@lem7558971)). Qed.
Lemma lem7558974 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7558975 : term532 = term533.
Proof. exact (@lem7558974 term470 term470). Qed.
Lemma lem7558976 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7558977 : term535 = term470.
Proof. exact (EQ_MP (@lem7558976) (@lem940073)). Qed.
Lemma lem7558978 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7558979 : term533 = term469.
Proof. exact (MK_COMB (@lem7558978) (@lem7558977)). Qed.
Lemma lem7558980 : term532 = term469.
Proof. exact (TRANS (@lem7558975) (@lem7558979)). Qed.
Lemma lem7558981 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7558982 : term863 = term829.
Proof. exact (MK_COMB (@lem7558981) (@lem7558980)). Qed.
Lemma lem7558984 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7558985 : term829 = term35.
Proof. exact (@lem7558984 term470). Qed.
Lemma lem7558986 : term863 = term35.
Proof. exact (TRANS (@lem7558982) (@lem7558985)). Qed.
Lemma lem7558987 : term35 = term863.
Proof. exact (SYM (@lem7558986)). Qed.
Lemma lem7558988 : term862 = term863.
Proof. exact (TRANS (@lem7558972) (@lem7558987)). Qed.
Lemma lem7558989 : term853 = term520.
Proof. exact (@lem7558939 (@lem7558988)). Qed.
Lemma lem7558990 : term852 = term520.
Proof. exact (TRANS (@lem7558905) (@lem7558989)). Qed.
Lemma lem7558992 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7558993 : term520 = term35.
Proof. exact (@lem7558992 term35). Qed.
Lemma lem7558994 : term852 = term35.
Proof. exact (TRANS (@lem7558990) (@lem7558993)). Qed.
Lemma lem7558995 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7558996 : term864 = term218.
Proof. exact (MK_COMB (@lem7558995) (@lem7558994)). Qed.
Lemma lem7558997 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7558998 (_97561 : int) : (term849 _97561) = (term865 _97561).
Proof. exact (MK_COMB (@lem7558996) (@lem7558997 _97561)). Qed.
Lemma lem7558999 (_97561 : int) : (term848 _97561) = (term865 _97561).
Proof. exact (TRANS (@lem7558896 _97561) (@lem7558998 _97561)). Qed.
Lemma lem7559000 (_97561 : int) : (term865 _97561) = term35.
Proof. exact (@lem1982719 (real_of_int _97561)). Qed.
Lemma lem7559001 (_97561 : int) : (term848 _97561) = term35.
Proof. exact (TRANS (@lem7558999 _97561) (@lem7559000 _97561)). Qed.
Lemma lem7559002 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559003 (_97561 : int) : (term866 _97561) = term560.
Proof. exact (MK_COMB (@lem7559002) (@lem7559001 _97561)). Qed.
Lemma lem7559004 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7559005 (_97561 : int) : (term847 _97561) = term867.
Proof. exact (MK_COMB (@lem7559003 _97561) (@lem7559004)). Qed.
Lemma lem7559006 (_97561 : int) : (term846 _97561) = term867.
Proof. exact (TRANS (@lem7558895 _97561) (@lem7559005 _97561)). Qed.
Lemma lem7559007 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7559008 (_97561 : int) : (term846 _97561) = term523.
Proof. exact (TRANS (@lem7559006 _97561) (@lem7559007)). Qed.
Lemma lem7559009 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7559010 (_97561 : int) : (term868 _97561) = term869.
Proof. exact (MK_COMB (@lem7559009) (@lem7559008 _97561)). Qed.
Lemma lem7559011 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7559012 (_97561 : int) : (term845 _97561) = term870.
Proof. exact (MK_COMB (@lem7559010 _97561) (@lem7559011)). Qed.
Lemma lem7559013 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : term870.
Proof. exact (EQ_MP (@lem7559012 _97561) (@lem7558894 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559015 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7559016 : term870 = term871.
Proof. exact (@lem7559015 term35 term523). Qed.
Lemma lem7559018 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7559019 : term523 = term524.
Proof. exact (@lem7559018 term470). Qed.
Lemma lem7559021 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559022 : term35 = term520.
Proof. exact (@lem7559021 (NUMERAL 0)). Qed.
Lemma lem7559023 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7559024 : term457 = term872.
Proof. exact (MK_COMB (@lem7559023) (@lem7559022)). Qed.
Lemma lem7559025 : term871 = term873.
Proof. exact (MK_COMB (@lem7559024) (@lem7559019)). Qed.
Lemma lem7559026 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7559028 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559029 : term818 = term824.
Proof. exact (@lem7559028 (NUMERAL 0) term470). Qed.
Lemma lem7559030 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559031 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559032 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559031 h1) (fun h1 : term824 = True => @lem7559030)). Qed.
Lemma lem7559033 : term824 = True.
Proof. exact (EQ_MP (@lem7559032) (@lem7559030)). Qed.
Lemma lem7559034 : term818 = True.
Proof. exact (TRANS (@lem7559029) (@lem7559033)). Qed.
Lemma lem7559035 : True = term818.
Proof. exact (SYM (@lem7559034)). Qed.
Lemma lem7559036 : term818.
Proof. exact (EQ_MP (@lem7559035) (@lem0)). Qed.
Lemma lem7559037 : term875.
Proof. exact (@lem7559026 (@lem7559036)). Qed.
Lemma lem7559039 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559040 : term818 = term824.
Proof. exact (@lem7559039 (NUMERAL 0) term470). Qed.
Lemma lem7559041 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559042 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559043 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559042 h1) (fun h1 : term824 = True => @lem7559041)). Qed.
Lemma lem7559044 : term824 = True.
Proof. exact (EQ_MP (@lem7559043) (@lem7559041)). Qed.
Lemma lem7559045 : term818 = True.
Proof. exact (TRANS (@lem7559040) (@lem7559044)). Qed.
Lemma lem7559046 : True = term818.
Proof. exact (SYM (@lem7559045)). Qed.
Lemma lem7559047 : term818.
Proof. exact (EQ_MP (@lem7559046) (@lem0)). Qed.
Lemma lem7559048 : term873 = term876.
Proof. exact (@lem7559037 (@lem7559047)). Qed.
Lemma lem7559050 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7559051 : term550 = term555.
Proof. exact (@lem7559050 term470 term470). Qed.
Lemma lem7559052 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559053 : term535 = term470.
Proof. exact (EQ_MP (@lem7559052) (@lem940073)). Qed.
Lemma lem7559054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559055 : term533 = term469.
Proof. exact (MK_COMB (@lem7559054) (@lem7559053)). Qed.
Lemma lem7559056 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7559057 : term555 = term523.
Proof. exact (MK_COMB (@lem7559056) (@lem7559055)). Qed.
Lemma lem7559058 : term550 = term523.
Proof. exact (TRANS (@lem7559051) (@lem7559057)). Qed.
Lemma lem7559060 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559061 : term829 = term35.
Proof. exact (@lem7559060 term470). Qed.
Lemma lem7559062 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7559063 : term877 = term457.
Proof. exact (MK_COMB (@lem7559062) (@lem7559061)). Qed.
Lemma lem7559064 : term876 = term871.
Proof. exact (MK_COMB (@lem7559063) (@lem7559058)). Qed.
Lemma lem7559066 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7559067 : term871 = term880.
Proof. exact (@lem7559066 (NUMERAL 0) term470). Qed.
Lemma lem7559068 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559069 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7559070 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559069 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7559068)). Qed.
Lemma lem7559071 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7559070) (@lem7559068)). Qed.
Lemma lem7559072 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7559073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7559074 : term881 = (and True).
Proof. exact (MK_COMB (@lem7559073) (@lem7559072)). Qed.
Lemma lem7559075 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7559074) (@lem7559071)). Qed.
Lemma lem7559077 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7559078 : term880 = False.
Proof. exact (TRANS (@lem7559075) (@lem7559077)). Qed.
Lemma lem7559079 : term871 = False.
Proof. exact (TRANS (@lem7559067) (@lem7559078)). Qed.
Lemma lem7559080 : term876 = False.
Proof. exact (TRANS (@lem7559064) (@lem7559079)). Qed.
Lemma lem7559081 : term873 = False.
Proof. exact (TRANS (@lem7559048) (@lem7559080)). Qed.
Lemma lem7559082 : term871 = False.
Proof. exact (TRANS (@lem7559025) (@lem7559081)). Qed.
Lemma lem7559083 : term870 = False.
Proof. exact (TRANS (@lem7559016) (@lem7559082)). Qed.
Lemma lem7559084 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term736 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7559083) (@lem7559013 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559085 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term752 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7559086 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term750 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559085 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559088 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term749 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559086 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559090 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term747 _97559 _97561.
Proof. exact (proj2 (@lem7559088 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559092 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term745 _97559 _97561.
Proof. exact (proj2 (@lem7559090 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559094 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term743 _97559 _97561.
Proof. exact (proj2 (@lem7559092 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559095 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term564 _97561.
Proof. exact (proj1 (@lem7559092 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559097 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term595 _97559 _97561.
Proof. exact (proj1 (@lem7559094 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559099 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term543 _97561.
Proof. exact (proj1 (@lem7559097 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559101 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7559102 : term817 = term818.
Proof. exact (@lem7559101 term35 term469). Qed.
Lemma lem7559104 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559105 : term469 = term549.
Proof. exact (@lem7559104 term470). Qed.
Lemma lem7559107 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559108 : term35 = term520.
Proof. exact (@lem7559107 (NUMERAL 0)). Qed.
Lemma lem7559109 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559110 : term819 = term820.
Proof. exact (MK_COMB (@lem7559109) (@lem7559108)). Qed.
Lemma lem7559111 : term818 = term821.
Proof. exact (MK_COMB (@lem7559110) (@lem7559105)). Qed.
Lemma lem7559112 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7559114 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559115 : term818 = term824.
Proof. exact (@lem7559114 (NUMERAL 0) term470). Qed.
Lemma lem7559116 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559117 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559118 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559117 h1) (fun h1 : term824 = True => @lem7559116)). Qed.
Lemma lem7559119 : term824 = True.
Proof. exact (EQ_MP (@lem7559118) (@lem7559116)). Qed.
Lemma lem7559120 : term818 = True.
Proof. exact (TRANS (@lem7559115) (@lem7559119)). Qed.
Lemma lem7559121 : True = term818.
Proof. exact (SYM (@lem7559120)). Qed.
Lemma lem7559122 : term818.
Proof. exact (EQ_MP (@lem7559121) (@lem0)). Qed.
Lemma lem7559123 : term826.
Proof. exact (@lem7559112 (@lem7559122)). Qed.
Lemma lem7559125 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559126 : term818 = term824.
Proof. exact (@lem7559125 (NUMERAL 0) term470). Qed.
Lemma lem7559127 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559128 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559129 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559128 h1) (fun h1 : term824 = True => @lem7559127)). Qed.
Lemma lem7559130 : term824 = True.
Proof. exact (EQ_MP (@lem7559129) (@lem7559127)). Qed.
Lemma lem7559131 : term818 = True.
Proof. exact (TRANS (@lem7559126) (@lem7559130)). Qed.
Lemma lem7559132 : True = term818.
Proof. exact (SYM (@lem7559131)). Qed.
Lemma lem7559133 : term818.
Proof. exact (EQ_MP (@lem7559132) (@lem0)). Qed.
Lemma lem7559134 : term821 = term827.
Proof. exact (@lem7559123 (@lem7559133)). Qed.
Lemma lem7559136 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559137 : term532 = term533.
Proof. exact (@lem7559136 term470 term470). Qed.
Lemma lem7559138 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559139 : term535 = term470.
Proof. exact (EQ_MP (@lem7559138) (@lem940073)). Qed.
Lemma lem7559140 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559141 : term533 = term469.
Proof. exact (MK_COMB (@lem7559140) (@lem7559139)). Qed.
Lemma lem7559142 : term532 = term469.
Proof. exact (TRANS (@lem7559137) (@lem7559141)). Qed.
Lemma lem7559144 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559145 : term829 = term35.
Proof. exact (@lem7559144 term470). Qed.
Lemma lem7559146 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559147 : term830 = term819.
Proof. exact (MK_COMB (@lem7559146) (@lem7559145)). Qed.
Lemma lem7559148 : term827 = term818.
Proof. exact (MK_COMB (@lem7559147) (@lem7559142)). Qed.
Lemma lem7559150 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559151 : term818 = term824.
Proof. exact (@lem7559150 (NUMERAL 0) term470). Qed.
Lemma lem7559152 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559153 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559154 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559153 h1) (fun h1 : term824 = True => @lem7559152)). Qed.
Lemma lem7559155 : term824 = True.
Proof. exact (EQ_MP (@lem7559154) (@lem7559152)). Qed.
Lemma lem7559156 : term818 = True.
Proof. exact (TRANS (@lem7559151) (@lem7559155)). Qed.
Lemma lem7559157 : term827 = True.
Proof. exact (TRANS (@lem7559148) (@lem7559156)). Qed.
Lemma lem7559158 : term821 = True.
Proof. exact (TRANS (@lem7559134) (@lem7559157)). Qed.
Lemma lem7559159 : term818 = True.
Proof. exact (TRANS (@lem7559111) (@lem7559158)). Qed.
Lemma lem7559160 : term817 = True.
Proof. exact (TRANS (@lem7559102) (@lem7559159)). Qed.
Lemma lem7559161 : True = term817.
Proof. exact (SYM (@lem7559160)). Qed.
Lemma lem7559162 : term817.
Proof. exact (EQ_MP (@lem7559161) (@lem0)). Qed.
Lemma lem7559163 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term831 _97561.
Proof. exact (conj (@lem7559162) (@lem7559099 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559165 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7559166 (_97561 : int) : term833 _97561.
Proof. exact (@lem7559165 term469 (real_of_int _97561)). Qed.
Lemma lem7559167 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term834 _97561.
Proof. exact (@lem7559166 _97561 (@lem7559163 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559168 (_97561 : int) : (term835 _97561) = (real_of_int _97561).
Proof. exact (@lem1982733 (real_of_int _97561)). Qed.
Lemma lem7559169 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7559170 (_97561 : int) : (term836 _97561) = (term542 _97561).
Proof. exact (MK_COMB (@lem7559169) (@lem7559168 _97561)). Qed.
Lemma lem7559171 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7559172 (_97561 : int) : (term834 _97561) = (term543 _97561).
Proof. exact (MK_COMB (@lem7559170 _97561) (@lem7559171)). Qed.
Lemma lem7559173 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term543 _97561.
Proof. exact (EQ_MP (@lem7559172 _97561) (@lem7559167 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559175 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7559176 : term817 = term818.
Proof. exact (@lem7559175 term35 term469). Qed.
Lemma lem7559178 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559179 : term469 = term549.
Proof. exact (@lem7559178 term470). Qed.
Lemma lem7559181 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559182 : term35 = term520.
Proof. exact (@lem7559181 (NUMERAL 0)). Qed.
Lemma lem7559183 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559184 : term819 = term820.
Proof. exact (MK_COMB (@lem7559183) (@lem7559182)). Qed.
Lemma lem7559185 : term818 = term821.
Proof. exact (MK_COMB (@lem7559184) (@lem7559179)). Qed.
Lemma lem7559186 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7559188 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559189 : term818 = term824.
Proof. exact (@lem7559188 (NUMERAL 0) term470). Qed.
Lemma lem7559190 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559191 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559192 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559191 h1) (fun h1 : term824 = True => @lem7559190)). Qed.
Lemma lem7559193 : term824 = True.
Proof. exact (EQ_MP (@lem7559192) (@lem7559190)). Qed.
Lemma lem7559194 : term818 = True.
Proof. exact (TRANS (@lem7559189) (@lem7559193)). Qed.
Lemma lem7559195 : True = term818.
Proof. exact (SYM (@lem7559194)). Qed.
Lemma lem7559196 : term818.
Proof. exact (EQ_MP (@lem7559195) (@lem0)). Qed.
Lemma lem7559197 : term826.
Proof. exact (@lem7559186 (@lem7559196)). Qed.
Lemma lem7559199 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559200 : term818 = term824.
Proof. exact (@lem7559199 (NUMERAL 0) term470). Qed.
Lemma lem7559201 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559202 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559203 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559202 h1) (fun h1 : term824 = True => @lem7559201)). Qed.
Lemma lem7559204 : term824 = True.
Proof. exact (EQ_MP (@lem7559203) (@lem7559201)). Qed.
Lemma lem7559205 : term818 = True.
Proof. exact (TRANS (@lem7559200) (@lem7559204)). Qed.
Lemma lem7559206 : True = term818.
Proof. exact (SYM (@lem7559205)). Qed.
Lemma lem7559207 : term818.
Proof. exact (EQ_MP (@lem7559206) (@lem0)). Qed.
Lemma lem7559208 : term821 = term827.
Proof. exact (@lem7559197 (@lem7559207)). Qed.
Lemma lem7559210 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559211 : term532 = term533.
Proof. exact (@lem7559210 term470 term470). Qed.
Lemma lem7559212 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559213 : term535 = term470.
Proof. exact (EQ_MP (@lem7559212) (@lem940073)). Qed.
Lemma lem7559214 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559215 : term533 = term469.
Proof. exact (MK_COMB (@lem7559214) (@lem7559213)). Qed.
Lemma lem7559216 : term532 = term469.
Proof. exact (TRANS (@lem7559211) (@lem7559215)). Qed.
Lemma lem7559218 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559219 : term829 = term35.
Proof. exact (@lem7559218 term470). Qed.
Lemma lem7559220 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559221 : term830 = term819.
Proof. exact (MK_COMB (@lem7559220) (@lem7559219)). Qed.
Lemma lem7559222 : term827 = term818.
Proof. exact (MK_COMB (@lem7559221) (@lem7559216)). Qed.
Lemma lem7559224 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559225 : term818 = term824.
Proof. exact (@lem7559224 (NUMERAL 0) term470). Qed.
Lemma lem7559226 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559227 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559228 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559227 h1) (fun h1 : term824 = True => @lem7559226)). Qed.
Lemma lem7559229 : term824 = True.
Proof. exact (EQ_MP (@lem7559228) (@lem7559226)). Qed.
Lemma lem7559230 : term818 = True.
Proof. exact (TRANS (@lem7559225) (@lem7559229)). Qed.
Lemma lem7559231 : term827 = True.
Proof. exact (TRANS (@lem7559222) (@lem7559230)). Qed.
Lemma lem7559232 : term821 = True.
Proof. exact (TRANS (@lem7559208) (@lem7559231)). Qed.
Lemma lem7559233 : term818 = True.
Proof. exact (TRANS (@lem7559185) (@lem7559232)). Qed.
Lemma lem7559234 : term817 = True.
Proof. exact (TRANS (@lem7559176) (@lem7559233)). Qed.
Lemma lem7559235 : True = term817.
Proof. exact (SYM (@lem7559234)). Qed.
Lemma lem7559236 : term817.
Proof. exact (EQ_MP (@lem7559235) (@lem0)). Qed.
Lemma lem7559237 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term837 _97561.
Proof. exact (conj (@lem7559236) (@lem7559095 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559239 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7559240 (_97561 : int) : term838 _97561.
Proof. exact (@lem7559239 term469 (term559 _97561)). Qed.
Lemma lem7559241 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term839 _97561.
Proof. exact (@lem7559240 _97561 (@lem7559237 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559242 (_97561 : int) : (term840 _97561) = (term559 _97561).
Proof. exact (@lem1982733 (term559 _97561)). Qed.
Lemma lem7559243 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7559244 (_97561 : int) : (term841 _97561) = (term563 _97561).
Proof. exact (MK_COMB (@lem7559243) (@lem7559242 _97561)). Qed.
Lemma lem7559245 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7559246 (_97561 : int) : (term839 _97561) = (term564 _97561).
Proof. exact (MK_COMB (@lem7559244 _97561) (@lem7559245)). Qed.
Lemma lem7559247 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term564 _97561.
Proof. exact (EQ_MP (@lem7559246 _97561) (@lem7559241 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559248 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term842 _97561.
Proof. exact (conj (@lem7559247 _97560 _97559 _97561 h1) (@lem7559173 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559250 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7559251 (_97561 : int) : term844 _97561.
Proof. exact (@lem7559250 (term559 _97561) (real_of_int _97561)). Qed.
Lemma lem7559252 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term845 _97561.
Proof. exact (@lem7559251 _97561 (@lem7559248 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559253 (_97561 : int) : (term846 _97561) = (term847 _97561).
Proof. exact (@lem1982759 (term570 _97561) (real_of_int _97561) term523). Qed.
Lemma lem7559254 (_97561 : int) : (term848 _97561) = (term849 _97561).
Proof. exact (@lem1982713 term523 (real_of_int _97561)). Qed.
Lemma lem7559256 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559257 : term469 = term549.
Proof. exact (@lem7559256 term470). Qed.
Lemma lem7559259 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7559260 : term523 = term524.
Proof. exact (@lem7559259 term470). Qed.
Lemma lem7559261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559262 : term850 = term851.
Proof. exact (MK_COMB (@lem7559261) (@lem7559260)). Qed.
Lemma lem7559263 : term852 = term853.
Proof. exact (MK_COMB (@lem7559262) (@lem7559257)). Qed.
Lemma lem7559264 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7559266 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559267 : term818 = term824.
Proof. exact (@lem7559266 (NUMERAL 0) term470). Qed.
Lemma lem7559268 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559269 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559270 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559269 h1) (fun h1 : term824 = True => @lem7559268)). Qed.
Lemma lem7559271 : term824 = True.
Proof. exact (EQ_MP (@lem7559270) (@lem7559268)). Qed.
Lemma lem7559272 : term818 = True.
Proof. exact (TRANS (@lem7559267) (@lem7559271)). Qed.
Lemma lem7559273 : True = term818.
Proof. exact (SYM (@lem7559272)). Qed.
Lemma lem7559274 : term818.
Proof. exact (EQ_MP (@lem7559273) (@lem0)). Qed.
Lemma lem7559275 : term855.
Proof. exact (@lem7559264 (@lem7559274)). Qed.
Lemma lem7559277 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559278 : term818 = term824.
Proof. exact (@lem7559277 (NUMERAL 0) term470). Qed.
Lemma lem7559279 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559280 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559281 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559280 h1) (fun h1 : term824 = True => @lem7559279)). Qed.
Lemma lem7559282 : term824 = True.
Proof. exact (EQ_MP (@lem7559281) (@lem7559279)). Qed.
Lemma lem7559283 : term818 = True.
Proof. exact (TRANS (@lem7559278) (@lem7559282)). Qed.
Lemma lem7559284 : True = term818.
Proof. exact (SYM (@lem7559283)). Qed.
Lemma lem7559285 : term818.
Proof. exact (EQ_MP (@lem7559284) (@lem0)). Qed.
Lemma lem7559286 : term856.
Proof. exact (@lem7559275 (@lem7559285)). Qed.
Lemma lem7559288 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559289 : term818 = term824.
Proof. exact (@lem7559288 (NUMERAL 0) term470). Qed.
Lemma lem7559290 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559291 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559292 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559291 h1) (fun h1 : term824 = True => @lem7559290)). Qed.
Lemma lem7559293 : term824 = True.
Proof. exact (EQ_MP (@lem7559292) (@lem7559290)). Qed.
Lemma lem7559294 : term818 = True.
Proof. exact (TRANS (@lem7559289) (@lem7559293)). Qed.
Lemma lem7559295 : True = term818.
Proof. exact (SYM (@lem7559294)). Qed.
Lemma lem7559296 : term818.
Proof. exact (EQ_MP (@lem7559295) (@lem0)). Qed.
Lemma lem7559297 : term857.
Proof. exact (@lem7559286 (@lem7559296)). Qed.
Lemma lem7559299 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559300 : term532 = term533.
Proof. exact (@lem7559299 term470 term470). Qed.
Lemma lem7559301 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559302 : term535 = term470.
Proof. exact (EQ_MP (@lem7559301) (@lem940073)). Qed.
Lemma lem7559303 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559304 : term533 = term469.
Proof. exact (MK_COMB (@lem7559303) (@lem7559302)). Qed.
Lemma lem7559305 : term532 = term469.
Proof. exact (TRANS (@lem7559300) (@lem7559304)). Qed.
Lemma lem7559307 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7559308 : term550 = term555.
Proof. exact (@lem7559307 term470 term470). Qed.
Lemma lem7559309 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559310 : term535 = term470.
Proof. exact (EQ_MP (@lem7559309) (@lem940073)). Qed.
Lemma lem7559311 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559312 : term533 = term469.
Proof. exact (MK_COMB (@lem7559311) (@lem7559310)). Qed.
Lemma lem7559313 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7559314 : term555 = term523.
Proof. exact (MK_COMB (@lem7559313) (@lem7559312)). Qed.
Lemma lem7559315 : term550 = term523.
Proof. exact (TRANS (@lem7559308) (@lem7559314)). Qed.
Lemma lem7559316 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559317 : term858 = term850.
Proof. exact (MK_COMB (@lem7559316) (@lem7559315)). Qed.
Lemma lem7559318 : term859 = term852.
Proof. exact (MK_COMB (@lem7559317) (@lem7559305)). Qed.
Lemma lem7559320 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7559321 : term852 = term35.
Proof. exact (@lem7559320 term470). Qed.
Lemma lem7559322 : term859 = term35.
Proof. exact (TRANS (@lem7559318) (@lem7559321)). Qed.
Lemma lem7559323 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7559324 : term861 = term218.
Proof. exact (MK_COMB (@lem7559323) (@lem7559322)). Qed.
Lemma lem7559325 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7559326 : term862 = term829.
Proof. exact (MK_COMB (@lem7559324) (@lem7559325)). Qed.
Lemma lem7559328 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559329 : term829 = term35.
Proof. exact (@lem7559328 term470). Qed.
Lemma lem7559330 : term862 = term35.
Proof. exact (TRANS (@lem7559326) (@lem7559329)). Qed.
Lemma lem7559332 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559333 : term532 = term533.
Proof. exact (@lem7559332 term470 term470). Qed.
Lemma lem7559334 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559335 : term535 = term470.
Proof. exact (EQ_MP (@lem7559334) (@lem940073)). Qed.
Lemma lem7559336 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559337 : term533 = term469.
Proof. exact (MK_COMB (@lem7559336) (@lem7559335)). Qed.
Lemma lem7559338 : term532 = term469.
Proof. exact (TRANS (@lem7559333) (@lem7559337)). Qed.
Lemma lem7559339 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7559340 : term863 = term829.
Proof. exact (MK_COMB (@lem7559339) (@lem7559338)). Qed.
Lemma lem7559342 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559343 : term829 = term35.
Proof. exact (@lem7559342 term470). Qed.
Lemma lem7559344 : term863 = term35.
Proof. exact (TRANS (@lem7559340) (@lem7559343)). Qed.
Lemma lem7559345 : term35 = term863.
Proof. exact (SYM (@lem7559344)). Qed.
Lemma lem7559346 : term862 = term863.
Proof. exact (TRANS (@lem7559330) (@lem7559345)). Qed.
Lemma lem7559347 : term853 = term520.
Proof. exact (@lem7559297 (@lem7559346)). Qed.
Lemma lem7559348 : term852 = term520.
Proof. exact (TRANS (@lem7559263) (@lem7559347)). Qed.
Lemma lem7559350 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7559351 : term520 = term35.
Proof. exact (@lem7559350 term35). Qed.
Lemma lem7559352 : term852 = term35.
Proof. exact (TRANS (@lem7559348) (@lem7559351)). Qed.
Lemma lem7559353 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7559354 : term864 = term218.
Proof. exact (MK_COMB (@lem7559353) (@lem7559352)). Qed.
Lemma lem7559355 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7559356 (_97561 : int) : (term849 _97561) = (term865 _97561).
Proof. exact (MK_COMB (@lem7559354) (@lem7559355 _97561)). Qed.
Lemma lem7559357 (_97561 : int) : (term848 _97561) = (term865 _97561).
Proof. exact (TRANS (@lem7559254 _97561) (@lem7559356 _97561)). Qed.
Lemma lem7559358 (_97561 : int) : (term865 _97561) = term35.
Proof. exact (@lem1982719 (real_of_int _97561)). Qed.
Lemma lem7559359 (_97561 : int) : (term848 _97561) = term35.
Proof. exact (TRANS (@lem7559357 _97561) (@lem7559358 _97561)). Qed.
Lemma lem7559360 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559361 (_97561 : int) : (term866 _97561) = term560.
Proof. exact (MK_COMB (@lem7559360) (@lem7559359 _97561)). Qed.
Lemma lem7559362 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7559363 (_97561 : int) : (term847 _97561) = term867.
Proof. exact (MK_COMB (@lem7559361 _97561) (@lem7559362)). Qed.
Lemma lem7559364 (_97561 : int) : (term846 _97561) = term867.
Proof. exact (TRANS (@lem7559253 _97561) (@lem7559363 _97561)). Qed.
Lemma lem7559365 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7559366 (_97561 : int) : (term846 _97561) = term523.
Proof. exact (TRANS (@lem7559364 _97561) (@lem7559365)). Qed.
Lemma lem7559367 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7559368 (_97561 : int) : (term868 _97561) = term869.
Proof. exact (MK_COMB (@lem7559367) (@lem7559366 _97561)). Qed.
Lemma lem7559369 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7559370 (_97561 : int) : (term845 _97561) = term870.
Proof. exact (MK_COMB (@lem7559368 _97561) (@lem7559369)). Qed.
Lemma lem7559371 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : term870.
Proof. exact (EQ_MP (@lem7559370 _97561) (@lem7559252 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559373 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7559374 : term870 = term871.
Proof. exact (@lem7559373 term35 term523). Qed.
Lemma lem7559376 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7559377 : term523 = term524.
Proof. exact (@lem7559376 term470). Qed.
Lemma lem7559379 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559380 : term35 = term520.
Proof. exact (@lem7559379 (NUMERAL 0)). Qed.
Lemma lem7559381 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7559382 : term457 = term872.
Proof. exact (MK_COMB (@lem7559381) (@lem7559380)). Qed.
Lemma lem7559383 : term871 = term873.
Proof. exact (MK_COMB (@lem7559382) (@lem7559377)). Qed.
Lemma lem7559384 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7559386 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559387 : term818 = term824.
Proof. exact (@lem7559386 (NUMERAL 0) term470). Qed.
Lemma lem7559388 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559389 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559390 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559389 h1) (fun h1 : term824 = True => @lem7559388)). Qed.
Lemma lem7559391 : term824 = True.
Proof. exact (EQ_MP (@lem7559390) (@lem7559388)). Qed.
Lemma lem7559392 : term818 = True.
Proof. exact (TRANS (@lem7559387) (@lem7559391)). Qed.
Lemma lem7559393 : True = term818.
Proof. exact (SYM (@lem7559392)). Qed.
Lemma lem7559394 : term818.
Proof. exact (EQ_MP (@lem7559393) (@lem0)). Qed.
Lemma lem7559395 : term875.
Proof. exact (@lem7559384 (@lem7559394)). Qed.
Lemma lem7559397 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559398 : term818 = term824.
Proof. exact (@lem7559397 (NUMERAL 0) term470). Qed.
Lemma lem7559399 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559400 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559401 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559400 h1) (fun h1 : term824 = True => @lem7559399)). Qed.
Lemma lem7559402 : term824 = True.
Proof. exact (EQ_MP (@lem7559401) (@lem7559399)). Qed.
Lemma lem7559403 : term818 = True.
Proof. exact (TRANS (@lem7559398) (@lem7559402)). Qed.
Lemma lem7559404 : True = term818.
Proof. exact (SYM (@lem7559403)). Qed.
Lemma lem7559405 : term818.
Proof. exact (EQ_MP (@lem7559404) (@lem0)). Qed.
Lemma lem7559406 : term873 = term876.
Proof. exact (@lem7559395 (@lem7559405)). Qed.
Lemma lem7559408 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7559409 : term550 = term555.
Proof. exact (@lem7559408 term470 term470). Qed.
Lemma lem7559410 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559411 : term535 = term470.
Proof. exact (EQ_MP (@lem7559410) (@lem940073)). Qed.
Lemma lem7559412 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559413 : term533 = term469.
Proof. exact (MK_COMB (@lem7559412) (@lem7559411)). Qed.
Lemma lem7559414 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7559415 : term555 = term523.
Proof. exact (MK_COMB (@lem7559414) (@lem7559413)). Qed.
Lemma lem7559416 : term550 = term523.
Proof. exact (TRANS (@lem7559409) (@lem7559415)). Qed.
Lemma lem7559418 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559419 : term829 = term35.
Proof. exact (@lem7559418 term470). Qed.
Lemma lem7559420 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7559421 : term877 = term457.
Proof. exact (MK_COMB (@lem7559420) (@lem7559419)). Qed.
Lemma lem7559422 : term876 = term871.
Proof. exact (MK_COMB (@lem7559421) (@lem7559416)). Qed.
Lemma lem7559424 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7559425 : term871 = term880.
Proof. exact (@lem7559424 (NUMERAL 0) term470). Qed.
Lemma lem7559426 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559427 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7559428 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559427 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7559426)). Qed.
Lemma lem7559429 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7559428) (@lem7559426)). Qed.
Lemma lem7559430 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7559431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7559432 : term881 = (and True).
Proof. exact (MK_COMB (@lem7559431) (@lem7559430)). Qed.
Lemma lem7559433 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7559432) (@lem7559429)). Qed.
Lemma lem7559435 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7559436 : term880 = False.
Proof. exact (TRANS (@lem7559433) (@lem7559435)). Qed.
Lemma lem7559437 : term871 = False.
Proof. exact (TRANS (@lem7559425) (@lem7559436)). Qed.
Lemma lem7559438 : term876 = False.
Proof. exact (TRANS (@lem7559422) (@lem7559437)). Qed.
Lemma lem7559439 : term873 = False.
Proof. exact (TRANS (@lem7559406) (@lem7559438)). Qed.
Lemma lem7559440 : term871 = False.
Proof. exact (TRANS (@lem7559383) (@lem7559439)). Qed.
Lemma lem7559441 : term870 = False.
Proof. exact (TRANS (@lem7559374) (@lem7559440)). Qed.
Lemma lem7559442 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term752 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7559441) (@lem7559371 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559443 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term754 _97560 _97559 _97561) : False.
Proof. exact (or_elim (@lem7558726 _97560 _97559 _97561 h1) (fun h0 : term736 _97560 _97559 _97561 => @lem7559084 _97560 _97559 _97561 h0) (fun h0 : term752 _97560 _97559 _97561 => @lem7559442 _97560 _97559 _97561 h0)). Qed.
Lemma lem7559444 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term795 _97560 _97559 _97561) : term795 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7559445 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term785 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7559446 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term784 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559445 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559448 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term783 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559446 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559450 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term781 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559448 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559452 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term779 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559450 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559454 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term726 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559452 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559455 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term573 _97559 _97561.
Proof. exact (proj1 (@lem7559452 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559456 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term590 _97559 _97561.
Proof. exact (proj2 (@lem7559454 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559461 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7559462 : term817 = term818.
Proof. exact (@lem7559461 term35 term469). Qed.
Lemma lem7559464 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559465 : term469 = term549.
Proof. exact (@lem7559464 term470). Qed.
Lemma lem7559467 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559468 : term35 = term520.
Proof. exact (@lem7559467 (NUMERAL 0)). Qed.
Lemma lem7559469 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559470 : term819 = term820.
Proof. exact (MK_COMB (@lem7559469) (@lem7559468)). Qed.
Lemma lem7559471 : term818 = term821.
Proof. exact (MK_COMB (@lem7559470) (@lem7559465)). Qed.
Lemma lem7559472 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7559474 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559475 : term818 = term824.
Proof. exact (@lem7559474 (NUMERAL 0) term470). Qed.
Lemma lem7559476 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559477 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559478 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559477 h1) (fun h1 : term824 = True => @lem7559476)). Qed.
Lemma lem7559479 : term824 = True.
Proof. exact (EQ_MP (@lem7559478) (@lem7559476)). Qed.
Lemma lem7559480 : term818 = True.
Proof. exact (TRANS (@lem7559475) (@lem7559479)). Qed.
Lemma lem7559481 : True = term818.
Proof. exact (SYM (@lem7559480)). Qed.
Lemma lem7559482 : term818.
Proof. exact (EQ_MP (@lem7559481) (@lem0)). Qed.
Lemma lem7559483 : term826.
Proof. exact (@lem7559472 (@lem7559482)). Qed.
Lemma lem7559485 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559486 : term818 = term824.
Proof. exact (@lem7559485 (NUMERAL 0) term470). Qed.
Lemma lem7559487 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559488 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559489 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559488 h1) (fun h1 : term824 = True => @lem7559487)). Qed.
Lemma lem7559490 : term824 = True.
Proof. exact (EQ_MP (@lem7559489) (@lem7559487)). Qed.
Lemma lem7559491 : term818 = True.
Proof. exact (TRANS (@lem7559486) (@lem7559490)). Qed.
Lemma lem7559492 : True = term818.
Proof. exact (SYM (@lem7559491)). Qed.
Lemma lem7559493 : term818.
Proof. exact (EQ_MP (@lem7559492) (@lem0)). Qed.
Lemma lem7559494 : term821 = term827.
Proof. exact (@lem7559483 (@lem7559493)). Qed.
Lemma lem7559496 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559497 : term532 = term533.
Proof. exact (@lem7559496 term470 term470). Qed.
Lemma lem7559498 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559499 : term535 = term470.
Proof. exact (EQ_MP (@lem7559498) (@lem940073)). Qed.
Lemma lem7559500 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559501 : term533 = term469.
Proof. exact (MK_COMB (@lem7559500) (@lem7559499)). Qed.
Lemma lem7559502 : term532 = term469.
Proof. exact (TRANS (@lem7559497) (@lem7559501)). Qed.
Lemma lem7559504 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559505 : term829 = term35.
Proof. exact (@lem7559504 term470). Qed.
Lemma lem7559506 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559507 : term830 = term819.
Proof. exact (MK_COMB (@lem7559506) (@lem7559505)). Qed.
Lemma lem7559508 : term827 = term818.
Proof. exact (MK_COMB (@lem7559507) (@lem7559502)). Qed.
Lemma lem7559510 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559511 : term818 = term824.
Proof. exact (@lem7559510 (NUMERAL 0) term470). Qed.
Lemma lem7559512 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559513 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559514 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559513 h1) (fun h1 : term824 = True => @lem7559512)). Qed.
Lemma lem7559515 : term824 = True.
Proof. exact (EQ_MP (@lem7559514) (@lem7559512)). Qed.
Lemma lem7559516 : term818 = True.
Proof. exact (TRANS (@lem7559511) (@lem7559515)). Qed.
Lemma lem7559517 : term827 = True.
Proof. exact (TRANS (@lem7559508) (@lem7559516)). Qed.
Lemma lem7559518 : term821 = True.
Proof. exact (TRANS (@lem7559494) (@lem7559517)). Qed.
Lemma lem7559519 : term818 = True.
Proof. exact (TRANS (@lem7559471) (@lem7559518)). Qed.
Lemma lem7559520 : term817 = True.
Proof. exact (TRANS (@lem7559462) (@lem7559519)). Qed.
Lemma lem7559521 : True = term817.
Proof. exact (SYM (@lem7559520)). Qed.
Lemma lem7559522 : term817.
Proof. exact (EQ_MP (@lem7559521) (@lem0)). Qed.
Lemma lem7559523 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term882 _97559 _97561.
Proof. exact (conj (@lem7559522) (@lem7559456 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559525 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7559526 (_97559 : int) (_97561 : int) : term883 _97559 _97561.
Proof. exact (@lem7559525 term469 (term587 _97559 _97561)). Qed.
Lemma lem7559527 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term884 _97559 _97561.
Proof. exact (@lem7559526 _97559 _97561 (@lem7559523 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559528 (_97559 : int) (_97561 : int) : (term885 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982733 (term587 _97559 _97561)). Qed.
Lemma lem7559529 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7559530 (_97559 : int) (_97561 : int) : (term886 _97559 _97561) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7559529) (@lem7559528 _97559 _97561)). Qed.
Lemma lem7559531 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7559532 (_97559 : int) (_97561 : int) : (term884 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7559530 _97559 _97561) (@lem7559531)). Qed.
Lemma lem7559533 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term590 _97559 _97561.
Proof. exact (EQ_MP (@lem7559532 _97559 _97561) (@lem7559527 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559535 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7559536 : term817 = term818.
Proof. exact (@lem7559535 term35 term469). Qed.
Lemma lem7559538 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559539 : term469 = term549.
Proof. exact (@lem7559538 term470). Qed.
Lemma lem7559541 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559542 : term35 = term520.
Proof. exact (@lem7559541 (NUMERAL 0)). Qed.
Lemma lem7559543 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559544 : term819 = term820.
Proof. exact (MK_COMB (@lem7559543) (@lem7559542)). Qed.
Lemma lem7559545 : term818 = term821.
Proof. exact (MK_COMB (@lem7559544) (@lem7559539)). Qed.
Lemma lem7559546 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7559548 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559549 : term818 = term824.
Proof. exact (@lem7559548 (NUMERAL 0) term470). Qed.
Lemma lem7559550 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559551 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559552 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559551 h1) (fun h1 : term824 = True => @lem7559550)). Qed.
Lemma lem7559553 : term824 = True.
Proof. exact (EQ_MP (@lem7559552) (@lem7559550)). Qed.
Lemma lem7559554 : term818 = True.
Proof. exact (TRANS (@lem7559549) (@lem7559553)). Qed.
Lemma lem7559555 : True = term818.
Proof. exact (SYM (@lem7559554)). Qed.
Lemma lem7559556 : term818.
Proof. exact (EQ_MP (@lem7559555) (@lem0)). Qed.
Lemma lem7559557 : term826.
Proof. exact (@lem7559546 (@lem7559556)). Qed.
Lemma lem7559559 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559560 : term818 = term824.
Proof. exact (@lem7559559 (NUMERAL 0) term470). Qed.
Lemma lem7559561 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559562 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559563 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559562 h1) (fun h1 : term824 = True => @lem7559561)). Qed.
Lemma lem7559564 : term824 = True.
Proof. exact (EQ_MP (@lem7559563) (@lem7559561)). Qed.
Lemma lem7559565 : term818 = True.
Proof. exact (TRANS (@lem7559560) (@lem7559564)). Qed.
Lemma lem7559566 : True = term818.
Proof. exact (SYM (@lem7559565)). Qed.
Lemma lem7559567 : term818.
Proof. exact (EQ_MP (@lem7559566) (@lem0)). Qed.
Lemma lem7559568 : term821 = term827.
Proof. exact (@lem7559557 (@lem7559567)). Qed.
Lemma lem7559570 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559571 : term532 = term533.
Proof. exact (@lem7559570 term470 term470). Qed.
Lemma lem7559572 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559573 : term535 = term470.
Proof. exact (EQ_MP (@lem7559572) (@lem940073)). Qed.
Lemma lem7559574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559575 : term533 = term469.
Proof. exact (MK_COMB (@lem7559574) (@lem7559573)). Qed.
Lemma lem7559576 : term532 = term469.
Proof. exact (TRANS (@lem7559571) (@lem7559575)). Qed.
Lemma lem7559578 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559579 : term829 = term35.
Proof. exact (@lem7559578 term470). Qed.
Lemma lem7559580 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559581 : term830 = term819.
Proof. exact (MK_COMB (@lem7559580) (@lem7559579)). Qed.
Lemma lem7559582 : term827 = term818.
Proof. exact (MK_COMB (@lem7559581) (@lem7559576)). Qed.
Lemma lem7559584 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559585 : term818 = term824.
Proof. exact (@lem7559584 (NUMERAL 0) term470). Qed.
Lemma lem7559586 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559587 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559588 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559587 h1) (fun h1 : term824 = True => @lem7559586)). Qed.
Lemma lem7559589 : term824 = True.
Proof. exact (EQ_MP (@lem7559588) (@lem7559586)). Qed.
Lemma lem7559590 : term818 = True.
Proof. exact (TRANS (@lem7559585) (@lem7559589)). Qed.
Lemma lem7559591 : term827 = True.
Proof. exact (TRANS (@lem7559582) (@lem7559590)). Qed.
Lemma lem7559592 : term821 = True.
Proof. exact (TRANS (@lem7559568) (@lem7559591)). Qed.
Lemma lem7559593 : term818 = True.
Proof. exact (TRANS (@lem7559545) (@lem7559592)). Qed.
Lemma lem7559594 : term817 = True.
Proof. exact (TRANS (@lem7559536) (@lem7559593)). Qed.
Lemma lem7559595 : True = term817.
Proof. exact (SYM (@lem7559594)). Qed.
Lemma lem7559596 : term817.
Proof. exact (EQ_MP (@lem7559595) (@lem0)). Qed.
Lemma lem7559597 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term887 _97559 _97561.
Proof. exact (conj (@lem7559596) (@lem7559455 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559599 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7559600 (_97559 : int) (_97561 : int) : term888 _97559 _97561.
Proof. exact (@lem7559599 term469 (term569 _97559 _97561)). Qed.
Lemma lem7559601 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term889 _97559 _97561.
Proof. exact (@lem7559600 _97559 _97561 (@lem7559597 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559602 (_97559 : int) (_97561 : int) : (term890 _97559 _97561) = (term569 _97559 _97561).
Proof. exact (@lem1982733 (term569 _97559 _97561)). Qed.
Lemma lem7559603 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7559604 (_97559 : int) (_97561 : int) : (term891 _97559 _97561) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7559603) (@lem7559602 _97559 _97561)). Qed.
Lemma lem7559605 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7559606 (_97559 : int) (_97561 : int) : (term889 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7559604 _97559 _97561) (@lem7559605)). Qed.
Lemma lem7559607 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term573 _97559 _97561.
Proof. exact (EQ_MP (@lem7559606 _97559 _97561) (@lem7559601 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559608 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term892 _97559 _97561.
Proof. exact (conj (@lem7559607 _97560 _97559 _97561 h1) (@lem7559533 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559610 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7559611 (_97559 : int) (_97561 : int) : term893 _97559 _97561.
Proof. exact (@lem7559610 (term569 _97559 _97561) (term587 _97559 _97561)). Qed.
Lemma lem7559612 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term894 _97559 _97561.
Proof. exact (@lem7559611 _97559 _97561 (@lem7559608 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559613 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = (term896 _97559 _97561).
Proof. exact (@lem1982753 (term570 _97559) (real_of_int _97559) (term897 _97561) (term570 _97561)). Qed.
Lemma lem7559614 (_97559 : int) : (term848 _97559) = (term849 _97559).
Proof. exact (@lem1982713 term523 (real_of_int _97559)). Qed.
Lemma lem7559616 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559617 : term469 = term549.
Proof. exact (@lem7559616 term470). Qed.
Lemma lem7559619 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7559620 : term523 = term524.
Proof. exact (@lem7559619 term470). Qed.
Lemma lem7559621 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559622 : term850 = term851.
Proof. exact (MK_COMB (@lem7559621) (@lem7559620)). Qed.
Lemma lem7559623 : term852 = term853.
Proof. exact (MK_COMB (@lem7559622) (@lem7559617)). Qed.
Lemma lem7559624 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7559626 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559627 : term818 = term824.
Proof. exact (@lem7559626 (NUMERAL 0) term470). Qed.
Lemma lem7559628 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559629 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559630 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559629 h1) (fun h1 : term824 = True => @lem7559628)). Qed.
Lemma lem7559631 : term824 = True.
Proof. exact (EQ_MP (@lem7559630) (@lem7559628)). Qed.
Lemma lem7559632 : term818 = True.
Proof. exact (TRANS (@lem7559627) (@lem7559631)). Qed.
Lemma lem7559633 : True = term818.
Proof. exact (SYM (@lem7559632)). Qed.
Lemma lem7559634 : term818.
Proof. exact (EQ_MP (@lem7559633) (@lem0)). Qed.
Lemma lem7559635 : term855.
Proof. exact (@lem7559624 (@lem7559634)). Qed.
Lemma lem7559637 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559638 : term818 = term824.
Proof. exact (@lem7559637 (NUMERAL 0) term470). Qed.
Lemma lem7559639 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559640 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559641 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559640 h1) (fun h1 : term824 = True => @lem7559639)). Qed.
Lemma lem7559642 : term824 = True.
Proof. exact (EQ_MP (@lem7559641) (@lem7559639)). Qed.
Lemma lem7559643 : term818 = True.
Proof. exact (TRANS (@lem7559638) (@lem7559642)). Qed.
Lemma lem7559644 : True = term818.
Proof. exact (SYM (@lem7559643)). Qed.
Lemma lem7559645 : term818.
Proof. exact (EQ_MP (@lem7559644) (@lem0)). Qed.
Lemma lem7559646 : term856.
Proof. exact (@lem7559635 (@lem7559645)). Qed.
Lemma lem7559648 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559649 : term818 = term824.
Proof. exact (@lem7559648 (NUMERAL 0) term470). Qed.
Lemma lem7559650 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559651 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559652 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559651 h1) (fun h1 : term824 = True => @lem7559650)). Qed.
Lemma lem7559653 : term824 = True.
Proof. exact (EQ_MP (@lem7559652) (@lem7559650)). Qed.
Lemma lem7559654 : term818 = True.
Proof. exact (TRANS (@lem7559649) (@lem7559653)). Qed.
Lemma lem7559655 : True = term818.
Proof. exact (SYM (@lem7559654)). Qed.
Lemma lem7559656 : term818.
Proof. exact (EQ_MP (@lem7559655) (@lem0)). Qed.
Lemma lem7559657 : term857.
Proof. exact (@lem7559646 (@lem7559656)). Qed.
Lemma lem7559659 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559660 : term532 = term533.
Proof. exact (@lem7559659 term470 term470). Qed.
Lemma lem7559661 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559662 : term535 = term470.
Proof. exact (EQ_MP (@lem7559661) (@lem940073)). Qed.
Lemma lem7559663 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559664 : term533 = term469.
Proof. exact (MK_COMB (@lem7559663) (@lem7559662)). Qed.
Lemma lem7559665 : term532 = term469.
Proof. exact (TRANS (@lem7559660) (@lem7559664)). Qed.
Lemma lem7559667 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7559668 : term550 = term555.
Proof. exact (@lem7559667 term470 term470). Qed.
Lemma lem7559669 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559670 : term535 = term470.
Proof. exact (EQ_MP (@lem7559669) (@lem940073)). Qed.
Lemma lem7559671 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559672 : term533 = term469.
Proof. exact (MK_COMB (@lem7559671) (@lem7559670)). Qed.
Lemma lem7559673 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7559674 : term555 = term523.
Proof. exact (MK_COMB (@lem7559673) (@lem7559672)). Qed.
Lemma lem7559675 : term550 = term523.
Proof. exact (TRANS (@lem7559668) (@lem7559674)). Qed.
Lemma lem7559676 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559677 : term858 = term850.
Proof. exact (MK_COMB (@lem7559676) (@lem7559675)). Qed.
Lemma lem7559678 : term859 = term852.
Proof. exact (MK_COMB (@lem7559677) (@lem7559665)). Qed.
Lemma lem7559680 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7559681 : term852 = term35.
Proof. exact (@lem7559680 term470). Qed.
Lemma lem7559682 : term859 = term35.
Proof. exact (TRANS (@lem7559678) (@lem7559681)). Qed.
Lemma lem7559683 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7559684 : term861 = term218.
Proof. exact (MK_COMB (@lem7559683) (@lem7559682)). Qed.
Lemma lem7559685 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7559686 : term862 = term829.
Proof. exact (MK_COMB (@lem7559684) (@lem7559685)). Qed.
Lemma lem7559688 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559689 : term829 = term35.
Proof. exact (@lem7559688 term470). Qed.
Lemma lem7559690 : term862 = term35.
Proof. exact (TRANS (@lem7559686) (@lem7559689)). Qed.
Lemma lem7559692 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559693 : term532 = term533.
Proof. exact (@lem7559692 term470 term470). Qed.
Lemma lem7559694 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559695 : term535 = term470.
Proof. exact (EQ_MP (@lem7559694) (@lem940073)). Qed.
Lemma lem7559696 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559697 : term533 = term469.
Proof. exact (MK_COMB (@lem7559696) (@lem7559695)). Qed.
Lemma lem7559698 : term532 = term469.
Proof. exact (TRANS (@lem7559693) (@lem7559697)). Qed.
Lemma lem7559699 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7559700 : term863 = term829.
Proof. exact (MK_COMB (@lem7559699) (@lem7559698)). Qed.
Lemma lem7559702 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559703 : term829 = term35.
Proof. exact (@lem7559702 term470). Qed.
Lemma lem7559704 : term863 = term35.
Proof. exact (TRANS (@lem7559700) (@lem7559703)). Qed.
Lemma lem7559705 : term35 = term863.
Proof. exact (SYM (@lem7559704)). Qed.
Lemma lem7559706 : term862 = term863.
Proof. exact (TRANS (@lem7559690) (@lem7559705)). Qed.
Lemma lem7559707 : term853 = term520.
Proof. exact (@lem7559657 (@lem7559706)). Qed.
Lemma lem7559708 : term852 = term520.
Proof. exact (TRANS (@lem7559623) (@lem7559707)). Qed.
Lemma lem7559710 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7559711 : term520 = term35.
Proof. exact (@lem7559710 term35). Qed.
Lemma lem7559712 : term852 = term35.
Proof. exact (TRANS (@lem7559708) (@lem7559711)). Qed.
Lemma lem7559713 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7559714 : term864 = term218.
Proof. exact (MK_COMB (@lem7559713) (@lem7559712)). Qed.
Lemma lem7559715 (_97559 : int) : (real_of_int _97559) = (real_of_int _97559).
Proof. exact (eq_refl (real_of_int _97559)). Qed.
Lemma lem7559716 (_97559 : int) : (term849 _97559) = (term865 _97559).
Proof. exact (MK_COMB (@lem7559714) (@lem7559715 _97559)). Qed.
Lemma lem7559717 (_97559 : int) : (term848 _97559) = (term865 _97559).
Proof. exact (TRANS (@lem7559614 _97559) (@lem7559716 _97559)). Qed.
Lemma lem7559718 (_97559 : int) : (term865 _97559) = term35.
Proof. exact (@lem1982719 (real_of_int _97559)). Qed.
Lemma lem7559719 (_97559 : int) : (term848 _97559) = term35.
Proof. exact (TRANS (@lem7559717 _97559) (@lem7559718 _97559)). Qed.
Lemma lem7559720 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559721 (_97559 : int) : (term866 _97559) = term560.
Proof. exact (MK_COMB (@lem7559720) (@lem7559719 _97559)). Qed.
Lemma lem7559722 (_97561 : int) : (term898 _97561) = (term899 _97561).
Proof. exact (@lem1982759 (real_of_int _97561) (term570 _97561) term523). Qed.
Lemma lem7559723 (_97561 : int) : (term900 _97561) = (term849 _97561).
Proof. exact (@lem1982715 term523 (real_of_int _97561)). Qed.
Lemma lem7559725 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559726 : term469 = term549.
Proof. exact (@lem7559725 term470). Qed.
Lemma lem7559728 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7559729 : term523 = term524.
Proof. exact (@lem7559728 term470). Qed.
Lemma lem7559730 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559731 : term850 = term851.
Proof. exact (MK_COMB (@lem7559730) (@lem7559729)). Qed.
Lemma lem7559732 : term852 = term853.
Proof. exact (MK_COMB (@lem7559731) (@lem7559726)). Qed.
Lemma lem7559733 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7559735 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559736 : term818 = term824.
Proof. exact (@lem7559735 (NUMERAL 0) term470). Qed.
Lemma lem7559737 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559738 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559739 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559738 h1) (fun h1 : term824 = True => @lem7559737)). Qed.
Lemma lem7559740 : term824 = True.
Proof. exact (EQ_MP (@lem7559739) (@lem7559737)). Qed.
Lemma lem7559741 : term818 = True.
Proof. exact (TRANS (@lem7559736) (@lem7559740)). Qed.
Lemma lem7559742 : True = term818.
Proof. exact (SYM (@lem7559741)). Qed.
Lemma lem7559743 : term818.
Proof. exact (EQ_MP (@lem7559742) (@lem0)). Qed.
Lemma lem7559744 : term855.
Proof. exact (@lem7559733 (@lem7559743)). Qed.
Lemma lem7559746 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559747 : term818 = term824.
Proof. exact (@lem7559746 (NUMERAL 0) term470). Qed.
Lemma lem7559748 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559749 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559750 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559749 h1) (fun h1 : term824 = True => @lem7559748)). Qed.
Lemma lem7559751 : term824 = True.
Proof. exact (EQ_MP (@lem7559750) (@lem7559748)). Qed.
Lemma lem7559752 : term818 = True.
Proof. exact (TRANS (@lem7559747) (@lem7559751)). Qed.
Lemma lem7559753 : True = term818.
Proof. exact (SYM (@lem7559752)). Qed.
Lemma lem7559754 : term818.
Proof. exact (EQ_MP (@lem7559753) (@lem0)). Qed.
Lemma lem7559755 : term856.
Proof. exact (@lem7559744 (@lem7559754)). Qed.
Lemma lem7559757 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559758 : term818 = term824.
Proof. exact (@lem7559757 (NUMERAL 0) term470). Qed.
Lemma lem7559759 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559760 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559761 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559760 h1) (fun h1 : term824 = True => @lem7559759)). Qed.
Lemma lem7559762 : term824 = True.
Proof. exact (EQ_MP (@lem7559761) (@lem7559759)). Qed.
Lemma lem7559763 : term818 = True.
Proof. exact (TRANS (@lem7559758) (@lem7559762)). Qed.
Lemma lem7559764 : True = term818.
Proof. exact (SYM (@lem7559763)). Qed.
Lemma lem7559765 : term818.
Proof. exact (EQ_MP (@lem7559764) (@lem0)). Qed.
Lemma lem7559766 : term857.
Proof. exact (@lem7559755 (@lem7559765)). Qed.
Lemma lem7559768 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559769 : term532 = term533.
Proof. exact (@lem7559768 term470 term470). Qed.
Lemma lem7559770 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559771 : term535 = term470.
Proof. exact (EQ_MP (@lem7559770) (@lem940073)). Qed.
Lemma lem7559772 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559773 : term533 = term469.
Proof. exact (MK_COMB (@lem7559772) (@lem7559771)). Qed.
Lemma lem7559774 : term532 = term469.
Proof. exact (TRANS (@lem7559769) (@lem7559773)). Qed.
Lemma lem7559776 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7559777 : term550 = term555.
Proof. exact (@lem7559776 term470 term470). Qed.
Lemma lem7559778 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559779 : term535 = term470.
Proof. exact (EQ_MP (@lem7559778) (@lem940073)). Qed.
Lemma lem7559780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559781 : term533 = term469.
Proof. exact (MK_COMB (@lem7559780) (@lem7559779)). Qed.
Lemma lem7559782 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7559783 : term555 = term523.
Proof. exact (MK_COMB (@lem7559782) (@lem7559781)). Qed.
Lemma lem7559784 : term550 = term523.
Proof. exact (TRANS (@lem7559777) (@lem7559783)). Qed.
Lemma lem7559785 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559786 : term858 = term850.
Proof. exact (MK_COMB (@lem7559785) (@lem7559784)). Qed.
Lemma lem7559787 : term859 = term852.
Proof. exact (MK_COMB (@lem7559786) (@lem7559774)). Qed.
Lemma lem7559789 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7559790 : term852 = term35.
Proof. exact (@lem7559789 term470). Qed.
Lemma lem7559791 : term859 = term35.
Proof. exact (TRANS (@lem7559787) (@lem7559790)). Qed.
Lemma lem7559792 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7559793 : term861 = term218.
Proof. exact (MK_COMB (@lem7559792) (@lem7559791)). Qed.
Lemma lem7559794 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7559795 : term862 = term829.
Proof. exact (MK_COMB (@lem7559793) (@lem7559794)). Qed.
Lemma lem7559797 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559798 : term829 = term35.
Proof. exact (@lem7559797 term470). Qed.
Lemma lem7559799 : term862 = term35.
Proof. exact (TRANS (@lem7559795) (@lem7559798)). Qed.
Lemma lem7559801 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559802 : term532 = term533.
Proof. exact (@lem7559801 term470 term470). Qed.
Lemma lem7559803 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559804 : term535 = term470.
Proof. exact (EQ_MP (@lem7559803) (@lem940073)). Qed.
Lemma lem7559805 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559806 : term533 = term469.
Proof. exact (MK_COMB (@lem7559805) (@lem7559804)). Qed.
Lemma lem7559807 : term532 = term469.
Proof. exact (TRANS (@lem7559802) (@lem7559806)). Qed.
Lemma lem7559808 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7559809 : term863 = term829.
Proof. exact (MK_COMB (@lem7559808) (@lem7559807)). Qed.
Lemma lem7559811 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559812 : term829 = term35.
Proof. exact (@lem7559811 term470). Qed.
Lemma lem7559813 : term863 = term35.
Proof. exact (TRANS (@lem7559809) (@lem7559812)). Qed.
Lemma lem7559814 : term35 = term863.
Proof. exact (SYM (@lem7559813)). Qed.
Lemma lem7559815 : term862 = term863.
Proof. exact (TRANS (@lem7559799) (@lem7559814)). Qed.
Lemma lem7559816 : term853 = term520.
Proof. exact (@lem7559766 (@lem7559815)). Qed.
Lemma lem7559817 : term852 = term520.
Proof. exact (TRANS (@lem7559732) (@lem7559816)). Qed.
Lemma lem7559819 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7559820 : term520 = term35.
Proof. exact (@lem7559819 term35). Qed.
Lemma lem7559821 : term852 = term35.
Proof. exact (TRANS (@lem7559817) (@lem7559820)). Qed.
Lemma lem7559822 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7559823 : term864 = term218.
Proof. exact (MK_COMB (@lem7559822) (@lem7559821)). Qed.
Lemma lem7559824 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7559825 (_97561 : int) : (term849 _97561) = (term865 _97561).
Proof. exact (MK_COMB (@lem7559823) (@lem7559824 _97561)). Qed.
Lemma lem7559826 (_97561 : int) : (term900 _97561) = (term865 _97561).
Proof. exact (TRANS (@lem7559723 _97561) (@lem7559825 _97561)). Qed.
Lemma lem7559827 (_97561 : int) : (term865 _97561) = term35.
Proof. exact (@lem1982719 (real_of_int _97561)). Qed.
Lemma lem7559828 (_97561 : int) : (term900 _97561) = term35.
Proof. exact (TRANS (@lem7559826 _97561) (@lem7559827 _97561)). Qed.
Lemma lem7559829 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7559830 (_97561 : int) : (term901 _97561) = term560.
Proof. exact (MK_COMB (@lem7559829) (@lem7559828 _97561)). Qed.
Lemma lem7559831 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7559832 (_97561 : int) : (term899 _97561) = term867.
Proof. exact (MK_COMB (@lem7559830 _97561) (@lem7559831)). Qed.
Lemma lem7559833 (_97561 : int) : (term898 _97561) = term867.
Proof. exact (TRANS (@lem7559722 _97561) (@lem7559832 _97561)). Qed.
Lemma lem7559834 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7559835 (_97561 : int) : (term898 _97561) = term523.
Proof. exact (TRANS (@lem7559833 _97561) (@lem7559834)). Qed.
Lemma lem7559836 (_97559 : int) (_97561 : int) : (term896 _97559 _97561) = term867.
Proof. exact (MK_COMB (@lem7559721 _97559) (@lem7559835 _97561)). Qed.
Lemma lem7559837 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term867.
Proof. exact (TRANS (@lem7559613 _97559 _97561) (@lem7559836 _97559 _97561)). Qed.
Lemma lem7559838 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7559839 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term523.
Proof. exact (TRANS (@lem7559837 _97559 _97561) (@lem7559838)). Qed.
Lemma lem7559840 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7559841 (_97559 : int) (_97561 : int) : (term902 _97559 _97561) = term869.
Proof. exact (MK_COMB (@lem7559840) (@lem7559839 _97559 _97561)). Qed.
Lemma lem7559842 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7559843 (_97559 : int) (_97561 : int) : (term894 _97559 _97561) = term870.
Proof. exact (MK_COMB (@lem7559841 _97559 _97561) (@lem7559842)). Qed.
Lemma lem7559844 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : term870.
Proof. exact (EQ_MP (@lem7559843 _97559 _97561) (@lem7559612 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559846 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7559847 : term870 = term871.
Proof. exact (@lem7559846 term35 term523). Qed.
Lemma lem7559849 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7559850 : term523 = term524.
Proof. exact (@lem7559849 term470). Qed.
Lemma lem7559852 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559853 : term35 = term520.
Proof. exact (@lem7559852 (NUMERAL 0)). Qed.
Lemma lem7559854 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7559855 : term457 = term872.
Proof. exact (MK_COMB (@lem7559854) (@lem7559853)). Qed.
Lemma lem7559856 : term871 = term873.
Proof. exact (MK_COMB (@lem7559855) (@lem7559850)). Qed.
Lemma lem7559857 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7559859 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559860 : term818 = term824.
Proof. exact (@lem7559859 (NUMERAL 0) term470). Qed.
Lemma lem7559861 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559862 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559863 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559862 h1) (fun h1 : term824 = True => @lem7559861)). Qed.
Lemma lem7559864 : term824 = True.
Proof. exact (EQ_MP (@lem7559863) (@lem7559861)). Qed.
Lemma lem7559865 : term818 = True.
Proof. exact (TRANS (@lem7559860) (@lem7559864)). Qed.
Lemma lem7559866 : True = term818.
Proof. exact (SYM (@lem7559865)). Qed.
Lemma lem7559867 : term818.
Proof. exact (EQ_MP (@lem7559866) (@lem0)). Qed.
Lemma lem7559868 : term875.
Proof. exact (@lem7559857 (@lem7559867)). Qed.
Lemma lem7559870 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559871 : term818 = term824.
Proof. exact (@lem7559870 (NUMERAL 0) term470). Qed.
Lemma lem7559872 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559873 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559874 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559873 h1) (fun h1 : term824 = True => @lem7559872)). Qed.
Lemma lem7559875 : term824 = True.
Proof. exact (EQ_MP (@lem7559874) (@lem7559872)). Qed.
Lemma lem7559876 : term818 = True.
Proof. exact (TRANS (@lem7559871) (@lem7559875)). Qed.
Lemma lem7559877 : True = term818.
Proof. exact (SYM (@lem7559876)). Qed.
Lemma lem7559878 : term818.
Proof. exact (EQ_MP (@lem7559877) (@lem0)). Qed.
Lemma lem7559879 : term873 = term876.
Proof. exact (@lem7559868 (@lem7559878)). Qed.
Lemma lem7559881 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7559882 : term550 = term555.
Proof. exact (@lem7559881 term470 term470). Qed.
Lemma lem7559883 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559884 : term535 = term470.
Proof. exact (EQ_MP (@lem7559883) (@lem940073)). Qed.
Lemma lem7559885 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559886 : term533 = term469.
Proof. exact (MK_COMB (@lem7559885) (@lem7559884)). Qed.
Lemma lem7559887 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7559888 : term555 = term523.
Proof. exact (MK_COMB (@lem7559887) (@lem7559886)). Qed.
Lemma lem7559889 : term550 = term523.
Proof. exact (TRANS (@lem7559882) (@lem7559888)). Qed.
Lemma lem7559891 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559892 : term829 = term35.
Proof. exact (@lem7559891 term470). Qed.
Lemma lem7559893 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7559894 : term877 = term457.
Proof. exact (MK_COMB (@lem7559893) (@lem7559892)). Qed.
Lemma lem7559895 : term876 = term871.
Proof. exact (MK_COMB (@lem7559894) (@lem7559889)). Qed.
Lemma lem7559897 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7559898 : term871 = term880.
Proof. exact (@lem7559897 (NUMERAL 0) term470). Qed.
Lemma lem7559899 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559900 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7559901 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559900 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7559899)). Qed.
Lemma lem7559902 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7559901) (@lem7559899)). Qed.
Lemma lem7559903 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7559904 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7559905 : term881 = (and True).
Proof. exact (MK_COMB (@lem7559904) (@lem7559903)). Qed.
Lemma lem7559906 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7559905) (@lem7559902)). Qed.
Lemma lem7559908 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7559909 : term880 = False.
Proof. exact (TRANS (@lem7559906) (@lem7559908)). Qed.
Lemma lem7559910 : term871 = False.
Proof. exact (TRANS (@lem7559898) (@lem7559909)). Qed.
Lemma lem7559911 : term876 = False.
Proof. exact (TRANS (@lem7559895) (@lem7559910)). Qed.
Lemma lem7559912 : term873 = False.
Proof. exact (TRANS (@lem7559879) (@lem7559911)). Qed.
Lemma lem7559913 : term871 = False.
Proof. exact (TRANS (@lem7559856) (@lem7559912)). Qed.
Lemma lem7559914 : term870 = False.
Proof. exact (TRANS (@lem7559847) (@lem7559913)). Qed.
Lemma lem7559915 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term785 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7559914) (@lem7559844 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559916 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term793 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7559917 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term792 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559916 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559919 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term791 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7559917 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559921 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term789 _97559 _97561.
Proof. exact (proj2 (@lem7559919 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559923 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term787 _97559 _97561.
Proof. exact (proj2 (@lem7559921 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559925 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term743 _97559 _97561.
Proof. exact (proj2 (@lem7559923 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559926 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term573 _97559 _97561.
Proof. exact (proj1 (@lem7559923 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559927 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term590 _97559 _97561.
Proof. exact (proj2 (@lem7559925 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559932 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7559933 : term817 = term818.
Proof. exact (@lem7559932 term35 term469). Qed.
Lemma lem7559935 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559936 : term469 = term549.
Proof. exact (@lem7559935 term470). Qed.
Lemma lem7559938 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7559939 : term35 = term520.
Proof. exact (@lem7559938 (NUMERAL 0)). Qed.
Lemma lem7559940 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559941 : term819 = term820.
Proof. exact (MK_COMB (@lem7559940) (@lem7559939)). Qed.
Lemma lem7559942 : term818 = term821.
Proof. exact (MK_COMB (@lem7559941) (@lem7559936)). Qed.
Lemma lem7559943 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7559945 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559946 : term818 = term824.
Proof. exact (@lem7559945 (NUMERAL 0) term470). Qed.
Lemma lem7559947 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559948 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559949 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559948 h1) (fun h1 : term824 = True => @lem7559947)). Qed.
Lemma lem7559950 : term824 = True.
Proof. exact (EQ_MP (@lem7559949) (@lem7559947)). Qed.
Lemma lem7559951 : term818 = True.
Proof. exact (TRANS (@lem7559946) (@lem7559950)). Qed.
Lemma lem7559952 : True = term818.
Proof. exact (SYM (@lem7559951)). Qed.
Lemma lem7559953 : term818.
Proof. exact (EQ_MP (@lem7559952) (@lem0)). Qed.
Lemma lem7559954 : term826.
Proof. exact (@lem7559943 (@lem7559953)). Qed.
Lemma lem7559956 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559957 : term818 = term824.
Proof. exact (@lem7559956 (NUMERAL 0) term470). Qed.
Lemma lem7559958 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559959 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559960 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559959 h1) (fun h1 : term824 = True => @lem7559958)). Qed.
Lemma lem7559961 : term824 = True.
Proof. exact (EQ_MP (@lem7559960) (@lem7559958)). Qed.
Lemma lem7559962 : term818 = True.
Proof. exact (TRANS (@lem7559957) (@lem7559961)). Qed.
Lemma lem7559963 : True = term818.
Proof. exact (SYM (@lem7559962)). Qed.
Lemma lem7559964 : term818.
Proof. exact (EQ_MP (@lem7559963) (@lem0)). Qed.
Lemma lem7559965 : term821 = term827.
Proof. exact (@lem7559954 (@lem7559964)). Qed.
Lemma lem7559967 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7559968 : term532 = term533.
Proof. exact (@lem7559967 term470 term470). Qed.
Lemma lem7559969 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7559970 : term535 = term470.
Proof. exact (EQ_MP (@lem7559969) (@lem940073)). Qed.
Lemma lem7559971 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7559972 : term533 = term469.
Proof. exact (MK_COMB (@lem7559971) (@lem7559970)). Qed.
Lemma lem7559973 : term532 = term469.
Proof. exact (TRANS (@lem7559968) (@lem7559972)). Qed.
Lemma lem7559975 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7559976 : term829 = term35.
Proof. exact (@lem7559975 term470). Qed.
Lemma lem7559977 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7559978 : term830 = term819.
Proof. exact (MK_COMB (@lem7559977) (@lem7559976)). Qed.
Lemma lem7559979 : term827 = term818.
Proof. exact (MK_COMB (@lem7559978) (@lem7559973)). Qed.
Lemma lem7559981 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7559982 : term818 = term824.
Proof. exact (@lem7559981 (NUMERAL 0) term470). Qed.
Lemma lem7559983 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7559984 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7559985 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7559984 h1) (fun h1 : term824 = True => @lem7559983)). Qed.
Lemma lem7559986 : term824 = True.
Proof. exact (EQ_MP (@lem7559985) (@lem7559983)). Qed.
Lemma lem7559987 : term818 = True.
Proof. exact (TRANS (@lem7559982) (@lem7559986)). Qed.
Lemma lem7559988 : term827 = True.
Proof. exact (TRANS (@lem7559979) (@lem7559987)). Qed.
Lemma lem7559989 : term821 = True.
Proof. exact (TRANS (@lem7559965) (@lem7559988)). Qed.
Lemma lem7559990 : term818 = True.
Proof. exact (TRANS (@lem7559942) (@lem7559989)). Qed.
Lemma lem7559991 : term817 = True.
Proof. exact (TRANS (@lem7559933) (@lem7559990)). Qed.
Lemma lem7559992 : True = term817.
Proof. exact (SYM (@lem7559991)). Qed.
Lemma lem7559993 : term817.
Proof. exact (EQ_MP (@lem7559992) (@lem0)). Qed.
Lemma lem7559994 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term882 _97559 _97561.
Proof. exact (conj (@lem7559993) (@lem7559927 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559996 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7559997 (_97559 : int) (_97561 : int) : term883 _97559 _97561.
Proof. exact (@lem7559996 term469 (term587 _97559 _97561)). Qed.
Lemma lem7559998 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term884 _97559 _97561.
Proof. exact (@lem7559997 _97559 _97561 (@lem7559994 _97560 _97559 _97561 h1)). Qed.
Lemma lem7559999 (_97559 : int) (_97561 : int) : (term885 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982733 (term587 _97559 _97561)). Qed.
Lemma lem7560000 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560001 (_97559 : int) (_97561 : int) : (term886 _97559 _97561) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7560000) (@lem7559999 _97559 _97561)). Qed.
Lemma lem7560002 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560003 (_97559 : int) (_97561 : int) : (term884 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7560001 _97559 _97561) (@lem7560002)). Qed.
Lemma lem7560004 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term590 _97559 _97561.
Proof. exact (EQ_MP (@lem7560003 _97559 _97561) (@lem7559998 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560006 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7560007 : term817 = term818.
Proof. exact (@lem7560006 term35 term469). Qed.
Lemma lem7560009 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560010 : term469 = term549.
Proof. exact (@lem7560009 term470). Qed.
Lemma lem7560012 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560013 : term35 = term520.
Proof. exact (@lem7560012 (NUMERAL 0)). Qed.
Lemma lem7560014 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560015 : term819 = term820.
Proof. exact (MK_COMB (@lem7560014) (@lem7560013)). Qed.
Lemma lem7560016 : term818 = term821.
Proof. exact (MK_COMB (@lem7560015) (@lem7560010)). Qed.
Lemma lem7560017 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7560019 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560020 : term818 = term824.
Proof. exact (@lem7560019 (NUMERAL 0) term470). Qed.
Lemma lem7560021 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560022 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560023 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560022 h1) (fun h1 : term824 = True => @lem7560021)). Qed.
Lemma lem7560024 : term824 = True.
Proof. exact (EQ_MP (@lem7560023) (@lem7560021)). Qed.
Lemma lem7560025 : term818 = True.
Proof. exact (TRANS (@lem7560020) (@lem7560024)). Qed.
Lemma lem7560026 : True = term818.
Proof. exact (SYM (@lem7560025)). Qed.
Lemma lem7560027 : term818.
Proof. exact (EQ_MP (@lem7560026) (@lem0)). Qed.
Lemma lem7560028 : term826.
Proof. exact (@lem7560017 (@lem7560027)). Qed.
Lemma lem7560030 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560031 : term818 = term824.
Proof. exact (@lem7560030 (NUMERAL 0) term470). Qed.
Lemma lem7560032 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560033 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560034 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560033 h1) (fun h1 : term824 = True => @lem7560032)). Qed.
Lemma lem7560035 : term824 = True.
Proof. exact (EQ_MP (@lem7560034) (@lem7560032)). Qed.
Lemma lem7560036 : term818 = True.
Proof. exact (TRANS (@lem7560031) (@lem7560035)). Qed.
Lemma lem7560037 : True = term818.
Proof. exact (SYM (@lem7560036)). Qed.
Lemma lem7560038 : term818.
Proof. exact (EQ_MP (@lem7560037) (@lem0)). Qed.
Lemma lem7560039 : term821 = term827.
Proof. exact (@lem7560028 (@lem7560038)). Qed.
Lemma lem7560041 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560042 : term532 = term533.
Proof. exact (@lem7560041 term470 term470). Qed.
Lemma lem7560043 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560044 : term535 = term470.
Proof. exact (EQ_MP (@lem7560043) (@lem940073)). Qed.
Lemma lem7560045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560046 : term533 = term469.
Proof. exact (MK_COMB (@lem7560045) (@lem7560044)). Qed.
Lemma lem7560047 : term532 = term469.
Proof. exact (TRANS (@lem7560042) (@lem7560046)). Qed.
Lemma lem7560049 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560050 : term829 = term35.
Proof. exact (@lem7560049 term470). Qed.
Lemma lem7560051 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560052 : term830 = term819.
Proof. exact (MK_COMB (@lem7560051) (@lem7560050)). Qed.
Lemma lem7560053 : term827 = term818.
Proof. exact (MK_COMB (@lem7560052) (@lem7560047)). Qed.
Lemma lem7560055 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560056 : term818 = term824.
Proof. exact (@lem7560055 (NUMERAL 0) term470). Qed.
Lemma lem7560057 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560058 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560059 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560058 h1) (fun h1 : term824 = True => @lem7560057)). Qed.
Lemma lem7560060 : term824 = True.
Proof. exact (EQ_MP (@lem7560059) (@lem7560057)). Qed.
Lemma lem7560061 : term818 = True.
Proof. exact (TRANS (@lem7560056) (@lem7560060)). Qed.
Lemma lem7560062 : term827 = True.
Proof. exact (TRANS (@lem7560053) (@lem7560061)). Qed.
Lemma lem7560063 : term821 = True.
Proof. exact (TRANS (@lem7560039) (@lem7560062)). Qed.
Lemma lem7560064 : term818 = True.
Proof. exact (TRANS (@lem7560016) (@lem7560063)). Qed.
Lemma lem7560065 : term817 = True.
Proof. exact (TRANS (@lem7560007) (@lem7560064)). Qed.
Lemma lem7560066 : True = term817.
Proof. exact (SYM (@lem7560065)). Qed.
Lemma lem7560067 : term817.
Proof. exact (EQ_MP (@lem7560066) (@lem0)). Qed.
Lemma lem7560068 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term887 _97559 _97561.
Proof. exact (conj (@lem7560067) (@lem7559926 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560070 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7560071 (_97559 : int) (_97561 : int) : term888 _97559 _97561.
Proof. exact (@lem7560070 term469 (term569 _97559 _97561)). Qed.
Lemma lem7560072 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term889 _97559 _97561.
Proof. exact (@lem7560071 _97559 _97561 (@lem7560068 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560073 (_97559 : int) (_97561 : int) : (term890 _97559 _97561) = (term569 _97559 _97561).
Proof. exact (@lem1982733 (term569 _97559 _97561)). Qed.
Lemma lem7560074 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560075 (_97559 : int) (_97561 : int) : (term891 _97559 _97561) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7560074) (@lem7560073 _97559 _97561)). Qed.
Lemma lem7560076 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560077 (_97559 : int) (_97561 : int) : (term889 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7560075 _97559 _97561) (@lem7560076)). Qed.
Lemma lem7560078 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term573 _97559 _97561.
Proof. exact (EQ_MP (@lem7560077 _97559 _97561) (@lem7560072 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560079 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term892 _97559 _97561.
Proof. exact (conj (@lem7560078 _97560 _97559 _97561 h1) (@lem7560004 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560081 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7560082 (_97559 : int) (_97561 : int) : term893 _97559 _97561.
Proof. exact (@lem7560081 (term569 _97559 _97561) (term587 _97559 _97561)). Qed.
Lemma lem7560083 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term894 _97559 _97561.
Proof. exact (@lem7560082 _97559 _97561 (@lem7560079 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560084 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = (term896 _97559 _97561).
Proof. exact (@lem1982753 (term570 _97559) (real_of_int _97559) (term897 _97561) (term570 _97561)). Qed.
Lemma lem7560085 (_97559 : int) : (term848 _97559) = (term849 _97559).
Proof. exact (@lem1982713 term523 (real_of_int _97559)). Qed.
Lemma lem7560087 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560088 : term469 = term549.
Proof. exact (@lem7560087 term470). Qed.
Lemma lem7560090 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7560091 : term523 = term524.
Proof. exact (@lem7560090 term470). Qed.
Lemma lem7560092 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560093 : term850 = term851.
Proof. exact (MK_COMB (@lem7560092) (@lem7560091)). Qed.
Lemma lem7560094 : term852 = term853.
Proof. exact (MK_COMB (@lem7560093) (@lem7560088)). Qed.
Lemma lem7560095 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7560097 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560098 : term818 = term824.
Proof. exact (@lem7560097 (NUMERAL 0) term470). Qed.
Lemma lem7560099 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560100 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560101 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560100 h1) (fun h1 : term824 = True => @lem7560099)). Qed.
Lemma lem7560102 : term824 = True.
Proof. exact (EQ_MP (@lem7560101) (@lem7560099)). Qed.
Lemma lem7560103 : term818 = True.
Proof. exact (TRANS (@lem7560098) (@lem7560102)). Qed.
Lemma lem7560104 : True = term818.
Proof. exact (SYM (@lem7560103)). Qed.
Lemma lem7560105 : term818.
Proof. exact (EQ_MP (@lem7560104) (@lem0)). Qed.
Lemma lem7560106 : term855.
Proof. exact (@lem7560095 (@lem7560105)). Qed.
Lemma lem7560108 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560109 : term818 = term824.
Proof. exact (@lem7560108 (NUMERAL 0) term470). Qed.
Lemma lem7560110 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560111 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560112 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560111 h1) (fun h1 : term824 = True => @lem7560110)). Qed.
Lemma lem7560113 : term824 = True.
Proof. exact (EQ_MP (@lem7560112) (@lem7560110)). Qed.
Lemma lem7560114 : term818 = True.
Proof. exact (TRANS (@lem7560109) (@lem7560113)). Qed.
Lemma lem7560115 : True = term818.
Proof. exact (SYM (@lem7560114)). Qed.
Lemma lem7560116 : term818.
Proof. exact (EQ_MP (@lem7560115) (@lem0)). Qed.
Lemma lem7560117 : term856.
Proof. exact (@lem7560106 (@lem7560116)). Qed.
Lemma lem7560119 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560120 : term818 = term824.
Proof. exact (@lem7560119 (NUMERAL 0) term470). Qed.
Lemma lem7560121 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560122 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560123 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560122 h1) (fun h1 : term824 = True => @lem7560121)). Qed.
Lemma lem7560124 : term824 = True.
Proof. exact (EQ_MP (@lem7560123) (@lem7560121)). Qed.
Lemma lem7560125 : term818 = True.
Proof. exact (TRANS (@lem7560120) (@lem7560124)). Qed.
Lemma lem7560126 : True = term818.
Proof. exact (SYM (@lem7560125)). Qed.
Lemma lem7560127 : term818.
Proof. exact (EQ_MP (@lem7560126) (@lem0)). Qed.
Lemma lem7560128 : term857.
Proof. exact (@lem7560117 (@lem7560127)). Qed.
Lemma lem7560130 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560131 : term532 = term533.
Proof. exact (@lem7560130 term470 term470). Qed.
Lemma lem7560132 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560133 : term535 = term470.
Proof. exact (EQ_MP (@lem7560132) (@lem940073)). Qed.
Lemma lem7560134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560135 : term533 = term469.
Proof. exact (MK_COMB (@lem7560134) (@lem7560133)). Qed.
Lemma lem7560136 : term532 = term469.
Proof. exact (TRANS (@lem7560131) (@lem7560135)). Qed.
Lemma lem7560138 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7560139 : term550 = term555.
Proof. exact (@lem7560138 term470 term470). Qed.
Lemma lem7560140 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560141 : term535 = term470.
Proof. exact (EQ_MP (@lem7560140) (@lem940073)). Qed.
Lemma lem7560142 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560143 : term533 = term469.
Proof. exact (MK_COMB (@lem7560142) (@lem7560141)). Qed.
Lemma lem7560144 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7560145 : term555 = term523.
Proof. exact (MK_COMB (@lem7560144) (@lem7560143)). Qed.
Lemma lem7560146 : term550 = term523.
Proof. exact (TRANS (@lem7560139) (@lem7560145)). Qed.
Lemma lem7560147 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560148 : term858 = term850.
Proof. exact (MK_COMB (@lem7560147) (@lem7560146)). Qed.
Lemma lem7560149 : term859 = term852.
Proof. exact (MK_COMB (@lem7560148) (@lem7560136)). Qed.
Lemma lem7560151 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7560152 : term852 = term35.
Proof. exact (@lem7560151 term470). Qed.
Lemma lem7560153 : term859 = term35.
Proof. exact (TRANS (@lem7560149) (@lem7560152)). Qed.
Lemma lem7560154 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7560155 : term861 = term218.
Proof. exact (MK_COMB (@lem7560154) (@lem7560153)). Qed.
Lemma lem7560156 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7560157 : term862 = term829.
Proof. exact (MK_COMB (@lem7560155) (@lem7560156)). Qed.
Lemma lem7560159 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560160 : term829 = term35.
Proof. exact (@lem7560159 term470). Qed.
Lemma lem7560161 : term862 = term35.
Proof. exact (TRANS (@lem7560157) (@lem7560160)). Qed.
Lemma lem7560163 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560164 : term532 = term533.
Proof. exact (@lem7560163 term470 term470). Qed.
Lemma lem7560165 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560166 : term535 = term470.
Proof. exact (EQ_MP (@lem7560165) (@lem940073)). Qed.
Lemma lem7560167 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560168 : term533 = term469.
Proof. exact (MK_COMB (@lem7560167) (@lem7560166)). Qed.
Lemma lem7560169 : term532 = term469.
Proof. exact (TRANS (@lem7560164) (@lem7560168)). Qed.
Lemma lem7560170 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7560171 : term863 = term829.
Proof. exact (MK_COMB (@lem7560170) (@lem7560169)). Qed.
Lemma lem7560173 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560174 : term829 = term35.
Proof. exact (@lem7560173 term470). Qed.
Lemma lem7560175 : term863 = term35.
Proof. exact (TRANS (@lem7560171) (@lem7560174)). Qed.
Lemma lem7560176 : term35 = term863.
Proof. exact (SYM (@lem7560175)). Qed.
Lemma lem7560177 : term862 = term863.
Proof. exact (TRANS (@lem7560161) (@lem7560176)). Qed.
Lemma lem7560178 : term853 = term520.
Proof. exact (@lem7560128 (@lem7560177)). Qed.
Lemma lem7560179 : term852 = term520.
Proof. exact (TRANS (@lem7560094) (@lem7560178)). Qed.
Lemma lem7560181 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7560182 : term520 = term35.
Proof. exact (@lem7560181 term35). Qed.
Lemma lem7560183 : term852 = term35.
Proof. exact (TRANS (@lem7560179) (@lem7560182)). Qed.
Lemma lem7560184 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7560185 : term864 = term218.
Proof. exact (MK_COMB (@lem7560184) (@lem7560183)). Qed.
Lemma lem7560186 (_97559 : int) : (real_of_int _97559) = (real_of_int _97559).
Proof. exact (eq_refl (real_of_int _97559)). Qed.
Lemma lem7560187 (_97559 : int) : (term849 _97559) = (term865 _97559).
Proof. exact (MK_COMB (@lem7560185) (@lem7560186 _97559)). Qed.
Lemma lem7560188 (_97559 : int) : (term848 _97559) = (term865 _97559).
Proof. exact (TRANS (@lem7560085 _97559) (@lem7560187 _97559)). Qed.
Lemma lem7560189 (_97559 : int) : (term865 _97559) = term35.
Proof. exact (@lem1982719 (real_of_int _97559)). Qed.
Lemma lem7560190 (_97559 : int) : (term848 _97559) = term35.
Proof. exact (TRANS (@lem7560188 _97559) (@lem7560189 _97559)). Qed.
Lemma lem7560191 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560192 (_97559 : int) : (term866 _97559) = term560.
Proof. exact (MK_COMB (@lem7560191) (@lem7560190 _97559)). Qed.
Lemma lem7560193 (_97561 : int) : (term898 _97561) = (term899 _97561).
Proof. exact (@lem1982759 (real_of_int _97561) (term570 _97561) term523). Qed.
Lemma lem7560194 (_97561 : int) : (term900 _97561) = (term849 _97561).
Proof. exact (@lem1982715 term523 (real_of_int _97561)). Qed.
Lemma lem7560196 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560197 : term469 = term549.
Proof. exact (@lem7560196 term470). Qed.
Lemma lem7560199 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7560200 : term523 = term524.
Proof. exact (@lem7560199 term470). Qed.
Lemma lem7560201 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560202 : term850 = term851.
Proof. exact (MK_COMB (@lem7560201) (@lem7560200)). Qed.
Lemma lem7560203 : term852 = term853.
Proof. exact (MK_COMB (@lem7560202) (@lem7560197)). Qed.
Lemma lem7560204 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7560206 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560207 : term818 = term824.
Proof. exact (@lem7560206 (NUMERAL 0) term470). Qed.
Lemma lem7560208 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560209 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560210 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560209 h1) (fun h1 : term824 = True => @lem7560208)). Qed.
Lemma lem7560211 : term824 = True.
Proof. exact (EQ_MP (@lem7560210) (@lem7560208)). Qed.
Lemma lem7560212 : term818 = True.
Proof. exact (TRANS (@lem7560207) (@lem7560211)). Qed.
Lemma lem7560213 : True = term818.
Proof. exact (SYM (@lem7560212)). Qed.
Lemma lem7560214 : term818.
Proof. exact (EQ_MP (@lem7560213) (@lem0)). Qed.
Lemma lem7560215 : term855.
Proof. exact (@lem7560204 (@lem7560214)). Qed.
Lemma lem7560217 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560218 : term818 = term824.
Proof. exact (@lem7560217 (NUMERAL 0) term470). Qed.
Lemma lem7560219 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560220 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560221 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560220 h1) (fun h1 : term824 = True => @lem7560219)). Qed.
Lemma lem7560222 : term824 = True.
Proof. exact (EQ_MP (@lem7560221) (@lem7560219)). Qed.
Lemma lem7560223 : term818 = True.
Proof. exact (TRANS (@lem7560218) (@lem7560222)). Qed.
Lemma lem7560224 : True = term818.
Proof. exact (SYM (@lem7560223)). Qed.
Lemma lem7560225 : term818.
Proof. exact (EQ_MP (@lem7560224) (@lem0)). Qed.
Lemma lem7560226 : term856.
Proof. exact (@lem7560215 (@lem7560225)). Qed.
Lemma lem7560228 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560229 : term818 = term824.
Proof. exact (@lem7560228 (NUMERAL 0) term470). Qed.
Lemma lem7560230 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560231 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560232 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560231 h1) (fun h1 : term824 = True => @lem7560230)). Qed.
Lemma lem7560233 : term824 = True.
Proof. exact (EQ_MP (@lem7560232) (@lem7560230)). Qed.
Lemma lem7560234 : term818 = True.
Proof. exact (TRANS (@lem7560229) (@lem7560233)). Qed.
Lemma lem7560235 : True = term818.
Proof. exact (SYM (@lem7560234)). Qed.
Lemma lem7560236 : term818.
Proof. exact (EQ_MP (@lem7560235) (@lem0)). Qed.
Lemma lem7560237 : term857.
Proof. exact (@lem7560226 (@lem7560236)). Qed.
Lemma lem7560239 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560240 : term532 = term533.
Proof. exact (@lem7560239 term470 term470). Qed.
Lemma lem7560241 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560242 : term535 = term470.
Proof. exact (EQ_MP (@lem7560241) (@lem940073)). Qed.
Lemma lem7560243 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560244 : term533 = term469.
Proof. exact (MK_COMB (@lem7560243) (@lem7560242)). Qed.
Lemma lem7560245 : term532 = term469.
Proof. exact (TRANS (@lem7560240) (@lem7560244)). Qed.
Lemma lem7560247 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7560248 : term550 = term555.
Proof. exact (@lem7560247 term470 term470). Qed.
Lemma lem7560249 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560250 : term535 = term470.
Proof. exact (EQ_MP (@lem7560249) (@lem940073)). Qed.
Lemma lem7560251 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560252 : term533 = term469.
Proof. exact (MK_COMB (@lem7560251) (@lem7560250)). Qed.
Lemma lem7560253 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7560254 : term555 = term523.
Proof. exact (MK_COMB (@lem7560253) (@lem7560252)). Qed.
Lemma lem7560255 : term550 = term523.
Proof. exact (TRANS (@lem7560248) (@lem7560254)). Qed.
Lemma lem7560256 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560257 : term858 = term850.
Proof. exact (MK_COMB (@lem7560256) (@lem7560255)). Qed.
Lemma lem7560258 : term859 = term852.
Proof. exact (MK_COMB (@lem7560257) (@lem7560245)). Qed.
Lemma lem7560260 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7560261 : term852 = term35.
Proof. exact (@lem7560260 term470). Qed.
Lemma lem7560262 : term859 = term35.
Proof. exact (TRANS (@lem7560258) (@lem7560261)). Qed.
Lemma lem7560263 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7560264 : term861 = term218.
Proof. exact (MK_COMB (@lem7560263) (@lem7560262)). Qed.
Lemma lem7560265 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7560266 : term862 = term829.
Proof. exact (MK_COMB (@lem7560264) (@lem7560265)). Qed.
Lemma lem7560268 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560269 : term829 = term35.
Proof. exact (@lem7560268 term470). Qed.
Lemma lem7560270 : term862 = term35.
Proof. exact (TRANS (@lem7560266) (@lem7560269)). Qed.
Lemma lem7560272 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560273 : term532 = term533.
Proof. exact (@lem7560272 term470 term470). Qed.
Lemma lem7560274 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560275 : term535 = term470.
Proof. exact (EQ_MP (@lem7560274) (@lem940073)). Qed.
Lemma lem7560276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560277 : term533 = term469.
Proof. exact (MK_COMB (@lem7560276) (@lem7560275)). Qed.
Lemma lem7560278 : term532 = term469.
Proof. exact (TRANS (@lem7560273) (@lem7560277)). Qed.
Lemma lem7560279 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7560280 : term863 = term829.
Proof. exact (MK_COMB (@lem7560279) (@lem7560278)). Qed.
Lemma lem7560282 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560283 : term829 = term35.
Proof. exact (@lem7560282 term470). Qed.
Lemma lem7560284 : term863 = term35.
Proof. exact (TRANS (@lem7560280) (@lem7560283)). Qed.
Lemma lem7560285 : term35 = term863.
Proof. exact (SYM (@lem7560284)). Qed.
Lemma lem7560286 : term862 = term863.
Proof. exact (TRANS (@lem7560270) (@lem7560285)). Qed.
Lemma lem7560287 : term853 = term520.
Proof. exact (@lem7560237 (@lem7560286)). Qed.
Lemma lem7560288 : term852 = term520.
Proof. exact (TRANS (@lem7560203) (@lem7560287)). Qed.
Lemma lem7560290 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7560291 : term520 = term35.
Proof. exact (@lem7560290 term35). Qed.
Lemma lem7560292 : term852 = term35.
Proof. exact (TRANS (@lem7560288) (@lem7560291)). Qed.
Lemma lem7560293 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7560294 : term864 = term218.
Proof. exact (MK_COMB (@lem7560293) (@lem7560292)). Qed.
Lemma lem7560295 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7560296 (_97561 : int) : (term849 _97561) = (term865 _97561).
Proof. exact (MK_COMB (@lem7560294) (@lem7560295 _97561)). Qed.
Lemma lem7560297 (_97561 : int) : (term900 _97561) = (term865 _97561).
Proof. exact (TRANS (@lem7560194 _97561) (@lem7560296 _97561)). Qed.
Lemma lem7560298 (_97561 : int) : (term865 _97561) = term35.
Proof. exact (@lem1982719 (real_of_int _97561)). Qed.
Lemma lem7560299 (_97561 : int) : (term900 _97561) = term35.
Proof. exact (TRANS (@lem7560297 _97561) (@lem7560298 _97561)). Qed.
Lemma lem7560300 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560301 (_97561 : int) : (term901 _97561) = term560.
Proof. exact (MK_COMB (@lem7560300) (@lem7560299 _97561)). Qed.
Lemma lem7560302 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7560303 (_97561 : int) : (term899 _97561) = term867.
Proof. exact (MK_COMB (@lem7560301 _97561) (@lem7560302)). Qed.
Lemma lem7560304 (_97561 : int) : (term898 _97561) = term867.
Proof. exact (TRANS (@lem7560193 _97561) (@lem7560303 _97561)). Qed.
Lemma lem7560305 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7560306 (_97561 : int) : (term898 _97561) = term523.
Proof. exact (TRANS (@lem7560304 _97561) (@lem7560305)). Qed.
Lemma lem7560307 (_97559 : int) (_97561 : int) : (term896 _97559 _97561) = term867.
Proof. exact (MK_COMB (@lem7560192 _97559) (@lem7560306 _97561)). Qed.
Lemma lem7560308 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term867.
Proof. exact (TRANS (@lem7560084 _97559 _97561) (@lem7560307 _97559 _97561)). Qed.
Lemma lem7560309 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7560310 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term523.
Proof. exact (TRANS (@lem7560308 _97559 _97561) (@lem7560309)). Qed.
Lemma lem7560311 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560312 (_97559 : int) (_97561 : int) : (term902 _97559 _97561) = term869.
Proof. exact (MK_COMB (@lem7560311) (@lem7560310 _97559 _97561)). Qed.
Lemma lem7560313 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560314 (_97559 : int) (_97561 : int) : (term894 _97559 _97561) = term870.
Proof. exact (MK_COMB (@lem7560312 _97559 _97561) (@lem7560313)). Qed.
Lemma lem7560315 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : term870.
Proof. exact (EQ_MP (@lem7560314 _97559 _97561) (@lem7560083 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560317 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7560318 : term870 = term871.
Proof. exact (@lem7560317 term35 term523). Qed.
Lemma lem7560320 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7560321 : term523 = term524.
Proof. exact (@lem7560320 term470). Qed.
Lemma lem7560323 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560324 : term35 = term520.
Proof. exact (@lem7560323 (NUMERAL 0)). Qed.
Lemma lem7560325 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7560326 : term457 = term872.
Proof. exact (MK_COMB (@lem7560325) (@lem7560324)). Qed.
Lemma lem7560327 : term871 = term873.
Proof. exact (MK_COMB (@lem7560326) (@lem7560321)). Qed.
Lemma lem7560328 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7560330 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560331 : term818 = term824.
Proof. exact (@lem7560330 (NUMERAL 0) term470). Qed.
Lemma lem7560332 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560333 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560334 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560333 h1) (fun h1 : term824 = True => @lem7560332)). Qed.
Lemma lem7560335 : term824 = True.
Proof. exact (EQ_MP (@lem7560334) (@lem7560332)). Qed.
Lemma lem7560336 : term818 = True.
Proof. exact (TRANS (@lem7560331) (@lem7560335)). Qed.
Lemma lem7560337 : True = term818.
Proof. exact (SYM (@lem7560336)). Qed.
Lemma lem7560338 : term818.
Proof. exact (EQ_MP (@lem7560337) (@lem0)). Qed.
Lemma lem7560339 : term875.
Proof. exact (@lem7560328 (@lem7560338)). Qed.
Lemma lem7560341 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560342 : term818 = term824.
Proof. exact (@lem7560341 (NUMERAL 0) term470). Qed.
Lemma lem7560343 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560344 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560345 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560344 h1) (fun h1 : term824 = True => @lem7560343)). Qed.
Lemma lem7560346 : term824 = True.
Proof. exact (EQ_MP (@lem7560345) (@lem7560343)). Qed.
Lemma lem7560347 : term818 = True.
Proof. exact (TRANS (@lem7560342) (@lem7560346)). Qed.
Lemma lem7560348 : True = term818.
Proof. exact (SYM (@lem7560347)). Qed.
Lemma lem7560349 : term818.
Proof. exact (EQ_MP (@lem7560348) (@lem0)). Qed.
Lemma lem7560350 : term873 = term876.
Proof. exact (@lem7560339 (@lem7560349)). Qed.
Lemma lem7560352 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7560353 : term550 = term555.
Proof. exact (@lem7560352 term470 term470). Qed.
Lemma lem7560354 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560355 : term535 = term470.
Proof. exact (EQ_MP (@lem7560354) (@lem940073)). Qed.
Lemma lem7560356 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560357 : term533 = term469.
Proof. exact (MK_COMB (@lem7560356) (@lem7560355)). Qed.
Lemma lem7560358 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7560359 : term555 = term523.
Proof. exact (MK_COMB (@lem7560358) (@lem7560357)). Qed.
Lemma lem7560360 : term550 = term523.
Proof. exact (TRANS (@lem7560353) (@lem7560359)). Qed.
Lemma lem7560362 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560363 : term829 = term35.
Proof. exact (@lem7560362 term470). Qed.
Lemma lem7560364 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7560365 : term877 = term457.
Proof. exact (MK_COMB (@lem7560364) (@lem7560363)). Qed.
Lemma lem7560366 : term876 = term871.
Proof. exact (MK_COMB (@lem7560365) (@lem7560360)). Qed.
Lemma lem7560368 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7560369 : term871 = term880.
Proof. exact (@lem7560368 (NUMERAL 0) term470). Qed.
Lemma lem7560370 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560371 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7560372 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560371 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7560370)). Qed.
Lemma lem7560373 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7560372) (@lem7560370)). Qed.
Lemma lem7560374 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7560375 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7560376 : term881 = (and True).
Proof. exact (MK_COMB (@lem7560375) (@lem7560374)). Qed.
Lemma lem7560377 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7560376) (@lem7560373)). Qed.
Lemma lem7560379 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7560380 : term880 = False.
Proof. exact (TRANS (@lem7560377) (@lem7560379)). Qed.
Lemma lem7560381 : term871 = False.
Proof. exact (TRANS (@lem7560369) (@lem7560380)). Qed.
Lemma lem7560382 : term876 = False.
Proof. exact (TRANS (@lem7560366) (@lem7560381)). Qed.
Lemma lem7560383 : term873 = False.
Proof. exact (TRANS (@lem7560350) (@lem7560382)). Qed.
Lemma lem7560384 : term871 = False.
Proof. exact (TRANS (@lem7560327) (@lem7560383)). Qed.
Lemma lem7560385 : term870 = False.
Proof. exact (TRANS (@lem7560318) (@lem7560384)). Qed.
Lemma lem7560386 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term793 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7560385) (@lem7560315 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560387 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term795 _97560 _97559 _97561) : False.
Proof. exact (or_elim (@lem7559444 _97560 _97559 _97561 h1) (fun h0 : term785 _97560 _97559 _97561 => @lem7559915 _97560 _97559 _97561 h0) (fun h0 : term793 _97560 _97559 _97561 => @lem7560386 _97560 _97559 _97561 h0)). Qed.
Lemma lem7560388 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term798 _97560 _97559 _97561) : False.
Proof. exact (or_elim (@lem7558725 _97560 _97559 _97561 h1) (fun h0 : term754 _97560 _97559 _97561 => @lem7559443 _97560 _97559 _97561 h0) (fun h0 : term795 _97560 _97559 _97561 => @lem7560387 _97560 _97559 _97561 h0)). Qed.
Lemma lem7560389 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term814 _97560 _97559 _97561) : term814 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7560390 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term812 _97559 _97560 _97561) : term812 _97559 _97560 _97561.
Proof. exact (h1). Qed.
Lemma lem7560391 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term903 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7560392 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term672 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7560391 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560394 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term653 _97559 _97561.
Proof. exact (proj2 (@lem7560392 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560396 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term634 _97559 _97561.
Proof. exact (proj2 (@lem7560394 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560398 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term564 _97561.
Proof. exact (proj2 (@lem7560396 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560399 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term595 _97559 _97561.
Proof. exact (proj1 (@lem7560396 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560401 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term543 _97561.
Proof. exact (proj1 (@lem7560399 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560403 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7560404 : term817 = term818.
Proof. exact (@lem7560403 term35 term469). Qed.
Lemma lem7560406 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560407 : term469 = term549.
Proof. exact (@lem7560406 term470). Qed.
Lemma lem7560409 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560410 : term35 = term520.
Proof. exact (@lem7560409 (NUMERAL 0)). Qed.
Lemma lem7560411 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560412 : term819 = term820.
Proof. exact (MK_COMB (@lem7560411) (@lem7560410)). Qed.
Lemma lem7560413 : term818 = term821.
Proof. exact (MK_COMB (@lem7560412) (@lem7560407)). Qed.
Lemma lem7560414 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7560416 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560417 : term818 = term824.
Proof. exact (@lem7560416 (NUMERAL 0) term470). Qed.
Lemma lem7560418 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560419 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560420 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560419 h1) (fun h1 : term824 = True => @lem7560418)). Qed.
Lemma lem7560421 : term824 = True.
Proof. exact (EQ_MP (@lem7560420) (@lem7560418)). Qed.
Lemma lem7560422 : term818 = True.
Proof. exact (TRANS (@lem7560417) (@lem7560421)). Qed.
Lemma lem7560423 : True = term818.
Proof. exact (SYM (@lem7560422)). Qed.
Lemma lem7560424 : term818.
Proof. exact (EQ_MP (@lem7560423) (@lem0)). Qed.
Lemma lem7560425 : term826.
Proof. exact (@lem7560414 (@lem7560424)). Qed.
Lemma lem7560427 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560428 : term818 = term824.
Proof. exact (@lem7560427 (NUMERAL 0) term470). Qed.
Lemma lem7560429 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560430 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560431 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560430 h1) (fun h1 : term824 = True => @lem7560429)). Qed.
Lemma lem7560432 : term824 = True.
Proof. exact (EQ_MP (@lem7560431) (@lem7560429)). Qed.
Lemma lem7560433 : term818 = True.
Proof. exact (TRANS (@lem7560428) (@lem7560432)). Qed.
Lemma lem7560434 : True = term818.
Proof. exact (SYM (@lem7560433)). Qed.
Lemma lem7560435 : term818.
Proof. exact (EQ_MP (@lem7560434) (@lem0)). Qed.
Lemma lem7560436 : term821 = term827.
Proof. exact (@lem7560425 (@lem7560435)). Qed.
Lemma lem7560438 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560439 : term532 = term533.
Proof. exact (@lem7560438 term470 term470). Qed.
Lemma lem7560440 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560441 : term535 = term470.
Proof. exact (EQ_MP (@lem7560440) (@lem940073)). Qed.
Lemma lem7560442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560443 : term533 = term469.
Proof. exact (MK_COMB (@lem7560442) (@lem7560441)). Qed.
Lemma lem7560444 : term532 = term469.
Proof. exact (TRANS (@lem7560439) (@lem7560443)). Qed.
Lemma lem7560446 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560447 : term829 = term35.
Proof. exact (@lem7560446 term470). Qed.
Lemma lem7560448 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560449 : term830 = term819.
Proof. exact (MK_COMB (@lem7560448) (@lem7560447)). Qed.
Lemma lem7560450 : term827 = term818.
Proof. exact (MK_COMB (@lem7560449) (@lem7560444)). Qed.
Lemma lem7560452 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560453 : term818 = term824.
Proof. exact (@lem7560452 (NUMERAL 0) term470). Qed.
Lemma lem7560454 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560455 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560456 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560455 h1) (fun h1 : term824 = True => @lem7560454)). Qed.
Lemma lem7560457 : term824 = True.
Proof. exact (EQ_MP (@lem7560456) (@lem7560454)). Qed.
Lemma lem7560458 : term818 = True.
Proof. exact (TRANS (@lem7560453) (@lem7560457)). Qed.
Lemma lem7560459 : term827 = True.
Proof. exact (TRANS (@lem7560450) (@lem7560458)). Qed.
Lemma lem7560460 : term821 = True.
Proof. exact (TRANS (@lem7560436) (@lem7560459)). Qed.
Lemma lem7560461 : term818 = True.
Proof. exact (TRANS (@lem7560413) (@lem7560460)). Qed.
Lemma lem7560462 : term817 = True.
Proof. exact (TRANS (@lem7560404) (@lem7560461)). Qed.
Lemma lem7560463 : True = term817.
Proof. exact (SYM (@lem7560462)). Qed.
Lemma lem7560464 : term817.
Proof. exact (EQ_MP (@lem7560463) (@lem0)). Qed.
Lemma lem7560465 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term831 _97561.
Proof. exact (conj (@lem7560464) (@lem7560401 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560467 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7560468 (_97561 : int) : term833 _97561.
Proof. exact (@lem7560467 term469 (real_of_int _97561)). Qed.
Lemma lem7560469 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term834 _97561.
Proof. exact (@lem7560468 _97561 (@lem7560465 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560470 (_97561 : int) : (term835 _97561) = (real_of_int _97561).
Proof. exact (@lem1982733 (real_of_int _97561)). Qed.
Lemma lem7560471 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560472 (_97561 : int) : (term836 _97561) = (term542 _97561).
Proof. exact (MK_COMB (@lem7560471) (@lem7560470 _97561)). Qed.
Lemma lem7560473 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560474 (_97561 : int) : (term834 _97561) = (term543 _97561).
Proof. exact (MK_COMB (@lem7560472 _97561) (@lem7560473)). Qed.
Lemma lem7560475 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term543 _97561.
Proof. exact (EQ_MP (@lem7560474 _97561) (@lem7560469 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560477 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7560478 : term817 = term818.
Proof. exact (@lem7560477 term35 term469). Qed.
Lemma lem7560480 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560481 : term469 = term549.
Proof. exact (@lem7560480 term470). Qed.
Lemma lem7560483 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560484 : term35 = term520.
Proof. exact (@lem7560483 (NUMERAL 0)). Qed.
Lemma lem7560485 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560486 : term819 = term820.
Proof. exact (MK_COMB (@lem7560485) (@lem7560484)). Qed.
Lemma lem7560487 : term818 = term821.
Proof. exact (MK_COMB (@lem7560486) (@lem7560481)). Qed.
Lemma lem7560488 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7560490 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560491 : term818 = term824.
Proof. exact (@lem7560490 (NUMERAL 0) term470). Qed.
Lemma lem7560492 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560493 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560494 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560493 h1) (fun h1 : term824 = True => @lem7560492)). Qed.
Lemma lem7560495 : term824 = True.
Proof. exact (EQ_MP (@lem7560494) (@lem7560492)). Qed.
Lemma lem7560496 : term818 = True.
Proof. exact (TRANS (@lem7560491) (@lem7560495)). Qed.
Lemma lem7560497 : True = term818.
Proof. exact (SYM (@lem7560496)). Qed.
Lemma lem7560498 : term818.
Proof. exact (EQ_MP (@lem7560497) (@lem0)). Qed.
Lemma lem7560499 : term826.
Proof. exact (@lem7560488 (@lem7560498)). Qed.
Lemma lem7560501 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560502 : term818 = term824.
Proof. exact (@lem7560501 (NUMERAL 0) term470). Qed.
Lemma lem7560503 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560504 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560505 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560504 h1) (fun h1 : term824 = True => @lem7560503)). Qed.
Lemma lem7560506 : term824 = True.
Proof. exact (EQ_MP (@lem7560505) (@lem7560503)). Qed.
Lemma lem7560507 : term818 = True.
Proof. exact (TRANS (@lem7560502) (@lem7560506)). Qed.
Lemma lem7560508 : True = term818.
Proof. exact (SYM (@lem7560507)). Qed.
Lemma lem7560509 : term818.
Proof. exact (EQ_MP (@lem7560508) (@lem0)). Qed.
Lemma lem7560510 : term821 = term827.
Proof. exact (@lem7560499 (@lem7560509)). Qed.
Lemma lem7560512 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560513 : term532 = term533.
Proof. exact (@lem7560512 term470 term470). Qed.
Lemma lem7560514 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560515 : term535 = term470.
Proof. exact (EQ_MP (@lem7560514) (@lem940073)). Qed.
Lemma lem7560516 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560517 : term533 = term469.
Proof. exact (MK_COMB (@lem7560516) (@lem7560515)). Qed.
Lemma lem7560518 : term532 = term469.
Proof. exact (TRANS (@lem7560513) (@lem7560517)). Qed.
Lemma lem7560520 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560521 : term829 = term35.
Proof. exact (@lem7560520 term470). Qed.
Lemma lem7560522 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560523 : term830 = term819.
Proof. exact (MK_COMB (@lem7560522) (@lem7560521)). Qed.
Lemma lem7560524 : term827 = term818.
Proof. exact (MK_COMB (@lem7560523) (@lem7560518)). Qed.
Lemma lem7560526 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560527 : term818 = term824.
Proof. exact (@lem7560526 (NUMERAL 0) term470). Qed.
Lemma lem7560528 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560529 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560530 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560529 h1) (fun h1 : term824 = True => @lem7560528)). Qed.
Lemma lem7560531 : term824 = True.
Proof. exact (EQ_MP (@lem7560530) (@lem7560528)). Qed.
Lemma lem7560532 : term818 = True.
Proof. exact (TRANS (@lem7560527) (@lem7560531)). Qed.
Lemma lem7560533 : term827 = True.
Proof. exact (TRANS (@lem7560524) (@lem7560532)). Qed.
Lemma lem7560534 : term821 = True.
Proof. exact (TRANS (@lem7560510) (@lem7560533)). Qed.
Lemma lem7560535 : term818 = True.
Proof. exact (TRANS (@lem7560487) (@lem7560534)). Qed.
Lemma lem7560536 : term817 = True.
Proof. exact (TRANS (@lem7560478) (@lem7560535)). Qed.
Lemma lem7560537 : True = term817.
Proof. exact (SYM (@lem7560536)). Qed.
Lemma lem7560538 : term817.
Proof. exact (EQ_MP (@lem7560537) (@lem0)). Qed.
Lemma lem7560539 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term837 _97561.
Proof. exact (conj (@lem7560538) (@lem7560398 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560541 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7560542 (_97561 : int) : term838 _97561.
Proof. exact (@lem7560541 term469 (term559 _97561)). Qed.
Lemma lem7560543 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term839 _97561.
Proof. exact (@lem7560542 _97561 (@lem7560539 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560544 (_97561 : int) : (term840 _97561) = (term559 _97561).
Proof. exact (@lem1982733 (term559 _97561)). Qed.
Lemma lem7560545 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560546 (_97561 : int) : (term841 _97561) = (term563 _97561).
Proof. exact (MK_COMB (@lem7560545) (@lem7560544 _97561)). Qed.
Lemma lem7560547 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560548 (_97561 : int) : (term839 _97561) = (term564 _97561).
Proof. exact (MK_COMB (@lem7560546 _97561) (@lem7560547)). Qed.
Lemma lem7560549 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term564 _97561.
Proof. exact (EQ_MP (@lem7560548 _97561) (@lem7560543 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560550 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term842 _97561.
Proof. exact (conj (@lem7560549 _97560 _97559 _97561 h1) (@lem7560475 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560552 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7560553 (_97561 : int) : term844 _97561.
Proof. exact (@lem7560552 (term559 _97561) (real_of_int _97561)). Qed.
Lemma lem7560554 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term845 _97561.
Proof. exact (@lem7560553 _97561 (@lem7560550 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560555 (_97561 : int) : (term846 _97561) = (term847 _97561).
Proof. exact (@lem1982759 (term570 _97561) (real_of_int _97561) term523). Qed.
Lemma lem7560556 (_97561 : int) : (term848 _97561) = (term849 _97561).
Proof. exact (@lem1982713 term523 (real_of_int _97561)). Qed.
Lemma lem7560558 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560559 : term469 = term549.
Proof. exact (@lem7560558 term470). Qed.
Lemma lem7560561 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7560562 : term523 = term524.
Proof. exact (@lem7560561 term470). Qed.
Lemma lem7560563 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560564 : term850 = term851.
Proof. exact (MK_COMB (@lem7560563) (@lem7560562)). Qed.
Lemma lem7560565 : term852 = term853.
Proof. exact (MK_COMB (@lem7560564) (@lem7560559)). Qed.
Lemma lem7560566 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7560568 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560569 : term818 = term824.
Proof. exact (@lem7560568 (NUMERAL 0) term470). Qed.
Lemma lem7560570 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560571 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560572 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560571 h1) (fun h1 : term824 = True => @lem7560570)). Qed.
Lemma lem7560573 : term824 = True.
Proof. exact (EQ_MP (@lem7560572) (@lem7560570)). Qed.
Lemma lem7560574 : term818 = True.
Proof. exact (TRANS (@lem7560569) (@lem7560573)). Qed.
Lemma lem7560575 : True = term818.
Proof. exact (SYM (@lem7560574)). Qed.
Lemma lem7560576 : term818.
Proof. exact (EQ_MP (@lem7560575) (@lem0)). Qed.
Lemma lem7560577 : term855.
Proof. exact (@lem7560566 (@lem7560576)). Qed.
Lemma lem7560579 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560580 : term818 = term824.
Proof. exact (@lem7560579 (NUMERAL 0) term470). Qed.
Lemma lem7560581 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560582 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560583 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560582 h1) (fun h1 : term824 = True => @lem7560581)). Qed.
Lemma lem7560584 : term824 = True.
Proof. exact (EQ_MP (@lem7560583) (@lem7560581)). Qed.
Lemma lem7560585 : term818 = True.
Proof. exact (TRANS (@lem7560580) (@lem7560584)). Qed.
Lemma lem7560586 : True = term818.
Proof. exact (SYM (@lem7560585)). Qed.
Lemma lem7560587 : term818.
Proof. exact (EQ_MP (@lem7560586) (@lem0)). Qed.
Lemma lem7560588 : term856.
Proof. exact (@lem7560577 (@lem7560587)). Qed.
Lemma lem7560590 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560591 : term818 = term824.
Proof. exact (@lem7560590 (NUMERAL 0) term470). Qed.
Lemma lem7560592 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560593 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560594 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560593 h1) (fun h1 : term824 = True => @lem7560592)). Qed.
Lemma lem7560595 : term824 = True.
Proof. exact (EQ_MP (@lem7560594) (@lem7560592)). Qed.
Lemma lem7560596 : term818 = True.
Proof. exact (TRANS (@lem7560591) (@lem7560595)). Qed.
Lemma lem7560597 : True = term818.
Proof. exact (SYM (@lem7560596)). Qed.
Lemma lem7560598 : term818.
Proof. exact (EQ_MP (@lem7560597) (@lem0)). Qed.
Lemma lem7560599 : term857.
Proof. exact (@lem7560588 (@lem7560598)). Qed.
Lemma lem7560601 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560602 : term532 = term533.
Proof. exact (@lem7560601 term470 term470). Qed.
Lemma lem7560603 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560604 : term535 = term470.
Proof. exact (EQ_MP (@lem7560603) (@lem940073)). Qed.
Lemma lem7560605 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560606 : term533 = term469.
Proof. exact (MK_COMB (@lem7560605) (@lem7560604)). Qed.
Lemma lem7560607 : term532 = term469.
Proof. exact (TRANS (@lem7560602) (@lem7560606)). Qed.
Lemma lem7560609 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7560610 : term550 = term555.
Proof. exact (@lem7560609 term470 term470). Qed.
Lemma lem7560611 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560612 : term535 = term470.
Proof. exact (EQ_MP (@lem7560611) (@lem940073)). Qed.
Lemma lem7560613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560614 : term533 = term469.
Proof. exact (MK_COMB (@lem7560613) (@lem7560612)). Qed.
Lemma lem7560615 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7560616 : term555 = term523.
Proof. exact (MK_COMB (@lem7560615) (@lem7560614)). Qed.
Lemma lem7560617 : term550 = term523.
Proof. exact (TRANS (@lem7560610) (@lem7560616)). Qed.
Lemma lem7560618 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560619 : term858 = term850.
Proof. exact (MK_COMB (@lem7560618) (@lem7560617)). Qed.
Lemma lem7560620 : term859 = term852.
Proof. exact (MK_COMB (@lem7560619) (@lem7560607)). Qed.
Lemma lem7560622 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7560623 : term852 = term35.
Proof. exact (@lem7560622 term470). Qed.
Lemma lem7560624 : term859 = term35.
Proof. exact (TRANS (@lem7560620) (@lem7560623)). Qed.
Lemma lem7560625 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7560626 : term861 = term218.
Proof. exact (MK_COMB (@lem7560625) (@lem7560624)). Qed.
Lemma lem7560627 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7560628 : term862 = term829.
Proof. exact (MK_COMB (@lem7560626) (@lem7560627)). Qed.
Lemma lem7560630 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560631 : term829 = term35.
Proof. exact (@lem7560630 term470). Qed.
Lemma lem7560632 : term862 = term35.
Proof. exact (TRANS (@lem7560628) (@lem7560631)). Qed.
Lemma lem7560634 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560635 : term532 = term533.
Proof. exact (@lem7560634 term470 term470). Qed.
Lemma lem7560636 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560637 : term535 = term470.
Proof. exact (EQ_MP (@lem7560636) (@lem940073)). Qed.
Lemma lem7560638 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560639 : term533 = term469.
Proof. exact (MK_COMB (@lem7560638) (@lem7560637)). Qed.
Lemma lem7560640 : term532 = term469.
Proof. exact (TRANS (@lem7560635) (@lem7560639)). Qed.
Lemma lem7560641 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7560642 : term863 = term829.
Proof. exact (MK_COMB (@lem7560641) (@lem7560640)). Qed.
Lemma lem7560644 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560645 : term829 = term35.
Proof. exact (@lem7560644 term470). Qed.
Lemma lem7560646 : term863 = term35.
Proof. exact (TRANS (@lem7560642) (@lem7560645)). Qed.
Lemma lem7560647 : term35 = term863.
Proof. exact (SYM (@lem7560646)). Qed.
Lemma lem7560648 : term862 = term863.
Proof. exact (TRANS (@lem7560632) (@lem7560647)). Qed.
Lemma lem7560649 : term853 = term520.
Proof. exact (@lem7560599 (@lem7560648)). Qed.
Lemma lem7560650 : term852 = term520.
Proof. exact (TRANS (@lem7560565) (@lem7560649)). Qed.
Lemma lem7560652 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7560653 : term520 = term35.
Proof. exact (@lem7560652 term35). Qed.
Lemma lem7560654 : term852 = term35.
Proof. exact (TRANS (@lem7560650) (@lem7560653)). Qed.
Lemma lem7560655 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7560656 : term864 = term218.
Proof. exact (MK_COMB (@lem7560655) (@lem7560654)). Qed.
Lemma lem7560657 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7560658 (_97561 : int) : (term849 _97561) = (term865 _97561).
Proof. exact (MK_COMB (@lem7560656) (@lem7560657 _97561)). Qed.
Lemma lem7560659 (_97561 : int) : (term848 _97561) = (term865 _97561).
Proof. exact (TRANS (@lem7560556 _97561) (@lem7560658 _97561)). Qed.
Lemma lem7560660 (_97561 : int) : (term865 _97561) = term35.
Proof. exact (@lem1982719 (real_of_int _97561)). Qed.
Lemma lem7560661 (_97561 : int) : (term848 _97561) = term35.
Proof. exact (TRANS (@lem7560659 _97561) (@lem7560660 _97561)). Qed.
Lemma lem7560662 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560663 (_97561 : int) : (term866 _97561) = term560.
Proof. exact (MK_COMB (@lem7560662) (@lem7560661 _97561)). Qed.
Lemma lem7560664 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7560665 (_97561 : int) : (term847 _97561) = term867.
Proof. exact (MK_COMB (@lem7560663 _97561) (@lem7560664)). Qed.
Lemma lem7560666 (_97561 : int) : (term846 _97561) = term867.
Proof. exact (TRANS (@lem7560555 _97561) (@lem7560665 _97561)). Qed.
Lemma lem7560667 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7560668 (_97561 : int) : (term846 _97561) = term523.
Proof. exact (TRANS (@lem7560666 _97561) (@lem7560667)). Qed.
Lemma lem7560669 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560670 (_97561 : int) : (term868 _97561) = term869.
Proof. exact (MK_COMB (@lem7560669) (@lem7560668 _97561)). Qed.
Lemma lem7560671 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560672 (_97561 : int) : (term845 _97561) = term870.
Proof. exact (MK_COMB (@lem7560670 _97561) (@lem7560671)). Qed.
Lemma lem7560673 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : term870.
Proof. exact (EQ_MP (@lem7560672 _97561) (@lem7560554 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560675 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7560676 : term870 = term871.
Proof. exact (@lem7560675 term35 term523). Qed.
Lemma lem7560678 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7560679 : term523 = term524.
Proof. exact (@lem7560678 term470). Qed.
Lemma lem7560681 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560682 : term35 = term520.
Proof. exact (@lem7560681 (NUMERAL 0)). Qed.
Lemma lem7560683 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7560684 : term457 = term872.
Proof. exact (MK_COMB (@lem7560683) (@lem7560682)). Qed.
Lemma lem7560685 : term871 = term873.
Proof. exact (MK_COMB (@lem7560684) (@lem7560679)). Qed.
Lemma lem7560686 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7560688 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560689 : term818 = term824.
Proof. exact (@lem7560688 (NUMERAL 0) term470). Qed.
Lemma lem7560690 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560691 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560692 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560691 h1) (fun h1 : term824 = True => @lem7560690)). Qed.
Lemma lem7560693 : term824 = True.
Proof. exact (EQ_MP (@lem7560692) (@lem7560690)). Qed.
Lemma lem7560694 : term818 = True.
Proof. exact (TRANS (@lem7560689) (@lem7560693)). Qed.
Lemma lem7560695 : True = term818.
Proof. exact (SYM (@lem7560694)). Qed.
Lemma lem7560696 : term818.
Proof. exact (EQ_MP (@lem7560695) (@lem0)). Qed.
Lemma lem7560697 : term875.
Proof. exact (@lem7560686 (@lem7560696)). Qed.
Lemma lem7560699 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560700 : term818 = term824.
Proof. exact (@lem7560699 (NUMERAL 0) term470). Qed.
Lemma lem7560701 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560702 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560703 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560702 h1) (fun h1 : term824 = True => @lem7560701)). Qed.
Lemma lem7560704 : term824 = True.
Proof. exact (EQ_MP (@lem7560703) (@lem7560701)). Qed.
Lemma lem7560705 : term818 = True.
Proof. exact (TRANS (@lem7560700) (@lem7560704)). Qed.
Lemma lem7560706 : True = term818.
Proof. exact (SYM (@lem7560705)). Qed.
Lemma lem7560707 : term818.
Proof. exact (EQ_MP (@lem7560706) (@lem0)). Qed.
Lemma lem7560708 : term873 = term876.
Proof. exact (@lem7560697 (@lem7560707)). Qed.
Lemma lem7560710 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7560711 : term550 = term555.
Proof. exact (@lem7560710 term470 term470). Qed.
Lemma lem7560712 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560713 : term535 = term470.
Proof. exact (EQ_MP (@lem7560712) (@lem940073)). Qed.
Lemma lem7560714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560715 : term533 = term469.
Proof. exact (MK_COMB (@lem7560714) (@lem7560713)). Qed.
Lemma lem7560716 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7560717 : term555 = term523.
Proof. exact (MK_COMB (@lem7560716) (@lem7560715)). Qed.
Lemma lem7560718 : term550 = term523.
Proof. exact (TRANS (@lem7560711) (@lem7560717)). Qed.
Lemma lem7560720 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560721 : term829 = term35.
Proof. exact (@lem7560720 term470). Qed.
Lemma lem7560722 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7560723 : term877 = term457.
Proof. exact (MK_COMB (@lem7560722) (@lem7560721)). Qed.
Lemma lem7560724 : term876 = term871.
Proof. exact (MK_COMB (@lem7560723) (@lem7560718)). Qed.
Lemma lem7560726 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7560727 : term871 = term880.
Proof. exact (@lem7560726 (NUMERAL 0) term470). Qed.
Lemma lem7560728 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560729 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7560730 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560729 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7560728)). Qed.
Lemma lem7560731 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7560730) (@lem7560728)). Qed.
Lemma lem7560732 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7560733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7560734 : term881 = (and True).
Proof. exact (MK_COMB (@lem7560733) (@lem7560732)). Qed.
Lemma lem7560735 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7560734) (@lem7560731)). Qed.
Lemma lem7560737 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7560738 : term880 = False.
Proof. exact (TRANS (@lem7560735) (@lem7560737)). Qed.
Lemma lem7560739 : term871 = False.
Proof. exact (TRANS (@lem7560727) (@lem7560738)). Qed.
Lemma lem7560740 : term876 = False.
Proof. exact (TRANS (@lem7560724) (@lem7560739)). Qed.
Lemma lem7560741 : term873 = False.
Proof. exact (TRANS (@lem7560708) (@lem7560740)). Qed.
Lemma lem7560742 : term871 = False.
Proof. exact (TRANS (@lem7560685) (@lem7560741)). Qed.
Lemma lem7560743 : term870 = False.
Proof. exact (TRANS (@lem7560676) (@lem7560742)). Qed.
Lemma lem7560744 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term903 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7560743) (@lem7560673 _97560 _97559 _97561 h1)). Qed.
Lemma lem7560745 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term810 _97559 _97560 _97561.
Proof. exact (h1). Qed.
Lemma lem7560746 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term808 _97559 _97560 _97561.
Proof. exact (proj2 (@lem7560745 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560748 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term807 _97559 _97560 _97561.
Proof. exact (proj2 (@lem7560746 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560750 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term806 _97559 _97560 _97561.
Proof. exact (proj2 (@lem7560748 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560752 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term805 _97559 _97560 _97561.
Proof. exact (proj2 (@lem7560750 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560753 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term595 _97559 _97561.
Proof. exact (proj1 (@lem7560750 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560754 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term590 _97559 _97561.
Proof. exact (proj2 (@lem7560753 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560757 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term573 _97559 _97561.
Proof. exact (proj1 (@lem7560752 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560759 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7560760 : term817 = term818.
Proof. exact (@lem7560759 term35 term469). Qed.
Lemma lem7560762 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560763 : term469 = term549.
Proof. exact (@lem7560762 term470). Qed.
Lemma lem7560765 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560766 : term35 = term520.
Proof. exact (@lem7560765 (NUMERAL 0)). Qed.
Lemma lem7560767 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560768 : term819 = term820.
Proof. exact (MK_COMB (@lem7560767) (@lem7560766)). Qed.
Lemma lem7560769 : term818 = term821.
Proof. exact (MK_COMB (@lem7560768) (@lem7560763)). Qed.
Lemma lem7560770 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7560772 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560773 : term818 = term824.
Proof. exact (@lem7560772 (NUMERAL 0) term470). Qed.
Lemma lem7560774 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560775 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560776 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560775 h1) (fun h1 : term824 = True => @lem7560774)). Qed.
Lemma lem7560777 : term824 = True.
Proof. exact (EQ_MP (@lem7560776) (@lem7560774)). Qed.
Lemma lem7560778 : term818 = True.
Proof. exact (TRANS (@lem7560773) (@lem7560777)). Qed.
Lemma lem7560779 : True = term818.
Proof. exact (SYM (@lem7560778)). Qed.
Lemma lem7560780 : term818.
Proof. exact (EQ_MP (@lem7560779) (@lem0)). Qed.
Lemma lem7560781 : term826.
Proof. exact (@lem7560770 (@lem7560780)). Qed.
Lemma lem7560783 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560784 : term818 = term824.
Proof. exact (@lem7560783 (NUMERAL 0) term470). Qed.
Lemma lem7560785 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560786 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560787 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560786 h1) (fun h1 : term824 = True => @lem7560785)). Qed.
Lemma lem7560788 : term824 = True.
Proof. exact (EQ_MP (@lem7560787) (@lem7560785)). Qed.
Lemma lem7560789 : term818 = True.
Proof. exact (TRANS (@lem7560784) (@lem7560788)). Qed.
Lemma lem7560790 : True = term818.
Proof. exact (SYM (@lem7560789)). Qed.
Lemma lem7560791 : term818.
Proof. exact (EQ_MP (@lem7560790) (@lem0)). Qed.
Lemma lem7560792 : term821 = term827.
Proof. exact (@lem7560781 (@lem7560791)). Qed.
Lemma lem7560794 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560795 : term532 = term533.
Proof. exact (@lem7560794 term470 term470). Qed.
Lemma lem7560796 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560797 : term535 = term470.
Proof. exact (EQ_MP (@lem7560796) (@lem940073)). Qed.
Lemma lem7560798 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560799 : term533 = term469.
Proof. exact (MK_COMB (@lem7560798) (@lem7560797)). Qed.
Lemma lem7560800 : term532 = term469.
Proof. exact (TRANS (@lem7560795) (@lem7560799)). Qed.
Lemma lem7560802 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560803 : term829 = term35.
Proof. exact (@lem7560802 term470). Qed.
Lemma lem7560804 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560805 : term830 = term819.
Proof. exact (MK_COMB (@lem7560804) (@lem7560803)). Qed.
Lemma lem7560806 : term827 = term818.
Proof. exact (MK_COMB (@lem7560805) (@lem7560800)). Qed.
Lemma lem7560808 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560809 : term818 = term824.
Proof. exact (@lem7560808 (NUMERAL 0) term470). Qed.
Lemma lem7560810 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560811 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560812 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560811 h1) (fun h1 : term824 = True => @lem7560810)). Qed.
Lemma lem7560813 : term824 = True.
Proof. exact (EQ_MP (@lem7560812) (@lem7560810)). Qed.
Lemma lem7560814 : term818 = True.
Proof. exact (TRANS (@lem7560809) (@lem7560813)). Qed.
Lemma lem7560815 : term827 = True.
Proof. exact (TRANS (@lem7560806) (@lem7560814)). Qed.
Lemma lem7560816 : term821 = True.
Proof. exact (TRANS (@lem7560792) (@lem7560815)). Qed.
Lemma lem7560817 : term818 = True.
Proof. exact (TRANS (@lem7560769) (@lem7560816)). Qed.
Lemma lem7560818 : term817 = True.
Proof. exact (TRANS (@lem7560760) (@lem7560817)). Qed.
Lemma lem7560819 : True = term817.
Proof. exact (SYM (@lem7560818)). Qed.
Lemma lem7560820 : term817.
Proof. exact (EQ_MP (@lem7560819) (@lem0)). Qed.
Lemma lem7560821 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term882 _97559 _97561.
Proof. exact (conj (@lem7560820) (@lem7560754 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560823 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7560824 (_97559 : int) (_97561 : int) : term883 _97559 _97561.
Proof. exact (@lem7560823 term469 (term587 _97559 _97561)). Qed.
Lemma lem7560825 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term884 _97559 _97561.
Proof. exact (@lem7560824 _97559 _97561 (@lem7560821 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560826 (_97559 : int) (_97561 : int) : (term885 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982733 (term587 _97559 _97561)). Qed.
Lemma lem7560827 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560828 (_97559 : int) (_97561 : int) : (term886 _97559 _97561) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7560827) (@lem7560826 _97559 _97561)). Qed.
Lemma lem7560829 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560830 (_97559 : int) (_97561 : int) : (term884 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7560828 _97559 _97561) (@lem7560829)). Qed.
Lemma lem7560831 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term590 _97559 _97561.
Proof. exact (EQ_MP (@lem7560830 _97559 _97561) (@lem7560825 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560833 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7560834 : term817 = term818.
Proof. exact (@lem7560833 term35 term469). Qed.
Lemma lem7560836 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560837 : term469 = term549.
Proof. exact (@lem7560836 term470). Qed.
Lemma lem7560839 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560840 : term35 = term520.
Proof. exact (@lem7560839 (NUMERAL 0)). Qed.
Lemma lem7560841 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560842 : term819 = term820.
Proof. exact (MK_COMB (@lem7560841) (@lem7560840)). Qed.
Lemma lem7560843 : term818 = term821.
Proof. exact (MK_COMB (@lem7560842) (@lem7560837)). Qed.
Lemma lem7560844 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7560846 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560847 : term818 = term824.
Proof. exact (@lem7560846 (NUMERAL 0) term470). Qed.
Lemma lem7560848 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560849 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560850 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560849 h1) (fun h1 : term824 = True => @lem7560848)). Qed.
Lemma lem7560851 : term824 = True.
Proof. exact (EQ_MP (@lem7560850) (@lem7560848)). Qed.
Lemma lem7560852 : term818 = True.
Proof. exact (TRANS (@lem7560847) (@lem7560851)). Qed.
Lemma lem7560853 : True = term818.
Proof. exact (SYM (@lem7560852)). Qed.
Lemma lem7560854 : term818.
Proof. exact (EQ_MP (@lem7560853) (@lem0)). Qed.
Lemma lem7560855 : term826.
Proof. exact (@lem7560844 (@lem7560854)). Qed.
Lemma lem7560857 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560858 : term818 = term824.
Proof. exact (@lem7560857 (NUMERAL 0) term470). Qed.
Lemma lem7560859 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560860 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560861 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560860 h1) (fun h1 : term824 = True => @lem7560859)). Qed.
Lemma lem7560862 : term824 = True.
Proof. exact (EQ_MP (@lem7560861) (@lem7560859)). Qed.
Lemma lem7560863 : term818 = True.
Proof. exact (TRANS (@lem7560858) (@lem7560862)). Qed.
Lemma lem7560864 : True = term818.
Proof. exact (SYM (@lem7560863)). Qed.
Lemma lem7560865 : term818.
Proof. exact (EQ_MP (@lem7560864) (@lem0)). Qed.
Lemma lem7560866 : term821 = term827.
Proof. exact (@lem7560855 (@lem7560865)). Qed.
Lemma lem7560868 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560869 : term532 = term533.
Proof. exact (@lem7560868 term470 term470). Qed.
Lemma lem7560870 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560871 : term535 = term470.
Proof. exact (EQ_MP (@lem7560870) (@lem940073)). Qed.
Lemma lem7560872 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560873 : term533 = term469.
Proof. exact (MK_COMB (@lem7560872) (@lem7560871)). Qed.
Lemma lem7560874 : term532 = term469.
Proof. exact (TRANS (@lem7560869) (@lem7560873)). Qed.
Lemma lem7560876 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560877 : term829 = term35.
Proof. exact (@lem7560876 term470). Qed.
Lemma lem7560878 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7560879 : term830 = term819.
Proof. exact (MK_COMB (@lem7560878) (@lem7560877)). Qed.
Lemma lem7560880 : term827 = term818.
Proof. exact (MK_COMB (@lem7560879) (@lem7560874)). Qed.
Lemma lem7560882 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560883 : term818 = term824.
Proof. exact (@lem7560882 (NUMERAL 0) term470). Qed.
Lemma lem7560884 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560885 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560886 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560885 h1) (fun h1 : term824 = True => @lem7560884)). Qed.
Lemma lem7560887 : term824 = True.
Proof. exact (EQ_MP (@lem7560886) (@lem7560884)). Qed.
Lemma lem7560888 : term818 = True.
Proof. exact (TRANS (@lem7560883) (@lem7560887)). Qed.
Lemma lem7560889 : term827 = True.
Proof. exact (TRANS (@lem7560880) (@lem7560888)). Qed.
Lemma lem7560890 : term821 = True.
Proof. exact (TRANS (@lem7560866) (@lem7560889)). Qed.
Lemma lem7560891 : term818 = True.
Proof. exact (TRANS (@lem7560843) (@lem7560890)). Qed.
Lemma lem7560892 : term817 = True.
Proof. exact (TRANS (@lem7560834) (@lem7560891)). Qed.
Lemma lem7560893 : True = term817.
Proof. exact (SYM (@lem7560892)). Qed.
Lemma lem7560894 : term817.
Proof. exact (EQ_MP (@lem7560893) (@lem0)). Qed.
Lemma lem7560895 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term887 _97559 _97561.
Proof. exact (conj (@lem7560894) (@lem7560757 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560897 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7560898 (_97559 : int) (_97561 : int) : term888 _97559 _97561.
Proof. exact (@lem7560897 term469 (term569 _97559 _97561)). Qed.
Lemma lem7560899 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term889 _97559 _97561.
Proof. exact (@lem7560898 _97559 _97561 (@lem7560895 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560900 (_97559 : int) (_97561 : int) : (term890 _97559 _97561) = (term569 _97559 _97561).
Proof. exact (@lem1982733 (term569 _97559 _97561)). Qed.
Lemma lem7560901 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7560902 (_97559 : int) (_97561 : int) : (term891 _97559 _97561) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7560901) (@lem7560900 _97559 _97561)). Qed.
Lemma lem7560903 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7560904 (_97559 : int) (_97561 : int) : (term889 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7560902 _97559 _97561) (@lem7560903)). Qed.
Lemma lem7560905 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term573 _97559 _97561.
Proof. exact (EQ_MP (@lem7560904 _97559 _97561) (@lem7560899 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560906 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term892 _97559 _97561.
Proof. exact (conj (@lem7560905 _97559 _97560 _97561 h1) (@lem7560831 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560908 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7560909 (_97559 : int) (_97561 : int) : term893 _97559 _97561.
Proof. exact (@lem7560908 (term569 _97559 _97561) (term587 _97559 _97561)). Qed.
Lemma lem7560910 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term894 _97559 _97561.
Proof. exact (@lem7560909 _97559 _97561 (@lem7560906 _97559 _97560 _97561 h1)). Qed.
Lemma lem7560911 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = (term896 _97559 _97561).
Proof. exact (@lem1982753 (term570 _97559) (real_of_int _97559) (term897 _97561) (term570 _97561)). Qed.
Lemma lem7560912 (_97559 : int) : (term848 _97559) = (term849 _97559).
Proof. exact (@lem1982713 term523 (real_of_int _97559)). Qed.
Lemma lem7560914 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7560915 : term469 = term549.
Proof. exact (@lem7560914 term470). Qed.
Lemma lem7560917 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7560918 : term523 = term524.
Proof. exact (@lem7560917 term470). Qed.
Lemma lem7560919 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560920 : term850 = term851.
Proof. exact (MK_COMB (@lem7560919) (@lem7560918)). Qed.
Lemma lem7560921 : term852 = term853.
Proof. exact (MK_COMB (@lem7560920) (@lem7560915)). Qed.
Lemma lem7560922 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7560924 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560925 : term818 = term824.
Proof. exact (@lem7560924 (NUMERAL 0) term470). Qed.
Lemma lem7560926 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560927 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560928 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560927 h1) (fun h1 : term824 = True => @lem7560926)). Qed.
Lemma lem7560929 : term824 = True.
Proof. exact (EQ_MP (@lem7560928) (@lem7560926)). Qed.
Lemma lem7560930 : term818 = True.
Proof. exact (TRANS (@lem7560925) (@lem7560929)). Qed.
Lemma lem7560931 : True = term818.
Proof. exact (SYM (@lem7560930)). Qed.
Lemma lem7560932 : term818.
Proof. exact (EQ_MP (@lem7560931) (@lem0)). Qed.
Lemma lem7560933 : term855.
Proof. exact (@lem7560922 (@lem7560932)). Qed.
Lemma lem7560935 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560936 : term818 = term824.
Proof. exact (@lem7560935 (NUMERAL 0) term470). Qed.
Lemma lem7560937 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560938 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560939 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560938 h1) (fun h1 : term824 = True => @lem7560937)). Qed.
Lemma lem7560940 : term824 = True.
Proof. exact (EQ_MP (@lem7560939) (@lem7560937)). Qed.
Lemma lem7560941 : term818 = True.
Proof. exact (TRANS (@lem7560936) (@lem7560940)). Qed.
Lemma lem7560942 : True = term818.
Proof. exact (SYM (@lem7560941)). Qed.
Lemma lem7560943 : term818.
Proof. exact (EQ_MP (@lem7560942) (@lem0)). Qed.
Lemma lem7560944 : term856.
Proof. exact (@lem7560933 (@lem7560943)). Qed.
Lemma lem7560946 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7560947 : term818 = term824.
Proof. exact (@lem7560946 (NUMERAL 0) term470). Qed.
Lemma lem7560948 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7560949 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7560950 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7560949 h1) (fun h1 : term824 = True => @lem7560948)). Qed.
Lemma lem7560951 : term824 = True.
Proof. exact (EQ_MP (@lem7560950) (@lem7560948)). Qed.
Lemma lem7560952 : term818 = True.
Proof. exact (TRANS (@lem7560947) (@lem7560951)). Qed.
Lemma lem7560953 : True = term818.
Proof. exact (SYM (@lem7560952)). Qed.
Lemma lem7560954 : term818.
Proof. exact (EQ_MP (@lem7560953) (@lem0)). Qed.
Lemma lem7560955 : term857.
Proof. exact (@lem7560944 (@lem7560954)). Qed.
Lemma lem7560957 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560958 : term532 = term533.
Proof. exact (@lem7560957 term470 term470). Qed.
Lemma lem7560959 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560960 : term535 = term470.
Proof. exact (EQ_MP (@lem7560959) (@lem940073)). Qed.
Lemma lem7560961 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560962 : term533 = term469.
Proof. exact (MK_COMB (@lem7560961) (@lem7560960)). Qed.
Lemma lem7560963 : term532 = term469.
Proof. exact (TRANS (@lem7560958) (@lem7560962)). Qed.
Lemma lem7560965 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7560966 : term550 = term555.
Proof. exact (@lem7560965 term470 term470). Qed.
Lemma lem7560967 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560968 : term535 = term470.
Proof. exact (EQ_MP (@lem7560967) (@lem940073)). Qed.
Lemma lem7560969 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560970 : term533 = term469.
Proof. exact (MK_COMB (@lem7560969) (@lem7560968)). Qed.
Lemma lem7560971 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7560972 : term555 = term523.
Proof. exact (MK_COMB (@lem7560971) (@lem7560970)). Qed.
Lemma lem7560973 : term550 = term523.
Proof. exact (TRANS (@lem7560966) (@lem7560972)). Qed.
Lemma lem7560974 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7560975 : term858 = term850.
Proof. exact (MK_COMB (@lem7560974) (@lem7560973)). Qed.
Lemma lem7560976 : term859 = term852.
Proof. exact (MK_COMB (@lem7560975) (@lem7560963)). Qed.
Lemma lem7560978 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7560979 : term852 = term35.
Proof. exact (@lem7560978 term470). Qed.
Lemma lem7560980 : term859 = term35.
Proof. exact (TRANS (@lem7560976) (@lem7560979)). Qed.
Lemma lem7560981 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7560982 : term861 = term218.
Proof. exact (MK_COMB (@lem7560981) (@lem7560980)). Qed.
Lemma lem7560983 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7560984 : term862 = term829.
Proof. exact (MK_COMB (@lem7560982) (@lem7560983)). Qed.
Lemma lem7560986 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7560987 : term829 = term35.
Proof. exact (@lem7560986 term470). Qed.
Lemma lem7560988 : term862 = term35.
Proof. exact (TRANS (@lem7560984) (@lem7560987)). Qed.
Lemma lem7560990 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7560991 : term532 = term533.
Proof. exact (@lem7560990 term470 term470). Qed.
Lemma lem7560992 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7560993 : term535 = term470.
Proof. exact (EQ_MP (@lem7560992) (@lem940073)). Qed.
Lemma lem7560994 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7560995 : term533 = term469.
Proof. exact (MK_COMB (@lem7560994) (@lem7560993)). Qed.
Lemma lem7560996 : term532 = term469.
Proof. exact (TRANS (@lem7560991) (@lem7560995)). Qed.
Lemma lem7560997 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7560998 : term863 = term829.
Proof. exact (MK_COMB (@lem7560997) (@lem7560996)). Qed.
Lemma lem7561000 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561001 : term829 = term35.
Proof. exact (@lem7561000 term470). Qed.
Lemma lem7561002 : term863 = term35.
Proof. exact (TRANS (@lem7560998) (@lem7561001)). Qed.
Lemma lem7561003 : term35 = term863.
Proof. exact (SYM (@lem7561002)). Qed.
Lemma lem7561004 : term862 = term863.
Proof. exact (TRANS (@lem7560988) (@lem7561003)). Qed.
Lemma lem7561005 : term853 = term520.
Proof. exact (@lem7560955 (@lem7561004)). Qed.
Lemma lem7561006 : term852 = term520.
Proof. exact (TRANS (@lem7560921) (@lem7561005)). Qed.
Lemma lem7561008 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7561009 : term520 = term35.
Proof. exact (@lem7561008 term35). Qed.
Lemma lem7561010 : term852 = term35.
Proof. exact (TRANS (@lem7561006) (@lem7561009)). Qed.
Lemma lem7561011 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7561012 : term864 = term218.
Proof. exact (MK_COMB (@lem7561011) (@lem7561010)). Qed.
Lemma lem7561013 (_97559 : int) : (real_of_int _97559) = (real_of_int _97559).
Proof. exact (eq_refl (real_of_int _97559)). Qed.
Lemma lem7561014 (_97559 : int) : (term849 _97559) = (term865 _97559).
Proof. exact (MK_COMB (@lem7561012) (@lem7561013 _97559)). Qed.
Lemma lem7561015 (_97559 : int) : (term848 _97559) = (term865 _97559).
Proof. exact (TRANS (@lem7560912 _97559) (@lem7561014 _97559)). Qed.
Lemma lem7561016 (_97559 : int) : (term865 _97559) = term35.
Proof. exact (@lem1982719 (real_of_int _97559)). Qed.
Lemma lem7561017 (_97559 : int) : (term848 _97559) = term35.
Proof. exact (TRANS (@lem7561015 _97559) (@lem7561016 _97559)). Qed.
Lemma lem7561018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561019 (_97559 : int) : (term866 _97559) = term560.
Proof. exact (MK_COMB (@lem7561018) (@lem7561017 _97559)). Qed.
Lemma lem7561020 (_97561 : int) : (term898 _97561) = (term899 _97561).
Proof. exact (@lem1982759 (real_of_int _97561) (term570 _97561) term523). Qed.
Lemma lem7561021 (_97561 : int) : (term900 _97561) = (term849 _97561).
Proof. exact (@lem1982715 term523 (real_of_int _97561)). Qed.
Lemma lem7561023 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561024 : term469 = term549.
Proof. exact (@lem7561023 term470). Qed.
Lemma lem7561026 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7561027 : term523 = term524.
Proof. exact (@lem7561026 term470). Qed.
Lemma lem7561028 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561029 : term850 = term851.
Proof. exact (MK_COMB (@lem7561028) (@lem7561027)). Qed.
Lemma lem7561030 : term852 = term853.
Proof. exact (MK_COMB (@lem7561029) (@lem7561024)). Qed.
Lemma lem7561031 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7561033 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561034 : term818 = term824.
Proof. exact (@lem7561033 (NUMERAL 0) term470). Qed.
Lemma lem7561035 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561036 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561037 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561036 h1) (fun h1 : term824 = True => @lem7561035)). Qed.
Lemma lem7561038 : term824 = True.
Proof. exact (EQ_MP (@lem7561037) (@lem7561035)). Qed.
Lemma lem7561039 : term818 = True.
Proof. exact (TRANS (@lem7561034) (@lem7561038)). Qed.
Lemma lem7561040 : True = term818.
Proof. exact (SYM (@lem7561039)). Qed.
Lemma lem7561041 : term818.
Proof. exact (EQ_MP (@lem7561040) (@lem0)). Qed.
Lemma lem7561042 : term855.
Proof. exact (@lem7561031 (@lem7561041)). Qed.
Lemma lem7561044 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561045 : term818 = term824.
Proof. exact (@lem7561044 (NUMERAL 0) term470). Qed.
Lemma lem7561046 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561047 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561048 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561047 h1) (fun h1 : term824 = True => @lem7561046)). Qed.
Lemma lem7561049 : term824 = True.
Proof. exact (EQ_MP (@lem7561048) (@lem7561046)). Qed.
Lemma lem7561050 : term818 = True.
Proof. exact (TRANS (@lem7561045) (@lem7561049)). Qed.
Lemma lem7561051 : True = term818.
Proof. exact (SYM (@lem7561050)). Qed.
Lemma lem7561052 : term818.
Proof. exact (EQ_MP (@lem7561051) (@lem0)). Qed.
Lemma lem7561053 : term856.
Proof. exact (@lem7561042 (@lem7561052)). Qed.
Lemma lem7561055 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561056 : term818 = term824.
Proof. exact (@lem7561055 (NUMERAL 0) term470). Qed.
Lemma lem7561057 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561058 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561059 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561058 h1) (fun h1 : term824 = True => @lem7561057)). Qed.
Lemma lem7561060 : term824 = True.
Proof. exact (EQ_MP (@lem7561059) (@lem7561057)). Qed.
Lemma lem7561061 : term818 = True.
Proof. exact (TRANS (@lem7561056) (@lem7561060)). Qed.
Lemma lem7561062 : True = term818.
Proof. exact (SYM (@lem7561061)). Qed.
Lemma lem7561063 : term818.
Proof. exact (EQ_MP (@lem7561062) (@lem0)). Qed.
Lemma lem7561064 : term857.
Proof. exact (@lem7561053 (@lem7561063)). Qed.
Lemma lem7561066 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561067 : term532 = term533.
Proof. exact (@lem7561066 term470 term470). Qed.
Lemma lem7561068 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561069 : term535 = term470.
Proof. exact (EQ_MP (@lem7561068) (@lem940073)). Qed.
Lemma lem7561070 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561071 : term533 = term469.
Proof. exact (MK_COMB (@lem7561070) (@lem7561069)). Qed.
Lemma lem7561072 : term532 = term469.
Proof. exact (TRANS (@lem7561067) (@lem7561071)). Qed.
Lemma lem7561074 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7561075 : term550 = term555.
Proof. exact (@lem7561074 term470 term470). Qed.
Lemma lem7561076 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561077 : term535 = term470.
Proof. exact (EQ_MP (@lem7561076) (@lem940073)). Qed.
Lemma lem7561078 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561079 : term533 = term469.
Proof. exact (MK_COMB (@lem7561078) (@lem7561077)). Qed.
Lemma lem7561080 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7561081 : term555 = term523.
Proof. exact (MK_COMB (@lem7561080) (@lem7561079)). Qed.
Lemma lem7561082 : term550 = term523.
Proof. exact (TRANS (@lem7561075) (@lem7561081)). Qed.
Lemma lem7561083 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561084 : term858 = term850.
Proof. exact (MK_COMB (@lem7561083) (@lem7561082)). Qed.
Lemma lem7561085 : term859 = term852.
Proof. exact (MK_COMB (@lem7561084) (@lem7561072)). Qed.
Lemma lem7561087 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7561088 : term852 = term35.
Proof. exact (@lem7561087 term470). Qed.
Lemma lem7561089 : term859 = term35.
Proof. exact (TRANS (@lem7561085) (@lem7561088)). Qed.
Lemma lem7561090 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7561091 : term861 = term218.
Proof. exact (MK_COMB (@lem7561090) (@lem7561089)). Qed.
Lemma lem7561092 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7561093 : term862 = term829.
Proof. exact (MK_COMB (@lem7561091) (@lem7561092)). Qed.
Lemma lem7561095 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561096 : term829 = term35.
Proof. exact (@lem7561095 term470). Qed.
Lemma lem7561097 : term862 = term35.
Proof. exact (TRANS (@lem7561093) (@lem7561096)). Qed.
Lemma lem7561099 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561100 : term532 = term533.
Proof. exact (@lem7561099 term470 term470). Qed.
Lemma lem7561101 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561102 : term535 = term470.
Proof. exact (EQ_MP (@lem7561101) (@lem940073)). Qed.
Lemma lem7561103 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561104 : term533 = term469.
Proof. exact (MK_COMB (@lem7561103) (@lem7561102)). Qed.
Lemma lem7561105 : term532 = term469.
Proof. exact (TRANS (@lem7561100) (@lem7561104)). Qed.
Lemma lem7561106 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7561107 : term863 = term829.
Proof. exact (MK_COMB (@lem7561106) (@lem7561105)). Qed.
Lemma lem7561109 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561110 : term829 = term35.
Proof. exact (@lem7561109 term470). Qed.
Lemma lem7561111 : term863 = term35.
Proof. exact (TRANS (@lem7561107) (@lem7561110)). Qed.
Lemma lem7561112 : term35 = term863.
Proof. exact (SYM (@lem7561111)). Qed.
Lemma lem7561113 : term862 = term863.
Proof. exact (TRANS (@lem7561097) (@lem7561112)). Qed.
Lemma lem7561114 : term853 = term520.
Proof. exact (@lem7561064 (@lem7561113)). Qed.
Lemma lem7561115 : term852 = term520.
Proof. exact (TRANS (@lem7561030) (@lem7561114)). Qed.
Lemma lem7561117 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7561118 : term520 = term35.
Proof. exact (@lem7561117 term35). Qed.
Lemma lem7561119 : term852 = term35.
Proof. exact (TRANS (@lem7561115) (@lem7561118)). Qed.
Lemma lem7561120 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7561121 : term864 = term218.
Proof. exact (MK_COMB (@lem7561120) (@lem7561119)). Qed.
Lemma lem7561122 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7561123 (_97561 : int) : (term849 _97561) = (term865 _97561).
Proof. exact (MK_COMB (@lem7561121) (@lem7561122 _97561)). Qed.
Lemma lem7561124 (_97561 : int) : (term900 _97561) = (term865 _97561).
Proof. exact (TRANS (@lem7561021 _97561) (@lem7561123 _97561)). Qed.
Lemma lem7561125 (_97561 : int) : (term865 _97561) = term35.
Proof. exact (@lem1982719 (real_of_int _97561)). Qed.
Lemma lem7561126 (_97561 : int) : (term900 _97561) = term35.
Proof. exact (TRANS (@lem7561124 _97561) (@lem7561125 _97561)). Qed.
Lemma lem7561127 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561128 (_97561 : int) : (term901 _97561) = term560.
Proof. exact (MK_COMB (@lem7561127) (@lem7561126 _97561)). Qed.
Lemma lem7561129 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7561130 (_97561 : int) : (term899 _97561) = term867.
Proof. exact (MK_COMB (@lem7561128 _97561) (@lem7561129)). Qed.
Lemma lem7561131 (_97561 : int) : (term898 _97561) = term867.
Proof. exact (TRANS (@lem7561020 _97561) (@lem7561130 _97561)). Qed.
Lemma lem7561132 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7561133 (_97561 : int) : (term898 _97561) = term523.
Proof. exact (TRANS (@lem7561131 _97561) (@lem7561132)). Qed.
Lemma lem7561134 (_97559 : int) (_97561 : int) : (term896 _97559 _97561) = term867.
Proof. exact (MK_COMB (@lem7561019 _97559) (@lem7561133 _97561)). Qed.
Lemma lem7561135 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term867.
Proof. exact (TRANS (@lem7560911 _97559 _97561) (@lem7561134 _97559 _97561)). Qed.
Lemma lem7561136 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7561137 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term523.
Proof. exact (TRANS (@lem7561135 _97559 _97561) (@lem7561136)). Qed.
Lemma lem7561138 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7561139 (_97559 : int) (_97561 : int) : (term902 _97559 _97561) = term869.
Proof. exact (MK_COMB (@lem7561138) (@lem7561137 _97559 _97561)). Qed.
Lemma lem7561140 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7561141 (_97559 : int) (_97561 : int) : (term894 _97559 _97561) = term870.
Proof. exact (MK_COMB (@lem7561139 _97559 _97561) (@lem7561140)). Qed.
Lemma lem7561142 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : term870.
Proof. exact (EQ_MP (@lem7561141 _97559 _97561) (@lem7560910 _97559 _97560 _97561 h1)). Qed.
Lemma lem7561144 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7561145 : term870 = term871.
Proof. exact (@lem7561144 term35 term523). Qed.
Lemma lem7561147 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7561148 : term523 = term524.
Proof. exact (@lem7561147 term470). Qed.
Lemma lem7561150 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561151 : term35 = term520.
Proof. exact (@lem7561150 (NUMERAL 0)). Qed.
Lemma lem7561152 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7561153 : term457 = term872.
Proof. exact (MK_COMB (@lem7561152) (@lem7561151)). Qed.
Lemma lem7561154 : term871 = term873.
Proof. exact (MK_COMB (@lem7561153) (@lem7561148)). Qed.
Lemma lem7561155 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7561157 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561158 : term818 = term824.
Proof. exact (@lem7561157 (NUMERAL 0) term470). Qed.
Lemma lem7561159 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561160 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561161 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561160 h1) (fun h1 : term824 = True => @lem7561159)). Qed.
Lemma lem7561162 : term824 = True.
Proof. exact (EQ_MP (@lem7561161) (@lem7561159)). Qed.
Lemma lem7561163 : term818 = True.
Proof. exact (TRANS (@lem7561158) (@lem7561162)). Qed.
Lemma lem7561164 : True = term818.
Proof. exact (SYM (@lem7561163)). Qed.
Lemma lem7561165 : term818.
Proof. exact (EQ_MP (@lem7561164) (@lem0)). Qed.
Lemma lem7561166 : term875.
Proof. exact (@lem7561155 (@lem7561165)). Qed.
Lemma lem7561168 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561169 : term818 = term824.
Proof. exact (@lem7561168 (NUMERAL 0) term470). Qed.
Lemma lem7561170 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561171 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561172 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561171 h1) (fun h1 : term824 = True => @lem7561170)). Qed.
Lemma lem7561173 : term824 = True.
Proof. exact (EQ_MP (@lem7561172) (@lem7561170)). Qed.
Lemma lem7561174 : term818 = True.
Proof. exact (TRANS (@lem7561169) (@lem7561173)). Qed.
Lemma lem7561175 : True = term818.
Proof. exact (SYM (@lem7561174)). Qed.
Lemma lem7561176 : term818.
Proof. exact (EQ_MP (@lem7561175) (@lem0)). Qed.
Lemma lem7561177 : term873 = term876.
Proof. exact (@lem7561166 (@lem7561176)). Qed.
Lemma lem7561179 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7561180 : term550 = term555.
Proof. exact (@lem7561179 term470 term470). Qed.
Lemma lem7561181 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561182 : term535 = term470.
Proof. exact (EQ_MP (@lem7561181) (@lem940073)). Qed.
Lemma lem7561183 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561184 : term533 = term469.
Proof. exact (MK_COMB (@lem7561183) (@lem7561182)). Qed.
Lemma lem7561185 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7561186 : term555 = term523.
Proof. exact (MK_COMB (@lem7561185) (@lem7561184)). Qed.
Lemma lem7561187 : term550 = term523.
Proof. exact (TRANS (@lem7561180) (@lem7561186)). Qed.
Lemma lem7561189 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561190 : term829 = term35.
Proof. exact (@lem7561189 term470). Qed.
Lemma lem7561191 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7561192 : term877 = term457.
Proof. exact (MK_COMB (@lem7561191) (@lem7561190)). Qed.
Lemma lem7561193 : term876 = term871.
Proof. exact (MK_COMB (@lem7561192) (@lem7561187)). Qed.
Lemma lem7561195 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7561196 : term871 = term880.
Proof. exact (@lem7561195 (NUMERAL 0) term470). Qed.
Lemma lem7561197 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561198 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7561199 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561198 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7561197)). Qed.
Lemma lem7561200 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7561199) (@lem7561197)). Qed.
Lemma lem7561201 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7561202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7561203 : term881 = (and True).
Proof. exact (MK_COMB (@lem7561202) (@lem7561201)). Qed.
Lemma lem7561204 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7561203) (@lem7561200)). Qed.
Lemma lem7561206 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7561207 : term880 = False.
Proof. exact (TRANS (@lem7561204) (@lem7561206)). Qed.
Lemma lem7561208 : term871 = False.
Proof. exact (TRANS (@lem7561196) (@lem7561207)). Qed.
Lemma lem7561209 : term876 = False.
Proof. exact (TRANS (@lem7561193) (@lem7561208)). Qed.
Lemma lem7561210 : term873 = False.
Proof. exact (TRANS (@lem7561177) (@lem7561209)). Qed.
Lemma lem7561211 : term871 = False.
Proof. exact (TRANS (@lem7561154) (@lem7561210)). Qed.
Lemma lem7561212 : term870 = False.
Proof. exact (TRANS (@lem7561145) (@lem7561211)). Qed.
Lemma lem7561213 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term810 _97559 _97560 _97561) : False.
Proof. exact (EQ_MP (@lem7561212) (@lem7561142 _97559 _97560 _97561 h1)). Qed.
Lemma lem7561214 (_97559 : int) (_97560 : int) (_97561 : int) (h1 : term812 _97559 _97560 _97561) : False.
Proof. exact (or_elim (@lem7560390 _97559 _97560 _97561 h1) (fun h0 : term903 _97560 _97559 _97561 => @lem7560744 _97560 _97559 _97561 h0) (fun h0 : term810 _97559 _97560 _97561 => @lem7561213 _97559 _97560 _97561 h0)). Qed.
Lemma lem7561215 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term669 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7561216 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term650 _97560 _97559 _97561.
Proof. exact (proj2 (@lem7561215 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561218 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term631 _97559 _97561.
Proof. exact (proj2 (@lem7561216 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561220 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term618 _97559 _97561.
Proof. exact (proj2 (@lem7561218 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561222 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term573 _97559 _97561.
Proof. exact (proj2 (@lem7561220 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561223 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term595 _97559 _97561.
Proof. exact (proj1 (@lem7561220 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561224 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term590 _97559 _97561.
Proof. exact (proj2 (@lem7561223 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561227 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7561228 : term817 = term818.
Proof. exact (@lem7561227 term35 term469). Qed.
Lemma lem7561230 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561231 : term469 = term549.
Proof. exact (@lem7561230 term470). Qed.
Lemma lem7561233 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561234 : term35 = term520.
Proof. exact (@lem7561233 (NUMERAL 0)). Qed.
Lemma lem7561235 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7561236 : term819 = term820.
Proof. exact (MK_COMB (@lem7561235) (@lem7561234)). Qed.
Lemma lem7561237 : term818 = term821.
Proof. exact (MK_COMB (@lem7561236) (@lem7561231)). Qed.
Lemma lem7561238 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7561240 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561241 : term818 = term824.
Proof. exact (@lem7561240 (NUMERAL 0) term470). Qed.
Lemma lem7561242 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561243 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561244 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561243 h1) (fun h1 : term824 = True => @lem7561242)). Qed.
Lemma lem7561245 : term824 = True.
Proof. exact (EQ_MP (@lem7561244) (@lem7561242)). Qed.
Lemma lem7561246 : term818 = True.
Proof. exact (TRANS (@lem7561241) (@lem7561245)). Qed.
Lemma lem7561247 : True = term818.
Proof. exact (SYM (@lem7561246)). Qed.
Lemma lem7561248 : term818.
Proof. exact (EQ_MP (@lem7561247) (@lem0)). Qed.
Lemma lem7561249 : term826.
Proof. exact (@lem7561238 (@lem7561248)). Qed.
Lemma lem7561251 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561252 : term818 = term824.
Proof. exact (@lem7561251 (NUMERAL 0) term470). Qed.
Lemma lem7561253 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561254 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561255 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561254 h1) (fun h1 : term824 = True => @lem7561253)). Qed.
Lemma lem7561256 : term824 = True.
Proof. exact (EQ_MP (@lem7561255) (@lem7561253)). Qed.
Lemma lem7561257 : term818 = True.
Proof. exact (TRANS (@lem7561252) (@lem7561256)). Qed.
Lemma lem7561258 : True = term818.
Proof. exact (SYM (@lem7561257)). Qed.
Lemma lem7561259 : term818.
Proof. exact (EQ_MP (@lem7561258) (@lem0)). Qed.
Lemma lem7561260 : term821 = term827.
Proof. exact (@lem7561249 (@lem7561259)). Qed.
Lemma lem7561262 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561263 : term532 = term533.
Proof. exact (@lem7561262 term470 term470). Qed.
Lemma lem7561264 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561265 : term535 = term470.
Proof. exact (EQ_MP (@lem7561264) (@lem940073)). Qed.
Lemma lem7561266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561267 : term533 = term469.
Proof. exact (MK_COMB (@lem7561266) (@lem7561265)). Qed.
Lemma lem7561268 : term532 = term469.
Proof. exact (TRANS (@lem7561263) (@lem7561267)). Qed.
Lemma lem7561270 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561271 : term829 = term35.
Proof. exact (@lem7561270 term470). Qed.
Lemma lem7561272 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7561273 : term830 = term819.
Proof. exact (MK_COMB (@lem7561272) (@lem7561271)). Qed.
Lemma lem7561274 : term827 = term818.
Proof. exact (MK_COMB (@lem7561273) (@lem7561268)). Qed.
Lemma lem7561276 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561277 : term818 = term824.
Proof. exact (@lem7561276 (NUMERAL 0) term470). Qed.
Lemma lem7561278 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561279 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561280 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561279 h1) (fun h1 : term824 = True => @lem7561278)). Qed.
Lemma lem7561281 : term824 = True.
Proof. exact (EQ_MP (@lem7561280) (@lem7561278)). Qed.
Lemma lem7561282 : term818 = True.
Proof. exact (TRANS (@lem7561277) (@lem7561281)). Qed.
Lemma lem7561283 : term827 = True.
Proof. exact (TRANS (@lem7561274) (@lem7561282)). Qed.
Lemma lem7561284 : term821 = True.
Proof. exact (TRANS (@lem7561260) (@lem7561283)). Qed.
Lemma lem7561285 : term818 = True.
Proof. exact (TRANS (@lem7561237) (@lem7561284)). Qed.
Lemma lem7561286 : term817 = True.
Proof. exact (TRANS (@lem7561228) (@lem7561285)). Qed.
Lemma lem7561287 : True = term817.
Proof. exact (SYM (@lem7561286)). Qed.
Lemma lem7561288 : term817.
Proof. exact (EQ_MP (@lem7561287) (@lem0)). Qed.
Lemma lem7561289 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term882 _97559 _97561.
Proof. exact (conj (@lem7561288) (@lem7561224 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561291 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7561292 (_97559 : int) (_97561 : int) : term883 _97559 _97561.
Proof. exact (@lem7561291 term469 (term587 _97559 _97561)). Qed.
Lemma lem7561293 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term884 _97559 _97561.
Proof. exact (@lem7561292 _97559 _97561 (@lem7561289 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561294 (_97559 : int) (_97561 : int) : (term885 _97559 _97561) = (term587 _97559 _97561).
Proof. exact (@lem1982733 (term587 _97559 _97561)). Qed.
Lemma lem7561295 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7561296 (_97559 : int) (_97561 : int) : (term886 _97559 _97561) = (term589 _97559 _97561).
Proof. exact (MK_COMB (@lem7561295) (@lem7561294 _97559 _97561)). Qed.
Lemma lem7561297 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7561298 (_97559 : int) (_97561 : int) : (term884 _97559 _97561) = (term590 _97559 _97561).
Proof. exact (MK_COMB (@lem7561296 _97559 _97561) (@lem7561297)). Qed.
Lemma lem7561299 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term590 _97559 _97561.
Proof. exact (EQ_MP (@lem7561298 _97559 _97561) (@lem7561293 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561301 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7561302 : term817 = term818.
Proof. exact (@lem7561301 term35 term469). Qed.
Lemma lem7561304 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561305 : term469 = term549.
Proof. exact (@lem7561304 term470). Qed.
Lemma lem7561307 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561308 : term35 = term520.
Proof. exact (@lem7561307 (NUMERAL 0)). Qed.
Lemma lem7561309 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7561310 : term819 = term820.
Proof. exact (MK_COMB (@lem7561309) (@lem7561308)). Qed.
Lemma lem7561311 : term818 = term821.
Proof. exact (MK_COMB (@lem7561310) (@lem7561305)). Qed.
Lemma lem7561312 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7561314 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561315 : term818 = term824.
Proof. exact (@lem7561314 (NUMERAL 0) term470). Qed.
Lemma lem7561316 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561317 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561318 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561317 h1) (fun h1 : term824 = True => @lem7561316)). Qed.
Lemma lem7561319 : term824 = True.
Proof. exact (EQ_MP (@lem7561318) (@lem7561316)). Qed.
Lemma lem7561320 : term818 = True.
Proof. exact (TRANS (@lem7561315) (@lem7561319)). Qed.
Lemma lem7561321 : True = term818.
Proof. exact (SYM (@lem7561320)). Qed.
Lemma lem7561322 : term818.
Proof. exact (EQ_MP (@lem7561321) (@lem0)). Qed.
Lemma lem7561323 : term826.
Proof. exact (@lem7561312 (@lem7561322)). Qed.
Lemma lem7561325 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561326 : term818 = term824.
Proof. exact (@lem7561325 (NUMERAL 0) term470). Qed.
Lemma lem7561327 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561328 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561329 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561328 h1) (fun h1 : term824 = True => @lem7561327)). Qed.
Lemma lem7561330 : term824 = True.
Proof. exact (EQ_MP (@lem7561329) (@lem7561327)). Qed.
Lemma lem7561331 : term818 = True.
Proof. exact (TRANS (@lem7561326) (@lem7561330)). Qed.
Lemma lem7561332 : True = term818.
Proof. exact (SYM (@lem7561331)). Qed.
Lemma lem7561333 : term818.
Proof. exact (EQ_MP (@lem7561332) (@lem0)). Qed.
Lemma lem7561334 : term821 = term827.
Proof. exact (@lem7561323 (@lem7561333)). Qed.
Lemma lem7561336 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561337 : term532 = term533.
Proof. exact (@lem7561336 term470 term470). Qed.
Lemma lem7561338 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561339 : term535 = term470.
Proof. exact (EQ_MP (@lem7561338) (@lem940073)). Qed.
Lemma lem7561340 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561341 : term533 = term469.
Proof. exact (MK_COMB (@lem7561340) (@lem7561339)). Qed.
Lemma lem7561342 : term532 = term469.
Proof. exact (TRANS (@lem7561337) (@lem7561341)). Qed.
Lemma lem7561344 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561345 : term829 = term35.
Proof. exact (@lem7561344 term470). Qed.
Lemma lem7561346 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7561347 : term830 = term819.
Proof. exact (MK_COMB (@lem7561346) (@lem7561345)). Qed.
Lemma lem7561348 : term827 = term818.
Proof. exact (MK_COMB (@lem7561347) (@lem7561342)). Qed.
Lemma lem7561350 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561351 : term818 = term824.
Proof. exact (@lem7561350 (NUMERAL 0) term470). Qed.
Lemma lem7561352 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561353 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561354 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561353 h1) (fun h1 : term824 = True => @lem7561352)). Qed.
Lemma lem7561355 : term824 = True.
Proof. exact (EQ_MP (@lem7561354) (@lem7561352)). Qed.
Lemma lem7561356 : term818 = True.
Proof. exact (TRANS (@lem7561351) (@lem7561355)). Qed.
Lemma lem7561357 : term827 = True.
Proof. exact (TRANS (@lem7561348) (@lem7561356)). Qed.
Lemma lem7561358 : term821 = True.
Proof. exact (TRANS (@lem7561334) (@lem7561357)). Qed.
Lemma lem7561359 : term818 = True.
Proof. exact (TRANS (@lem7561311) (@lem7561358)). Qed.
Lemma lem7561360 : term817 = True.
Proof. exact (TRANS (@lem7561302) (@lem7561359)). Qed.
Lemma lem7561361 : True = term817.
Proof. exact (SYM (@lem7561360)). Qed.
Lemma lem7561362 : term817.
Proof. exact (EQ_MP (@lem7561361) (@lem0)). Qed.
Lemma lem7561363 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term887 _97559 _97561.
Proof. exact (conj (@lem7561362) (@lem7561222 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561365 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7561366 (_97559 : int) (_97561 : int) : term888 _97559 _97561.
Proof. exact (@lem7561365 term469 (term569 _97559 _97561)). Qed.
Lemma lem7561367 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term889 _97559 _97561.
Proof. exact (@lem7561366 _97559 _97561 (@lem7561363 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561368 (_97559 : int) (_97561 : int) : (term890 _97559 _97561) = (term569 _97559 _97561).
Proof. exact (@lem1982733 (term569 _97559 _97561)). Qed.
Lemma lem7561369 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7561370 (_97559 : int) (_97561 : int) : (term891 _97559 _97561) = (term572 _97559 _97561).
Proof. exact (MK_COMB (@lem7561369) (@lem7561368 _97559 _97561)). Qed.
Lemma lem7561371 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7561372 (_97559 : int) (_97561 : int) : (term889 _97559 _97561) = (term573 _97559 _97561).
Proof. exact (MK_COMB (@lem7561370 _97559 _97561) (@lem7561371)). Qed.
Lemma lem7561373 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term573 _97559 _97561.
Proof. exact (EQ_MP (@lem7561372 _97559 _97561) (@lem7561367 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561374 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term892 _97559 _97561.
Proof. exact (conj (@lem7561373 _97560 _97559 _97561 h1) (@lem7561299 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561376 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7561377 (_97559 : int) (_97561 : int) : term893 _97559 _97561.
Proof. exact (@lem7561376 (term569 _97559 _97561) (term587 _97559 _97561)). Qed.
Lemma lem7561378 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term894 _97559 _97561.
Proof. exact (@lem7561377 _97559 _97561 (@lem7561374 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561379 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = (term896 _97559 _97561).
Proof. exact (@lem1982753 (term570 _97559) (real_of_int _97559) (term897 _97561) (term570 _97561)). Qed.
Lemma lem7561380 (_97559 : int) : (term848 _97559) = (term849 _97559).
Proof. exact (@lem1982713 term523 (real_of_int _97559)). Qed.
Lemma lem7561382 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561383 : term469 = term549.
Proof. exact (@lem7561382 term470). Qed.
Lemma lem7561385 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7561386 : term523 = term524.
Proof. exact (@lem7561385 term470). Qed.
Lemma lem7561387 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561388 : term850 = term851.
Proof. exact (MK_COMB (@lem7561387) (@lem7561386)). Qed.
Lemma lem7561389 : term852 = term853.
Proof. exact (MK_COMB (@lem7561388) (@lem7561383)). Qed.
Lemma lem7561390 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7561392 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561393 : term818 = term824.
Proof. exact (@lem7561392 (NUMERAL 0) term470). Qed.
Lemma lem7561394 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561395 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561396 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561395 h1) (fun h1 : term824 = True => @lem7561394)). Qed.
Lemma lem7561397 : term824 = True.
Proof. exact (EQ_MP (@lem7561396) (@lem7561394)). Qed.
Lemma lem7561398 : term818 = True.
Proof. exact (TRANS (@lem7561393) (@lem7561397)). Qed.
Lemma lem7561399 : True = term818.
Proof. exact (SYM (@lem7561398)). Qed.
Lemma lem7561400 : term818.
Proof. exact (EQ_MP (@lem7561399) (@lem0)). Qed.
Lemma lem7561401 : term855.
Proof. exact (@lem7561390 (@lem7561400)). Qed.
Lemma lem7561403 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561404 : term818 = term824.
Proof. exact (@lem7561403 (NUMERAL 0) term470). Qed.
Lemma lem7561405 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561406 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561407 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561406 h1) (fun h1 : term824 = True => @lem7561405)). Qed.
Lemma lem7561408 : term824 = True.
Proof. exact (EQ_MP (@lem7561407) (@lem7561405)). Qed.
Lemma lem7561409 : term818 = True.
Proof. exact (TRANS (@lem7561404) (@lem7561408)). Qed.
Lemma lem7561410 : True = term818.
Proof. exact (SYM (@lem7561409)). Qed.
Lemma lem7561411 : term818.
Proof. exact (EQ_MP (@lem7561410) (@lem0)). Qed.
Lemma lem7561412 : term856.
Proof. exact (@lem7561401 (@lem7561411)). Qed.
Lemma lem7561414 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561415 : term818 = term824.
Proof. exact (@lem7561414 (NUMERAL 0) term470). Qed.
Lemma lem7561416 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561417 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561418 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561417 h1) (fun h1 : term824 = True => @lem7561416)). Qed.
Lemma lem7561419 : term824 = True.
Proof. exact (EQ_MP (@lem7561418) (@lem7561416)). Qed.
Lemma lem7561420 : term818 = True.
Proof. exact (TRANS (@lem7561415) (@lem7561419)). Qed.
Lemma lem7561421 : True = term818.
Proof. exact (SYM (@lem7561420)). Qed.
Lemma lem7561422 : term818.
Proof. exact (EQ_MP (@lem7561421) (@lem0)). Qed.
Lemma lem7561423 : term857.
Proof. exact (@lem7561412 (@lem7561422)). Qed.
Lemma lem7561425 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561426 : term532 = term533.
Proof. exact (@lem7561425 term470 term470). Qed.
Lemma lem7561427 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561428 : term535 = term470.
Proof. exact (EQ_MP (@lem7561427) (@lem940073)). Qed.
Lemma lem7561429 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561430 : term533 = term469.
Proof. exact (MK_COMB (@lem7561429) (@lem7561428)). Qed.
Lemma lem7561431 : term532 = term469.
Proof. exact (TRANS (@lem7561426) (@lem7561430)). Qed.
Lemma lem7561433 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7561434 : term550 = term555.
Proof. exact (@lem7561433 term470 term470). Qed.
Lemma lem7561435 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561436 : term535 = term470.
Proof. exact (EQ_MP (@lem7561435) (@lem940073)). Qed.
Lemma lem7561437 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561438 : term533 = term469.
Proof. exact (MK_COMB (@lem7561437) (@lem7561436)). Qed.
Lemma lem7561439 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7561440 : term555 = term523.
Proof. exact (MK_COMB (@lem7561439) (@lem7561438)). Qed.
Lemma lem7561441 : term550 = term523.
Proof. exact (TRANS (@lem7561434) (@lem7561440)). Qed.
Lemma lem7561442 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561443 : term858 = term850.
Proof. exact (MK_COMB (@lem7561442) (@lem7561441)). Qed.
Lemma lem7561444 : term859 = term852.
Proof. exact (MK_COMB (@lem7561443) (@lem7561431)). Qed.
Lemma lem7561446 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7561447 : term852 = term35.
Proof. exact (@lem7561446 term470). Qed.
Lemma lem7561448 : term859 = term35.
Proof. exact (TRANS (@lem7561444) (@lem7561447)). Qed.
Lemma lem7561449 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7561450 : term861 = term218.
Proof. exact (MK_COMB (@lem7561449) (@lem7561448)). Qed.
Lemma lem7561451 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7561452 : term862 = term829.
Proof. exact (MK_COMB (@lem7561450) (@lem7561451)). Qed.
Lemma lem7561454 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561455 : term829 = term35.
Proof. exact (@lem7561454 term470). Qed.
Lemma lem7561456 : term862 = term35.
Proof. exact (TRANS (@lem7561452) (@lem7561455)). Qed.
Lemma lem7561458 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561459 : term532 = term533.
Proof. exact (@lem7561458 term470 term470). Qed.
Lemma lem7561460 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561461 : term535 = term470.
Proof. exact (EQ_MP (@lem7561460) (@lem940073)). Qed.
Lemma lem7561462 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561463 : term533 = term469.
Proof. exact (MK_COMB (@lem7561462) (@lem7561461)). Qed.
Lemma lem7561464 : term532 = term469.
Proof. exact (TRANS (@lem7561459) (@lem7561463)). Qed.
Lemma lem7561465 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7561466 : term863 = term829.
Proof. exact (MK_COMB (@lem7561465) (@lem7561464)). Qed.
Lemma lem7561468 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561469 : term829 = term35.
Proof. exact (@lem7561468 term470). Qed.
Lemma lem7561470 : term863 = term35.
Proof. exact (TRANS (@lem7561466) (@lem7561469)). Qed.
Lemma lem7561471 : term35 = term863.
Proof. exact (SYM (@lem7561470)). Qed.
Lemma lem7561472 : term862 = term863.
Proof. exact (TRANS (@lem7561456) (@lem7561471)). Qed.
Lemma lem7561473 : term853 = term520.
Proof. exact (@lem7561423 (@lem7561472)). Qed.
Lemma lem7561474 : term852 = term520.
Proof. exact (TRANS (@lem7561389) (@lem7561473)). Qed.
Lemma lem7561476 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7561477 : term520 = term35.
Proof. exact (@lem7561476 term35). Qed.
Lemma lem7561478 : term852 = term35.
Proof. exact (TRANS (@lem7561474) (@lem7561477)). Qed.
Lemma lem7561479 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7561480 : term864 = term218.
Proof. exact (MK_COMB (@lem7561479) (@lem7561478)). Qed.
Lemma lem7561481 (_97559 : int) : (real_of_int _97559) = (real_of_int _97559).
Proof. exact (eq_refl (real_of_int _97559)). Qed.
Lemma lem7561482 (_97559 : int) : (term849 _97559) = (term865 _97559).
Proof. exact (MK_COMB (@lem7561480) (@lem7561481 _97559)). Qed.
Lemma lem7561483 (_97559 : int) : (term848 _97559) = (term865 _97559).
Proof. exact (TRANS (@lem7561380 _97559) (@lem7561482 _97559)). Qed.
Lemma lem7561484 (_97559 : int) : (term865 _97559) = term35.
Proof. exact (@lem1982719 (real_of_int _97559)). Qed.
Lemma lem7561485 (_97559 : int) : (term848 _97559) = term35.
Proof. exact (TRANS (@lem7561483 _97559) (@lem7561484 _97559)). Qed.
Lemma lem7561486 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561487 (_97559 : int) : (term866 _97559) = term560.
Proof. exact (MK_COMB (@lem7561486) (@lem7561485 _97559)). Qed.
Lemma lem7561488 (_97561 : int) : (term898 _97561) = (term899 _97561).
Proof. exact (@lem1982759 (real_of_int _97561) (term570 _97561) term523). Qed.
Lemma lem7561489 (_97561 : int) : (term900 _97561) = (term849 _97561).
Proof. exact (@lem1982715 term523 (real_of_int _97561)). Qed.
Lemma lem7561491 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561492 : term469 = term549.
Proof. exact (@lem7561491 term470). Qed.
Lemma lem7561494 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7561495 : term523 = term524.
Proof. exact (@lem7561494 term470). Qed.
Lemma lem7561496 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561497 : term850 = term851.
Proof. exact (MK_COMB (@lem7561496) (@lem7561495)). Qed.
Lemma lem7561498 : term852 = term853.
Proof. exact (MK_COMB (@lem7561497) (@lem7561492)). Qed.
Lemma lem7561499 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7561501 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561502 : term818 = term824.
Proof. exact (@lem7561501 (NUMERAL 0) term470). Qed.
Lemma lem7561503 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561504 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561505 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561504 h1) (fun h1 : term824 = True => @lem7561503)). Qed.
Lemma lem7561506 : term824 = True.
Proof. exact (EQ_MP (@lem7561505) (@lem7561503)). Qed.
Lemma lem7561507 : term818 = True.
Proof. exact (TRANS (@lem7561502) (@lem7561506)). Qed.
Lemma lem7561508 : True = term818.
Proof. exact (SYM (@lem7561507)). Qed.
Lemma lem7561509 : term818.
Proof. exact (EQ_MP (@lem7561508) (@lem0)). Qed.
Lemma lem7561510 : term855.
Proof. exact (@lem7561499 (@lem7561509)). Qed.
Lemma lem7561512 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561513 : term818 = term824.
Proof. exact (@lem7561512 (NUMERAL 0) term470). Qed.
Lemma lem7561514 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561515 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561516 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561515 h1) (fun h1 : term824 = True => @lem7561514)). Qed.
Lemma lem7561517 : term824 = True.
Proof. exact (EQ_MP (@lem7561516) (@lem7561514)). Qed.
Lemma lem7561518 : term818 = True.
Proof. exact (TRANS (@lem7561513) (@lem7561517)). Qed.
Lemma lem7561519 : True = term818.
Proof. exact (SYM (@lem7561518)). Qed.
Lemma lem7561520 : term818.
Proof. exact (EQ_MP (@lem7561519) (@lem0)). Qed.
Lemma lem7561521 : term856.
Proof. exact (@lem7561510 (@lem7561520)). Qed.
Lemma lem7561523 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561524 : term818 = term824.
Proof. exact (@lem7561523 (NUMERAL 0) term470). Qed.
Lemma lem7561525 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561526 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561527 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561526 h1) (fun h1 : term824 = True => @lem7561525)). Qed.
Lemma lem7561528 : term824 = True.
Proof. exact (EQ_MP (@lem7561527) (@lem7561525)). Qed.
Lemma lem7561529 : term818 = True.
Proof. exact (TRANS (@lem7561524) (@lem7561528)). Qed.
Lemma lem7561530 : True = term818.
Proof. exact (SYM (@lem7561529)). Qed.
Lemma lem7561531 : term818.
Proof. exact (EQ_MP (@lem7561530) (@lem0)). Qed.
Lemma lem7561532 : term857.
Proof. exact (@lem7561521 (@lem7561531)). Qed.
Lemma lem7561534 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561535 : term532 = term533.
Proof. exact (@lem7561534 term470 term470). Qed.
Lemma lem7561536 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561537 : term535 = term470.
Proof. exact (EQ_MP (@lem7561536) (@lem940073)). Qed.
Lemma lem7561538 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561539 : term533 = term469.
Proof. exact (MK_COMB (@lem7561538) (@lem7561537)). Qed.
Lemma lem7561540 : term532 = term469.
Proof. exact (TRANS (@lem7561535) (@lem7561539)). Qed.
Lemma lem7561542 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7561543 : term550 = term555.
Proof. exact (@lem7561542 term470 term470). Qed.
Lemma lem7561544 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561545 : term535 = term470.
Proof. exact (EQ_MP (@lem7561544) (@lem940073)). Qed.
Lemma lem7561546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561547 : term533 = term469.
Proof. exact (MK_COMB (@lem7561546) (@lem7561545)). Qed.
Lemma lem7561548 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7561549 : term555 = term523.
Proof. exact (MK_COMB (@lem7561548) (@lem7561547)). Qed.
Lemma lem7561550 : term550 = term523.
Proof. exact (TRANS (@lem7561543) (@lem7561549)). Qed.
Lemma lem7561551 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561552 : term858 = term850.
Proof. exact (MK_COMB (@lem7561551) (@lem7561550)). Qed.
Lemma lem7561553 : term859 = term852.
Proof. exact (MK_COMB (@lem7561552) (@lem7561540)). Qed.
Lemma lem7561555 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7561556 : term852 = term35.
Proof. exact (@lem7561555 term470). Qed.
Lemma lem7561557 : term859 = term35.
Proof. exact (TRANS (@lem7561553) (@lem7561556)). Qed.
Lemma lem7561558 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7561559 : term861 = term218.
Proof. exact (MK_COMB (@lem7561558) (@lem7561557)). Qed.
Lemma lem7561560 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7561561 : term862 = term829.
Proof. exact (MK_COMB (@lem7561559) (@lem7561560)). Qed.
Lemma lem7561563 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561564 : term829 = term35.
Proof. exact (@lem7561563 term470). Qed.
Lemma lem7561565 : term862 = term35.
Proof. exact (TRANS (@lem7561561) (@lem7561564)). Qed.
Lemma lem7561567 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7561568 : term532 = term533.
Proof. exact (@lem7561567 term470 term470). Qed.
Lemma lem7561569 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561570 : term535 = term470.
Proof. exact (EQ_MP (@lem7561569) (@lem940073)). Qed.
Lemma lem7561571 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561572 : term533 = term469.
Proof. exact (MK_COMB (@lem7561571) (@lem7561570)). Qed.
Lemma lem7561573 : term532 = term469.
Proof. exact (TRANS (@lem7561568) (@lem7561572)). Qed.
Lemma lem7561574 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7561575 : term863 = term829.
Proof. exact (MK_COMB (@lem7561574) (@lem7561573)). Qed.
Lemma lem7561577 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561578 : term829 = term35.
Proof. exact (@lem7561577 term470). Qed.
Lemma lem7561579 : term863 = term35.
Proof. exact (TRANS (@lem7561575) (@lem7561578)). Qed.
Lemma lem7561580 : term35 = term863.
Proof. exact (SYM (@lem7561579)). Qed.
Lemma lem7561581 : term862 = term863.
Proof. exact (TRANS (@lem7561565) (@lem7561580)). Qed.
Lemma lem7561582 : term853 = term520.
Proof. exact (@lem7561532 (@lem7561581)). Qed.
Lemma lem7561583 : term852 = term520.
Proof. exact (TRANS (@lem7561498) (@lem7561582)). Qed.
Lemma lem7561585 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7561586 : term520 = term35.
Proof. exact (@lem7561585 term35). Qed.
Lemma lem7561587 : term852 = term35.
Proof. exact (TRANS (@lem7561583) (@lem7561586)). Qed.
Lemma lem7561588 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7561589 : term864 = term218.
Proof. exact (MK_COMB (@lem7561588) (@lem7561587)). Qed.
Lemma lem7561590 (_97561 : int) : (real_of_int _97561) = (real_of_int _97561).
Proof. exact (eq_refl (real_of_int _97561)). Qed.
Lemma lem7561591 (_97561 : int) : (term849 _97561) = (term865 _97561).
Proof. exact (MK_COMB (@lem7561589) (@lem7561590 _97561)). Qed.
Lemma lem7561592 (_97561 : int) : (term900 _97561) = (term865 _97561).
Proof. exact (TRANS (@lem7561489 _97561) (@lem7561591 _97561)). Qed.
Lemma lem7561593 (_97561 : int) : (term865 _97561) = term35.
Proof. exact (@lem1982719 (real_of_int _97561)). Qed.
Lemma lem7561594 (_97561 : int) : (term900 _97561) = term35.
Proof. exact (TRANS (@lem7561592 _97561) (@lem7561593 _97561)). Qed.
Lemma lem7561595 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7561596 (_97561 : int) : (term901 _97561) = term560.
Proof. exact (MK_COMB (@lem7561595) (@lem7561594 _97561)). Qed.
Lemma lem7561597 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7561598 (_97561 : int) : (term899 _97561) = term867.
Proof. exact (MK_COMB (@lem7561596 _97561) (@lem7561597)). Qed.
Lemma lem7561599 (_97561 : int) : (term898 _97561) = term867.
Proof. exact (TRANS (@lem7561488 _97561) (@lem7561598 _97561)). Qed.
Lemma lem7561600 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7561601 (_97561 : int) : (term898 _97561) = term523.
Proof. exact (TRANS (@lem7561599 _97561) (@lem7561600)). Qed.
Lemma lem7561602 (_97559 : int) (_97561 : int) : (term896 _97559 _97561) = term867.
Proof. exact (MK_COMB (@lem7561487 _97559) (@lem7561601 _97561)). Qed.
Lemma lem7561603 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term867.
Proof. exact (TRANS (@lem7561379 _97559 _97561) (@lem7561602 _97559 _97561)). Qed.
Lemma lem7561604 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7561605 (_97559 : int) (_97561 : int) : (term895 _97559 _97561) = term523.
Proof. exact (TRANS (@lem7561603 _97559 _97561) (@lem7561604)). Qed.
Lemma lem7561606 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7561607 (_97559 : int) (_97561 : int) : (term902 _97559 _97561) = term869.
Proof. exact (MK_COMB (@lem7561606) (@lem7561605 _97559 _97561)). Qed.
Lemma lem7561608 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7561609 (_97559 : int) (_97561 : int) : (term894 _97559 _97561) = term870.
Proof. exact (MK_COMB (@lem7561607 _97559 _97561) (@lem7561608)). Qed.
Lemma lem7561610 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : term870.
Proof. exact (EQ_MP (@lem7561609 _97559 _97561) (@lem7561378 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561612 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7561613 : term870 = term871.
Proof. exact (@lem7561612 term35 term523). Qed.
Lemma lem7561615 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7561616 : term523 = term524.
Proof. exact (@lem7561615 term470). Qed.
Lemma lem7561618 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7561619 : term35 = term520.
Proof. exact (@lem7561618 (NUMERAL 0)). Qed.
Lemma lem7561620 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7561621 : term457 = term872.
Proof. exact (MK_COMB (@lem7561620) (@lem7561619)). Qed.
Lemma lem7561622 : term871 = term873.
Proof. exact (MK_COMB (@lem7561621) (@lem7561616)). Qed.
Lemma lem7561623 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7561625 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561626 : term818 = term824.
Proof. exact (@lem7561625 (NUMERAL 0) term470). Qed.
Lemma lem7561627 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561628 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561629 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561628 h1) (fun h1 : term824 = True => @lem7561627)). Qed.
Lemma lem7561630 : term824 = True.
Proof. exact (EQ_MP (@lem7561629) (@lem7561627)). Qed.
Lemma lem7561631 : term818 = True.
Proof. exact (TRANS (@lem7561626) (@lem7561630)). Qed.
Lemma lem7561632 : True = term818.
Proof. exact (SYM (@lem7561631)). Qed.
Lemma lem7561633 : term818.
Proof. exact (EQ_MP (@lem7561632) (@lem0)). Qed.
Lemma lem7561634 : term875.
Proof. exact (@lem7561623 (@lem7561633)). Qed.
Lemma lem7561636 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7561637 : term818 = term824.
Proof. exact (@lem7561636 (NUMERAL 0) term470). Qed.
Lemma lem7561638 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561639 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7561640 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561639 h1) (fun h1 : term824 = True => @lem7561638)). Qed.
Lemma lem7561641 : term824 = True.
Proof. exact (EQ_MP (@lem7561640) (@lem7561638)). Qed.
Lemma lem7561642 : term818 = True.
Proof. exact (TRANS (@lem7561637) (@lem7561641)). Qed.
Lemma lem7561643 : True = term818.
Proof. exact (SYM (@lem7561642)). Qed.
Lemma lem7561644 : term818.
Proof. exact (EQ_MP (@lem7561643) (@lem0)). Qed.
Lemma lem7561645 : term873 = term876.
Proof. exact (@lem7561634 (@lem7561644)). Qed.
Lemma lem7561647 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7561648 : term550 = term555.
Proof. exact (@lem7561647 term470 term470). Qed.
Lemma lem7561649 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7561650 : term535 = term470.
Proof. exact (EQ_MP (@lem7561649) (@lem940073)). Qed.
Lemma lem7561651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7561652 : term533 = term469.
Proof. exact (MK_COMB (@lem7561651) (@lem7561650)). Qed.
Lemma lem7561653 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7561654 : term555 = term523.
Proof. exact (MK_COMB (@lem7561653) (@lem7561652)). Qed.
Lemma lem7561655 : term550 = term523.
Proof. exact (TRANS (@lem7561648) (@lem7561654)). Qed.
Lemma lem7561657 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7561658 : term829 = term35.
Proof. exact (@lem7561657 term470). Qed.
Lemma lem7561659 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7561660 : term877 = term457.
Proof. exact (MK_COMB (@lem7561659) (@lem7561658)). Qed.
Lemma lem7561661 : term876 = term871.
Proof. exact (MK_COMB (@lem7561660) (@lem7561655)). Qed.
Lemma lem7561663 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7561664 : term871 = term880.
Proof. exact (@lem7561663 (NUMERAL 0) term470). Qed.
Lemma lem7561665 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7561666 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7561667 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7561666 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7561665)). Qed.
Lemma lem7561668 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7561667) (@lem7561665)). Qed.
Lemma lem7561669 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7561670 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7561671 : term881 = (and True).
Proof. exact (MK_COMB (@lem7561670) (@lem7561669)). Qed.
Lemma lem7561672 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7561671) (@lem7561668)). Qed.
Lemma lem7561674 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7561675 : term880 = False.
Proof. exact (TRANS (@lem7561672) (@lem7561674)). Qed.
Lemma lem7561676 : term871 = False.
Proof. exact (TRANS (@lem7561664) (@lem7561675)). Qed.
Lemma lem7561677 : term876 = False.
Proof. exact (TRANS (@lem7561661) (@lem7561676)). Qed.
Lemma lem7561678 : term873 = False.
Proof. exact (TRANS (@lem7561645) (@lem7561677)). Qed.
Lemma lem7561679 : term871 = False.
Proof. exact (TRANS (@lem7561622) (@lem7561678)). Qed.
Lemma lem7561680 : term870 = False.
Proof. exact (TRANS (@lem7561613) (@lem7561679)). Qed.
Lemma lem7561681 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term669 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7561680) (@lem7561610 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561682 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term814 _97560 _97559 _97561) : False.
Proof. exact (or_elim (@lem7560389 _97560 _97559 _97561 h1) (fun h0 : term812 _97559 _97560 _97561 => @lem7561214 _97559 _97560 _97561 h0) (fun h0 : term669 _97560 _97559 _97561 => @lem7561681 _97560 _97559 _97561 h0)). Qed.
Lemma lem7561683 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term816 _97560 _97559 _97561) : False.
Proof. exact (or_elim (@lem7558724 _97560 _97559 _97561 h1) (fun h0 : term798 _97560 _97559 _97561 => @lem7560388 _97560 _97559 _97561 h0) (fun h0 : term814 _97560 _97559 _97561 => @lem7561682 _97560 _97559 _97561 h0)). Qed.
Lemma lem7561684 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term683 _97560 _97559 _97561) : term683 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7561685 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term683 _97560 _97559 _97561) : term816 _97560 _97559 _97561.
Proof. exact (EQ_MP (@lem7558723 _97560 _97559 _97561) (@lem7561684 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561686 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term683 _97560 _97559 _97561) : (term816 _97560 _97559 _97561) = False.
Proof. exact (prop_ext (fun h2 : term816 _97560 _97559 _97561 => @lem7561683 _97560 _97559 _97561 h2) (fun h2 : False => @lem7561685 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561687 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term683 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7561686 _97560 _97559 _97561 h1) (@lem7561685 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561688 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term515 _97560 _97559 _97561) : term515 _97560 _97559 _97561.
Proof. exact (h1). Qed.
Lemma lem7561689 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term515 _97560 _97559 _97561) : term683 _97560 _97559 _97561.
Proof. exact (EQ_MP (@lem7557998 _97560 _97559 _97561) (@lem7561688 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561690 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term515 _97560 _97559 _97561) : (term683 _97560 _97559 _97561) = False.
Proof. exact (prop_ext (fun h2 : term683 _97560 _97559 _97561 => @lem7561687 _97560 _97559 _97561 h2) (fun h2 : False => @lem7561689 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561691 (_97560 : int) (_97559 : int) (_97561 : int) (h1 : term515 _97560 _97559 _97561) : False.
Proof. exact (EQ_MP (@lem7561690 _97560 _97559 _97561 h1) (@lem7561689 _97560 _97559 _97561 h1)). Qed.
Lemma lem7561692 (_97560 : int) (_97559 : int) (_97561 : int) : term904 _97560 _97559 _97561.
Proof. exact (fun h0 : term515 _97560 _97559 _97561 => @lem7561691 _97560 _97559 _97561 h0). Qed.
Lemma lem7561693 (_97560 : int) (_97559 : int) (_97561 : int) : term905 _97560 _97559 _97561.
Proof. exact (@lem1386578 (term906 _97560 _97559 _97561)). Qed.
Lemma lem7561696 (_97560 : int) (_97559 : int) (_97561 : int) : term906 _97560 _97559 _97561.
Proof. exact (@lem7561693 _97560 _97559 _97561 (@lem7561692 _97560 _97559 _97561)). Qed.
Lemma lem7561697 (_97560 : int) (_97561 : int) (_97559 : int) : (term513 _97560 _97559 _97561) = (term449 _97560 _97561 _97559).
Proof. exact (SYM (@lem7557021 _97560 _97559 _97561)). Qed.
Lemma lem7561698 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7561699 (_97560 : int) (_97561 : int) (_97559 : int) : (term906 _97560 _97559 _97561) = (term390 _97560 _97561 _97559).
Proof. exact (MK_COMB (@lem7561698) (@lem7561697 _97560 _97561 _97559)). Qed.
Lemma lem7561700 (_97560 : int) (_97561 : int) (_97559 : int) : term390 _97560 _97561 _97559.
Proof. exact (EQ_MP (@lem7561699 _97560 _97561 _97559) (@lem7561696 _97560 _97559 _97561)). Qed.
Lemma lem7561701 (_97560 : int) (_97561 : int) (_97559 : int) : term391 _97560 _97561 _97559.
Proof. exact (EQ_MP (@lem7556612 _97560 _97561 _97559) (@lem7561700 _97560 _97561 _97559)). Qed.
Lemma lem7561702 (n : nat) (x : nat) (m : nat) : term907 n x m.
Proof. exact (@lem7561701 (int_of_num n) (int_of_num x) (int_of_num m)). Qed.
Lemma lem7561703 (n : nat) (x : nat) (m : nat) : term908 n x m.
Proof. exact (@lem7561702 n x m (@lem7556605 m)). Qed.
Lemma lem7561704 (n : nat) (x : nat) (m : nat) : term909 n x m.
Proof. exact (@lem7561703 n x m (@lem7556608 n)). Qed.
Lemma lem7561705 (n : nat) (x : nat) (m : nat) : term386 n x m.
Proof. exact (@lem7561704 n x m (@lem7556611 x)). Qed.
Lemma lem7561706 (n : nat) (m : nat) : term388 n m.
Proof. exact (fun x : nat => @lem7561705 n x m). Qed.
Lemma lem7561707 (n : nat) (m : nat) : (term388 n m) = (term314 n m).
Proof. exact (SYM (@lem7556602 n m)). Qed.
Lemma lem7561708 (n : nat) (m : nat) : term314 n m.
Proof. exact (EQ_MP (@lem7561707 n m) (@lem7561706 n m)). Qed.
Lemma lem7561709 (n : nat) (m : nat) : (term314 n m) = ((term314 n m) = True).
Proof. exact (@lem7 (term314 n m)). Qed.
Lemma lem7561710 (n : nat) (m : nat) : (term314 n m) = True.
Proof. exact (EQ_MP (@lem7561709 n m) (@lem7561708 n m)). Qed.
Lemma lem7561711 (n : nat) (m : nat) : True = (term314 n m).
Proof. exact (SYM (@lem7561710 n m)). Qed.
Lemma lem7561712 (n : nat) (m : nat) : term314 n m.
Proof. exact (EQ_MP (@lem7561711 n m) (@lem0)). Qed.
Lemma lem7561742 (m : nat) (x : nat) (n : nat) : ((term292 x n) = (term328 m x n)) = ((term292 x n) = (term328 m x n)).
Proof. exact (eq_refl ((term292 x n) = (term328 m x n))). Qed.
Lemma lem7561743 (m : nat) (n : nat) : (term330 m n) = (term330 m n).
Proof. exact (fun_ext (fun x : nat => @lem7561742 m x n)). Qed.
Lemma lem7561744 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7561746 (m : nat) (n : nat) : (term331 m n) = (term331 m n).
Proof. exact (MK_COMB (@lem7561744) (@lem7561743 m n)). Qed.
Lemma lem7561755 (x : nat) (n : nat) : (term332 x n) = (term333 x n).
Proof. exact (@lem17045 (term334 x) (Peano.le x n)). Qed.
Lemma lem7561767 (x : nat) (m : nat) (n : nat) : (term335 x m n) = (term336 x m n).
Proof. exact (@lem17045 (term334 x) (term337 x m n)). Qed.
Lemma lem7561771 (x : nat) (n : nat) : (term338 x n) = (term338 x n).
Proof. exact (eq_refl (term338 x n)). Qed.
Lemma lem7561773 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7561774 (x : nat) (m : nat) (n : nat) : (term339 x m n) = (term340 x m n).
Proof. exact (MK_COMB (@lem7561773) (@lem7561767 x m n)). Qed.
Lemma lem7561775 (m : nat) (x : nat) (n : nat) : (term910 m x n) = (term911 m x n).
Proof. exact (MK_COMB (@lem7561774 x m n) (@lem7561771 x n)). Qed.
Lemma lem7561776 (m : nat) (x : nat) (n : nat) : (term912 m x n) = (term910 m x n).
Proof. exact (@lem17045 (term309 x m n) (Peano.le x n)). Qed.
Lemma lem7561777 (m : nat) (x : nat) (n : nat) : (term912 m x n) = (term911 m x n).
Proof. exact (TRANS (@lem7561776 m x n) (@lem7561775 m x n)). Qed.
Lemma lem7561780 (m : nat) (x : nat) (n : nat) : (term328 m x n) = (term328 m x n).
Proof. exact (eq_refl (term328 m x n)). Qed.
Lemma lem7561781 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7561782 (x : nat) (n : nat) : (term344 x n) = (term345 x n).
Proof. exact (MK_COMB (@lem7561781) (@lem7561755 x n)). Qed.
Lemma lem7561783 (m : nat) (x : nat) (n : nat) : (term913 m x n) = (term914 m x n).
Proof. exact (MK_COMB (@lem7561782 x n) (@lem7561780 m x n)). Qed.
Lemma lem7561785 (x : nat) (n : nat) : (term348 x n) = (term348 x n).
Proof. exact (eq_refl (term348 x n)). Qed.
Lemma lem7561786 (m : nat) (x : nat) (n : nat) : (term915 m x n) = (term916 m x n).
Proof. exact (MK_COMB (@lem7561785 x n) (@lem7561777 m x n)). Qed.
Lemma lem7561787 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7561788 (m : nat) (x : nat) (n : nat) : (term917 m x n) = (term918 m x n).
Proof. exact (MK_COMB (@lem7561787) (@lem7561786 m x n)). Qed.
Lemma lem7561789 (m : nat) (x : nat) (n : nat) : (term919 m x n) = (term920 m x n).
Proof. exact (MK_COMB (@lem7561788 m x n) (@lem7561783 m x n)). Qed.
Lemma lem7561790 (m : nat) (x : nat) (n : nat) : ((term292 x n) = (term328 m x n)) = (term919 m x n).
Proof. exact (@lem17784 (term292 x n) (term328 m x n)). Qed.
Lemma lem7561791 (m : nat) (x : nat) (n : nat) : ((term292 x n) = (term328 m x n)) = (term920 m x n).
Proof. exact (TRANS (@lem7561790 m x n) (@lem7561789 m x n)). Qed.
Lemma lem7561792 (m : nat) (n : nat) : (term330 m n) = (term921 m n).
Proof. exact (fun_ext (fun x : nat => @lem7561791 m x n)). Qed.
Lemma lem7561793 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7561794 (m : nat) (n : nat) : (term331 m n) = (term922 m n).
Proof. exact (MK_COMB (@lem7561793) (@lem7561792 m n)). Qed.
Lemma lem7561795 (m : nat) (n : nat) : (term331 m n) = (term922 m n).
Proof. exact (TRANS (@lem7561746 m n) (@lem7561794 m n)). Qed.
Lemma lem7561796 (m : nat) (x : nat) (n : nat) : (term920 m x n) = (term920 m x n).
Proof. exact (eq_refl (term920 m x n)). Qed.
Lemma lem7561797 (m : nat) (n : nat) : (term921 m n) = (term921 m n).
Proof. exact (fun_ext (fun x : nat => @lem7561796 m x n)). Qed.
Lemma lem7561798 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7561799 (m : nat) (n : nat) : (term922 m n) = (term922 m n).
Proof. exact (MK_COMB (@lem7561798) (@lem7561797 m n)). Qed.
Lemma lem7561828 (m : nat) (n : nat) : (term331 m n) = (term922 m n).
Proof. exact (TRANS (@lem7561795 m n) (@lem7561799 m n)). Qed.
Lemma lem7561915 (m : nat) (x : nat) (n : nat) : (term920 m x n) = (term920 m x n).
Proof. exact (eq_refl (term920 m x n)). Qed.
Lemma lem7561916 (m : nat) (n : nat) : (term921 m n) = (term921 m n).
Proof. exact (fun_ext (fun x : nat => @lem7561915 m x n)). Qed.
Lemma lem7561917 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7561918 (m : nat) (n : nat) : (term922 m n) = (term922 m n).
Proof. exact (MK_COMB (@lem7561917) (@lem7561916 m n)). Qed.
Lemma lem7561921 (m : nat) (n : nat) : (term331 m n) = (term922 m n).
Proof. exact (TRANS (@lem7561828 m n) (@lem7561918 m n)). Qed.
Lemma lem7561923 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561924 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7561923 (NUMERAL 0) x). Qed.
Lemma lem7561925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7561926 (x : nat) : (term359 x) = (term360 x).
Proof. exact (MK_COMB (@lem7561925) (@lem7561924 x)). Qed.
Lemma lem7561928 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561929 (x : nat) (n : nat) : (Peano.le x n) = (term357 x n).
Proof. exact (@lem7561928 x n). Qed.
Lemma lem7561930 (x : nat) (n : nat) : (term292 x n) = (term361 x n).
Proof. exact (MK_COMB (@lem7561926 x) (@lem7561929 x n)). Qed.
Lemma lem7561931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7561932 (x : nat) (n : nat) : (term348 x n) = (term362 x n).
Proof. exact (MK_COMB (@lem7561931) (@lem7561930 x n)). Qed.
Lemma lem7561934 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561935 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7561934 (NUMERAL 0) x). Qed.
Lemma lem7561936 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7561937 (x : nat) : (term363 x) = (term364 x).
Proof. exact (MK_COMB (@lem7561936) (@lem7561935 x)). Qed.
Lemma lem7561938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7561939 (x : nat) : (term365 x) = (term366 x).
Proof. exact (MK_COMB (@lem7561938) (@lem7561937 x)). Qed.
Lemma lem7561941 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561942 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term367 x m n).
Proof. exact (@lem7561941 x (Nat.max m n)). Qed.
Lemma lem7561944 (m : nat) (n : nat) : (term368 m n) = (term369 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem7561945 (x : nat) : (term370 x) = (term370 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem7561946 (x : nat) (m : nat) (n : nat) : (term367 x m n) = (term371 x m n).
Proof. exact (MK_COMB (@lem7561945 x) (@lem7561944 m n)). Qed.
Lemma lem7561947 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term371 x m n).
Proof. exact (TRANS (@lem7561942 x m n) (@lem7561946 x m n)). Qed.
Lemma lem7561948 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7561949 (x : nat) (m : nat) (n : nat) : (term372 x m n) = (term373 x m n).
Proof. exact (MK_COMB (@lem7561948) (@lem7561947 x m n)). Qed.
Lemma lem7561950 (x : nat) (m : nat) (n : nat) : (term336 x m n) = (term374 x m n).
Proof. exact (MK_COMB (@lem7561939 x) (@lem7561949 x m n)). Qed.
Lemma lem7561951 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7561952 (x : nat) (m : nat) (n : nat) : (term340 x m n) = (term375 x m n).
Proof. exact (MK_COMB (@lem7561951) (@lem7561950 x m n)). Qed.
Lemma lem7561954 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561955 (x : nat) (n : nat) : (Peano.le x n) = (term357 x n).
Proof. exact (@lem7561954 x n). Qed.
Lemma lem7561956 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7561957 (x : nat) (n : nat) : (term338 x n) = (term376 x n).
Proof. exact (MK_COMB (@lem7561956) (@lem7561955 x n)). Qed.
Lemma lem7561958 (m : nat) (x : nat) (n : nat) : (term911 m x n) = (term923 m x n).
Proof. exact (MK_COMB (@lem7561952 x m n) (@lem7561957 x n)). Qed.
Lemma lem7561959 (m : nat) (x : nat) (n : nat) : (term916 m x n) = (term924 m x n).
Proof. exact (MK_COMB (@lem7561932 x n) (@lem7561958 m x n)). Qed.
Lemma lem7561960 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7561961 (m : nat) (x : nat) (n : nat) : (term918 m x n) = (term925 m x n).
Proof. exact (MK_COMB (@lem7561960) (@lem7561959 m x n)). Qed.
Lemma lem7561963 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561964 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7561963 (NUMERAL 0) x). Qed.
Lemma lem7561965 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7561966 (x : nat) : (term363 x) = (term364 x).
Proof. exact (MK_COMB (@lem7561965) (@lem7561964 x)). Qed.
Lemma lem7561967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7561968 (x : nat) : (term365 x) = (term366 x).
Proof. exact (MK_COMB (@lem7561967) (@lem7561966 x)). Qed.
Lemma lem7561970 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561971 (x : nat) (n : nat) : (Peano.le x n) = (term357 x n).
Proof. exact (@lem7561970 x n). Qed.
Lemma lem7561972 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7561973 (x : nat) (n : nat) : (term338 x n) = (term376 x n).
Proof. exact (MK_COMB (@lem7561972) (@lem7561971 x n)). Qed.
Lemma lem7561974 (x : nat) (n : nat) : (term333 x n) = (term380 x n).
Proof. exact (MK_COMB (@lem7561968 x) (@lem7561973 x n)). Qed.
Lemma lem7561975 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7561976 (x : nat) (n : nat) : (term345 x n) = (term381 x n).
Proof. exact (MK_COMB (@lem7561975) (@lem7561974 x n)). Qed.
Lemma lem7561978 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561979 (x : nat) : (term334 x) = (term358 x).
Proof. exact (@lem7561978 (NUMERAL 0) x). Qed.
Lemma lem7561980 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7561981 (x : nat) : (term359 x) = (term360 x).
Proof. exact (MK_COMB (@lem7561980) (@lem7561979 x)). Qed.
Lemma lem7561983 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561984 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term367 x m n).
Proof. exact (@lem7561983 x (Nat.max m n)). Qed.
Lemma lem7561986 (m : nat) (n : nat) : (term368 m n) = (term369 m n).
Proof. exact (EQ_MP (@lem2841375 m n) (@lem2841374 m n)). Qed.
Lemma lem7561987 (x : nat) : (term370 x) = (term370 x).
Proof. exact (eq_refl (term370 x)). Qed.
Lemma lem7561988 (x : nat) (m : nat) (n : nat) : (term367 x m n) = (term371 x m n).
Proof. exact (MK_COMB (@lem7561987 x) (@lem7561986 m n)). Qed.
Lemma lem7561989 (x : nat) (m : nat) (n : nat) : (term337 x m n) = (term371 x m n).
Proof. exact (TRANS (@lem7561984 x m n) (@lem7561988 x m n)). Qed.
Lemma lem7561990 (x : nat) (m : nat) (n : nat) : (term309 x m n) = (term382 x m n).
Proof. exact (MK_COMB (@lem7561981 x) (@lem7561989 x m n)). Qed.
Lemma lem7561991 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7561992 (x : nat) (m : nat) (n : nat) : (term310 x m n) = (term383 x m n).
Proof. exact (MK_COMB (@lem7561991) (@lem7561990 x m n)). Qed.
Lemma lem7561994 (m : nat) (n : nat) : (Peano.le m n) = (term357 m n).
Proof. exact (EQ_MP (@lem2841408 m n) (@lem2841407 m n)). Qed.
Lemma lem7561995 (x : nat) (n : nat) : (Peano.le x n) = (term357 x n).
Proof. exact (@lem7561994 x n). Qed.
Lemma lem7561996 (m : nat) (x : nat) (n : nat) : (term328 m x n) = (term926 m x n).
Proof. exact (MK_COMB (@lem7561992 x m n) (@lem7561995 x n)). Qed.
Lemma lem7561997 (m : nat) (x : nat) (n : nat) : (term914 m x n) = (term927 m x n).
Proof. exact (MK_COMB (@lem7561976 x n) (@lem7561996 m x n)). Qed.
Lemma lem7561998 (m : nat) (x : nat) (n : nat) : (term920 m x n) = (term928 m x n).
Proof. exact (MK_COMB (@lem7561961 m x n) (@lem7561997 m x n)). Qed.
Lemma lem7561999 (m : nat) (n : nat) : (term921 m n) = (term929 m n).
Proof. exact (fun_ext (fun x : nat => @lem7561998 m x n)). Qed.
Lemma lem7562000 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7562001 (m : nat) (n : nat) : (term922 m n) = (term930 m n).
Proof. exact (MK_COMB (@lem7562000) (@lem7561999 m n)). Qed.
Lemma lem7562002 (m : nat) (n : nat) : (term331 m n) = (term930 m n).
Proof. exact (TRANS (@lem7561921 m n) (@lem7562001 m n)). Qed.
Lemma lem7562003 (m : nat) : term389 m.
Proof. exact (@lem2307535 m). Qed.
Lemma lem7562004 (m : nat) : (term389 m) = (term358 m).
Proof. exact (eq_refl (term389 m)). Qed.
Lemma lem7562005 (m : nat) : term358 m.
Proof. exact (EQ_MP (@lem7562004 m) (@lem7562003 m)). Qed.
Lemma lem7562006 (n : nat) : term389 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem7562007 (n : nat) : (term389 n) = (term358 n).
Proof. exact (eq_refl (term389 n)). Qed.
Lemma lem7562008 (n : nat) : term358 n.
Proof. exact (EQ_MP (@lem7562007 n) (@lem7562006 n)). Qed.
Lemma lem7562009 (x : nat) : term389 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem7562010 (x : nat) : (term389 x) = (term358 x).
Proof. exact (eq_refl (term389 x)). Qed.
Lemma lem7562011 (x : nat) : term358 x.
Proof. exact (EQ_MP (@lem7562010 x) (@lem7562009 x)). Qed.
Lemma lem7562012 (_97569 : int) (_97571 : int) (_97570 : int) : (term931 _97569 _97571 _97570) = (term932 _97569 _97571 _97570).
Proof. exact (@lem2318604 (term932 _97569 _97571 _97570)). Qed.
Lemma lem7562051 (_97571 : int) (_97570 : int) : (term392 _97571 _97570) = (term393 _97571 _97570).
Proof. exact (@lem17045 (term394 _97571) (int_le _97571 _97570)). Qed.
Lemma lem7562054 (_97571 : int) : (term395 _97571) = (term394 _97571).
Proof. exact (@lem16933 (term394 _97571)). Qed.
Lemma lem7562057 (_97571 : int) (_97569 : int) (_97570 : int) : (term396 _97571 _97569 _97570) = (term397 _97571 _97569 _97570).
Proof. exact (@lem16933 (term397 _97571 _97569 _97570)). Qed.
Lemma lem7562058 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562059 (_97571 : int) : (term398 _97571) = (term399 _97571).
Proof. exact (MK_COMB (@lem7562058) (@lem7562054 _97571)). Qed.
Lemma lem7562060 (_97571 : int) (_97569 : int) (_97570 : int) : (term400 _97571 _97569 _97570) = (term401 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562059 _97571) (@lem7562057 _97571 _97569 _97570)). Qed.
Lemma lem7562061 (_97571 : int) (_97569 : int) (_97570 : int) : (term402 _97571 _97569 _97570) = (term400 _97571 _97569 _97570).
Proof. exact (@lem17160 (term403 _97571) (term404 _97571 _97569 _97570)). Qed.
Lemma lem7562062 (_97571 : int) (_97569 : int) (_97570 : int) : (term402 _97571 _97569 _97570) = (term401 _97571 _97569 _97570).
Proof. exact (TRANS (@lem7562061 _97571 _97569 _97570) (@lem7562060 _97571 _97569 _97570)). Qed.
Lemma lem7562065 (_97571 : int) (_97570 : int) : (term405 _97571 _97570) = (int_le _97571 _97570).
Proof. exact (@lem16933 (int_le _97571 _97570)). Qed.
Lemma lem7562066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562067 (_97571 : int) (_97569 : int) (_97570 : int) : (term406 _97571 _97569 _97570) = (term407 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562066) (@lem7562062 _97571 _97569 _97570)). Qed.
Lemma lem7562068 (_97569 : int) (_97571 : int) (_97570 : int) : (term933 _97569 _97571 _97570) = (term934 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562067 _97571 _97569 _97570) (@lem7562065 _97571 _97570)). Qed.
Lemma lem7562069 (_97569 : int) (_97571 : int) (_97570 : int) : (term935 _97569 _97571 _97570) = (term933 _97569 _97571 _97570).
Proof. exact (@lem17160 (term411 _97571 _97569 _97570) (term412 _97571 _97570)). Qed.
Lemma lem7562070 (_97569 : int) (_97571 : int) (_97570 : int) : (term935 _97569 _97571 _97570) = (term934 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562069 _97569 _97571 _97570) (@lem7562068 _97569 _97571 _97570)). Qed.
Lemma lem7562071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562072 (_97571 : int) (_97570 : int) : (term413 _97571 _97570) = (term414 _97571 _97570).
Proof. exact (MK_COMB (@lem7562071) (@lem7562051 _97571 _97570)). Qed.
Lemma lem7562073 (_97569 : int) (_97571 : int) (_97570 : int) : (term936 _97569 _97571 _97570) = (term937 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562072 _97571 _97570) (@lem7562070 _97569 _97571 _97570)). Qed.
Lemma lem7562074 (_97569 : int) (_97571 : int) (_97570 : int) : (term938 _97569 _97571 _97570) = (term936 _97569 _97571 _97570).
Proof. exact (@lem17160 (term418 _97571 _97570) (term939 _97569 _97571 _97570)). Qed.
Lemma lem7562075 (_97569 : int) (_97571 : int) (_97570 : int) : (term938 _97569 _97571 _97570) = (term937 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562074 _97569 _97571 _97570) (@lem7562073 _97569 _97571 _97570)). Qed.
Lemma lem7562078 (_97571 : int) : (term395 _97571) = (term394 _97571).
Proof. exact (@lem16933 (term394 _97571)). Qed.
Lemma lem7562081 (_97571 : int) (_97570 : int) : (term405 _97571 _97570) = (int_le _97571 _97570).
Proof. exact (@lem16933 (int_le _97571 _97570)). Qed.
Lemma lem7562082 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562083 (_97571 : int) : (term398 _97571) = (term399 _97571).
Proof. exact (MK_COMB (@lem7562082) (@lem7562078 _97571)). Qed.
Lemma lem7562084 (_97571 : int) (_97570 : int) : (term420 _97571 _97570) = (term418 _97571 _97570).
Proof. exact (MK_COMB (@lem7562083 _97571) (@lem7562081 _97571 _97570)). Qed.
Lemma lem7562085 (_97571 : int) (_97570 : int) : (term421 _97571 _97570) = (term420 _97571 _97570).
Proof. exact (@lem17160 (term403 _97571) (term412 _97571 _97570)). Qed.
Lemma lem7562086 (_97571 : int) (_97570 : int) : (term421 _97571 _97570) = (term418 _97571 _97570).
Proof. exact (TRANS (@lem7562085 _97571 _97570) (@lem7562084 _97571 _97570)). Qed.
Lemma lem7562093 (_97571 : int) (_97569 : int) (_97570 : int) : (term422 _97571 _97569 _97570) = (term411 _97571 _97569 _97570).
Proof. exact (@lem17045 (term394 _97571) (term397 _97571 _97569 _97570)). Qed.
Lemma lem7562094 (_97571 : int) (_97570 : int) : (term412 _97571 _97570) = (term412 _97571 _97570).
Proof. exact (eq_refl (term412 _97571 _97570)). Qed.
Lemma lem7562095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7562096 (_97571 : int) (_97569 : int) (_97570 : int) : (term423 _97571 _97569 _97570) = (term424 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562095) (@lem7562093 _97571 _97569 _97570)). Qed.
Lemma lem7562097 (_97569 : int) (_97571 : int) (_97570 : int) : (term940 _97569 _97571 _97570) = (term939 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562096 _97571 _97569 _97570) (@lem7562094 _97571 _97570)). Qed.
Lemma lem7562098 (_97569 : int) (_97571 : int) (_97570 : int) : (term941 _97569 _97571 _97570) = (term940 _97569 _97571 _97570).
Proof. exact (@lem17045 (term401 _97571 _97569 _97570) (int_le _97571 _97570)). Qed.
Lemma lem7562099 (_97569 : int) (_97571 : int) (_97570 : int) : (term941 _97569 _97571 _97570) = (term939 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562098 _97569 _97571 _97570) (@lem7562097 _97569 _97571 _97570)). Qed.
Lemma lem7562100 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562101 (_97571 : int) (_97570 : int) : (term427 _97571 _97570) = (term428 _97571 _97570).
Proof. exact (MK_COMB (@lem7562100) (@lem7562086 _97571 _97570)). Qed.
Lemma lem7562102 (_97569 : int) (_97571 : int) (_97570 : int) : (term942 _97569 _97571 _97570) = (term943 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562101 _97571 _97570) (@lem7562099 _97569 _97571 _97570)). Qed.
Lemma lem7562103 (_97569 : int) (_97571 : int) (_97570 : int) : (term944 _97569 _97571 _97570) = (term942 _97569 _97571 _97570).
Proof. exact (@lem17160 (term393 _97571 _97570) (term934 _97569 _97571 _97570)). Qed.
Lemma lem7562104 (_97569 : int) (_97571 : int) (_97570 : int) : (term944 _97569 _97571 _97570) = (term943 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562103 _97569 _97571 _97570) (@lem7562102 _97569 _97571 _97570)). Qed.
Lemma lem7562105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7562106 (_97569 : int) (_97571 : int) (_97570 : int) : (term945 _97569 _97571 _97570) = (term946 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562105) (@lem7562075 _97569 _97571 _97570)). Qed.
Lemma lem7562107 (_97569 : int) (_97571 : int) (_97570 : int) : (term947 _97569 _97571 _97570) = (term948 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562106 _97569 _97571 _97570) (@lem7562104 _97569 _97571 _97570)). Qed.
Lemma lem7562108 (_97569 : int) (_97571 : int) (_97570 : int) : (term949 _97569 _97571 _97570) = (term947 _97569 _97571 _97570).
Proof. exact (@lem17045 (term950 _97569 _97571 _97570) (term951 _97569 _97571 _97570)). Qed.
Lemma lem7562109 (_97569 : int) (_97571 : int) (_97570 : int) : (term949 _97569 _97571 _97570) = (term948 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562108 _97569 _97571 _97570) (@lem7562107 _97569 _97571 _97570)). Qed.
Lemma lem7562111 (_97571 : int) : (term399 _97571) = (term399 _97571).
Proof. exact (eq_refl (term399 _97571)). Qed.
Lemma lem7562112 (_97569 : int) (_97571 : int) (_97570 : int) : (term952 _97569 _97571 _97570) = (term953 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562111 _97571) (@lem7562109 _97569 _97571 _97570)). Qed.
Lemma lem7562113 (_97569 : int) (_97571 : int) (_97570 : int) : (term954 _97569 _97571 _97570) = (term952 _97569 _97571 _97570).
Proof. exact (@lem17362 (term394 _97571) (term955 _97569 _97571 _97570)). Qed.
Lemma lem7562114 (_97569 : int) (_97571 : int) (_97570 : int) : (term954 _97569 _97571 _97570) = (term953 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562113 _97569 _97571 _97570) (@lem7562112 _97569 _97571 _97570)). Qed.
Lemma lem7562116 (_97570 : int) : (term399 _97570) = (term399 _97570).
Proof. exact (eq_refl (term399 _97570)). Qed.
Lemma lem7562117 (_97569 : int) (_97571 : int) (_97570 : int) : (term956 _97569 _97571 _97570) = (term957 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562116 _97570) (@lem7562114 _97569 _97571 _97570)). Qed.
Lemma lem7562118 (_97569 : int) (_97571 : int) (_97570 : int) : (term958 _97569 _97571 _97570) = (term956 _97569 _97571 _97570).
Proof. exact (@lem17362 (term394 _97570) (term959 _97569 _97571 _97570)). Qed.
Lemma lem7562119 (_97569 : int) (_97571 : int) (_97570 : int) : (term958 _97569 _97571 _97570) = (term957 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562118 _97569 _97571 _97570) (@lem7562117 _97569 _97571 _97570)). Qed.
Lemma lem7562121 (_97569 : int) : (term399 _97569) = (term399 _97569).
Proof. exact (eq_refl (term399 _97569)). Qed.
Lemma lem7562122 (_97569 : int) (_97571 : int) (_97570 : int) : (term960 _97569 _97571 _97570) = (term961 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562121 _97569) (@lem7562119 _97569 _97571 _97570)). Qed.
Lemma lem7562123 (_97569 : int) (_97571 : int) (_97570 : int) : (term962 _97569 _97571 _97570) = (term960 _97569 _97571 _97570).
Proof. exact (@lem17362 (term394 _97569) (term963 _97569 _97571 _97570)). Qed.
Lemma lem7562185 (_97569 : int) (_97571 : int) (_97570 : int) : (term962 _97569 _97571 _97570) = (term961 _97569 _97571 _97570).
Proof. exact (TRANS (@lem7562123 _97569 _97571 _97570) (@lem7562122 _97569 _97571 _97570)). Qed.
Lemma lem7562188 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562189 (_97569 : int) : (term394 _97569) = (term452 _97569).
Proof. exact (@lem7562188 term453 _97569). Qed.
Lemma lem7562191 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562192 : term455 = term35.
Proof. exact (@lem7562191 (NUMERAL 0)). Qed.
Lemma lem7562193 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562194 : term456 = term457.
Proof. exact (MK_COMB (@lem7562193) (@lem7562192)). Qed.
Lemma lem7562195 (_97569 : int) : (real_of_int _97569) = (real_of_int _97569).
Proof. exact (eq_refl (real_of_int _97569)). Qed.
Lemma lem7562196 (_97569 : int) : (term452 _97569) = (term458 _97569).
Proof. exact (MK_COMB (@lem7562194) (@lem7562195 _97569)). Qed.
Lemma lem7562198 (_97569 : int) : (term394 _97569) = (term458 _97569).
Proof. exact (TRANS (@lem7562189 _97569) (@lem7562196 _97569)). Qed.
Lemma lem7562201 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562202 (_97570 : int) : (term394 _97570) = (term452 _97570).
Proof. exact (@lem7562201 term453 _97570). Qed.
Lemma lem7562204 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562205 : term455 = term35.
Proof. exact (@lem7562204 (NUMERAL 0)). Qed.
Lemma lem7562206 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562207 : term456 = term457.
Proof. exact (MK_COMB (@lem7562206) (@lem7562205)). Qed.
Lemma lem7562208 (_97570 : int) : (real_of_int _97570) = (real_of_int _97570).
Proof. exact (eq_refl (real_of_int _97570)). Qed.
Lemma lem7562209 (_97570 : int) : (term452 _97570) = (term458 _97570).
Proof. exact (MK_COMB (@lem7562207) (@lem7562208 _97570)). Qed.
Lemma lem7562211 (_97570 : int) : (term394 _97570) = (term458 _97570).
Proof. exact (TRANS (@lem7562202 _97570) (@lem7562209 _97570)). Qed.
Lemma lem7562214 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562215 (_97571 : int) : (term394 _97571) = (term452 _97571).
Proof. exact (@lem7562214 term453 _97571). Qed.
Lemma lem7562217 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562218 : term455 = term35.
Proof. exact (@lem7562217 (NUMERAL 0)). Qed.
Lemma lem7562219 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562220 : term456 = term457.
Proof. exact (MK_COMB (@lem7562219) (@lem7562218)). Qed.
Lemma lem7562221 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7562222 (_97571 : int) : (term452 _97571) = (term458 _97571).
Proof. exact (MK_COMB (@lem7562220) (@lem7562221 _97571)). Qed.
Lemma lem7562224 (_97571 : int) : (term394 _97571) = (term458 _97571).
Proof. exact (TRANS (@lem7562215 _97571) (@lem7562222 _97571)). Qed.
Lemma lem7562226 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7562227 (_97571 : int) : (term403 _97571) = (term460 _97571).
Proof. exact (@lem7562226 _97571 term453). Qed.
Lemma lem7562229 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562230 (_97571 : int) : (term460 _97571) = (term461 _97571).
Proof. exact (@lem7562229 (term462 _97571) term453). Qed.
Lemma lem7562232 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7562233 (_97571 : int) : (term465 _97571) = (term466 _97571).
Proof. exact (@lem7562232 _97571 term467). Qed.
Lemma lem7562235 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562236 : term468 = term469.
Proof. exact (@lem7562235 term470). Qed.
Lemma lem7562237 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7562238 (_97571 : int) : (term466 _97571) = (term472 _97571).
Proof. exact (MK_COMB (@lem7562237 _97571) (@lem7562236)). Qed.
Lemma lem7562239 (_97571 : int) : (term465 _97571) = (term472 _97571).
Proof. exact (TRANS (@lem7562233 _97571) (@lem7562238 _97571)). Qed.
Lemma lem7562240 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562241 (_97571 : int) : (term473 _97571) = (term474 _97571).
Proof. exact (MK_COMB (@lem7562240) (@lem7562239 _97571)). Qed.
Lemma lem7562243 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562244 : term455 = term35.
Proof. exact (@lem7562243 (NUMERAL 0)). Qed.
Lemma lem7562245 (_97571 : int) : (term461 _97571) = (term475 _97571).
Proof. exact (MK_COMB (@lem7562241 _97571) (@lem7562244)). Qed.
Lemma lem7562246 (_97571 : int) : (term460 _97571) = (term475 _97571).
Proof. exact (TRANS (@lem7562230 _97571) (@lem7562245 _97571)). Qed.
Lemma lem7562247 (_97571 : int) : (term403 _97571) = (term475 _97571).
Proof. exact (TRANS (@lem7562227 _97571) (@lem7562246 _97571)). Qed.
Lemma lem7562249 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7562250 (_97570 : int) (_97571 : int) : (term412 _97571 _97570) = (term459 _97570 _97571).
Proof. exact (@lem7562249 _97570 _97571). Qed.
Lemma lem7562252 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562253 (_97570 : int) (_97571 : int) : (term459 _97570 _97571) = (term476 _97570 _97571).
Proof. exact (@lem7562252 (term462 _97570) _97571). Qed.
Lemma lem7562255 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7562256 (_97570 : int) : (term465 _97570) = (term466 _97570).
Proof. exact (@lem7562255 _97570 term467). Qed.
Lemma lem7562258 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562259 : term468 = term469.
Proof. exact (@lem7562258 term470). Qed.
Lemma lem7562260 (_97570 : int) : (term471 _97570) = (term471 _97570).
Proof. exact (eq_refl (term471 _97570)). Qed.
Lemma lem7562261 (_97570 : int) : (term466 _97570) = (term472 _97570).
Proof. exact (MK_COMB (@lem7562260 _97570) (@lem7562259)). Qed.
Lemma lem7562262 (_97570 : int) : (term465 _97570) = (term472 _97570).
Proof. exact (TRANS (@lem7562256 _97570) (@lem7562261 _97570)). Qed.
Lemma lem7562263 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562264 (_97570 : int) : (term473 _97570) = (term474 _97570).
Proof. exact (MK_COMB (@lem7562263) (@lem7562262 _97570)). Qed.
Lemma lem7562265 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7562266 (_97570 : int) (_97571 : int) : (term476 _97570 _97571) = (term477 _97570 _97571).
Proof. exact (MK_COMB (@lem7562264 _97570) (@lem7562265 _97571)). Qed.
Lemma lem7562267 (_97570 : int) (_97571 : int) : (term459 _97570 _97571) = (term477 _97570 _97571).
Proof. exact (TRANS (@lem7562253 _97570 _97571) (@lem7562266 _97570 _97571)). Qed.
Lemma lem7562268 (_97570 : int) (_97571 : int) : (term412 _97571 _97570) = (term477 _97570 _97571).
Proof. exact (TRANS (@lem7562250 _97570 _97571) (@lem7562267 _97570 _97571)). Qed.
Lemma lem7562269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7562270 (_97571 : int) : (term478 _97571) = (term479 _97571).
Proof. exact (MK_COMB (@lem7562269) (@lem7562247 _97571)). Qed.
Lemma lem7562271 (_97570 : int) (_97571 : int) : (term393 _97571 _97570) = (term480 _97570 _97571).
Proof. exact (MK_COMB (@lem7562270 _97571) (@lem7562268 _97570 _97571)). Qed.
Lemma lem7562274 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562275 (_97571 : int) : (term394 _97571) = (term452 _97571).
Proof. exact (@lem7562274 term453 _97571). Qed.
Lemma lem7562277 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562278 : term455 = term35.
Proof. exact (@lem7562277 (NUMERAL 0)). Qed.
Lemma lem7562279 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562280 : term456 = term457.
Proof. exact (MK_COMB (@lem7562279) (@lem7562278)). Qed.
Lemma lem7562281 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7562282 (_97571 : int) : (term452 _97571) = (term458 _97571).
Proof. exact (MK_COMB (@lem7562280) (@lem7562281 _97571)). Qed.
Lemma lem7562284 (_97571 : int) : (term394 _97571) = (term458 _97571).
Proof. exact (TRANS (@lem7562275 _97571) (@lem7562282 _97571)). Qed.
Lemma lem7562287 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562288 (_97571 : int) (_97569 : int) (_97570 : int) : (term397 _97571 _97569 _97570) = (term481 _97571 _97569 _97570).
Proof. exact (@lem7562287 _97571 (int_max _97569 _97570)). Qed.
Lemma lem7562290 (x : int) (y : int) : (term482 x y) = (term483 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem7562291 (_97569 : int) (_97570 : int) : (term482 _97569 _97570) = (term483 _97569 _97570).
Proof. exact (@lem7562290 _97569 _97570). Qed.
Lemma lem7562292 (_97571 : int) : (term484 _97571) = (term484 _97571).
Proof. exact (eq_refl (term484 _97571)). Qed.
Lemma lem7562293 (_97571 : int) (_97569 : int) (_97570 : int) : (term481 _97571 _97569 _97570) = (term485 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562292 _97571) (@lem7562291 _97569 _97570)). Qed.
Lemma lem7562295 (_97571 : int) (_97569 : int) (_97570 : int) : (term397 _97571 _97569 _97570) = (term485 _97571 _97569 _97570).
Proof. exact (TRANS (@lem7562288 _97571 _97569 _97570) (@lem7562293 _97571 _97569 _97570)). Qed.
Lemma lem7562296 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562297 (_97571 : int) : (term399 _97571) = (term486 _97571).
Proof. exact (MK_COMB (@lem7562296) (@lem7562284 _97571)). Qed.
Lemma lem7562298 (_97571 : int) (_97569 : int) (_97570 : int) : (term401 _97571 _97569 _97570) = (term487 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562297 _97571) (@lem7562295 _97571 _97569 _97570)). Qed.
Lemma lem7562301 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562303 (_97571 : int) (_97570 : int) : (int_le _97571 _97570) = (term451 _97571 _97570).
Proof. exact (@lem7562301 _97571 _97570). Qed.
Lemma lem7562304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562305 (_97571 : int) (_97569 : int) (_97570 : int) : (term407 _97571 _97569 _97570) = (term488 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562304) (@lem7562298 _97571 _97569 _97570)). Qed.
Lemma lem7562306 (_97569 : int) (_97571 : int) (_97570 : int) : (term934 _97569 _97571 _97570) = (term964 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562305 _97571 _97569 _97570) (@lem7562303 _97571 _97570)). Qed.
Lemma lem7562307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562308 (_97570 : int) (_97571 : int) : (term414 _97571 _97570) = (term490 _97570 _97571).
Proof. exact (MK_COMB (@lem7562307) (@lem7562271 _97570 _97571)). Qed.
Lemma lem7562309 (_97569 : int) (_97571 : int) (_97570 : int) : (term937 _97569 _97571 _97570) = (term965 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562308 _97570 _97571) (@lem7562306 _97569 _97571 _97570)). Qed.
Lemma lem7562312 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562313 (_97571 : int) : (term394 _97571) = (term452 _97571).
Proof. exact (@lem7562312 term453 _97571). Qed.
Lemma lem7562315 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562316 : term455 = term35.
Proof. exact (@lem7562315 (NUMERAL 0)). Qed.
Lemma lem7562317 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562318 : term456 = term457.
Proof. exact (MK_COMB (@lem7562317) (@lem7562316)). Qed.
Lemma lem7562319 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7562320 (_97571 : int) : (term452 _97571) = (term458 _97571).
Proof. exact (MK_COMB (@lem7562318) (@lem7562319 _97571)). Qed.
Lemma lem7562322 (_97571 : int) : (term394 _97571) = (term458 _97571).
Proof. exact (TRANS (@lem7562313 _97571) (@lem7562320 _97571)). Qed.
Lemma lem7562325 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562327 (_97571 : int) (_97570 : int) : (int_le _97571 _97570) = (term451 _97571 _97570).
Proof. exact (@lem7562325 _97571 _97570). Qed.
Lemma lem7562328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562329 (_97571 : int) : (term399 _97571) = (term486 _97571).
Proof. exact (MK_COMB (@lem7562328) (@lem7562322 _97571)). Qed.
Lemma lem7562330 (_97571 : int) (_97570 : int) : (term418 _97571 _97570) = (term492 _97571 _97570).
Proof. exact (MK_COMB (@lem7562329 _97571) (@lem7562327 _97571 _97570)). Qed.
Lemma lem7562332 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7562333 (_97571 : int) : (term403 _97571) = (term460 _97571).
Proof. exact (@lem7562332 _97571 term453). Qed.
Lemma lem7562335 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562336 (_97571 : int) : (term460 _97571) = (term461 _97571).
Proof. exact (@lem7562335 (term462 _97571) term453). Qed.
Lemma lem7562338 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7562339 (_97571 : int) : (term465 _97571) = (term466 _97571).
Proof. exact (@lem7562338 _97571 term467). Qed.
Lemma lem7562341 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562342 : term468 = term469.
Proof. exact (@lem7562341 term470). Qed.
Lemma lem7562343 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7562344 (_97571 : int) : (term466 _97571) = (term472 _97571).
Proof. exact (MK_COMB (@lem7562343 _97571) (@lem7562342)). Qed.
Lemma lem7562345 (_97571 : int) : (term465 _97571) = (term472 _97571).
Proof. exact (TRANS (@lem7562339 _97571) (@lem7562344 _97571)). Qed.
Lemma lem7562346 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562347 (_97571 : int) : (term473 _97571) = (term474 _97571).
Proof. exact (MK_COMB (@lem7562346) (@lem7562345 _97571)). Qed.
Lemma lem7562349 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562350 : term455 = term35.
Proof. exact (@lem7562349 (NUMERAL 0)). Qed.
Lemma lem7562351 (_97571 : int) : (term461 _97571) = (term475 _97571).
Proof. exact (MK_COMB (@lem7562347 _97571) (@lem7562350)). Qed.
Lemma lem7562352 (_97571 : int) : (term460 _97571) = (term475 _97571).
Proof. exact (TRANS (@lem7562336 _97571) (@lem7562351 _97571)). Qed.
Lemma lem7562353 (_97571 : int) : (term403 _97571) = (term475 _97571).
Proof. exact (TRANS (@lem7562333 _97571) (@lem7562352 _97571)). Qed.
Lemma lem7562355 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7562356 (_97569 : int) (_97570 : int) (_97571 : int) : (term404 _97571 _97569 _97570) = (term493 _97569 _97570 _97571).
Proof. exact (@lem7562355 (int_max _97569 _97570) _97571). Qed.
Lemma lem7562358 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562359 (_97569 : int) (_97570 : int) (_97571 : int) : (term493 _97569 _97570 _97571) = (term494 _97569 _97570 _97571).
Proof. exact (@lem7562358 (term495 _97569 _97570) _97571). Qed.
Lemma lem7562361 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7562362 (_97569 : int) (_97570 : int) : (term496 _97569 _97570) = (term497 _97569 _97570).
Proof. exact (@lem7562361 (int_max _97569 _97570) term467). Qed.
Lemma lem7562364 (x : int) (y : int) : (term482 x y) = (term483 x y).
Proof. exact (EQ_MP (@lem2318512 x y) (@lem2318511 x y)). Qed.
Lemma lem7562365 (_97569 : int) (_97570 : int) : (term482 _97569 _97570) = (term483 _97569 _97570).
Proof. exact (@lem7562364 _97569 _97570). Qed.
Lemma lem7562366 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7562367 (_97569 : int) (_97570 : int) : (term498 _97569 _97570) = (term499 _97569 _97570).
Proof. exact (MK_COMB (@lem7562366) (@lem7562365 _97569 _97570)). Qed.
Lemma lem7562369 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562370 : term468 = term469.
Proof. exact (@lem7562369 term470). Qed.
Lemma lem7562371 (_97569 : int) (_97570 : int) : (term497 _97569 _97570) = (term500 _97569 _97570).
Proof. exact (MK_COMB (@lem7562367 _97569 _97570) (@lem7562370)). Qed.
Lemma lem7562372 (_97569 : int) (_97570 : int) : (term496 _97569 _97570) = (term500 _97569 _97570).
Proof. exact (TRANS (@lem7562362 _97569 _97570) (@lem7562371 _97569 _97570)). Qed.
Lemma lem7562373 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562374 (_97569 : int) (_97570 : int) : (term501 _97569 _97570) = (term502 _97569 _97570).
Proof. exact (MK_COMB (@lem7562373) (@lem7562372 _97569 _97570)). Qed.
Lemma lem7562375 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7562376 (_97569 : int) (_97570 : int) (_97571 : int) : (term494 _97569 _97570 _97571) = (term503 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562374 _97569 _97570) (@lem7562375 _97571)). Qed.
Lemma lem7562377 (_97569 : int) (_97570 : int) (_97571 : int) : (term493 _97569 _97570 _97571) = (term503 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7562359 _97569 _97570 _97571) (@lem7562376 _97569 _97570 _97571)). Qed.
Lemma lem7562378 (_97569 : int) (_97570 : int) (_97571 : int) : (term404 _97571 _97569 _97570) = (term503 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7562356 _97569 _97570 _97571) (@lem7562377 _97569 _97570 _97571)). Qed.
Lemma lem7562379 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7562380 (_97571 : int) : (term478 _97571) = (term479 _97571).
Proof. exact (MK_COMB (@lem7562379) (@lem7562353 _97571)). Qed.
Lemma lem7562381 (_97569 : int) (_97570 : int) (_97571 : int) : (term411 _97571 _97569 _97570) = (term504 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562380 _97571) (@lem7562378 _97569 _97570 _97571)). Qed.
Lemma lem7562383 (y : int) (x : int) : (term412 x y) = (term459 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem7562384 (_97570 : int) (_97571 : int) : (term412 _97571 _97570) = (term459 _97570 _97571).
Proof. exact (@lem7562383 _97570 _97571). Qed.
Lemma lem7562386 (x : int) (y : int) : (int_le x y) = (term451 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem7562387 (_97570 : int) (_97571 : int) : (term459 _97570 _97571) = (term476 _97570 _97571).
Proof. exact (@lem7562386 (term462 _97570) _97571). Qed.
Lemma lem7562389 (x : int) (y : int) : (term463 x y) = (term464 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem7562390 (_97570 : int) : (term465 _97570) = (term466 _97570).
Proof. exact (@lem7562389 _97570 term467). Qed.
Lemma lem7562392 (n : nat) : (term454 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem7562393 : term468 = term469.
Proof. exact (@lem7562392 term470). Qed.
Lemma lem7562394 (_97570 : int) : (term471 _97570) = (term471 _97570).
Proof. exact (eq_refl (term471 _97570)). Qed.
Lemma lem7562395 (_97570 : int) : (term466 _97570) = (term472 _97570).
Proof. exact (MK_COMB (@lem7562394 _97570) (@lem7562393)). Qed.
Lemma lem7562396 (_97570 : int) : (term465 _97570) = (term472 _97570).
Proof. exact (TRANS (@lem7562390 _97570) (@lem7562395 _97570)). Qed.
Lemma lem7562397 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7562398 (_97570 : int) : (term473 _97570) = (term474 _97570).
Proof. exact (MK_COMB (@lem7562397) (@lem7562396 _97570)). Qed.
Lemma lem7562399 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7562400 (_97570 : int) (_97571 : int) : (term476 _97570 _97571) = (term477 _97570 _97571).
Proof. exact (MK_COMB (@lem7562398 _97570) (@lem7562399 _97571)). Qed.
Lemma lem7562401 (_97570 : int) (_97571 : int) : (term459 _97570 _97571) = (term477 _97570 _97571).
Proof. exact (TRANS (@lem7562387 _97570 _97571) (@lem7562400 _97570 _97571)). Qed.
Lemma lem7562402 (_97570 : int) (_97571 : int) : (term412 _97571 _97570) = (term477 _97570 _97571).
Proof. exact (TRANS (@lem7562384 _97570 _97571) (@lem7562401 _97570 _97571)). Qed.
Lemma lem7562403 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7562404 (_97569 : int) (_97570 : int) (_97571 : int) : (term424 _97571 _97569 _97570) = (term505 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562403) (@lem7562381 _97569 _97570 _97571)). Qed.
Lemma lem7562405 (_97569 : int) (_97570 : int) (_97571 : int) : (term939 _97569 _97571 _97570) = (term966 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562404 _97569 _97570 _97571) (@lem7562402 _97570 _97571)). Qed.
Lemma lem7562406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562407 (_97571 : int) (_97570 : int) : (term428 _97571 _97570) = (term507 _97571 _97570).
Proof. exact (MK_COMB (@lem7562406) (@lem7562330 _97571 _97570)). Qed.
Lemma lem7562408 (_97569 : int) (_97570 : int) (_97571 : int) : (term943 _97569 _97571 _97570) = (term967 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562407 _97571 _97570) (@lem7562405 _97569 _97570 _97571)). Qed.
Lemma lem7562409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7562410 (_97569 : int) (_97571 : int) (_97570 : int) : (term946 _97569 _97571 _97570) = (term968 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7562409) (@lem7562309 _97569 _97571 _97570)). Qed.
Lemma lem7562411 (_97569 : int) (_97570 : int) (_97571 : int) : (term948 _97569 _97571 _97570) = (term969 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562410 _97569 _97571 _97570) (@lem7562408 _97569 _97570 _97571)). Qed.
Lemma lem7562412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562413 (_97571 : int) : (term399 _97571) = (term486 _97571).
Proof. exact (MK_COMB (@lem7562412) (@lem7562224 _97571)). Qed.
Lemma lem7562414 (_97569 : int) (_97570 : int) (_97571 : int) : (term953 _97569 _97571 _97570) = (term970 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562413 _97571) (@lem7562411 _97569 _97570 _97571)). Qed.
Lemma lem7562415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562416 (_97570 : int) : (term399 _97570) = (term486 _97570).
Proof. exact (MK_COMB (@lem7562415) (@lem7562211 _97570)). Qed.
Lemma lem7562417 (_97569 : int) (_97570 : int) (_97571 : int) : (term957 _97569 _97571 _97570) = (term971 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562416 _97570) (@lem7562414 _97569 _97570 _97571)). Qed.
Lemma lem7562418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562419 (_97569 : int) : (term399 _97569) = (term486 _97569).
Proof. exact (MK_COMB (@lem7562418) (@lem7562198 _97569)). Qed.
Lemma lem7562420 (_97569 : int) (_97570 : int) (_97571 : int) : (term961 _97569 _97571 _97570) = (term972 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562419 _97569) (@lem7562417 _97569 _97570 _97571)). Qed.
Lemma lem7562421 (_97569 : int) (_97570 : int) (_97571 : int) : (term962 _97569 _97571 _97570) = (term972 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7562185 _97569 _97571 _97570) (@lem7562420 _97569 _97570 _97571)). Qed.
Lemma lem7562425 (t : Prop) : (term514 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem7562551 (_97569 : int) (_97570 : int) (_97571 : int) : (term973 _97569 _97570 _97571) = (term972 _97569 _97570 _97571).
Proof. exact (@lem7562425 (term972 _97569 _97570 _97571)). Qed.
Lemma lem7562552 (_97569 : int) : (term458 _97569) = (term516 _97569).
Proof. exact (@lem1988287 (real_of_int _97569) term35). Qed.
Lemma lem7562558 (_97569 : int) : (term517 _97569) = (term518 _97569).
Proof. exact (@lem1982792 (real_of_int _97569) term35). Qed.
Lemma lem7562560 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7562561 : term35 = term520.
Proof. exact (@lem7562560 (NUMERAL 0)). Qed.
Lemma lem7562563 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7562564 : term523 = term524.
Proof. exact (@lem7562563 term470). Qed.
Lemma lem7562565 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7562566 : term525 = term526.
Proof. exact (MK_COMB (@lem7562565) (@lem7562564)). Qed.
Lemma lem7562567 : term527 = term528.
Proof. exact (MK_COMB (@lem7562566) (@lem7562561)). Qed.
Lemma lem7562568 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7562570 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7562571 : term532 = term533.
Proof. exact (@lem7562570 term470 term470). Qed.
Lemma lem7562572 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562573 : term535 = term470.
Proof. exact (EQ_MP (@lem7562572) (@lem940073)). Qed.
Lemma lem7562574 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562575 : term533 = term469.
Proof. exact (MK_COMB (@lem7562574) (@lem7562573)). Qed.
Lemma lem7562576 : term532 = term469.
Proof. exact (TRANS (@lem7562571) (@lem7562575)). Qed.
Lemma lem7562578 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7562579 : term527 = term35.
Proof. exact (@lem7562578 term470). Qed.
Lemma lem7562580 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7562581 : term537 = term538.
Proof. exact (MK_COMB (@lem7562580) (@lem7562579)). Qed.
Lemma lem7562582 : term529 = term520.
Proof. exact (MK_COMB (@lem7562581) (@lem7562576)). Qed.
Lemma lem7562583 : term528 = term520.
Proof. exact (TRANS (@lem7562568) (@lem7562582)). Qed.
Lemma lem7562584 : term527 = term520.
Proof. exact (TRANS (@lem7562567) (@lem7562583)). Qed.
Lemma lem7562586 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7562587 : term520 = term35.
Proof. exact (@lem7562586 term35). Qed.
Lemma lem7562588 : term527 = term35.
Proof. exact (TRANS (@lem7562584) (@lem7562587)). Qed.
Lemma lem7562589 (_97569 : int) : (term471 _97569) = (term471 _97569).
Proof. exact (eq_refl (term471 _97569)). Qed.
Lemma lem7562590 (_97569 : int) : (term518 _97569) = (term540 _97569).
Proof. exact (MK_COMB (@lem7562589 _97569) (@lem7562588)). Qed.
Lemma lem7562591 (_97569 : int) : (term540 _97569) = (real_of_int _97569).
Proof. exact (@lem1982723 (real_of_int _97569)). Qed.
Lemma lem7562592 (_97569 : int) : (term518 _97569) = (real_of_int _97569).
Proof. exact (TRANS (@lem7562590 _97569) (@lem7562591 _97569)). Qed.
Lemma lem7562594 (_97569 : int) : (term517 _97569) = (real_of_int _97569).
Proof. exact (TRANS (@lem7562558 _97569) (@lem7562592 _97569)). Qed.
Lemma lem7562595 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562596 (_97569 : int) : (term541 _97569) = (term542 _97569).
Proof. exact (MK_COMB (@lem7562595) (@lem7562594 _97569)). Qed.
Lemma lem7562597 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562598 (_97569 : int) : (term516 _97569) = (term543 _97569).
Proof. exact (MK_COMB (@lem7562596 _97569) (@lem7562597)). Qed.
Lemma lem7562599 (_97569 : int) : (term458 _97569) = (term543 _97569).
Proof. exact (TRANS (@lem7562552 _97569) (@lem7562598 _97569)). Qed.
Lemma lem7562600 (_97570 : int) : (term458 _97570) = (term516 _97570).
Proof. exact (@lem1988287 (real_of_int _97570) term35). Qed.
Lemma lem7562606 (_97570 : int) : (term517 _97570) = (term518 _97570).
Proof. exact (@lem1982792 (real_of_int _97570) term35). Qed.
Lemma lem7562608 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7562609 : term35 = term520.
Proof. exact (@lem7562608 (NUMERAL 0)). Qed.
Lemma lem7562611 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7562612 : term523 = term524.
Proof. exact (@lem7562611 term470). Qed.
Lemma lem7562613 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7562614 : term525 = term526.
Proof. exact (MK_COMB (@lem7562613) (@lem7562612)). Qed.
Lemma lem7562615 : term527 = term528.
Proof. exact (MK_COMB (@lem7562614) (@lem7562609)). Qed.
Lemma lem7562616 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7562618 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7562619 : term532 = term533.
Proof. exact (@lem7562618 term470 term470). Qed.
Lemma lem7562620 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562621 : term535 = term470.
Proof. exact (EQ_MP (@lem7562620) (@lem940073)). Qed.
Lemma lem7562622 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562623 : term533 = term469.
Proof. exact (MK_COMB (@lem7562622) (@lem7562621)). Qed.
Lemma lem7562624 : term532 = term469.
Proof. exact (TRANS (@lem7562619) (@lem7562623)). Qed.
Lemma lem7562626 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7562627 : term527 = term35.
Proof. exact (@lem7562626 term470). Qed.
Lemma lem7562628 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7562629 : term537 = term538.
Proof. exact (MK_COMB (@lem7562628) (@lem7562627)). Qed.
Lemma lem7562630 : term529 = term520.
Proof. exact (MK_COMB (@lem7562629) (@lem7562624)). Qed.
Lemma lem7562631 : term528 = term520.
Proof. exact (TRANS (@lem7562616) (@lem7562630)). Qed.
Lemma lem7562632 : term527 = term520.
Proof. exact (TRANS (@lem7562615) (@lem7562631)). Qed.
Lemma lem7562634 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7562635 : term520 = term35.
Proof. exact (@lem7562634 term35). Qed.
Lemma lem7562636 : term527 = term35.
Proof. exact (TRANS (@lem7562632) (@lem7562635)). Qed.
Lemma lem7562637 (_97570 : int) : (term471 _97570) = (term471 _97570).
Proof. exact (eq_refl (term471 _97570)). Qed.
Lemma lem7562638 (_97570 : int) : (term518 _97570) = (term540 _97570).
Proof. exact (MK_COMB (@lem7562637 _97570) (@lem7562636)). Qed.
Lemma lem7562639 (_97570 : int) : (term540 _97570) = (real_of_int _97570).
Proof. exact (@lem1982723 (real_of_int _97570)). Qed.
Lemma lem7562640 (_97570 : int) : (term518 _97570) = (real_of_int _97570).
Proof. exact (TRANS (@lem7562638 _97570) (@lem7562639 _97570)). Qed.
Lemma lem7562642 (_97570 : int) : (term517 _97570) = (real_of_int _97570).
Proof. exact (TRANS (@lem7562606 _97570) (@lem7562640 _97570)). Qed.
Lemma lem7562643 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562644 (_97570 : int) : (term541 _97570) = (term542 _97570).
Proof. exact (MK_COMB (@lem7562643) (@lem7562642 _97570)). Qed.
Lemma lem7562645 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562646 (_97570 : int) : (term516 _97570) = (term543 _97570).
Proof. exact (MK_COMB (@lem7562644 _97570) (@lem7562645)). Qed.
Lemma lem7562647 (_97570 : int) : (term458 _97570) = (term543 _97570).
Proof. exact (TRANS (@lem7562600 _97570) (@lem7562646 _97570)). Qed.
Lemma lem7562648 (_97571 : int) : (term458 _97571) = (term516 _97571).
Proof. exact (@lem1988287 (real_of_int _97571) term35). Qed.
Lemma lem7562654 (_97571 : int) : (term517 _97571) = (term518 _97571).
Proof. exact (@lem1982792 (real_of_int _97571) term35). Qed.
Lemma lem7562656 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7562657 : term35 = term520.
Proof. exact (@lem7562656 (NUMERAL 0)). Qed.
Lemma lem7562659 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7562660 : term523 = term524.
Proof. exact (@lem7562659 term470). Qed.
Lemma lem7562661 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7562662 : term525 = term526.
Proof. exact (MK_COMB (@lem7562661) (@lem7562660)). Qed.
Lemma lem7562663 : term527 = term528.
Proof. exact (MK_COMB (@lem7562662) (@lem7562657)). Qed.
Lemma lem7562664 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7562666 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7562667 : term532 = term533.
Proof. exact (@lem7562666 term470 term470). Qed.
Lemma lem7562668 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562669 : term535 = term470.
Proof. exact (EQ_MP (@lem7562668) (@lem940073)). Qed.
Lemma lem7562670 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562671 : term533 = term469.
Proof. exact (MK_COMB (@lem7562670) (@lem7562669)). Qed.
Lemma lem7562672 : term532 = term469.
Proof. exact (TRANS (@lem7562667) (@lem7562671)). Qed.
Lemma lem7562674 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7562675 : term527 = term35.
Proof. exact (@lem7562674 term470). Qed.
Lemma lem7562676 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7562677 : term537 = term538.
Proof. exact (MK_COMB (@lem7562676) (@lem7562675)). Qed.
Lemma lem7562678 : term529 = term520.
Proof. exact (MK_COMB (@lem7562677) (@lem7562672)). Qed.
Lemma lem7562679 : term528 = term520.
Proof. exact (TRANS (@lem7562664) (@lem7562678)). Qed.
Lemma lem7562680 : term527 = term520.
Proof. exact (TRANS (@lem7562663) (@lem7562679)). Qed.
Lemma lem7562682 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7562683 : term520 = term35.
Proof. exact (@lem7562682 term35). Qed.
Lemma lem7562684 : term527 = term35.
Proof. exact (TRANS (@lem7562680) (@lem7562683)). Qed.
Lemma lem7562685 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7562686 (_97571 : int) : (term518 _97571) = (term540 _97571).
Proof. exact (MK_COMB (@lem7562685 _97571) (@lem7562684)). Qed.
Lemma lem7562687 (_97571 : int) : (term540 _97571) = (real_of_int _97571).
Proof. exact (@lem1982723 (real_of_int _97571)). Qed.
Lemma lem7562688 (_97571 : int) : (term518 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7562686 _97571) (@lem7562687 _97571)). Qed.
Lemma lem7562690 (_97571 : int) : (term517 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7562654 _97571) (@lem7562688 _97571)). Qed.
Lemma lem7562691 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562692 (_97571 : int) : (term541 _97571) = (term542 _97571).
Proof. exact (MK_COMB (@lem7562691) (@lem7562690 _97571)). Qed.
Lemma lem7562693 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562694 (_97571 : int) : (term516 _97571) = (term543 _97571).
Proof. exact (MK_COMB (@lem7562692 _97571) (@lem7562693)). Qed.
Lemma lem7562695 (_97571 : int) : (term458 _97571) = (term543 _97571).
Proof. exact (TRANS (@lem7562648 _97571) (@lem7562694 _97571)). Qed.
Lemma lem7562696 (_97571 : int) : (term475 _97571) = (term544 _97571).
Proof. exact (@lem1988287 term35 (term472 _97571)). Qed.
Lemma lem7562708 (_97571 : int) : (term545 _97571) = (term546 _97571).
Proof. exact (@lem1982792 term35 (term472 _97571)). Qed.
Lemma lem7562709 (_97571 : int) : (term547 _97571) = (term548 _97571).
Proof. exact (@lem1982781 (real_of_int _97571) term523 term469). Qed.
Lemma lem7562711 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7562712 : term469 = term549.
Proof. exact (@lem7562711 term470). Qed.
Lemma lem7562714 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7562715 : term523 = term524.
Proof. exact (@lem7562714 term470). Qed.
Lemma lem7562716 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7562717 : term525 = term526.
Proof. exact (MK_COMB (@lem7562716) (@lem7562715)). Qed.
Lemma lem7562718 : term550 = term551.
Proof. exact (MK_COMB (@lem7562717) (@lem7562712)). Qed.
Lemma lem7562719 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7562721 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7562722 : term532 = term533.
Proof. exact (@lem7562721 term470 term470). Qed.
Lemma lem7562723 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562724 : term535 = term470.
Proof. exact (EQ_MP (@lem7562723) (@lem940073)). Qed.
Lemma lem7562725 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562726 : term533 = term469.
Proof. exact (MK_COMB (@lem7562725) (@lem7562724)). Qed.
Lemma lem7562727 : term532 = term469.
Proof. exact (TRANS (@lem7562722) (@lem7562726)). Qed.
Lemma lem7562729 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7562730 : term550 = term555.
Proof. exact (@lem7562729 term470 term470). Qed.
Lemma lem7562731 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562732 : term535 = term470.
Proof. exact (EQ_MP (@lem7562731) (@lem940073)). Qed.
Lemma lem7562733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562734 : term533 = term469.
Proof. exact (MK_COMB (@lem7562733) (@lem7562732)). Qed.
Lemma lem7562735 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7562736 : term555 = term523.
Proof. exact (MK_COMB (@lem7562735) (@lem7562734)). Qed.
Lemma lem7562737 : term550 = term523.
Proof. exact (TRANS (@lem7562730) (@lem7562736)). Qed.
Lemma lem7562738 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7562739 : term556 = term557.
Proof. exact (MK_COMB (@lem7562738) (@lem7562737)). Qed.
Lemma lem7562740 : term552 = term524.
Proof. exact (MK_COMB (@lem7562739) (@lem7562727)). Qed.
Lemma lem7562741 : term551 = term524.
Proof. exact (TRANS (@lem7562719) (@lem7562740)). Qed.
Lemma lem7562742 : term550 = term524.
Proof. exact (TRANS (@lem7562718) (@lem7562741)). Qed.
Lemma lem7562744 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7562745 : term524 = term523.
Proof. exact (@lem7562744 term523). Qed.
Lemma lem7562746 : term550 = term523.
Proof. exact (TRANS (@lem7562742) (@lem7562745)). Qed.
Lemma lem7562749 (_97571 : int) : (term558 _97571) = (term558 _97571).
Proof. exact (eq_refl (term558 _97571)). Qed.
Lemma lem7562750 (_97571 : int) : (term548 _97571) = (term559 _97571).
Proof. exact (MK_COMB (@lem7562749 _97571) (@lem7562746)). Qed.
Lemma lem7562751 (_97571 : int) : (term547 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7562709 _97571) (@lem7562750 _97571)). Qed.
Lemma lem7562752 : term560 = term560.
Proof. exact (eq_refl term560). Qed.
Lemma lem7562753 (_97571 : int) : (term546 _97571) = (term561 _97571).
Proof. exact (MK_COMB (@lem7562752) (@lem7562751 _97571)). Qed.
Lemma lem7562754 (_97571 : int) : (term561 _97571) = (term559 _97571).
Proof. exact (@lem1982721 (term559 _97571)). Qed.
Lemma lem7562755 (_97571 : int) : (term546 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7562753 _97571) (@lem7562754 _97571)). Qed.
Lemma lem7562757 (_97571 : int) : (term545 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7562708 _97571) (@lem7562755 _97571)). Qed.
Lemma lem7562758 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562759 (_97571 : int) : (term562 _97571) = (term563 _97571).
Proof. exact (MK_COMB (@lem7562758) (@lem7562757 _97571)). Qed.
Lemma lem7562760 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562761 (_97571 : int) : (term544 _97571) = (term564 _97571).
Proof. exact (MK_COMB (@lem7562759 _97571) (@lem7562760)). Qed.
Lemma lem7562762 (_97571 : int) : (term475 _97571) = (term564 _97571).
Proof. exact (TRANS (@lem7562696 _97571) (@lem7562761 _97571)). Qed.
Lemma lem7562763 (_97571 : int) (_97570 : int) : (term477 _97570 _97571) = (term565 _97571 _97570).
Proof. exact (@lem1988287 (real_of_int _97571) (term472 _97570)). Qed.
Lemma lem7562775 (_97571 : int) (_97570 : int) : (term566 _97571 _97570) = (term567 _97571 _97570).
Proof. exact (@lem1982792 (real_of_int _97571) (term472 _97570)). Qed.
Lemma lem7562776 (_97570 : int) : (term547 _97570) = (term548 _97570).
Proof. exact (@lem1982781 (real_of_int _97570) term523 term469). Qed.
Lemma lem7562778 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7562779 : term469 = term549.
Proof. exact (@lem7562778 term470). Qed.
Lemma lem7562781 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7562782 : term523 = term524.
Proof. exact (@lem7562781 term470). Qed.
Lemma lem7562783 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7562784 : term525 = term526.
Proof. exact (MK_COMB (@lem7562783) (@lem7562782)). Qed.
Lemma lem7562785 : term550 = term551.
Proof. exact (MK_COMB (@lem7562784) (@lem7562779)). Qed.
Lemma lem7562786 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7562788 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7562789 : term532 = term533.
Proof. exact (@lem7562788 term470 term470). Qed.
Lemma lem7562790 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562791 : term535 = term470.
Proof. exact (EQ_MP (@lem7562790) (@lem940073)). Qed.
Lemma lem7562792 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562793 : term533 = term469.
Proof. exact (MK_COMB (@lem7562792) (@lem7562791)). Qed.
Lemma lem7562794 : term532 = term469.
Proof. exact (TRANS (@lem7562789) (@lem7562793)). Qed.
Lemma lem7562796 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7562797 : term550 = term555.
Proof. exact (@lem7562796 term470 term470). Qed.
Lemma lem7562798 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562799 : term535 = term470.
Proof. exact (EQ_MP (@lem7562798) (@lem940073)). Qed.
Lemma lem7562800 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562801 : term533 = term469.
Proof. exact (MK_COMB (@lem7562800) (@lem7562799)). Qed.
Lemma lem7562802 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7562803 : term555 = term523.
Proof. exact (MK_COMB (@lem7562802) (@lem7562801)). Qed.
Lemma lem7562804 : term550 = term523.
Proof. exact (TRANS (@lem7562797) (@lem7562803)). Qed.
Lemma lem7562805 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7562806 : term556 = term557.
Proof. exact (MK_COMB (@lem7562805) (@lem7562804)). Qed.
Lemma lem7562807 : term552 = term524.
Proof. exact (MK_COMB (@lem7562806) (@lem7562794)). Qed.
Lemma lem7562808 : term551 = term524.
Proof. exact (TRANS (@lem7562786) (@lem7562807)). Qed.
Lemma lem7562809 : term550 = term524.
Proof. exact (TRANS (@lem7562785) (@lem7562808)). Qed.
Lemma lem7562811 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7562812 : term524 = term523.
Proof. exact (@lem7562811 term523). Qed.
Lemma lem7562813 : term550 = term523.
Proof. exact (TRANS (@lem7562809) (@lem7562812)). Qed.
Lemma lem7562816 (_97570 : int) : (term558 _97570) = (term558 _97570).
Proof. exact (eq_refl (term558 _97570)). Qed.
Lemma lem7562817 (_97570 : int) : (term548 _97570) = (term559 _97570).
Proof. exact (MK_COMB (@lem7562816 _97570) (@lem7562813)). Qed.
Lemma lem7562818 (_97570 : int) : (term547 _97570) = (term559 _97570).
Proof. exact (TRANS (@lem7562776 _97570) (@lem7562817 _97570)). Qed.
Lemma lem7562819 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7562820 (_97571 : int) (_97570 : int) : (term567 _97571 _97570) = (term568 _97571 _97570).
Proof. exact (MK_COMB (@lem7562819 _97571) (@lem7562818 _97570)). Qed.
Lemma lem7562825 (_97570 : int) (_97571 : int) : (term568 _97571 _97570) = (term569 _97570 _97571).
Proof. exact (@lem1982757 (term570 _97570) (real_of_int _97571) term523). Qed.
Lemma lem7562826 (_97570 : int) (_97571 : int) : (term567 _97571 _97570) = (term569 _97570 _97571).
Proof. exact (TRANS (@lem7562820 _97571 _97570) (@lem7562825 _97570 _97571)). Qed.
Lemma lem7562828 (_97570 : int) (_97571 : int) : (term566 _97571 _97570) = (term569 _97570 _97571).
Proof. exact (TRANS (@lem7562775 _97571 _97570) (@lem7562826 _97570 _97571)). Qed.
Lemma lem7562829 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562830 (_97570 : int) (_97571 : int) : (term571 _97571 _97570) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7562829) (@lem7562828 _97570 _97571)). Qed.
Lemma lem7562831 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562832 (_97570 : int) (_97571 : int) : (term565 _97571 _97570) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7562830 _97570 _97571) (@lem7562831)). Qed.
Lemma lem7562833 (_97570 : int) (_97571 : int) : (term477 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (TRANS (@lem7562763 _97571 _97570) (@lem7562832 _97570 _97571)). Qed.
Lemma lem7562834 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7562835 (_97571 : int) : (term479 _97571) = (term574 _97571).
Proof. exact (MK_COMB (@lem7562834) (@lem7562762 _97571)). Qed.
Lemma lem7562836 (_97570 : int) (_97571 : int) : (term480 _97570 _97571) = (term575 _97570 _97571).
Proof. exact (MK_COMB (@lem7562835 _97571) (@lem7562833 _97570 _97571)). Qed.
Lemma lem7562837 (_97571 : int) : (term458 _97571) = (term516 _97571).
Proof. exact (@lem1988287 (real_of_int _97571) term35). Qed.
Lemma lem7562843 (_97571 : int) : (term517 _97571) = (term518 _97571).
Proof. exact (@lem1982792 (real_of_int _97571) term35). Qed.
Lemma lem7562845 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7562846 : term35 = term520.
Proof. exact (@lem7562845 (NUMERAL 0)). Qed.
Lemma lem7562848 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7562849 : term523 = term524.
Proof. exact (@lem7562848 term470). Qed.
Lemma lem7562850 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7562851 : term525 = term526.
Proof. exact (MK_COMB (@lem7562850) (@lem7562849)). Qed.
Lemma lem7562852 : term527 = term528.
Proof. exact (MK_COMB (@lem7562851) (@lem7562846)). Qed.
Lemma lem7562853 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7562855 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7562856 : term532 = term533.
Proof. exact (@lem7562855 term470 term470). Qed.
Lemma lem7562857 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562858 : term535 = term470.
Proof. exact (EQ_MP (@lem7562857) (@lem940073)). Qed.
Lemma lem7562859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562860 : term533 = term469.
Proof. exact (MK_COMB (@lem7562859) (@lem7562858)). Qed.
Lemma lem7562861 : term532 = term469.
Proof. exact (TRANS (@lem7562856) (@lem7562860)). Qed.
Lemma lem7562863 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7562864 : term527 = term35.
Proof. exact (@lem7562863 term470). Qed.
Lemma lem7562865 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7562866 : term537 = term538.
Proof. exact (MK_COMB (@lem7562865) (@lem7562864)). Qed.
Lemma lem7562867 : term529 = term520.
Proof. exact (MK_COMB (@lem7562866) (@lem7562861)). Qed.
Lemma lem7562868 : term528 = term520.
Proof. exact (TRANS (@lem7562853) (@lem7562867)). Qed.
Lemma lem7562869 : term527 = term520.
Proof. exact (TRANS (@lem7562852) (@lem7562868)). Qed.
Lemma lem7562871 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7562872 : term520 = term35.
Proof. exact (@lem7562871 term35). Qed.
Lemma lem7562873 : term527 = term35.
Proof. exact (TRANS (@lem7562869) (@lem7562872)). Qed.
Lemma lem7562874 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7562875 (_97571 : int) : (term518 _97571) = (term540 _97571).
Proof. exact (MK_COMB (@lem7562874 _97571) (@lem7562873)). Qed.
Lemma lem7562876 (_97571 : int) : (term540 _97571) = (real_of_int _97571).
Proof. exact (@lem1982723 (real_of_int _97571)). Qed.
Lemma lem7562877 (_97571 : int) : (term518 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7562875 _97571) (@lem7562876 _97571)). Qed.
Lemma lem7562879 (_97571 : int) : (term517 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7562843 _97571) (@lem7562877 _97571)). Qed.
Lemma lem7562880 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562881 (_97571 : int) : (term541 _97571) = (term542 _97571).
Proof. exact (MK_COMB (@lem7562880) (@lem7562879 _97571)). Qed.
Lemma lem7562882 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562883 (_97571 : int) : (term516 _97571) = (term543 _97571).
Proof. exact (MK_COMB (@lem7562881 _97571) (@lem7562882)). Qed.
Lemma lem7562884 (_97571 : int) : (term458 _97571) = (term543 _97571).
Proof. exact (TRANS (@lem7562837 _97571) (@lem7562883 _97571)). Qed.
Lemma lem7562885 (_97569 : int) (_97570 : int) (_97571 : int) : (term485 _97571 _97569 _97570) = (term576 _97569 _97570 _97571).
Proof. exact (@lem1988287 (term483 _97569 _97570) (real_of_int _97571)). Qed.
Lemma lem7562895 (_97569 : int) (_97570 : int) (_97571 : int) : (term577 _97569 _97570 _97571) = (term578 _97569 _97570 _97571).
Proof. exact (@lem1982792 (term483 _97569 _97570) (real_of_int _97571)). Qed.
Lemma lem7562900 (_97571 : int) (_97569 : int) (_97570 : int) : (term578 _97569 _97570 _97571) = (term579 _97571 _97569 _97570).
Proof. exact (@lem1982761 (term570 _97571) (term483 _97569 _97570)). Qed.
Lemma lem7562902 (_97571 : int) (_97569 : int) (_97570 : int) : (term577 _97569 _97570 _97571) = (term579 _97571 _97569 _97570).
Proof. exact (TRANS (@lem7562895 _97569 _97570 _97571) (@lem7562900 _97571 _97569 _97570)). Qed.
Lemma lem7562903 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562904 (_97571 : int) (_97569 : int) (_97570 : int) : (term580 _97569 _97570 _97571) = (term581 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562903) (@lem7562902 _97571 _97569 _97570)). Qed.
Lemma lem7562905 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562906 (_97571 : int) (_97569 : int) (_97570 : int) : (term576 _97569 _97570 _97571) = (term582 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562904 _97571 _97569 _97570) (@lem7562905)). Qed.
Lemma lem7562907 (_97571 : int) (_97569 : int) (_97570 : int) : (term485 _97571 _97569 _97570) = (term582 _97571 _97569 _97570).
Proof. exact (TRANS (@lem7562885 _97569 _97570 _97571) (@lem7562906 _97571 _97569 _97570)). Qed.
Lemma lem7562908 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562909 (_97571 : int) : (term486 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7562908) (@lem7562884 _97571)). Qed.
Lemma lem7562910 (_97571 : int) (_97569 : int) (_97570 : int) : (term487 _97571 _97569 _97570) = (term584 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562909 _97571) (@lem7562907 _97571 _97569 _97570)). Qed.
Lemma lem7562911 (_97570 : int) (_97571 : int) : (term451 _97571 _97570) = (term585 _97570 _97571).
Proof. exact (@lem1988287 (real_of_int _97570) (real_of_int _97571)). Qed.
Lemma lem7562924 (_97570 : int) (_97571 : int) : (term586 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982792 (real_of_int _97570) (real_of_int _97571)). Qed.
Lemma lem7562925 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562926 (_97570 : int) (_97571 : int) : (term588 _97570 _97571) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7562925) (@lem7562924 _97570 _97571)). Qed.
Lemma lem7562927 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562928 (_97570 : int) (_97571 : int) : (term585 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7562926 _97570 _97571) (@lem7562927)). Qed.
Lemma lem7562929 (_97570 : int) (_97571 : int) : (term451 _97571 _97570) = (term590 _97570 _97571).
Proof. exact (TRANS (@lem7562911 _97570 _97571) (@lem7562928 _97570 _97571)). Qed.
Lemma lem7562930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562931 (_97571 : int) (_97569 : int) (_97570 : int) : (term488 _97571 _97569 _97570) = (term591 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7562930) (@lem7562910 _97571 _97569 _97570)). Qed.
Lemma lem7562932 (_97569 : int) (_97570 : int) (_97571 : int) : (term964 _97569 _97571 _97570) = (term974 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562931 _97571 _97569 _97570) (@lem7562929 _97570 _97571)). Qed.
Lemma lem7562933 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7562934 (_97570 : int) (_97571 : int) : (term490 _97570 _97571) = (term593 _97570 _97571).
Proof. exact (MK_COMB (@lem7562933) (@lem7562836 _97570 _97571)). Qed.
Lemma lem7562935 (_97569 : int) (_97570 : int) (_97571 : int) : (term965 _97569 _97571 _97570) = (term975 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7562934 _97570 _97571) (@lem7562932 _97569 _97570 _97571)). Qed.
Lemma lem7562936 (_97571 : int) : (term458 _97571) = (term516 _97571).
Proof. exact (@lem1988287 (real_of_int _97571) term35). Qed.
Lemma lem7562942 (_97571 : int) : (term517 _97571) = (term518 _97571).
Proof. exact (@lem1982792 (real_of_int _97571) term35). Qed.
Lemma lem7562944 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7562945 : term35 = term520.
Proof. exact (@lem7562944 (NUMERAL 0)). Qed.
Lemma lem7562947 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7562948 : term523 = term524.
Proof. exact (@lem7562947 term470). Qed.
Lemma lem7562949 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7562950 : term525 = term526.
Proof. exact (MK_COMB (@lem7562949) (@lem7562948)). Qed.
Lemma lem7562951 : term527 = term528.
Proof. exact (MK_COMB (@lem7562950) (@lem7562945)). Qed.
Lemma lem7562952 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7562954 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7562955 : term532 = term533.
Proof. exact (@lem7562954 term470 term470). Qed.
Lemma lem7562956 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7562957 : term535 = term470.
Proof. exact (EQ_MP (@lem7562956) (@lem940073)). Qed.
Lemma lem7562958 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7562959 : term533 = term469.
Proof. exact (MK_COMB (@lem7562958) (@lem7562957)). Qed.
Lemma lem7562960 : term532 = term469.
Proof. exact (TRANS (@lem7562955) (@lem7562959)). Qed.
Lemma lem7562962 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7562963 : term527 = term35.
Proof. exact (@lem7562962 term470). Qed.
Lemma lem7562964 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7562965 : term537 = term538.
Proof. exact (MK_COMB (@lem7562964) (@lem7562963)). Qed.
Lemma lem7562966 : term529 = term520.
Proof. exact (MK_COMB (@lem7562965) (@lem7562960)). Qed.
Lemma lem7562967 : term528 = term520.
Proof. exact (TRANS (@lem7562952) (@lem7562966)). Qed.
Lemma lem7562968 : term527 = term520.
Proof. exact (TRANS (@lem7562951) (@lem7562967)). Qed.
Lemma lem7562970 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7562971 : term520 = term35.
Proof. exact (@lem7562970 term35). Qed.
Lemma lem7562972 : term527 = term35.
Proof. exact (TRANS (@lem7562968) (@lem7562971)). Qed.
Lemma lem7562973 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7562974 (_97571 : int) : (term518 _97571) = (term540 _97571).
Proof. exact (MK_COMB (@lem7562973 _97571) (@lem7562972)). Qed.
Lemma lem7562975 (_97571 : int) : (term540 _97571) = (real_of_int _97571).
Proof. exact (@lem1982723 (real_of_int _97571)). Qed.
Lemma lem7562976 (_97571 : int) : (term518 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7562974 _97571) (@lem7562975 _97571)). Qed.
Lemma lem7562978 (_97571 : int) : (term517 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7562942 _97571) (@lem7562976 _97571)). Qed.
Lemma lem7562979 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562980 (_97571 : int) : (term541 _97571) = (term542 _97571).
Proof. exact (MK_COMB (@lem7562979) (@lem7562978 _97571)). Qed.
Lemma lem7562981 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7562982 (_97571 : int) : (term516 _97571) = (term543 _97571).
Proof. exact (MK_COMB (@lem7562980 _97571) (@lem7562981)). Qed.
Lemma lem7562983 (_97571 : int) : (term458 _97571) = (term543 _97571).
Proof. exact (TRANS (@lem7562936 _97571) (@lem7562982 _97571)). Qed.
Lemma lem7562984 (_97570 : int) (_97571 : int) : (term451 _97571 _97570) = (term585 _97570 _97571).
Proof. exact (@lem1988287 (real_of_int _97570) (real_of_int _97571)). Qed.
Lemma lem7562997 (_97570 : int) (_97571 : int) : (term586 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982792 (real_of_int _97570) (real_of_int _97571)). Qed.
Lemma lem7562998 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7562999 (_97570 : int) (_97571 : int) : (term588 _97570 _97571) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7562998) (@lem7562997 _97570 _97571)). Qed.
Lemma lem7563000 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563001 (_97570 : int) (_97571 : int) : (term585 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7562999 _97570 _97571) (@lem7563000)). Qed.
Lemma lem7563002 (_97570 : int) (_97571 : int) : (term451 _97571 _97570) = (term590 _97570 _97571).
Proof. exact (TRANS (@lem7562984 _97570 _97571) (@lem7563001 _97570 _97571)). Qed.
Lemma lem7563003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563004 (_97571 : int) : (term486 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563003) (@lem7562983 _97571)). Qed.
Lemma lem7563005 (_97570 : int) (_97571 : int) : (term492 _97571 _97570) = (term595 _97570 _97571).
Proof. exact (MK_COMB (@lem7563004 _97571) (@lem7563002 _97570 _97571)). Qed.
Lemma lem7563006 (_97571 : int) : (term475 _97571) = (term544 _97571).
Proof. exact (@lem1988287 term35 (term472 _97571)). Qed.
Lemma lem7563018 (_97571 : int) : (term545 _97571) = (term546 _97571).
Proof. exact (@lem1982792 term35 (term472 _97571)). Qed.
Lemma lem7563019 (_97571 : int) : (term547 _97571) = (term548 _97571).
Proof. exact (@lem1982781 (real_of_int _97571) term523 term469). Qed.
Lemma lem7563021 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563022 : term469 = term549.
Proof. exact (@lem7563021 term470). Qed.
Lemma lem7563024 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563025 : term523 = term524.
Proof. exact (@lem7563024 term470). Qed.
Lemma lem7563026 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563027 : term525 = term526.
Proof. exact (MK_COMB (@lem7563026) (@lem7563025)). Qed.
Lemma lem7563028 : term550 = term551.
Proof. exact (MK_COMB (@lem7563027) (@lem7563022)). Qed.
Lemma lem7563029 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7563031 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563032 : term532 = term533.
Proof. exact (@lem7563031 term470 term470). Qed.
Lemma lem7563033 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563034 : term535 = term470.
Proof. exact (EQ_MP (@lem7563033) (@lem940073)). Qed.
Lemma lem7563035 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563036 : term533 = term469.
Proof. exact (MK_COMB (@lem7563035) (@lem7563034)). Qed.
Lemma lem7563037 : term532 = term469.
Proof. exact (TRANS (@lem7563032) (@lem7563036)). Qed.
Lemma lem7563039 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7563040 : term550 = term555.
Proof. exact (@lem7563039 term470 term470). Qed.
Lemma lem7563041 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563042 : term535 = term470.
Proof. exact (EQ_MP (@lem7563041) (@lem940073)). Qed.
Lemma lem7563043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563044 : term533 = term469.
Proof. exact (MK_COMB (@lem7563043) (@lem7563042)). Qed.
Lemma lem7563045 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7563046 : term555 = term523.
Proof. exact (MK_COMB (@lem7563045) (@lem7563044)). Qed.
Lemma lem7563047 : term550 = term523.
Proof. exact (TRANS (@lem7563040) (@lem7563046)). Qed.
Lemma lem7563048 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563049 : term556 = term557.
Proof. exact (MK_COMB (@lem7563048) (@lem7563047)). Qed.
Lemma lem7563050 : term552 = term524.
Proof. exact (MK_COMB (@lem7563049) (@lem7563037)). Qed.
Lemma lem7563051 : term551 = term524.
Proof. exact (TRANS (@lem7563029) (@lem7563050)). Qed.
Lemma lem7563052 : term550 = term524.
Proof. exact (TRANS (@lem7563028) (@lem7563051)). Qed.
Lemma lem7563054 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563055 : term524 = term523.
Proof. exact (@lem7563054 term523). Qed.
Lemma lem7563056 : term550 = term523.
Proof. exact (TRANS (@lem7563052) (@lem7563055)). Qed.
Lemma lem7563059 (_97571 : int) : (term558 _97571) = (term558 _97571).
Proof. exact (eq_refl (term558 _97571)). Qed.
Lemma lem7563060 (_97571 : int) : (term548 _97571) = (term559 _97571).
Proof. exact (MK_COMB (@lem7563059 _97571) (@lem7563056)). Qed.
Lemma lem7563061 (_97571 : int) : (term547 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7563019 _97571) (@lem7563060 _97571)). Qed.
Lemma lem7563062 : term560 = term560.
Proof. exact (eq_refl term560). Qed.
Lemma lem7563063 (_97571 : int) : (term546 _97571) = (term561 _97571).
Proof. exact (MK_COMB (@lem7563062) (@lem7563061 _97571)). Qed.
Lemma lem7563064 (_97571 : int) : (term561 _97571) = (term559 _97571).
Proof. exact (@lem1982721 (term559 _97571)). Qed.
Lemma lem7563065 (_97571 : int) : (term546 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7563063 _97571) (@lem7563064 _97571)). Qed.
Lemma lem7563067 (_97571 : int) : (term545 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7563018 _97571) (@lem7563065 _97571)). Qed.
Lemma lem7563068 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563069 (_97571 : int) : (term562 _97571) = (term563 _97571).
Proof. exact (MK_COMB (@lem7563068) (@lem7563067 _97571)). Qed.
Lemma lem7563070 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563071 (_97571 : int) : (term544 _97571) = (term564 _97571).
Proof. exact (MK_COMB (@lem7563069 _97571) (@lem7563070)). Qed.
Lemma lem7563072 (_97571 : int) : (term475 _97571) = (term564 _97571).
Proof. exact (TRANS (@lem7563006 _97571) (@lem7563071 _97571)). Qed.
Lemma lem7563073 (_97571 : int) (_97569 : int) (_97570 : int) : (term503 _97569 _97570 _97571) = (term596 _97571 _97569 _97570).
Proof. exact (@lem1988287 (real_of_int _97571) (term500 _97569 _97570)). Qed.
Lemma lem7563089 (_97571 : int) (_97569 : int) (_97570 : int) : (term597 _97571 _97569 _97570) = (term598 _97571 _97569 _97570).
Proof. exact (@lem1982792 (real_of_int _97571) (term500 _97569 _97570)). Qed.
Lemma lem7563090 (_97569 : int) (_97570 : int) : (term599 _97569 _97570) = (term600 _97569 _97570).
Proof. exact (@lem1982781 (term483 _97569 _97570) term523 term469). Qed.
Lemma lem7563092 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563093 : term469 = term549.
Proof. exact (@lem7563092 term470). Qed.
Lemma lem7563095 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563096 : term523 = term524.
Proof. exact (@lem7563095 term470). Qed.
Lemma lem7563097 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563098 : term525 = term526.
Proof. exact (MK_COMB (@lem7563097) (@lem7563096)). Qed.
Lemma lem7563099 : term550 = term551.
Proof. exact (MK_COMB (@lem7563098) (@lem7563093)). Qed.
Lemma lem7563100 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7563102 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563103 : term532 = term533.
Proof. exact (@lem7563102 term470 term470). Qed.
Lemma lem7563104 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563105 : term535 = term470.
Proof. exact (EQ_MP (@lem7563104) (@lem940073)). Qed.
Lemma lem7563106 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563107 : term533 = term469.
Proof. exact (MK_COMB (@lem7563106) (@lem7563105)). Qed.
Lemma lem7563108 : term532 = term469.
Proof. exact (TRANS (@lem7563103) (@lem7563107)). Qed.
Lemma lem7563110 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7563111 : term550 = term555.
Proof. exact (@lem7563110 term470 term470). Qed.
Lemma lem7563112 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563113 : term535 = term470.
Proof. exact (EQ_MP (@lem7563112) (@lem940073)). Qed.
Lemma lem7563114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563115 : term533 = term469.
Proof. exact (MK_COMB (@lem7563114) (@lem7563113)). Qed.
Lemma lem7563116 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7563117 : term555 = term523.
Proof. exact (MK_COMB (@lem7563116) (@lem7563115)). Qed.
Lemma lem7563118 : term550 = term523.
Proof. exact (TRANS (@lem7563111) (@lem7563117)). Qed.
Lemma lem7563119 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563120 : term556 = term557.
Proof. exact (MK_COMB (@lem7563119) (@lem7563118)). Qed.
Lemma lem7563121 : term552 = term524.
Proof. exact (MK_COMB (@lem7563120) (@lem7563108)). Qed.
Lemma lem7563122 : term551 = term524.
Proof. exact (TRANS (@lem7563100) (@lem7563121)). Qed.
Lemma lem7563123 : term550 = term524.
Proof. exact (TRANS (@lem7563099) (@lem7563122)). Qed.
Lemma lem7563125 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563126 : term524 = term523.
Proof. exact (@lem7563125 term523). Qed.
Lemma lem7563127 : term550 = term523.
Proof. exact (TRANS (@lem7563123) (@lem7563126)). Qed.
Lemma lem7563130 (_97569 : int) (_97570 : int) : (term601 _97569 _97570) = (term601 _97569 _97570).
Proof. exact (eq_refl (term601 _97569 _97570)). Qed.
Lemma lem7563131 (_97569 : int) (_97570 : int) : (term600 _97569 _97570) = (term602 _97569 _97570).
Proof. exact (MK_COMB (@lem7563130 _97569 _97570) (@lem7563127)). Qed.
Lemma lem7563132 (_97569 : int) (_97570 : int) : (term599 _97569 _97570) = (term602 _97569 _97570).
Proof. exact (TRANS (@lem7563090 _97569 _97570) (@lem7563131 _97569 _97570)). Qed.
Lemma lem7563133 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7563136 (_97571 : int) (_97569 : int) (_97570 : int) : (term598 _97571 _97569 _97570) = (term603 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563133 _97571) (@lem7563132 _97569 _97570)). Qed.
Lemma lem7563138 (_97571 : int) (_97569 : int) (_97570 : int) : (term597 _97571 _97569 _97570) = (term603 _97571 _97569 _97570).
Proof. exact (TRANS (@lem7563089 _97571 _97569 _97570) (@lem7563136 _97571 _97569 _97570)). Qed.
Lemma lem7563139 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563140 (_97571 : int) (_97569 : int) (_97570 : int) : (term604 _97571 _97569 _97570) = (term605 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563139) (@lem7563138 _97571 _97569 _97570)). Qed.
Lemma lem7563141 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563142 (_97571 : int) (_97569 : int) (_97570 : int) : (term596 _97571 _97569 _97570) = (term606 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563140 _97571 _97569 _97570) (@lem7563141)). Qed.
Lemma lem7563143 (_97571 : int) (_97569 : int) (_97570 : int) : (term503 _97569 _97570 _97571) = (term606 _97571 _97569 _97570).
Proof. exact (TRANS (@lem7563073 _97571 _97569 _97570) (@lem7563142 _97571 _97569 _97570)). Qed.
Lemma lem7563144 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563145 (_97571 : int) : (term479 _97571) = (term574 _97571).
Proof. exact (MK_COMB (@lem7563144) (@lem7563072 _97571)). Qed.
Lemma lem7563146 (_97571 : int) (_97569 : int) (_97570 : int) : (term504 _97569 _97570 _97571) = (term607 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563145 _97571) (@lem7563143 _97571 _97569 _97570)). Qed.
Lemma lem7563147 (_97571 : int) (_97570 : int) : (term477 _97570 _97571) = (term565 _97571 _97570).
Proof. exact (@lem1988287 (real_of_int _97571) (term472 _97570)). Qed.
Lemma lem7563159 (_97571 : int) (_97570 : int) : (term566 _97571 _97570) = (term567 _97571 _97570).
Proof. exact (@lem1982792 (real_of_int _97571) (term472 _97570)). Qed.
Lemma lem7563160 (_97570 : int) : (term547 _97570) = (term548 _97570).
Proof. exact (@lem1982781 (real_of_int _97570) term523 term469). Qed.
Lemma lem7563162 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563163 : term469 = term549.
Proof. exact (@lem7563162 term470). Qed.
Lemma lem7563165 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563166 : term523 = term524.
Proof. exact (@lem7563165 term470). Qed.
Lemma lem7563167 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563168 : term525 = term526.
Proof. exact (MK_COMB (@lem7563167) (@lem7563166)). Qed.
Lemma lem7563169 : term550 = term551.
Proof. exact (MK_COMB (@lem7563168) (@lem7563163)). Qed.
Lemma lem7563170 : term551 = term552.
Proof. exact (@lem1981613 term523 term469 term469 term469). Qed.
Lemma lem7563172 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563173 : term532 = term533.
Proof. exact (@lem7563172 term470 term470). Qed.
Lemma lem7563174 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563175 : term535 = term470.
Proof. exact (EQ_MP (@lem7563174) (@lem940073)). Qed.
Lemma lem7563176 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563177 : term533 = term469.
Proof. exact (MK_COMB (@lem7563176) (@lem7563175)). Qed.
Lemma lem7563178 : term532 = term469.
Proof. exact (TRANS (@lem7563173) (@lem7563177)). Qed.
Lemma lem7563180 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7563181 : term550 = term555.
Proof. exact (@lem7563180 term470 term470). Qed.
Lemma lem7563182 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563183 : term535 = term470.
Proof. exact (EQ_MP (@lem7563182) (@lem940073)). Qed.
Lemma lem7563184 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563185 : term533 = term469.
Proof. exact (MK_COMB (@lem7563184) (@lem7563183)). Qed.
Lemma lem7563186 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7563187 : term555 = term523.
Proof. exact (MK_COMB (@lem7563186) (@lem7563185)). Qed.
Lemma lem7563188 : term550 = term523.
Proof. exact (TRANS (@lem7563181) (@lem7563187)). Qed.
Lemma lem7563189 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563190 : term556 = term557.
Proof. exact (MK_COMB (@lem7563189) (@lem7563188)). Qed.
Lemma lem7563191 : term552 = term524.
Proof. exact (MK_COMB (@lem7563190) (@lem7563178)). Qed.
Lemma lem7563192 : term551 = term524.
Proof. exact (TRANS (@lem7563170) (@lem7563191)). Qed.
Lemma lem7563193 : term550 = term524.
Proof. exact (TRANS (@lem7563169) (@lem7563192)). Qed.
Lemma lem7563195 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563196 : term524 = term523.
Proof. exact (@lem7563195 term523). Qed.
Lemma lem7563197 : term550 = term523.
Proof. exact (TRANS (@lem7563193) (@lem7563196)). Qed.
Lemma lem7563200 (_97570 : int) : (term558 _97570) = (term558 _97570).
Proof. exact (eq_refl (term558 _97570)). Qed.
Lemma lem7563201 (_97570 : int) : (term548 _97570) = (term559 _97570).
Proof. exact (MK_COMB (@lem7563200 _97570) (@lem7563197)). Qed.
Lemma lem7563202 (_97570 : int) : (term547 _97570) = (term559 _97570).
Proof. exact (TRANS (@lem7563160 _97570) (@lem7563201 _97570)). Qed.
Lemma lem7563203 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7563204 (_97571 : int) (_97570 : int) : (term567 _97571 _97570) = (term568 _97571 _97570).
Proof. exact (MK_COMB (@lem7563203 _97571) (@lem7563202 _97570)). Qed.
Lemma lem7563209 (_97570 : int) (_97571 : int) : (term568 _97571 _97570) = (term569 _97570 _97571).
Proof. exact (@lem1982757 (term570 _97570) (real_of_int _97571) term523). Qed.
Lemma lem7563210 (_97570 : int) (_97571 : int) : (term567 _97571 _97570) = (term569 _97570 _97571).
Proof. exact (TRANS (@lem7563204 _97571 _97570) (@lem7563209 _97570 _97571)). Qed.
Lemma lem7563212 (_97570 : int) (_97571 : int) : (term566 _97571 _97570) = (term569 _97570 _97571).
Proof. exact (TRANS (@lem7563159 _97571 _97570) (@lem7563210 _97570 _97571)). Qed.
Lemma lem7563213 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563214 (_97570 : int) (_97571 : int) : (term571 _97571 _97570) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7563213) (@lem7563212 _97570 _97571)). Qed.
Lemma lem7563215 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563216 (_97570 : int) (_97571 : int) : (term565 _97571 _97570) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7563214 _97570 _97571) (@lem7563215)). Qed.
Lemma lem7563217 (_97570 : int) (_97571 : int) : (term477 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (TRANS (@lem7563147 _97571 _97570) (@lem7563216 _97570 _97571)). Qed.
Lemma lem7563218 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563219 (_97571 : int) (_97569 : int) (_97570 : int) : (term505 _97569 _97570 _97571) = (term608 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563218) (@lem7563146 _97571 _97569 _97570)). Qed.
Lemma lem7563220 (_97569 : int) (_97570 : int) (_97571 : int) : (term966 _97569 _97570 _97571) = (term976 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563219 _97571 _97569 _97570) (@lem7563217 _97570 _97571)). Qed.
Lemma lem7563221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563222 (_97570 : int) (_97571 : int) : (term507 _97571 _97570) = (term610 _97570 _97571).
Proof. exact (MK_COMB (@lem7563221) (@lem7563005 _97570 _97571)). Qed.
Lemma lem7563223 (_97569 : int) (_97570 : int) (_97571 : int) : (term967 _97569 _97570 _97571) = (term977 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563222 _97570 _97571) (@lem7563220 _97569 _97570 _97571)). Qed.
Lemma lem7563224 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563225 (_97569 : int) (_97570 : int) (_97571 : int) : (term968 _97569 _97571 _97570) = (term978 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563224) (@lem7562935 _97569 _97570 _97571)). Qed.
Lemma lem7563226 (_97569 : int) (_97570 : int) (_97571 : int) : (term969 _97569 _97570 _97571) = (term979 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563225 _97569 _97570 _97571) (@lem7563223 _97569 _97570 _97571)). Qed.
Lemma lem7563227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563228 (_97571 : int) : (term486 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563227) (@lem7562695 _97571)). Qed.
Lemma lem7563229 (_97569 : int) (_97570 : int) (_97571 : int) : (term970 _97569 _97570 _97571) = (term980 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563228 _97571) (@lem7563226 _97569 _97570 _97571)). Qed.
Lemma lem7563230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563231 (_97570 : int) : (term486 _97570) = (term583 _97570).
Proof. exact (MK_COMB (@lem7563230) (@lem7562647 _97570)). Qed.
Lemma lem7563232 (_97569 : int) (_97570 : int) (_97571 : int) : (term971 _97569 _97570 _97571) = (term981 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563231 _97570) (@lem7563229 _97569 _97570 _97571)). Qed.
Lemma lem7563233 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563234 (_97569 : int) : (term486 _97569) = (term583 _97569).
Proof. exact (MK_COMB (@lem7563233) (@lem7562599 _97569)). Qed.
Lemma lem7563235 (_97569 : int) (_97570 : int) (_97571 : int) : (term972 _97569 _97570 _97571) = (term982 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563234 _97569) (@lem7563232 _97569 _97570 _97571)). Qed.
Lemma lem7563242 (_97569 : int) (_97570 : int) (_97571 : int) : (term973 _97569 _97570 _97571) = (term982 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7562551 _97569 _97570 _97571) (@lem7563235 _97569 _97570 _97571)). Qed.
Lemma lem7563262 (_97569 : int) (_97570 : int) (_97571 : int) : (term977 _97569 _97570 _97571) = (term983 _97569 _97570 _97571).
Proof. exact (@lem19158 (term607 _97571 _97569 _97570) (term595 _97570 _97571) (term573 _97570 _97571)). Qed.
Lemma lem7563263 (_97570 : int) (_97571 : int) : (term618 _97570 _97571) = (term618 _97570 _97571).
Proof. exact (eq_refl (term618 _97570 _97571)). Qed.
Lemma lem7563270 (_97571 : int) (_97569 : int) (_97570 : int) : (term984 _97571 _97569 _97570) = (term985 _97571 _97569 _97570).
Proof. exact (@lem19158 (term564 _97571) (term595 _97570 _97571) (term606 _97571 _97569 _97570)). Qed.
Lemma lem7563271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563272 (_97571 : int) (_97569 : int) (_97570 : int) : (term986 _97571 _97569 _97570) = (term987 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563271) (@lem7563270 _97571 _97569 _97570)). Qed.
Lemma lem7563273 (_97569 : int) (_97570 : int) (_97571 : int) : (term983 _97569 _97570 _97571) = (term988 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563272 _97571 _97569 _97570) (@lem7563263 _97570 _97571)). Qed.
Lemma lem7563275 (_97569 : int) (_97570 : int) (_97571 : int) : (term977 _97569 _97570 _97571) = (term988 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563262 _97569 _97570 _97571) (@lem7563273 _97569 _97570 _97571)). Qed.
Lemma lem7563304 (_97569 : int) (_97570 : int) (_97571 : int) : (term975 _97569 _97570 _97571) = (term989 _97569 _97570 _97571).
Proof. exact (@lem19367 (term564 _97571) (term573 _97570 _97571) (term974 _97569 _97570 _97571)). Qed.
Lemma lem7563305 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563306 (_97569 : int) (_97570 : int) (_97571 : int) : (term978 _97569 _97570 _97571) = (term990 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563305) (@lem7563304 _97569 _97570 _97571)). Qed.
Lemma lem7563307 (_97569 : int) (_97570 : int) (_97571 : int) : (term979 _97569 _97570 _97571) = (term991 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563306 _97569 _97570 _97571) (@lem7563275 _97569 _97570 _97571)). Qed.
Lemma lem7563310 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (eq_refl (term583 _97571)). Qed.
Lemma lem7563311 (_97569 : int) (_97570 : int) (_97571 : int) : (term980 _97569 _97570 _97571) = (term992 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563310 _97571) (@lem7563307 _97569 _97570 _97571)). Qed.
Lemma lem7563312 (_97569 : int) (_97570 : int) (_97571 : int) : (term992 _97569 _97570 _97571) = (term993 _97569 _97570 _97571).
Proof. exact (@lem19158 (term989 _97569 _97570 _97571) (term543 _97571) (term988 _97569 _97570 _97571)). Qed.
Lemma lem7563313 (_97569 : int) (_97570 : int) (_97571 : int) : (term994 _97569 _97570 _97571) = (term995 _97569 _97570 _97571).
Proof. exact (@lem19158 (term985 _97571 _97569 _97570) (term543 _97571) (term618 _97570 _97571)). Qed.
Lemma lem7563314 (_97570 : int) (_97571 : int) : (term631 _97570 _97571) = (term631 _97570 _97571).
Proof. exact (eq_refl (term631 _97570 _97571)). Qed.
Lemma lem7563321 (_97571 : int) (_97569 : int) (_97570 : int) : (term996 _97571 _97569 _97570) = (term997 _97571 _97569 _97570).
Proof. exact (@lem19158 (term634 _97570 _97571) (term543 _97571) (term998 _97571 _97569 _97570)). Qed.
Lemma lem7563322 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563323 (_97571 : int) (_97569 : int) (_97570 : int) : (term999 _97571 _97569 _97570) = (term1000 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563322) (@lem7563321 _97571 _97569 _97570)). Qed.
Lemma lem7563324 (_97569 : int) (_97570 : int) (_97571 : int) : (term995 _97569 _97570 _97571) = (term1001 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563323 _97571 _97569 _97570) (@lem7563314 _97570 _97571)). Qed.
Lemma lem7563325 (_97569 : int) (_97570 : int) (_97571 : int) : (term994 _97569 _97570 _97571) = (term1001 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563313 _97569 _97570 _97571) (@lem7563324 _97569 _97570 _97571)). Qed.
Lemma lem7563332 (_97569 : int) (_97570 : int) (_97571 : int) : (term1002 _97569 _97570 _97571) = (term1003 _97569 _97570 _97571).
Proof. exact (@lem19158 (term1004 _97569 _97570 _97571) (term543 _97571) (term1005 _97569 _97570 _97571)). Qed.
Lemma lem7563333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563334 (_97569 : int) (_97570 : int) (_97571 : int) : (term1006 _97569 _97570 _97571) = (term1007 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563333) (@lem7563332 _97569 _97570 _97571)). Qed.
Lemma lem7563335 (_97569 : int) (_97570 : int) (_97571 : int) : (term993 _97569 _97570 _97571) = (term1008 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563334 _97569 _97570 _97571) (@lem7563325 _97569 _97570 _97571)). Qed.
Lemma lem7563336 (_97569 : int) (_97570 : int) (_97571 : int) : (term992 _97569 _97570 _97571) = (term1008 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563312 _97569 _97570 _97571) (@lem7563335 _97569 _97570 _97571)). Qed.
Lemma lem7563337 (_97569 : int) (_97570 : int) (_97571 : int) : (term980 _97569 _97570 _97571) = (term1008 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563311 _97569 _97570 _97571) (@lem7563336 _97569 _97570 _97571)). Qed.
Lemma lem7563340 (_97570 : int) : (term583 _97570) = (term583 _97570).
Proof. exact (eq_refl (term583 _97570)). Qed.
Lemma lem7563341 (_97569 : int) (_97570 : int) (_97571 : int) : (term981 _97569 _97570 _97571) = (term1009 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563340 _97570) (@lem7563337 _97569 _97570 _97571)). Qed.
Lemma lem7563342 (_97569 : int) (_97570 : int) (_97571 : int) : (term1009 _97569 _97570 _97571) = (term1010 _97569 _97570 _97571).
Proof. exact (@lem19158 (term1003 _97569 _97570 _97571) (term543 _97570) (term1001 _97569 _97570 _97571)). Qed.
Lemma lem7563343 (_97569 : int) (_97570 : int) (_97571 : int) : (term1011 _97569 _97570 _97571) = (term1012 _97569 _97570 _97571).
Proof. exact (@lem19158 (term997 _97571 _97569 _97570) (term543 _97570) (term631 _97570 _97571)). Qed.
Lemma lem7563344 (_97570 : int) (_97571 : int) : (term1013 _97570 _97571) = (term1013 _97570 _97571).
Proof. exact (eq_refl (term1013 _97570 _97571)). Qed.
Lemma lem7563351 (_97571 : int) (_97569 : int) (_97570 : int) : (term1014 _97571 _97569 _97570) = (term1015 _97571 _97569 _97570).
Proof. exact (@lem19158 (term653 _97570 _97571) (term543 _97570) (term1016 _97571 _97569 _97570)). Qed.
Lemma lem7563352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563353 (_97571 : int) (_97569 : int) (_97570 : int) : (term1017 _97571 _97569 _97570) = (term1018 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563352) (@lem7563351 _97571 _97569 _97570)). Qed.
Lemma lem7563354 (_97569 : int) (_97570 : int) (_97571 : int) : (term1012 _97569 _97570 _97571) = (term1019 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563353 _97571 _97569 _97570) (@lem7563344 _97570 _97571)). Qed.
Lemma lem7563355 (_97569 : int) (_97570 : int) (_97571 : int) : (term1011 _97569 _97570 _97571) = (term1019 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563343 _97569 _97570 _97571) (@lem7563354 _97569 _97570 _97571)). Qed.
Lemma lem7563362 (_97569 : int) (_97570 : int) (_97571 : int) : (term1020 _97569 _97570 _97571) = (term1021 _97569 _97570 _97571).
Proof. exact (@lem19158 (term1022 _97569 _97570 _97571) (term543 _97570) (term1023 _97569 _97570 _97571)). Qed.
Lemma lem7563363 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563364 (_97569 : int) (_97570 : int) (_97571 : int) : (term1024 _97569 _97570 _97571) = (term1025 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563363) (@lem7563362 _97569 _97570 _97571)). Qed.
Lemma lem7563365 (_97569 : int) (_97570 : int) (_97571 : int) : (term1010 _97569 _97570 _97571) = (term1026 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563364 _97569 _97570 _97571) (@lem7563355 _97569 _97570 _97571)). Qed.
Lemma lem7563366 (_97569 : int) (_97570 : int) (_97571 : int) : (term1009 _97569 _97570 _97571) = (term1026 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563342 _97569 _97570 _97571) (@lem7563365 _97569 _97570 _97571)). Qed.
Lemma lem7563367 (_97569 : int) (_97570 : int) (_97571 : int) : (term981 _97569 _97570 _97571) = (term1026 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563341 _97569 _97570 _97571) (@lem7563366 _97569 _97570 _97571)). Qed.
Lemma lem7563370 (_97569 : int) : (term583 _97569) = (term583 _97569).
Proof. exact (eq_refl (term583 _97569)). Qed.
Lemma lem7563371 (_97569 : int) (_97570 : int) (_97571 : int) : (term982 _97569 _97570 _97571) = (term1027 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563370 _97569) (@lem7563367 _97569 _97570 _97571)). Qed.
Lemma lem7563372 (_97569 : int) (_97570 : int) (_97571 : int) : (term1027 _97569 _97570 _97571) = (term1028 _97569 _97570 _97571).
Proof. exact (@lem19158 (term1021 _97569 _97570 _97571) (term543 _97569) (term1019 _97569 _97570 _97571)). Qed.
Lemma lem7563373 (_97569 : int) (_97570 : int) (_97571 : int) : (term1029 _97569 _97570 _97571) = (term1030 _97569 _97570 _97571).
Proof. exact (@lem19158 (term1015 _97571 _97569 _97570) (term543 _97569) (term1013 _97570 _97571)). Qed.
Lemma lem7563374 (_97569 : int) (_97570 : int) (_97571 : int) : (term1031 _97569 _97570 _97571) = (term1031 _97569 _97570 _97571).
Proof. exact (eq_refl (term1031 _97569 _97570 _97571)). Qed.
Lemma lem7563381 (_97571 : int) (_97569 : int) (_97570 : int) : (term1032 _97571 _97569 _97570) = (term1033 _97571 _97569 _97570).
Proof. exact (@lem19158 (term1034 _97570 _97571) (term543 _97569) (term1035 _97571 _97569 _97570)). Qed.
Lemma lem7563382 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563383 (_97571 : int) (_97569 : int) (_97570 : int) : (term1036 _97571 _97569 _97570) = (term1037 _97571 _97569 _97570).
Proof. exact (MK_COMB (@lem7563382) (@lem7563381 _97571 _97569 _97570)). Qed.
Lemma lem7563384 (_97569 : int) (_97570 : int) (_97571 : int) : (term1030 _97569 _97570 _97571) = (term1038 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563383 _97571 _97569 _97570) (@lem7563374 _97569 _97570 _97571)). Qed.
Lemma lem7563385 (_97569 : int) (_97570 : int) (_97571 : int) : (term1029 _97569 _97570 _97571) = (term1038 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563373 _97569 _97570 _97571) (@lem7563384 _97569 _97570 _97571)). Qed.
Lemma lem7563392 (_97569 : int) (_97570 : int) (_97571 : int) : (term1039 _97569 _97570 _97571) = (term1040 _97569 _97570 _97571).
Proof. exact (@lem19158 (term1041 _97569 _97570 _97571) (term543 _97569) (term1042 _97569 _97570 _97571)). Qed.
Lemma lem7563393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563394 (_97569 : int) (_97570 : int) (_97571 : int) : (term1043 _97569 _97570 _97571) = (term1044 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563393) (@lem7563392 _97569 _97570 _97571)). Qed.
Lemma lem7563395 (_97569 : int) (_97570 : int) (_97571 : int) : (term1028 _97569 _97570 _97571) = (term1045 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563394 _97569 _97570 _97571) (@lem7563385 _97569 _97570 _97571)). Qed.
Lemma lem7563396 (_97569 : int) (_97570 : int) (_97571 : int) : (term1027 _97569 _97570 _97571) = (term1045 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563372 _97569 _97570 _97571) (@lem7563395 _97569 _97570 _97571)). Qed.
Lemma lem7563397 (_97569 : int) (_97570 : int) (_97571 : int) : (term982 _97569 _97570 _97571) = (term1045 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563371 _97569 _97570 _97571) (@lem7563396 _97569 _97570 _97571)). Qed.
Lemma lem7563398 (_97569 : int) (_97570 : int) (_97571 : int) : (term973 _97569 _97570 _97571) = (term1045 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563242 _97569 _97570 _97571) (@lem7563397 _97569 _97570 _97571)). Qed.
Lemma lem7563400 (_97569 : int) (_97570 : int) (_97571 : int) : (term1046 _97571 _97569 _97570) = (term1047 _97569 _97570 _97571).
Proof. exact (eq_refl (term1046 _97571 _97569 _97570)). Qed.
Lemma lem7563401 (_97571 : int) (_97569 : int) (_97570 : int) : (term1047 _97569 _97570 _97571) = (term1046 _97571 _97569 _97570).
Proof. exact (SYM (@lem7563400 _97569 _97570 _97571)). Qed.
Lemma lem7563402 (_97570 : int) (_97571 : int) (_97569 : int) : (term1046 _97571 _97569 _97570) = (term1048 _97570 _97571 _97569).
Proof. exact (@lem1483205 (real_of_int _97570) (term1049 _97569 _97570 _97571) (real_of_int _97569)). Qed.
Lemma lem7563403 (_97570 : int) (_97571 : int) (_97569 : int) : (term1047 _97569 _97570 _97571) = (term1048 _97570 _97571 _97569).
Proof. exact (TRANS (@lem7563401 _97571 _97569 _97570) (@lem7563402 _97570 _97571 _97569)). Qed.
Lemma lem7563404 (_97569 : int) (_97570 : int) (_97571 : int) : (term1050 _97570 _97571 _97569) = (term1051 _97569 _97570 _97571).
Proof. exact (eq_refl (term1050 _97570 _97571 _97569)). Qed.
Lemma lem7563405 (_97569 : int) (_97570 : int) : (term690 _97569 _97570) = (term690 _97569 _97570).
Proof. exact (eq_refl (term690 _97569 _97570)). Qed.
Lemma lem7563406 (_97569 : int) (_97570 : int) (_97571 : int) : (term1052 _97570 _97571 _97569) = (term1053 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563405 _97569 _97570) (@lem7563404 _97569 _97570 _97571)). Qed.
Lemma lem7563407 (_97569 : int) (_97570 : int) (_97571 : int) : (term1054 _97569 _97571 _97570) = (term1055 _97569 _97570 _97571).
Proof. exact (eq_refl (term1054 _97569 _97571 _97570)). Qed.
Lemma lem7563408 (_97570 : int) (_97569 : int) : (term695 _97570 _97569) = (term695 _97570 _97569).
Proof. exact (eq_refl (term695 _97570 _97569)). Qed.
Lemma lem7563409 (_97569 : int) (_97570 : int) (_97571 : int) : (term1056 _97569 _97571 _97570) = (term1057 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563408 _97570 _97569) (@lem7563407 _97569 _97570 _97571)). Qed.
Lemma lem7563410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563411 (_97569 : int) (_97570 : int) (_97571 : int) : (term1058 _97569 _97571 _97570) = (term1059 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563410) (@lem7563409 _97569 _97570 _97571)). Qed.
Lemma lem7563412 (_97569 : int) (_97570 : int) (_97571 : int) : (term1048 _97570 _97571 _97569) = (term1060 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563411 _97569 _97570 _97571) (@lem7563406 _97569 _97570 _97571)). Qed.
Lemma lem7563413 (_97569 : int) (_97570 : int) (_97571 : int) : (term1061 _97569 _97570 _97571) = (term1061 _97569 _97570 _97571).
Proof. exact (eq_refl (term1061 _97569 _97570 _97571)). Qed.
Lemma lem7563414 (_97569 : int) (_97570 : int) (_97571 : int) : ((term1047 _97569 _97570 _97571) = (term1048 _97570 _97571 _97569)) = ((term1047 _97569 _97570 _97571) = (term1060 _97569 _97570 _97571)).
Proof. exact (MK_COMB (@lem7563413 _97569 _97570 _97571) (@lem7563412 _97569 _97570 _97571)). Qed.
Lemma lem7563415 (_97569 : int) (_97570 : int) (_97571 : int) : (term1047 _97569 _97570 _97571) = (term1060 _97569 _97570 _97571).
Proof. exact (EQ_MP (@lem7563414 _97569 _97570 _97571) (@lem7563403 _97570 _97571 _97569)). Qed.
Lemma lem7563416 (_97570 : int) (_97569 : int) : (term702 _97570 _97569) = (term585 _97570 _97569).
Proof. exact (@lem1988291 (real_of_int _97570) (real_of_int _97569)). Qed.
Lemma lem7563422 (_97570 : int) (_97569 : int) : (term586 _97570 _97569) = (term587 _97570 _97569).
Proof. exact (@lem1982792 (real_of_int _97570) (real_of_int _97569)). Qed.
Lemma lem7563427 (_97569 : int) (_97570 : int) : (term587 _97570 _97569) = (term703 _97569 _97570).
Proof. exact (@lem1982761 (term570 _97569) (real_of_int _97570)). Qed.
Lemma lem7563429 (_97569 : int) (_97570 : int) : (term586 _97570 _97569) = (term703 _97569 _97570).
Proof. exact (TRANS (@lem7563422 _97570 _97569) (@lem7563427 _97569 _97570)). Qed.
Lemma lem7563430 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563431 (_97569 : int) (_97570 : int) : (term588 _97570 _97569) = (term704 _97569 _97570).
Proof. exact (MK_COMB (@lem7563430) (@lem7563429 _97569 _97570)). Qed.
Lemma lem7563432 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563433 (_97569 : int) (_97570 : int) : (term585 _97570 _97569) = (term705 _97569 _97570).
Proof. exact (MK_COMB (@lem7563431 _97569 _97570) (@lem7563432)). Qed.
Lemma lem7563434 (_97569 : int) (_97570 : int) : (term702 _97570 _97569) = (term705 _97569 _97570).
Proof. exact (TRANS (@lem7563416 _97570 _97569) (@lem7563433 _97569 _97570)). Qed.
Lemma lem7563435 (_97569 : int) : (term543 _97569) = (term516 _97569).
Proof. exact (@lem1988291 (real_of_int _97569) term35). Qed.
Lemma lem7563441 (_97569 : int) : (term517 _97569) = (term518 _97569).
Proof. exact (@lem1982792 (real_of_int _97569) term35). Qed.
Lemma lem7563443 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563444 : term35 = term520.
Proof. exact (@lem7563443 (NUMERAL 0)). Qed.
Lemma lem7563446 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563447 : term523 = term524.
Proof. exact (@lem7563446 term470). Qed.
Lemma lem7563448 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563449 : term525 = term526.
Proof. exact (MK_COMB (@lem7563448) (@lem7563447)). Qed.
Lemma lem7563450 : term527 = term528.
Proof. exact (MK_COMB (@lem7563449) (@lem7563444)). Qed.
Lemma lem7563451 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563453 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563454 : term532 = term533.
Proof. exact (@lem7563453 term470 term470). Qed.
Lemma lem7563455 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563456 : term535 = term470.
Proof. exact (EQ_MP (@lem7563455) (@lem940073)). Qed.
Lemma lem7563457 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563458 : term533 = term469.
Proof. exact (MK_COMB (@lem7563457) (@lem7563456)). Qed.
Lemma lem7563459 : term532 = term469.
Proof. exact (TRANS (@lem7563454) (@lem7563458)). Qed.
Lemma lem7563461 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563462 : term527 = term35.
Proof. exact (@lem7563461 term470). Qed.
Lemma lem7563463 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563464 : term537 = term538.
Proof. exact (MK_COMB (@lem7563463) (@lem7563462)). Qed.
Lemma lem7563465 : term529 = term520.
Proof. exact (MK_COMB (@lem7563464) (@lem7563459)). Qed.
Lemma lem7563466 : term528 = term520.
Proof. exact (TRANS (@lem7563451) (@lem7563465)). Qed.
Lemma lem7563467 : term527 = term520.
Proof. exact (TRANS (@lem7563450) (@lem7563466)). Qed.
Lemma lem7563469 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563470 : term520 = term35.
Proof. exact (@lem7563469 term35). Qed.
Lemma lem7563471 : term527 = term35.
Proof. exact (TRANS (@lem7563467) (@lem7563470)). Qed.
Lemma lem7563472 (_97569 : int) : (term471 _97569) = (term471 _97569).
Proof. exact (eq_refl (term471 _97569)). Qed.
Lemma lem7563473 (_97569 : int) : (term518 _97569) = (term540 _97569).
Proof. exact (MK_COMB (@lem7563472 _97569) (@lem7563471)). Qed.
Lemma lem7563474 (_97569 : int) : (term540 _97569) = (real_of_int _97569).
Proof. exact (@lem1982723 (real_of_int _97569)). Qed.
Lemma lem7563475 (_97569 : int) : (term518 _97569) = (real_of_int _97569).
Proof. exact (TRANS (@lem7563473 _97569) (@lem7563474 _97569)). Qed.
Lemma lem7563477 (_97569 : int) : (term517 _97569) = (real_of_int _97569).
Proof. exact (TRANS (@lem7563441 _97569) (@lem7563475 _97569)). Qed.
Lemma lem7563478 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563479 (_97569 : int) : (term541 _97569) = (term542 _97569).
Proof. exact (MK_COMB (@lem7563478) (@lem7563477 _97569)). Qed.
Lemma lem7563480 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563481 (_97569 : int) : (term516 _97569) = (term543 _97569).
Proof. exact (MK_COMB (@lem7563479 _97569) (@lem7563480)). Qed.
Lemma lem7563482 (_97569 : int) : (term543 _97569) = (term543 _97569).
Proof. exact (TRANS (@lem7563435 _97569) (@lem7563481 _97569)). Qed.
Lemma lem7563483 (_97570 : int) : (term543 _97570) = (term516 _97570).
Proof. exact (@lem1988291 (real_of_int _97570) term35). Qed.
Lemma lem7563489 (_97570 : int) : (term517 _97570) = (term518 _97570).
Proof. exact (@lem1982792 (real_of_int _97570) term35). Qed.
Lemma lem7563491 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563492 : term35 = term520.
Proof. exact (@lem7563491 (NUMERAL 0)). Qed.
Lemma lem7563494 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563495 : term523 = term524.
Proof. exact (@lem7563494 term470). Qed.
Lemma lem7563496 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563497 : term525 = term526.
Proof. exact (MK_COMB (@lem7563496) (@lem7563495)). Qed.
Lemma lem7563498 : term527 = term528.
Proof. exact (MK_COMB (@lem7563497) (@lem7563492)). Qed.
Lemma lem7563499 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563501 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563502 : term532 = term533.
Proof. exact (@lem7563501 term470 term470). Qed.
Lemma lem7563503 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563504 : term535 = term470.
Proof. exact (EQ_MP (@lem7563503) (@lem940073)). Qed.
Lemma lem7563505 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563506 : term533 = term469.
Proof. exact (MK_COMB (@lem7563505) (@lem7563504)). Qed.
Lemma lem7563507 : term532 = term469.
Proof. exact (TRANS (@lem7563502) (@lem7563506)). Qed.
Lemma lem7563509 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563510 : term527 = term35.
Proof. exact (@lem7563509 term470). Qed.
Lemma lem7563511 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563512 : term537 = term538.
Proof. exact (MK_COMB (@lem7563511) (@lem7563510)). Qed.
Lemma lem7563513 : term529 = term520.
Proof. exact (MK_COMB (@lem7563512) (@lem7563507)). Qed.
Lemma lem7563514 : term528 = term520.
Proof. exact (TRANS (@lem7563499) (@lem7563513)). Qed.
Lemma lem7563515 : term527 = term520.
Proof. exact (TRANS (@lem7563498) (@lem7563514)). Qed.
Lemma lem7563517 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563518 : term520 = term35.
Proof. exact (@lem7563517 term35). Qed.
Lemma lem7563519 : term527 = term35.
Proof. exact (TRANS (@lem7563515) (@lem7563518)). Qed.
Lemma lem7563520 (_97570 : int) : (term471 _97570) = (term471 _97570).
Proof. exact (eq_refl (term471 _97570)). Qed.
Lemma lem7563521 (_97570 : int) : (term518 _97570) = (term540 _97570).
Proof. exact (MK_COMB (@lem7563520 _97570) (@lem7563519)). Qed.
Lemma lem7563522 (_97570 : int) : (term540 _97570) = (real_of_int _97570).
Proof. exact (@lem1982723 (real_of_int _97570)). Qed.
Lemma lem7563523 (_97570 : int) : (term518 _97570) = (real_of_int _97570).
Proof. exact (TRANS (@lem7563521 _97570) (@lem7563522 _97570)). Qed.
Lemma lem7563525 (_97570 : int) : (term517 _97570) = (real_of_int _97570).
Proof. exact (TRANS (@lem7563489 _97570) (@lem7563523 _97570)). Qed.
Lemma lem7563526 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563527 (_97570 : int) : (term541 _97570) = (term542 _97570).
Proof. exact (MK_COMB (@lem7563526) (@lem7563525 _97570)). Qed.
Lemma lem7563528 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563529 (_97570 : int) : (term516 _97570) = (term543 _97570).
Proof. exact (MK_COMB (@lem7563527 _97570) (@lem7563528)). Qed.
Lemma lem7563530 (_97570 : int) : (term543 _97570) = (term543 _97570).
Proof. exact (TRANS (@lem7563483 _97570) (@lem7563529 _97570)). Qed.
Lemma lem7563531 (_97571 : int) : (term543 _97571) = (term516 _97571).
Proof. exact (@lem1988291 (real_of_int _97571) term35). Qed.
Lemma lem7563537 (_97571 : int) : (term517 _97571) = (term518 _97571).
Proof. exact (@lem1982792 (real_of_int _97571) term35). Qed.
Lemma lem7563539 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563540 : term35 = term520.
Proof. exact (@lem7563539 (NUMERAL 0)). Qed.
Lemma lem7563542 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563543 : term523 = term524.
Proof. exact (@lem7563542 term470). Qed.
Lemma lem7563544 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563545 : term525 = term526.
Proof. exact (MK_COMB (@lem7563544) (@lem7563543)). Qed.
Lemma lem7563546 : term527 = term528.
Proof. exact (MK_COMB (@lem7563545) (@lem7563540)). Qed.
Lemma lem7563547 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563549 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563550 : term532 = term533.
Proof. exact (@lem7563549 term470 term470). Qed.
Lemma lem7563551 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563552 : term535 = term470.
Proof. exact (EQ_MP (@lem7563551) (@lem940073)). Qed.
Lemma lem7563553 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563554 : term533 = term469.
Proof. exact (MK_COMB (@lem7563553) (@lem7563552)). Qed.
Lemma lem7563555 : term532 = term469.
Proof. exact (TRANS (@lem7563550) (@lem7563554)). Qed.
Lemma lem7563557 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563558 : term527 = term35.
Proof. exact (@lem7563557 term470). Qed.
Lemma lem7563559 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563560 : term537 = term538.
Proof. exact (MK_COMB (@lem7563559) (@lem7563558)). Qed.
Lemma lem7563561 : term529 = term520.
Proof. exact (MK_COMB (@lem7563560) (@lem7563555)). Qed.
Lemma lem7563562 : term528 = term520.
Proof. exact (TRANS (@lem7563547) (@lem7563561)). Qed.
Lemma lem7563563 : term527 = term520.
Proof. exact (TRANS (@lem7563546) (@lem7563562)). Qed.
Lemma lem7563565 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563566 : term520 = term35.
Proof. exact (@lem7563565 term35). Qed.
Lemma lem7563567 : term527 = term35.
Proof. exact (TRANS (@lem7563563) (@lem7563566)). Qed.
Lemma lem7563568 (_97571 : int) : (term471 _97571) = (term471 _97571).
Proof. exact (eq_refl (term471 _97571)). Qed.
Lemma lem7563569 (_97571 : int) : (term518 _97571) = (term540 _97571).
Proof. exact (MK_COMB (@lem7563568 _97571) (@lem7563567)). Qed.
Lemma lem7563570 (_97571 : int) : (term540 _97571) = (real_of_int _97571).
Proof. exact (@lem1982723 (real_of_int _97571)). Qed.
Lemma lem7563571 (_97571 : int) : (term518 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7563569 _97571) (@lem7563570 _97571)). Qed.
Lemma lem7563573 (_97571 : int) : (term517 _97571) = (real_of_int _97571).
Proof. exact (TRANS (@lem7563537 _97571) (@lem7563571 _97571)). Qed.
Lemma lem7563574 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563575 (_97571 : int) : (term541 _97571) = (term542 _97571).
Proof. exact (MK_COMB (@lem7563574) (@lem7563573 _97571)). Qed.
Lemma lem7563576 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563577 (_97571 : int) : (term516 _97571) = (term543 _97571).
Proof. exact (MK_COMB (@lem7563575 _97571) (@lem7563576)). Qed.
Lemma lem7563578 (_97571 : int) : (term543 _97571) = (term543 _97571).
Proof. exact (TRANS (@lem7563531 _97571) (@lem7563577 _97571)). Qed.
Lemma lem7563579 (_97571 : int) : (term564 _97571) = (term706 _97571).
Proof. exact (@lem1988291 (term559 _97571) term35). Qed.
Lemma lem7563597 (_97571 : int) : (term707 _97571) = (term708 _97571).
Proof. exact (@lem1982792 (term559 _97571) term35). Qed.
Lemma lem7563599 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563600 : term35 = term520.
Proof. exact (@lem7563599 (NUMERAL 0)). Qed.
Lemma lem7563602 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563603 : term523 = term524.
Proof. exact (@lem7563602 term470). Qed.
Lemma lem7563604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563605 : term525 = term526.
Proof. exact (MK_COMB (@lem7563604) (@lem7563603)). Qed.
Lemma lem7563606 : term527 = term528.
Proof. exact (MK_COMB (@lem7563605) (@lem7563600)). Qed.
Lemma lem7563607 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563609 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563610 : term532 = term533.
Proof. exact (@lem7563609 term470 term470). Qed.
Lemma lem7563611 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563612 : term535 = term470.
Proof. exact (EQ_MP (@lem7563611) (@lem940073)). Qed.
Lemma lem7563613 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563614 : term533 = term469.
Proof. exact (MK_COMB (@lem7563613) (@lem7563612)). Qed.
Lemma lem7563615 : term532 = term469.
Proof. exact (TRANS (@lem7563610) (@lem7563614)). Qed.
Lemma lem7563617 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563618 : term527 = term35.
Proof. exact (@lem7563617 term470). Qed.
Lemma lem7563619 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563620 : term537 = term538.
Proof. exact (MK_COMB (@lem7563619) (@lem7563618)). Qed.
Lemma lem7563621 : term529 = term520.
Proof. exact (MK_COMB (@lem7563620) (@lem7563615)). Qed.
Lemma lem7563622 : term528 = term520.
Proof. exact (TRANS (@lem7563607) (@lem7563621)). Qed.
Lemma lem7563623 : term527 = term520.
Proof. exact (TRANS (@lem7563606) (@lem7563622)). Qed.
Lemma lem7563625 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563626 : term520 = term35.
Proof. exact (@lem7563625 term35). Qed.
Lemma lem7563627 : term527 = term35.
Proof. exact (TRANS (@lem7563623) (@lem7563626)). Qed.
Lemma lem7563628 (_97571 : int) : (term709 _97571) = (term709 _97571).
Proof. exact (eq_refl (term709 _97571)). Qed.
Lemma lem7563629 (_97571 : int) : (term708 _97571) = (term710 _97571).
Proof. exact (MK_COMB (@lem7563628 _97571) (@lem7563627)). Qed.
Lemma lem7563630 (_97571 : int) : (term710 _97571) = (term559 _97571).
Proof. exact (@lem1982723 (term559 _97571)). Qed.
Lemma lem7563631 (_97571 : int) : (term708 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7563629 _97571) (@lem7563630 _97571)). Qed.
Lemma lem7563633 (_97571 : int) : (term707 _97571) = (term559 _97571).
Proof. exact (TRANS (@lem7563597 _97571) (@lem7563631 _97571)). Qed.
Lemma lem7563634 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563635 (_97571 : int) : (term711 _97571) = (term563 _97571).
Proof. exact (MK_COMB (@lem7563634) (@lem7563633 _97571)). Qed.
Lemma lem7563636 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563637 (_97571 : int) : (term706 _97571) = (term564 _97571).
Proof. exact (MK_COMB (@lem7563635 _97571) (@lem7563636)). Qed.
Lemma lem7563638 (_97571 : int) : (term564 _97571) = (term564 _97571).
Proof. exact (TRANS (@lem7563579 _97571) (@lem7563637 _97571)). Qed.
Lemma lem7563639 (_97571 : int) (_97570 : int) : (term705 _97571 _97570) = (term712 _97571 _97570).
Proof. exact (@lem1988291 (term703 _97571 _97570) term35). Qed.
Lemma lem7563640 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563653 (_97570 : int) (_97571 : int) : (term703 _97571 _97570) = (term587 _97570 _97571).
Proof. exact (@lem1982761 (real_of_int _97570) (term570 _97571)). Qed.
Lemma lem7563654 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7563655 (_97570 : int) (_97571 : int) : (term713 _97571 _97570) = (term714 _97570 _97571).
Proof. exact (MK_COMB (@lem7563654) (@lem7563653 _97570 _97571)). Qed.
Lemma lem7563656 (_97570 : int) (_97571 : int) : (term715 _97571 _97570) = (term716 _97570 _97571).
Proof. exact (MK_COMB (@lem7563655 _97570 _97571) (@lem7563640)). Qed.
Lemma lem7563657 (_97570 : int) (_97571 : int) : (term716 _97570 _97571) = (term717 _97570 _97571).
Proof. exact (@lem1982792 (term587 _97570 _97571) term35). Qed.
Lemma lem7563659 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563660 : term35 = term520.
Proof. exact (@lem7563659 (NUMERAL 0)). Qed.
Lemma lem7563662 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563663 : term523 = term524.
Proof. exact (@lem7563662 term470). Qed.
Lemma lem7563664 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563665 : term525 = term526.
Proof. exact (MK_COMB (@lem7563664) (@lem7563663)). Qed.
Lemma lem7563666 : term527 = term528.
Proof. exact (MK_COMB (@lem7563665) (@lem7563660)). Qed.
Lemma lem7563667 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563669 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563670 : term532 = term533.
Proof. exact (@lem7563669 term470 term470). Qed.
Lemma lem7563671 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563672 : term535 = term470.
Proof. exact (EQ_MP (@lem7563671) (@lem940073)). Qed.
Lemma lem7563673 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563674 : term533 = term469.
Proof. exact (MK_COMB (@lem7563673) (@lem7563672)). Qed.
Lemma lem7563675 : term532 = term469.
Proof. exact (TRANS (@lem7563670) (@lem7563674)). Qed.
Lemma lem7563677 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563678 : term527 = term35.
Proof. exact (@lem7563677 term470). Qed.
Lemma lem7563679 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563680 : term537 = term538.
Proof. exact (MK_COMB (@lem7563679) (@lem7563678)). Qed.
Lemma lem7563681 : term529 = term520.
Proof. exact (MK_COMB (@lem7563680) (@lem7563675)). Qed.
Lemma lem7563682 : term528 = term520.
Proof. exact (TRANS (@lem7563667) (@lem7563681)). Qed.
Lemma lem7563683 : term527 = term520.
Proof. exact (TRANS (@lem7563666) (@lem7563682)). Qed.
Lemma lem7563685 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563686 : term520 = term35.
Proof. exact (@lem7563685 term35). Qed.
Lemma lem7563687 : term527 = term35.
Proof. exact (TRANS (@lem7563683) (@lem7563686)). Qed.
Lemma lem7563688 (_97570 : int) (_97571 : int) : (term718 _97570 _97571) = (term718 _97570 _97571).
Proof. exact (eq_refl (term718 _97570 _97571)). Qed.
Lemma lem7563689 (_97570 : int) (_97571 : int) : (term717 _97570 _97571) = (term719 _97570 _97571).
Proof. exact (MK_COMB (@lem7563688 _97570 _97571) (@lem7563687)). Qed.
Lemma lem7563690 (_97570 : int) (_97571 : int) : (term719 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982723 (term587 _97570 _97571)). Qed.
Lemma lem7563691 (_97570 : int) (_97571 : int) : (term717 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (TRANS (@lem7563689 _97570 _97571) (@lem7563690 _97570 _97571)). Qed.
Lemma lem7563692 (_97570 : int) (_97571 : int) : (term716 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (TRANS (@lem7563657 _97570 _97571) (@lem7563691 _97570 _97571)). Qed.
Lemma lem7563693 (_97570 : int) (_97571 : int) : (term715 _97571 _97570) = (term587 _97570 _97571).
Proof. exact (TRANS (@lem7563656 _97570 _97571) (@lem7563692 _97570 _97571)). Qed.
Lemma lem7563694 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563695 (_97570 : int) (_97571 : int) : (term720 _97571 _97570) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7563694) (@lem7563693 _97570 _97571)). Qed.
Lemma lem7563696 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563697 (_97570 : int) (_97571 : int) : (term712 _97571 _97570) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7563695 _97570 _97571) (@lem7563696)). Qed.
Lemma lem7563698 (_97570 : int) (_97571 : int) : (term705 _97571 _97570) = (term590 _97570 _97571).
Proof. exact (TRANS (@lem7563639 _97571 _97570) (@lem7563697 _97570 _97571)). Qed.
Lemma lem7563699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563700 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563699) (@lem7563578 _97571)). Qed.
Lemma lem7563701 (_97570 : int) (_97571 : int) : (term721 _97571 _97570) = (term595 _97570 _97571).
Proof. exact (MK_COMB (@lem7563700 _97571) (@lem7563698 _97570 _97571)). Qed.
Lemma lem7563702 (_97570 : int) (_97571 : int) : (term590 _97570 _97571) = (term722 _97570 _97571).
Proof. exact (@lem1988291 (term587 _97570 _97571) term35). Qed.
Lemma lem7563720 (_97570 : int) (_97571 : int) : (term716 _97570 _97571) = (term717 _97570 _97571).
Proof. exact (@lem1982792 (term587 _97570 _97571) term35). Qed.
Lemma lem7563722 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563723 : term35 = term520.
Proof. exact (@lem7563722 (NUMERAL 0)). Qed.
Lemma lem7563725 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563726 : term523 = term524.
Proof. exact (@lem7563725 term470). Qed.
Lemma lem7563727 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563728 : term525 = term526.
Proof. exact (MK_COMB (@lem7563727) (@lem7563726)). Qed.
Lemma lem7563729 : term527 = term528.
Proof. exact (MK_COMB (@lem7563728) (@lem7563723)). Qed.
Lemma lem7563730 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563732 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563733 : term532 = term533.
Proof. exact (@lem7563732 term470 term470). Qed.
Lemma lem7563734 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563735 : term535 = term470.
Proof. exact (EQ_MP (@lem7563734) (@lem940073)). Qed.
Lemma lem7563736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563737 : term533 = term469.
Proof. exact (MK_COMB (@lem7563736) (@lem7563735)). Qed.
Lemma lem7563738 : term532 = term469.
Proof. exact (TRANS (@lem7563733) (@lem7563737)). Qed.
Lemma lem7563740 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563741 : term527 = term35.
Proof. exact (@lem7563740 term470). Qed.
Lemma lem7563742 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563743 : term537 = term538.
Proof. exact (MK_COMB (@lem7563742) (@lem7563741)). Qed.
Lemma lem7563744 : term529 = term520.
Proof. exact (MK_COMB (@lem7563743) (@lem7563738)). Qed.
Lemma lem7563745 : term528 = term520.
Proof. exact (TRANS (@lem7563730) (@lem7563744)). Qed.
Lemma lem7563746 : term527 = term520.
Proof. exact (TRANS (@lem7563729) (@lem7563745)). Qed.
Lemma lem7563748 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563749 : term520 = term35.
Proof. exact (@lem7563748 term35). Qed.
Lemma lem7563750 : term527 = term35.
Proof. exact (TRANS (@lem7563746) (@lem7563749)). Qed.
Lemma lem7563751 (_97570 : int) (_97571 : int) : (term718 _97570 _97571) = (term718 _97570 _97571).
Proof. exact (eq_refl (term718 _97570 _97571)). Qed.
Lemma lem7563752 (_97570 : int) (_97571 : int) : (term717 _97570 _97571) = (term719 _97570 _97571).
Proof. exact (MK_COMB (@lem7563751 _97570 _97571) (@lem7563750)). Qed.
Lemma lem7563753 (_97570 : int) (_97571 : int) : (term719 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982723 (term587 _97570 _97571)). Qed.
Lemma lem7563754 (_97570 : int) (_97571 : int) : (term717 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (TRANS (@lem7563752 _97570 _97571) (@lem7563753 _97570 _97571)). Qed.
Lemma lem7563756 (_97570 : int) (_97571 : int) : (term716 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (TRANS (@lem7563720 _97570 _97571) (@lem7563754 _97570 _97571)). Qed.
Lemma lem7563757 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563758 (_97570 : int) (_97571 : int) : (term723 _97570 _97571) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7563757) (@lem7563756 _97570 _97571)). Qed.
Lemma lem7563759 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563760 (_97570 : int) (_97571 : int) : (term722 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7563758 _97570 _97571) (@lem7563759)). Qed.
Lemma lem7563761 (_97570 : int) (_97571 : int) : (term590 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (TRANS (@lem7563702 _97570 _97571) (@lem7563760 _97570 _97571)). Qed.
Lemma lem7563762 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563763 (_97570 : int) (_97571 : int) : (term724 _97571 _97570) = (term610 _97570 _97571).
Proof. exact (MK_COMB (@lem7563762) (@lem7563701 _97570 _97571)). Qed.
Lemma lem7563764 (_97570 : int) (_97571 : int) : (term742 _97570 _97571) = (term743 _97570 _97571).
Proof. exact (MK_COMB (@lem7563763 _97570 _97571) (@lem7563761 _97570 _97571)). Qed.
Lemma lem7563765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563766 (_97571 : int) : (term727 _97571) = (term727 _97571).
Proof. exact (MK_COMB (@lem7563765) (@lem7563638 _97571)). Qed.
Lemma lem7563767 (_97570 : int) (_97571 : int) : (term744 _97570 _97571) = (term745 _97570 _97571).
Proof. exact (MK_COMB (@lem7563766 _97571) (@lem7563764 _97570 _97571)). Qed.
Lemma lem7563768 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563769 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563768) (@lem7563578 _97571)). Qed.
Lemma lem7563770 (_97570 : int) (_97571 : int) : (term746 _97570 _97571) = (term747 _97570 _97571).
Proof. exact (MK_COMB (@lem7563769 _97571) (@lem7563767 _97570 _97571)). Qed.
Lemma lem7563771 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563772 (_97570 : int) : (term583 _97570) = (term583 _97570).
Proof. exact (MK_COMB (@lem7563771) (@lem7563530 _97570)). Qed.
Lemma lem7563773 (_97570 : int) (_97571 : int) : (term1062 _97570 _97571) = (term1063 _97570 _97571).
Proof. exact (MK_COMB (@lem7563772 _97570) (@lem7563770 _97570 _97571)). Qed.
Lemma lem7563774 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563775 (_97569 : int) : (term583 _97569) = (term583 _97569).
Proof. exact (MK_COMB (@lem7563774) (@lem7563482 _97569)). Qed.
Lemma lem7563776 (_97569 : int) (_97570 : int) (_97571 : int) : (term1055 _97569 _97570 _97571) = (term1064 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563775 _97569) (@lem7563773 _97570 _97571)). Qed.
Lemma lem7563777 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563778 (_97569 : int) (_97570 : int) : (term695 _97570 _97569) = (term735 _97569 _97570).
Proof. exact (MK_COMB (@lem7563777) (@lem7563434 _97569 _97570)). Qed.
Lemma lem7563779 (_97569 : int) (_97570 : int) (_97571 : int) : (term1057 _97569 _97570 _97571) = (term1065 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563778 _97569 _97570) (@lem7563776 _97569 _97570 _97571)). Qed.
Lemma lem7563780 (_97569 : int) (_97570 : int) : (term737 _97569 _97570) = (term738 _97569 _97570).
Proof. exact (@lem1988289 (real_of_int _97569) (real_of_int _97570)). Qed.
Lemma lem7563793 (_97569 : int) (_97570 : int) : (term586 _97569 _97570) = (term587 _97569 _97570).
Proof. exact (@lem1982792 (real_of_int _97569) (real_of_int _97570)). Qed.
Lemma lem7563794 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem7563795 (_97569 : int) (_97570 : int) : (term739 _97569 _97570) = (term740 _97569 _97570).
Proof. exact (MK_COMB (@lem7563794) (@lem7563793 _97569 _97570)). Qed.
Lemma lem7563796 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563797 (_97569 : int) (_97570 : int) : (term738 _97569 _97570) = (term741 _97569 _97570).
Proof. exact (MK_COMB (@lem7563795 _97569 _97570) (@lem7563796)). Qed.
Lemma lem7563798 (_97569 : int) (_97570 : int) : (term737 _97569 _97570) = (term741 _97569 _97570).
Proof. exact (TRANS (@lem7563780 _97569 _97570) (@lem7563797 _97569 _97570)). Qed.
Lemma lem7563799 (_97571 : int) (_97569 : int) : (term705 _97571 _97569) = (term712 _97571 _97569).
Proof. exact (@lem1988291 (term703 _97571 _97569) term35). Qed.
Lemma lem7563800 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563813 (_97569 : int) (_97571 : int) : (term703 _97571 _97569) = (term587 _97569 _97571).
Proof. exact (@lem1982761 (real_of_int _97569) (term570 _97571)). Qed.
Lemma lem7563814 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem7563815 (_97569 : int) (_97571 : int) : (term713 _97571 _97569) = (term714 _97569 _97571).
Proof. exact (MK_COMB (@lem7563814) (@lem7563813 _97569 _97571)). Qed.
Lemma lem7563816 (_97569 : int) (_97571 : int) : (term715 _97571 _97569) = (term716 _97569 _97571).
Proof. exact (MK_COMB (@lem7563815 _97569 _97571) (@lem7563800)). Qed.
Lemma lem7563817 (_97569 : int) (_97571 : int) : (term716 _97569 _97571) = (term717 _97569 _97571).
Proof. exact (@lem1982792 (term587 _97569 _97571) term35). Qed.
Lemma lem7563819 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563820 : term35 = term520.
Proof. exact (@lem7563819 (NUMERAL 0)). Qed.
Lemma lem7563822 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563823 : term523 = term524.
Proof. exact (@lem7563822 term470). Qed.
Lemma lem7563824 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563825 : term525 = term526.
Proof. exact (MK_COMB (@lem7563824) (@lem7563823)). Qed.
Lemma lem7563826 : term527 = term528.
Proof. exact (MK_COMB (@lem7563825) (@lem7563820)). Qed.
Lemma lem7563827 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563829 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563830 : term532 = term533.
Proof. exact (@lem7563829 term470 term470). Qed.
Lemma lem7563831 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563832 : term535 = term470.
Proof. exact (EQ_MP (@lem7563831) (@lem940073)). Qed.
Lemma lem7563833 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563834 : term533 = term469.
Proof. exact (MK_COMB (@lem7563833) (@lem7563832)). Qed.
Lemma lem7563835 : term532 = term469.
Proof. exact (TRANS (@lem7563830) (@lem7563834)). Qed.
Lemma lem7563837 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563838 : term527 = term35.
Proof. exact (@lem7563837 term470). Qed.
Lemma lem7563839 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563840 : term537 = term538.
Proof. exact (MK_COMB (@lem7563839) (@lem7563838)). Qed.
Lemma lem7563841 : term529 = term520.
Proof. exact (MK_COMB (@lem7563840) (@lem7563835)). Qed.
Lemma lem7563842 : term528 = term520.
Proof. exact (TRANS (@lem7563827) (@lem7563841)). Qed.
Lemma lem7563843 : term527 = term520.
Proof. exact (TRANS (@lem7563826) (@lem7563842)). Qed.
Lemma lem7563845 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563846 : term520 = term35.
Proof. exact (@lem7563845 term35). Qed.
Lemma lem7563847 : term527 = term35.
Proof. exact (TRANS (@lem7563843) (@lem7563846)). Qed.
Lemma lem7563848 (_97569 : int) (_97571 : int) : (term718 _97569 _97571) = (term718 _97569 _97571).
Proof. exact (eq_refl (term718 _97569 _97571)). Qed.
Lemma lem7563849 (_97569 : int) (_97571 : int) : (term717 _97569 _97571) = (term719 _97569 _97571).
Proof. exact (MK_COMB (@lem7563848 _97569 _97571) (@lem7563847)). Qed.
Lemma lem7563850 (_97569 : int) (_97571 : int) : (term719 _97569 _97571) = (term587 _97569 _97571).
Proof. exact (@lem1982723 (term587 _97569 _97571)). Qed.
Lemma lem7563851 (_97569 : int) (_97571 : int) : (term717 _97569 _97571) = (term587 _97569 _97571).
Proof. exact (TRANS (@lem7563849 _97569 _97571) (@lem7563850 _97569 _97571)). Qed.
Lemma lem7563852 (_97569 : int) (_97571 : int) : (term716 _97569 _97571) = (term587 _97569 _97571).
Proof. exact (TRANS (@lem7563817 _97569 _97571) (@lem7563851 _97569 _97571)). Qed.
Lemma lem7563853 (_97569 : int) (_97571 : int) : (term715 _97571 _97569) = (term587 _97569 _97571).
Proof. exact (TRANS (@lem7563816 _97569 _97571) (@lem7563852 _97569 _97571)). Qed.
Lemma lem7563854 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563855 (_97569 : int) (_97571 : int) : (term720 _97571 _97569) = (term589 _97569 _97571).
Proof. exact (MK_COMB (@lem7563854) (@lem7563853 _97569 _97571)). Qed.
Lemma lem7563856 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563857 (_97569 : int) (_97571 : int) : (term712 _97571 _97569) = (term590 _97569 _97571).
Proof. exact (MK_COMB (@lem7563855 _97569 _97571) (@lem7563856)). Qed.
Lemma lem7563858 (_97569 : int) (_97571 : int) : (term705 _97571 _97569) = (term590 _97569 _97571).
Proof. exact (TRANS (@lem7563799 _97571 _97569) (@lem7563857 _97569 _97571)). Qed.
Lemma lem7563859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563860 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563859) (@lem7563578 _97571)). Qed.
Lemma lem7563861 (_97569 : int) (_97571 : int) : (term721 _97571 _97569) = (term595 _97569 _97571).
Proof. exact (MK_COMB (@lem7563860 _97571) (@lem7563858 _97569 _97571)). Qed.
Lemma lem7563862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563863 (_97569 : int) (_97571 : int) : (term724 _97571 _97569) = (term610 _97569 _97571).
Proof. exact (MK_COMB (@lem7563862) (@lem7563861 _97569 _97571)). Qed.
Lemma lem7563864 (_97569 : int) (_97570 : int) (_97571 : int) : (term725 _97569 _97570 _97571) = (term726 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563863 _97569 _97571) (@lem7563761 _97570 _97571)). Qed.
Lemma lem7563865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563866 (_97571 : int) : (term727 _97571) = (term727 _97571).
Proof. exact (MK_COMB (@lem7563865) (@lem7563638 _97571)). Qed.
Lemma lem7563867 (_97569 : int) (_97570 : int) (_97571 : int) : (term728 _97569 _97570 _97571) = (term729 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563866 _97571) (@lem7563864 _97569 _97570 _97571)). Qed.
Lemma lem7563868 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563869 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563868) (@lem7563578 _97571)). Qed.
Lemma lem7563870 (_97569 : int) (_97570 : int) (_97571 : int) : (term730 _97569 _97570 _97571) = (term731 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563869 _97571) (@lem7563867 _97569 _97570 _97571)). Qed.
Lemma lem7563871 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563872 (_97570 : int) : (term583 _97570) = (term583 _97570).
Proof. exact (MK_COMB (@lem7563871) (@lem7563530 _97570)). Qed.
Lemma lem7563873 (_97569 : int) (_97570 : int) (_97571 : int) : (term1066 _97569 _97570 _97571) = (term1067 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563872 _97570) (@lem7563870 _97569 _97570 _97571)). Qed.
Lemma lem7563874 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563875 (_97569 : int) : (term583 _97569) = (term583 _97569).
Proof. exact (MK_COMB (@lem7563874) (@lem7563482 _97569)). Qed.
Lemma lem7563876 (_97569 : int) (_97570 : int) (_97571 : int) : (term1051 _97569 _97570 _97571) = (term1068 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563875 _97569) (@lem7563873 _97569 _97570 _97571)). Qed.
Lemma lem7563877 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563878 (_97569 : int) (_97570 : int) : (term690 _97569 _97570) = (term751 _97569 _97570).
Proof. exact (MK_COMB (@lem7563877) (@lem7563798 _97569 _97570)). Qed.
Lemma lem7563879 (_97569 : int) (_97570 : int) (_97571 : int) : (term1053 _97569 _97570 _97571) = (term1069 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563878 _97569 _97570) (@lem7563876 _97569 _97570 _97571)). Qed.
Lemma lem7563880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563881 (_97569 : int) (_97570 : int) (_97571 : int) : (term1059 _97569 _97570 _97571) = (term1070 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563880) (@lem7563779 _97569 _97570 _97571)). Qed.
Lemma lem7563882 (_97569 : int) (_97570 : int) (_97571 : int) : (term1060 _97569 _97570 _97571) = (term1071 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563881 _97569 _97570 _97571) (@lem7563879 _97569 _97570 _97571)). Qed.
Lemma lem7563894 (_97569 : int) (_97570 : int) (_97571 : int) : (term1047 _97569 _97570 _97571) = (term1071 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563415 _97569 _97570 _97571) (@lem7563882 _97569 _97570 _97571)). Qed.
Lemma lem7563896 (_97569 : int) (_97570 : int) (_97571 : int) : (term1072 _97571 _97569 _97570) = (term1073 _97569 _97570 _97571).
Proof. exact (eq_refl (term1072 _97571 _97569 _97570)). Qed.
Lemma lem7563897 (_97571 : int) (_97569 : int) (_97570 : int) : (term1073 _97569 _97570 _97571) = (term1072 _97571 _97569 _97570).
Proof. exact (SYM (@lem7563896 _97569 _97570 _97571)). Qed.
Lemma lem7563898 (_97570 : int) (_97571 : int) (_97569 : int) : (term1072 _97571 _97569 _97570) = (term1074 _97570 _97571 _97569).
Proof. exact (@lem1483205 (real_of_int _97570) (term1075 _97569 _97570 _97571) (real_of_int _97569)). Qed.
Lemma lem7563899 (_97570 : int) (_97571 : int) (_97569 : int) : (term1073 _97569 _97570 _97571) = (term1074 _97570 _97571 _97569).
Proof. exact (TRANS (@lem7563897 _97571 _97569 _97570) (@lem7563898 _97570 _97571 _97569)). Qed.
Lemma lem7563900 (_97569 : int) (_97570 : int) (_97571 : int) : (term1076 _97570 _97571 _97569) = (term1077 _97569 _97570 _97571).
Proof. exact (eq_refl (term1076 _97570 _97571 _97569)). Qed.
Lemma lem7563901 (_97569 : int) (_97570 : int) : (term690 _97569 _97570) = (term690 _97569 _97570).
Proof. exact (eq_refl (term690 _97569 _97570)). Qed.
Lemma lem7563902 (_97569 : int) (_97570 : int) (_97571 : int) : (term1078 _97570 _97571 _97569) = (term1079 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563901 _97569 _97570) (@lem7563900 _97569 _97570 _97571)). Qed.
Lemma lem7563903 (_97569 : int) (_97570 : int) (_97571 : int) : (term1080 _97569 _97571 _97570) = (term1081 _97569 _97570 _97571).
Proof. exact (eq_refl (term1080 _97569 _97571 _97570)). Qed.
Lemma lem7563904 (_97570 : int) (_97569 : int) : (term695 _97570 _97569) = (term695 _97570 _97569).
Proof. exact (eq_refl (term695 _97570 _97569)). Qed.
Lemma lem7563905 (_97569 : int) (_97570 : int) (_97571 : int) : (term1082 _97569 _97571 _97570) = (term1083 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563904 _97570 _97569) (@lem7563903 _97569 _97570 _97571)). Qed.
Lemma lem7563906 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7563907 (_97569 : int) (_97570 : int) (_97571 : int) : (term1084 _97569 _97571 _97570) = (term1085 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563906) (@lem7563905 _97569 _97570 _97571)). Qed.
Lemma lem7563908 (_97569 : int) (_97570 : int) (_97571 : int) : (term1074 _97570 _97571 _97569) = (term1086 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563907 _97569 _97570 _97571) (@lem7563902 _97569 _97570 _97571)). Qed.
Lemma lem7563909 (_97569 : int) (_97570 : int) (_97571 : int) : (term1087 _97569 _97570 _97571) = (term1087 _97569 _97570 _97571).
Proof. exact (eq_refl (term1087 _97569 _97570 _97571)). Qed.
Lemma lem7563910 (_97569 : int) (_97570 : int) (_97571 : int) : ((term1073 _97569 _97570 _97571) = (term1074 _97570 _97571 _97569)) = ((term1073 _97569 _97570 _97571) = (term1086 _97569 _97570 _97571)).
Proof. exact (MK_COMB (@lem7563909 _97569 _97570 _97571) (@lem7563908 _97569 _97570 _97571)). Qed.
Lemma lem7563911 (_97569 : int) (_97570 : int) (_97571 : int) : (term1073 _97569 _97570 _97571) = (term1086 _97569 _97570 _97571).
Proof. exact (EQ_MP (@lem7563910 _97569 _97570 _97571) (@lem7563899 _97570 _97571 _97569)). Qed.
Lemma lem7563912 (_97570 : int) (_97571 : int) : (term573 _97570 _97571) = (term771 _97570 _97571).
Proof. exact (@lem1988291 (term569 _97570 _97571) term35). Qed.
Lemma lem7563936 (_97570 : int) (_97571 : int) : (term772 _97570 _97571) = (term773 _97570 _97571).
Proof. exact (@lem1982792 (term569 _97570 _97571) term35). Qed.
Lemma lem7563938 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7563939 : term35 = term520.
Proof. exact (@lem7563938 (NUMERAL 0)). Qed.
Lemma lem7563941 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7563942 : term523 = term524.
Proof. exact (@lem7563941 term470). Qed.
Lemma lem7563943 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7563944 : term525 = term526.
Proof. exact (MK_COMB (@lem7563943) (@lem7563942)). Qed.
Lemma lem7563945 : term527 = term528.
Proof. exact (MK_COMB (@lem7563944) (@lem7563939)). Qed.
Lemma lem7563946 : term528 = term529.
Proof. exact (@lem1981613 term523 term35 term469 term469). Qed.
Lemma lem7563948 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7563949 : term532 = term533.
Proof. exact (@lem7563948 term470 term470). Qed.
Lemma lem7563950 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7563951 : term535 = term470.
Proof. exact (EQ_MP (@lem7563950) (@lem940073)). Qed.
Lemma lem7563952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7563953 : term533 = term469.
Proof. exact (MK_COMB (@lem7563952) (@lem7563951)). Qed.
Lemma lem7563954 : term532 = term469.
Proof. exact (TRANS (@lem7563949) (@lem7563953)). Qed.
Lemma lem7563956 (x : nat) : (term536 x) = term35.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem7563957 : term527 = term35.
Proof. exact (@lem7563956 term470). Qed.
Lemma lem7563958 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem7563959 : term537 = term538.
Proof. exact (MK_COMB (@lem7563958) (@lem7563957)). Qed.
Lemma lem7563960 : term529 = term520.
Proof. exact (MK_COMB (@lem7563959) (@lem7563954)). Qed.
Lemma lem7563961 : term528 = term520.
Proof. exact (TRANS (@lem7563946) (@lem7563960)). Qed.
Lemma lem7563962 : term527 = term520.
Proof. exact (TRANS (@lem7563945) (@lem7563961)). Qed.
Lemma lem7563964 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem7563965 : term520 = term35.
Proof. exact (@lem7563964 term35). Qed.
Lemma lem7563966 : term527 = term35.
Proof. exact (TRANS (@lem7563962) (@lem7563965)). Qed.
Lemma lem7563967 (_97570 : int) (_97571 : int) : (term774 _97570 _97571) = (term774 _97570 _97571).
Proof. exact (eq_refl (term774 _97570 _97571)). Qed.
Lemma lem7563968 (_97570 : int) (_97571 : int) : (term773 _97570 _97571) = (term775 _97570 _97571).
Proof. exact (MK_COMB (@lem7563967 _97570 _97571) (@lem7563966)). Qed.
Lemma lem7563969 (_97570 : int) (_97571 : int) : (term775 _97570 _97571) = (term569 _97570 _97571).
Proof. exact (@lem1982723 (term569 _97570 _97571)). Qed.
Lemma lem7563970 (_97570 : int) (_97571 : int) : (term773 _97570 _97571) = (term569 _97570 _97571).
Proof. exact (TRANS (@lem7563968 _97570 _97571) (@lem7563969 _97570 _97571)). Qed.
Lemma lem7563972 (_97570 : int) (_97571 : int) : (term772 _97570 _97571) = (term569 _97570 _97571).
Proof. exact (TRANS (@lem7563936 _97570 _97571) (@lem7563970 _97570 _97571)). Qed.
Lemma lem7563973 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7563974 (_97570 : int) (_97571 : int) : (term776 _97570 _97571) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7563973) (@lem7563972 _97570 _97571)). Qed.
Lemma lem7563975 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7563976 (_97570 : int) (_97571 : int) : (term771 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7563974 _97570 _97571) (@lem7563975)). Qed.
Lemma lem7563977 (_97570 : int) (_97571 : int) : (term573 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (TRANS (@lem7563912 _97570 _97571) (@lem7563976 _97570 _97571)). Qed.
Lemma lem7563978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563979 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563978) (@lem7563578 _97571)). Qed.
Lemma lem7563980 (_97570 : int) (_97571 : int) : (term721 _97571 _97570) = (term595 _97570 _97571).
Proof. exact (MK_COMB (@lem7563979 _97571) (@lem7563698 _97570 _97571)). Qed.
Lemma lem7563981 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563982 (_97570 : int) (_97571 : int) : (term724 _97571 _97570) = (term610 _97570 _97571).
Proof. exact (MK_COMB (@lem7563981) (@lem7563980 _97570 _97571)). Qed.
Lemma lem7563983 (_97570 : int) (_97571 : int) : (term742 _97570 _97571) = (term743 _97570 _97571).
Proof. exact (MK_COMB (@lem7563982 _97570 _97571) (@lem7563761 _97570 _97571)). Qed.
Lemma lem7563984 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563985 (_97570 : int) (_97571 : int) : (term777 _97570 _97571) = (term777 _97570 _97571).
Proof. exact (MK_COMB (@lem7563984) (@lem7563977 _97570 _97571)). Qed.
Lemma lem7563986 (_97570 : int) (_97571 : int) : (term786 _97570 _97571) = (term787 _97570 _97571).
Proof. exact (MK_COMB (@lem7563985 _97570 _97571) (@lem7563983 _97570 _97571)). Qed.
Lemma lem7563987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563988 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563987) (@lem7563578 _97571)). Qed.
Lemma lem7563989 (_97570 : int) (_97571 : int) : (term788 _97570 _97571) = (term789 _97570 _97571).
Proof. exact (MK_COMB (@lem7563988 _97571) (@lem7563986 _97570 _97571)). Qed.
Lemma lem7563990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563991 (_97570 : int) : (term583 _97570) = (term583 _97570).
Proof. exact (MK_COMB (@lem7563990) (@lem7563530 _97570)). Qed.
Lemma lem7563992 (_97570 : int) (_97571 : int) : (term1088 _97570 _97571) = (term1089 _97570 _97571).
Proof. exact (MK_COMB (@lem7563991 _97570) (@lem7563989 _97570 _97571)). Qed.
Lemma lem7563993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563994 (_97569 : int) : (term583 _97569) = (term583 _97569).
Proof. exact (MK_COMB (@lem7563993) (@lem7563482 _97569)). Qed.
Lemma lem7563995 (_97569 : int) (_97570 : int) (_97571 : int) : (term1081 _97569 _97570 _97571) = (term1090 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563994 _97569) (@lem7563992 _97570 _97571)). Qed.
Lemma lem7563996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7563997 (_97569 : int) (_97570 : int) : (term695 _97570 _97569) = (term735 _97569 _97570).
Proof. exact (MK_COMB (@lem7563996) (@lem7563434 _97569 _97570)). Qed.
Lemma lem7563998 (_97569 : int) (_97570 : int) (_97571 : int) : (term1083 _97569 _97570 _97571) = (term1091 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7563997 _97569 _97570) (@lem7563995 _97569 _97570 _97571)). Qed.
Lemma lem7563999 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564000 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7563999) (@lem7563578 _97571)). Qed.
Lemma lem7564001 (_97569 : int) (_97571 : int) : (term721 _97571 _97569) = (term595 _97569 _97571).
Proof. exact (MK_COMB (@lem7564000 _97571) (@lem7563858 _97569 _97571)). Qed.
Lemma lem7564002 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564003 (_97569 : int) (_97571 : int) : (term724 _97571 _97569) = (term610 _97569 _97571).
Proof. exact (MK_COMB (@lem7564002) (@lem7564001 _97569 _97571)). Qed.
Lemma lem7564004 (_97569 : int) (_97570 : int) (_97571 : int) : (term725 _97569 _97570 _97571) = (term726 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564003 _97569 _97571) (@lem7563761 _97570 _97571)). Qed.
Lemma lem7564005 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564006 (_97570 : int) (_97571 : int) : (term777 _97570 _97571) = (term777 _97570 _97571).
Proof. exact (MK_COMB (@lem7564005) (@lem7563977 _97570 _97571)). Qed.
Lemma lem7564007 (_97569 : int) (_97570 : int) (_97571 : int) : (term778 _97569 _97570 _97571) = (term779 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564006 _97570 _97571) (@lem7564004 _97569 _97570 _97571)). Qed.
Lemma lem7564008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564009 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (MK_COMB (@lem7564008) (@lem7563578 _97571)). Qed.
Lemma lem7564010 (_97569 : int) (_97570 : int) (_97571 : int) : (term780 _97569 _97570 _97571) = (term781 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564009 _97571) (@lem7564007 _97569 _97570 _97571)). Qed.
Lemma lem7564011 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564012 (_97570 : int) : (term583 _97570) = (term583 _97570).
Proof. exact (MK_COMB (@lem7564011) (@lem7563530 _97570)). Qed.
Lemma lem7564013 (_97569 : int) (_97570 : int) (_97571 : int) : (term1092 _97569 _97570 _97571) = (term1093 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564012 _97570) (@lem7564010 _97569 _97570 _97571)). Qed.
Lemma lem7564014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564015 (_97569 : int) : (term583 _97569) = (term583 _97569).
Proof. exact (MK_COMB (@lem7564014) (@lem7563482 _97569)). Qed.
Lemma lem7564016 (_97569 : int) (_97570 : int) (_97571 : int) : (term1077 _97569 _97570 _97571) = (term1094 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564015 _97569) (@lem7564013 _97569 _97570 _97571)). Qed.
Lemma lem7564017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564018 (_97569 : int) (_97570 : int) : (term690 _97569 _97570) = (term751 _97569 _97570).
Proof. exact (MK_COMB (@lem7564017) (@lem7563798 _97569 _97570)). Qed.
Lemma lem7564019 (_97569 : int) (_97570 : int) (_97571 : int) : (term1079 _97569 _97570 _97571) = (term1095 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564018 _97569 _97570) (@lem7564016 _97569 _97570 _97571)). Qed.
Lemma lem7564020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7564021 (_97569 : int) (_97570 : int) (_97571 : int) : (term1085 _97569 _97570 _97571) = (term1096 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564020) (@lem7563998 _97569 _97570 _97571)). Qed.
Lemma lem7564022 (_97569 : int) (_97570 : int) (_97571 : int) : (term1086 _97569 _97570 _97571) = (term1097 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564021 _97569 _97570 _97571) (@lem7564019 _97569 _97570 _97571)). Qed.
Lemma lem7564034 (_97569 : int) (_97570 : int) (_97571 : int) : (term1073 _97569 _97570 _97571) = (term1097 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7563911 _97569 _97570 _97571) (@lem7564022 _97569 _97570 _97571)). Qed.
Lemma lem7564035 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7564036 (_97569 : int) (_97570 : int) (_97571 : int) : (term1098 _97569 _97570 _97571) = (term1099 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564035) (@lem7563894 _97569 _97570 _97571)). Qed.
Lemma lem7564037 (_97569 : int) (_97570 : int) (_97571 : int) : (term1040 _97569 _97570 _97571) = (term1100 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564036 _97569 _97570 _97571) (@lem7564034 _97569 _97570 _97571)). Qed.
Lemma lem7564042 (x : real) (a : real) (y : real) (b : real) (r : real) : (term799 a x y b r) = (term800 x a y b r).
Proof. exact (proj1 (@lem1482687 x a b y (@el real) r)). Qed.
Lemma lem7564043 (_97569 : int) (_97571 : int) (_97570 : int) : (term606 _97571 _97569 _97570) = (term801 _97569 _97571 _97570).
Proof. exact (@lem7564042 (real_of_int _97569) (real_of_int _97571) (real_of_int _97570) term523 term35). Qed.
Lemma lem7564066 (_97570 : int) (_97571 : int) : (term568 _97571 _97570) = (term569 _97570 _97571).
Proof. exact (@lem1982757 (term570 _97570) (real_of_int _97571) term523). Qed.
Lemma lem7564067 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564068 (_97570 : int) (_97571 : int) : (term802 _97571 _97570) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7564067) (@lem7564066 _97570 _97571)). Qed.
Lemma lem7564069 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564070 (_97570 : int) (_97571 : int) : (term803 _97571 _97570) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7564068 _97570 _97571) (@lem7564069)). Qed.
Lemma lem7564093 (_97569 : int) (_97571 : int) : (term568 _97571 _97569) = (term569 _97569 _97571).
Proof. exact (@lem1982757 (term570 _97569) (real_of_int _97571) term523). Qed.
Lemma lem7564094 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564095 (_97569 : int) (_97571 : int) : (term802 _97571 _97569) = (term572 _97569 _97571).
Proof. exact (MK_COMB (@lem7564094) (@lem7564093 _97569 _97571)). Qed.
Lemma lem7564096 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564097 (_97569 : int) (_97571 : int) : (term803 _97571 _97569) = (term573 _97569 _97571).
Proof. exact (MK_COMB (@lem7564095 _97569 _97571) (@lem7564096)). Qed.
Lemma lem7564098 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564099 (_97569 : int) (_97571 : int) : (term804 _97571 _97569) = (term777 _97569 _97571).
Proof. exact (MK_COMB (@lem7564098) (@lem7564097 _97569 _97571)). Qed.
Lemma lem7564100 (_97569 : int) (_97570 : int) (_97571 : int) : (term801 _97569 _97571 _97570) = (term805 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564099 _97569 _97571) (@lem7564070 _97570 _97571)). Qed.
Lemma lem7564101 (_97569 : int) (_97570 : int) (_97571 : int) : (term606 _97571 _97569 _97570) = (term805 _97569 _97570 _97571).
Proof. exact (TRANS (@lem7564043 _97569 _97571 _97570) (@lem7564100 _97569 _97570 _97571)). Qed.
Lemma lem7564102 (_97570 : int) (_97571 : int) : (term610 _97570 _97571) = (term610 _97570 _97571).
Proof. exact (eq_refl (term610 _97570 _97571)). Qed.
Lemma lem7564103 (_97569 : int) (_97570 : int) (_97571 : int) : (term998 _97571 _97569 _97570) = (term1101 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564102 _97570 _97571) (@lem7564101 _97569 _97570 _97571)). Qed.
Lemma lem7564104 (_97571 : int) : (term583 _97571) = (term583 _97571).
Proof. exact (eq_refl (term583 _97571)). Qed.
Lemma lem7564105 (_97569 : int) (_97570 : int) (_97571 : int) : (term1016 _97571 _97569 _97570) = (term1102 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564104 _97571) (@lem7564103 _97569 _97570 _97571)). Qed.
Lemma lem7564106 (_97570 : int) : (term583 _97570) = (term583 _97570).
Proof. exact (eq_refl (term583 _97570)). Qed.
Lemma lem7564107 (_97569 : int) (_97570 : int) (_97571 : int) : (term1035 _97571 _97569 _97570) = (term1103 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564106 _97570) (@lem7564105 _97569 _97570 _97571)). Qed.
Lemma lem7564108 (_97569 : int) : (term583 _97569) = (term583 _97569).
Proof. exact (eq_refl (term583 _97569)). Qed.
Lemma lem7564111 (_97569 : int) (_97570 : int) (_97571 : int) : (term1104 _97571 _97569 _97570) = (term1105 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564108 _97569) (@lem7564107 _97569 _97570 _97571)). Qed.
Lemma lem7564113 (_97569 : int) (_97570 : int) (_97571 : int) : (term1106 _97569 _97570 _97571) = (term1106 _97569 _97570 _97571).
Proof. exact (eq_refl (term1106 _97569 _97570 _97571)). Qed.
Lemma lem7564114 (_97569 : int) (_97570 : int) (_97571 : int) : (term1033 _97571 _97569 _97570) = (term1107 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564113 _97569 _97570 _97571) (@lem7564111 _97569 _97570 _97571)). Qed.
Lemma lem7564117 (_97569 : int) (_97570 : int) (_97571 : int) : (term1031 _97569 _97570 _97571) = (term1031 _97569 _97570 _97571).
Proof. exact (eq_refl (term1031 _97569 _97570 _97571)). Qed.
Lemma lem7564118 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7564119 (_97569 : int) (_97570 : int) (_97571 : int) : (term1037 _97571 _97569 _97570) = (term1108 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564118) (@lem7564114 _97569 _97570 _97571)). Qed.
Lemma lem7564120 (_97569 : int) (_97570 : int) (_97571 : int) : (term1038 _97569 _97570 _97571) = (term1109 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564119 _97569 _97570 _97571) (@lem7564117 _97569 _97570 _97571)). Qed.
Lemma lem7564121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7564122 (_97569 : int) (_97570 : int) (_97571 : int) : (term1044 _97569 _97570 _97571) = (term1110 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564121) (@lem7564037 _97569 _97570 _97571)). Qed.
Lemma lem7564123 (_97569 : int) (_97570 : int) (_97571 : int) : (term1045 _97569 _97570 _97571) = (term1111 _97569 _97570 _97571).
Proof. exact (MK_COMB (@lem7564122 _97569 _97570 _97571) (@lem7564120 _97569 _97570 _97571)). Qed.
Lemma lem7564124 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1111 _97569 _97570 _97571) : term1111 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7564125 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1100 _97569 _97570 _97571) : term1100 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7564126 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1071 _97569 _97570 _97571) : term1071 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7564127 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term1065 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7564128 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term1064 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7564127 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564130 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term1063 _97570 _97571.
Proof. exact (proj2 (@lem7564128 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564132 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term747 _97570 _97571.
Proof. exact (proj2 (@lem7564130 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564134 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term745 _97570 _97571.
Proof. exact (proj2 (@lem7564132 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564136 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term743 _97570 _97571.
Proof. exact (proj2 (@lem7564134 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564137 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term564 _97571.
Proof. exact (proj1 (@lem7564134 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564139 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term595 _97570 _97571.
Proof. exact (proj1 (@lem7564136 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564141 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term543 _97571.
Proof. exact (proj1 (@lem7564139 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564143 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7564144 : term817 = term818.
Proof. exact (@lem7564143 term35 term469). Qed.
Lemma lem7564146 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564147 : term469 = term549.
Proof. exact (@lem7564146 term470). Qed.
Lemma lem7564149 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564150 : term35 = term520.
Proof. exact (@lem7564149 (NUMERAL 0)). Qed.
Lemma lem7564151 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564152 : term819 = term820.
Proof. exact (MK_COMB (@lem7564151) (@lem7564150)). Qed.
Lemma lem7564153 : term818 = term821.
Proof. exact (MK_COMB (@lem7564152) (@lem7564147)). Qed.
Lemma lem7564154 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7564156 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564157 : term818 = term824.
Proof. exact (@lem7564156 (NUMERAL 0) term470). Qed.
Lemma lem7564158 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564159 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564160 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564159 h1) (fun h1 : term824 = True => @lem7564158)). Qed.
Lemma lem7564161 : term824 = True.
Proof. exact (EQ_MP (@lem7564160) (@lem7564158)). Qed.
Lemma lem7564162 : term818 = True.
Proof. exact (TRANS (@lem7564157) (@lem7564161)). Qed.
Lemma lem7564163 : True = term818.
Proof. exact (SYM (@lem7564162)). Qed.
Lemma lem7564164 : term818.
Proof. exact (EQ_MP (@lem7564163) (@lem0)). Qed.
Lemma lem7564165 : term826.
Proof. exact (@lem7564154 (@lem7564164)). Qed.
Lemma lem7564167 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564168 : term818 = term824.
Proof. exact (@lem7564167 (NUMERAL 0) term470). Qed.
Lemma lem7564169 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564170 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564171 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564170 h1) (fun h1 : term824 = True => @lem7564169)). Qed.
Lemma lem7564172 : term824 = True.
Proof. exact (EQ_MP (@lem7564171) (@lem7564169)). Qed.
Lemma lem7564173 : term818 = True.
Proof. exact (TRANS (@lem7564168) (@lem7564172)). Qed.
Lemma lem7564174 : True = term818.
Proof. exact (SYM (@lem7564173)). Qed.
Lemma lem7564175 : term818.
Proof. exact (EQ_MP (@lem7564174) (@lem0)). Qed.
Lemma lem7564176 : term821 = term827.
Proof. exact (@lem7564165 (@lem7564175)). Qed.
Lemma lem7564178 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564179 : term532 = term533.
Proof. exact (@lem7564178 term470 term470). Qed.
Lemma lem7564180 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564181 : term535 = term470.
Proof. exact (EQ_MP (@lem7564180) (@lem940073)). Qed.
Lemma lem7564182 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564183 : term533 = term469.
Proof. exact (MK_COMB (@lem7564182) (@lem7564181)). Qed.
Lemma lem7564184 : term532 = term469.
Proof. exact (TRANS (@lem7564179) (@lem7564183)). Qed.
Lemma lem7564186 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564187 : term829 = term35.
Proof. exact (@lem7564186 term470). Qed.
Lemma lem7564188 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564189 : term830 = term819.
Proof. exact (MK_COMB (@lem7564188) (@lem7564187)). Qed.
Lemma lem7564190 : term827 = term818.
Proof. exact (MK_COMB (@lem7564189) (@lem7564184)). Qed.
Lemma lem7564192 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564193 : term818 = term824.
Proof. exact (@lem7564192 (NUMERAL 0) term470). Qed.
Lemma lem7564194 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564195 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564196 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564195 h1) (fun h1 : term824 = True => @lem7564194)). Qed.
Lemma lem7564197 : term824 = True.
Proof. exact (EQ_MP (@lem7564196) (@lem7564194)). Qed.
Lemma lem7564198 : term818 = True.
Proof. exact (TRANS (@lem7564193) (@lem7564197)). Qed.
Lemma lem7564199 : term827 = True.
Proof. exact (TRANS (@lem7564190) (@lem7564198)). Qed.
Lemma lem7564200 : term821 = True.
Proof. exact (TRANS (@lem7564176) (@lem7564199)). Qed.
Lemma lem7564201 : term818 = True.
Proof. exact (TRANS (@lem7564153) (@lem7564200)). Qed.
Lemma lem7564202 : term817 = True.
Proof. exact (TRANS (@lem7564144) (@lem7564201)). Qed.
Lemma lem7564203 : True = term817.
Proof. exact (SYM (@lem7564202)). Qed.
Lemma lem7564204 : term817.
Proof. exact (EQ_MP (@lem7564203) (@lem0)). Qed.
Lemma lem7564205 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term831 _97571.
Proof. exact (conj (@lem7564204) (@lem7564141 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564207 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7564208 (_97571 : int) : term833 _97571.
Proof. exact (@lem7564207 term469 (real_of_int _97571)). Qed.
Lemma lem7564209 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term834 _97571.
Proof. exact (@lem7564208 _97571 (@lem7564205 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564210 (_97571 : int) : (term835 _97571) = (real_of_int _97571).
Proof. exact (@lem1982733 (real_of_int _97571)). Qed.
Lemma lem7564211 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564212 (_97571 : int) : (term836 _97571) = (term542 _97571).
Proof. exact (MK_COMB (@lem7564211) (@lem7564210 _97571)). Qed.
Lemma lem7564213 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564214 (_97571 : int) : (term834 _97571) = (term543 _97571).
Proof. exact (MK_COMB (@lem7564212 _97571) (@lem7564213)). Qed.
Lemma lem7564215 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term543 _97571.
Proof. exact (EQ_MP (@lem7564214 _97571) (@lem7564209 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564217 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7564218 : term817 = term818.
Proof. exact (@lem7564217 term35 term469). Qed.
Lemma lem7564220 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564221 : term469 = term549.
Proof. exact (@lem7564220 term470). Qed.
Lemma lem7564223 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564224 : term35 = term520.
Proof. exact (@lem7564223 (NUMERAL 0)). Qed.
Lemma lem7564225 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564226 : term819 = term820.
Proof. exact (MK_COMB (@lem7564225) (@lem7564224)). Qed.
Lemma lem7564227 : term818 = term821.
Proof. exact (MK_COMB (@lem7564226) (@lem7564221)). Qed.
Lemma lem7564228 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7564230 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564231 : term818 = term824.
Proof. exact (@lem7564230 (NUMERAL 0) term470). Qed.
Lemma lem7564232 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564233 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564234 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564233 h1) (fun h1 : term824 = True => @lem7564232)). Qed.
Lemma lem7564235 : term824 = True.
Proof. exact (EQ_MP (@lem7564234) (@lem7564232)). Qed.
Lemma lem7564236 : term818 = True.
Proof. exact (TRANS (@lem7564231) (@lem7564235)). Qed.
Lemma lem7564237 : True = term818.
Proof. exact (SYM (@lem7564236)). Qed.
Lemma lem7564238 : term818.
Proof. exact (EQ_MP (@lem7564237) (@lem0)). Qed.
Lemma lem7564239 : term826.
Proof. exact (@lem7564228 (@lem7564238)). Qed.
Lemma lem7564241 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564242 : term818 = term824.
Proof. exact (@lem7564241 (NUMERAL 0) term470). Qed.
Lemma lem7564243 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564244 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564245 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564244 h1) (fun h1 : term824 = True => @lem7564243)). Qed.
Lemma lem7564246 : term824 = True.
Proof. exact (EQ_MP (@lem7564245) (@lem7564243)). Qed.
Lemma lem7564247 : term818 = True.
Proof. exact (TRANS (@lem7564242) (@lem7564246)). Qed.
Lemma lem7564248 : True = term818.
Proof. exact (SYM (@lem7564247)). Qed.
Lemma lem7564249 : term818.
Proof. exact (EQ_MP (@lem7564248) (@lem0)). Qed.
Lemma lem7564250 : term821 = term827.
Proof. exact (@lem7564239 (@lem7564249)). Qed.
Lemma lem7564252 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564253 : term532 = term533.
Proof. exact (@lem7564252 term470 term470). Qed.
Lemma lem7564254 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564255 : term535 = term470.
Proof. exact (EQ_MP (@lem7564254) (@lem940073)). Qed.
Lemma lem7564256 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564257 : term533 = term469.
Proof. exact (MK_COMB (@lem7564256) (@lem7564255)). Qed.
Lemma lem7564258 : term532 = term469.
Proof. exact (TRANS (@lem7564253) (@lem7564257)). Qed.
Lemma lem7564260 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564261 : term829 = term35.
Proof. exact (@lem7564260 term470). Qed.
Lemma lem7564262 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564263 : term830 = term819.
Proof. exact (MK_COMB (@lem7564262) (@lem7564261)). Qed.
Lemma lem7564264 : term827 = term818.
Proof. exact (MK_COMB (@lem7564263) (@lem7564258)). Qed.
Lemma lem7564266 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564267 : term818 = term824.
Proof. exact (@lem7564266 (NUMERAL 0) term470). Qed.
Lemma lem7564268 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564269 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564270 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564269 h1) (fun h1 : term824 = True => @lem7564268)). Qed.
Lemma lem7564271 : term824 = True.
Proof. exact (EQ_MP (@lem7564270) (@lem7564268)). Qed.
Lemma lem7564272 : term818 = True.
Proof. exact (TRANS (@lem7564267) (@lem7564271)). Qed.
Lemma lem7564273 : term827 = True.
Proof. exact (TRANS (@lem7564264) (@lem7564272)). Qed.
Lemma lem7564274 : term821 = True.
Proof. exact (TRANS (@lem7564250) (@lem7564273)). Qed.
Lemma lem7564275 : term818 = True.
Proof. exact (TRANS (@lem7564227) (@lem7564274)). Qed.
Lemma lem7564276 : term817 = True.
Proof. exact (TRANS (@lem7564218) (@lem7564275)). Qed.
Lemma lem7564277 : True = term817.
Proof. exact (SYM (@lem7564276)). Qed.
Lemma lem7564278 : term817.
Proof. exact (EQ_MP (@lem7564277) (@lem0)). Qed.
Lemma lem7564279 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term837 _97571.
Proof. exact (conj (@lem7564278) (@lem7564137 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564281 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7564282 (_97571 : int) : term838 _97571.
Proof. exact (@lem7564281 term469 (term559 _97571)). Qed.
Lemma lem7564283 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term839 _97571.
Proof. exact (@lem7564282 _97571 (@lem7564279 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564284 (_97571 : int) : (term840 _97571) = (term559 _97571).
Proof. exact (@lem1982733 (term559 _97571)). Qed.
Lemma lem7564285 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564286 (_97571 : int) : (term841 _97571) = (term563 _97571).
Proof. exact (MK_COMB (@lem7564285) (@lem7564284 _97571)). Qed.
Lemma lem7564287 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564288 (_97571 : int) : (term839 _97571) = (term564 _97571).
Proof. exact (MK_COMB (@lem7564286 _97571) (@lem7564287)). Qed.
Lemma lem7564289 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term564 _97571.
Proof. exact (EQ_MP (@lem7564288 _97571) (@lem7564283 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564290 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term842 _97571.
Proof. exact (conj (@lem7564289 _97569 _97570 _97571 h1) (@lem7564215 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564292 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7564293 (_97571 : int) : term844 _97571.
Proof. exact (@lem7564292 (term559 _97571) (real_of_int _97571)). Qed.
Lemma lem7564294 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term845 _97571.
Proof. exact (@lem7564293 _97571 (@lem7564290 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564295 (_97571 : int) : (term846 _97571) = (term847 _97571).
Proof. exact (@lem1982759 (term570 _97571) (real_of_int _97571) term523). Qed.
Lemma lem7564296 (_97571 : int) : (term848 _97571) = (term849 _97571).
Proof. exact (@lem1982713 term523 (real_of_int _97571)). Qed.
Lemma lem7564298 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564299 : term469 = term549.
Proof. exact (@lem7564298 term470). Qed.
Lemma lem7564301 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7564302 : term523 = term524.
Proof. exact (@lem7564301 term470). Qed.
Lemma lem7564303 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7564304 : term850 = term851.
Proof. exact (MK_COMB (@lem7564303) (@lem7564302)). Qed.
Lemma lem7564305 : term852 = term853.
Proof. exact (MK_COMB (@lem7564304) (@lem7564299)). Qed.
Lemma lem7564306 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7564308 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564309 : term818 = term824.
Proof. exact (@lem7564308 (NUMERAL 0) term470). Qed.
Lemma lem7564310 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564311 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564312 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564311 h1) (fun h1 : term824 = True => @lem7564310)). Qed.
Lemma lem7564313 : term824 = True.
Proof. exact (EQ_MP (@lem7564312) (@lem7564310)). Qed.
Lemma lem7564314 : term818 = True.
Proof. exact (TRANS (@lem7564309) (@lem7564313)). Qed.
Lemma lem7564315 : True = term818.
Proof. exact (SYM (@lem7564314)). Qed.
Lemma lem7564316 : term818.
Proof. exact (EQ_MP (@lem7564315) (@lem0)). Qed.
Lemma lem7564317 : term855.
Proof. exact (@lem7564306 (@lem7564316)). Qed.
Lemma lem7564319 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564320 : term818 = term824.
Proof. exact (@lem7564319 (NUMERAL 0) term470). Qed.
Lemma lem7564321 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564322 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564323 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564322 h1) (fun h1 : term824 = True => @lem7564321)). Qed.
Lemma lem7564324 : term824 = True.
Proof. exact (EQ_MP (@lem7564323) (@lem7564321)). Qed.
Lemma lem7564325 : term818 = True.
Proof. exact (TRANS (@lem7564320) (@lem7564324)). Qed.
Lemma lem7564326 : True = term818.
Proof. exact (SYM (@lem7564325)). Qed.
Lemma lem7564327 : term818.
Proof. exact (EQ_MP (@lem7564326) (@lem0)). Qed.
Lemma lem7564328 : term856.
Proof. exact (@lem7564317 (@lem7564327)). Qed.
Lemma lem7564330 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564331 : term818 = term824.
Proof. exact (@lem7564330 (NUMERAL 0) term470). Qed.
Lemma lem7564332 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564333 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564334 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564333 h1) (fun h1 : term824 = True => @lem7564332)). Qed.
Lemma lem7564335 : term824 = True.
Proof. exact (EQ_MP (@lem7564334) (@lem7564332)). Qed.
Lemma lem7564336 : term818 = True.
Proof. exact (TRANS (@lem7564331) (@lem7564335)). Qed.
Lemma lem7564337 : True = term818.
Proof. exact (SYM (@lem7564336)). Qed.
Lemma lem7564338 : term818.
Proof. exact (EQ_MP (@lem7564337) (@lem0)). Qed.
Lemma lem7564339 : term857.
Proof. exact (@lem7564328 (@lem7564338)). Qed.
Lemma lem7564341 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564342 : term532 = term533.
Proof. exact (@lem7564341 term470 term470). Qed.
Lemma lem7564343 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564344 : term535 = term470.
Proof. exact (EQ_MP (@lem7564343) (@lem940073)). Qed.
Lemma lem7564345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564346 : term533 = term469.
Proof. exact (MK_COMB (@lem7564345) (@lem7564344)). Qed.
Lemma lem7564347 : term532 = term469.
Proof. exact (TRANS (@lem7564342) (@lem7564346)). Qed.
Lemma lem7564349 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7564350 : term550 = term555.
Proof. exact (@lem7564349 term470 term470). Qed.
Lemma lem7564351 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564352 : term535 = term470.
Proof. exact (EQ_MP (@lem7564351) (@lem940073)). Qed.
Lemma lem7564353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564354 : term533 = term469.
Proof. exact (MK_COMB (@lem7564353) (@lem7564352)). Qed.
Lemma lem7564355 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7564356 : term555 = term523.
Proof. exact (MK_COMB (@lem7564355) (@lem7564354)). Qed.
Lemma lem7564357 : term550 = term523.
Proof. exact (TRANS (@lem7564350) (@lem7564356)). Qed.
Lemma lem7564358 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7564359 : term858 = term850.
Proof. exact (MK_COMB (@lem7564358) (@lem7564357)). Qed.
Lemma lem7564360 : term859 = term852.
Proof. exact (MK_COMB (@lem7564359) (@lem7564347)). Qed.
Lemma lem7564362 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7564363 : term852 = term35.
Proof. exact (@lem7564362 term470). Qed.
Lemma lem7564364 : term859 = term35.
Proof. exact (TRANS (@lem7564360) (@lem7564363)). Qed.
Lemma lem7564365 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7564366 : term861 = term218.
Proof. exact (MK_COMB (@lem7564365) (@lem7564364)). Qed.
Lemma lem7564367 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7564368 : term862 = term829.
Proof. exact (MK_COMB (@lem7564366) (@lem7564367)). Qed.
Lemma lem7564370 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564371 : term829 = term35.
Proof. exact (@lem7564370 term470). Qed.
Lemma lem7564372 : term862 = term35.
Proof. exact (TRANS (@lem7564368) (@lem7564371)). Qed.
Lemma lem7564374 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564375 : term532 = term533.
Proof. exact (@lem7564374 term470 term470). Qed.
Lemma lem7564376 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564377 : term535 = term470.
Proof. exact (EQ_MP (@lem7564376) (@lem940073)). Qed.
Lemma lem7564378 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564379 : term533 = term469.
Proof. exact (MK_COMB (@lem7564378) (@lem7564377)). Qed.
Lemma lem7564380 : term532 = term469.
Proof. exact (TRANS (@lem7564375) (@lem7564379)). Qed.
Lemma lem7564381 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7564382 : term863 = term829.
Proof. exact (MK_COMB (@lem7564381) (@lem7564380)). Qed.
Lemma lem7564384 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564385 : term829 = term35.
Proof. exact (@lem7564384 term470). Qed.
Lemma lem7564386 : term863 = term35.
Proof. exact (TRANS (@lem7564382) (@lem7564385)). Qed.
Lemma lem7564387 : term35 = term863.
Proof. exact (SYM (@lem7564386)). Qed.
Lemma lem7564388 : term862 = term863.
Proof. exact (TRANS (@lem7564372) (@lem7564387)). Qed.
Lemma lem7564389 : term853 = term520.
Proof. exact (@lem7564339 (@lem7564388)). Qed.
Lemma lem7564390 : term852 = term520.
Proof. exact (TRANS (@lem7564305) (@lem7564389)). Qed.
Lemma lem7564392 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7564393 : term520 = term35.
Proof. exact (@lem7564392 term35). Qed.
Lemma lem7564394 : term852 = term35.
Proof. exact (TRANS (@lem7564390) (@lem7564393)). Qed.
Lemma lem7564395 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7564396 : term864 = term218.
Proof. exact (MK_COMB (@lem7564395) (@lem7564394)). Qed.
Lemma lem7564397 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7564398 (_97571 : int) : (term849 _97571) = (term865 _97571).
Proof. exact (MK_COMB (@lem7564396) (@lem7564397 _97571)). Qed.
Lemma lem7564399 (_97571 : int) : (term848 _97571) = (term865 _97571).
Proof. exact (TRANS (@lem7564296 _97571) (@lem7564398 _97571)). Qed.
Lemma lem7564400 (_97571 : int) : (term865 _97571) = term35.
Proof. exact (@lem1982719 (real_of_int _97571)). Qed.
Lemma lem7564401 (_97571 : int) : (term848 _97571) = term35.
Proof. exact (TRANS (@lem7564399 _97571) (@lem7564400 _97571)). Qed.
Lemma lem7564402 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7564403 (_97571 : int) : (term866 _97571) = term560.
Proof. exact (MK_COMB (@lem7564402) (@lem7564401 _97571)). Qed.
Lemma lem7564404 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7564405 (_97571 : int) : (term847 _97571) = term867.
Proof. exact (MK_COMB (@lem7564403 _97571) (@lem7564404)). Qed.
Lemma lem7564406 (_97571 : int) : (term846 _97571) = term867.
Proof. exact (TRANS (@lem7564295 _97571) (@lem7564405 _97571)). Qed.
Lemma lem7564407 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7564408 (_97571 : int) : (term846 _97571) = term523.
Proof. exact (TRANS (@lem7564406 _97571) (@lem7564407)). Qed.
Lemma lem7564409 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564410 (_97571 : int) : (term868 _97571) = term869.
Proof. exact (MK_COMB (@lem7564409) (@lem7564408 _97571)). Qed.
Lemma lem7564411 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564412 (_97571 : int) : (term845 _97571) = term870.
Proof. exact (MK_COMB (@lem7564410 _97571) (@lem7564411)). Qed.
Lemma lem7564413 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : term870.
Proof. exact (EQ_MP (@lem7564412 _97571) (@lem7564294 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564415 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7564416 : term870 = term871.
Proof. exact (@lem7564415 term35 term523). Qed.
Lemma lem7564418 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7564419 : term523 = term524.
Proof. exact (@lem7564418 term470). Qed.
Lemma lem7564421 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564422 : term35 = term520.
Proof. exact (@lem7564421 (NUMERAL 0)). Qed.
Lemma lem7564423 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7564424 : term457 = term872.
Proof. exact (MK_COMB (@lem7564423) (@lem7564422)). Qed.
Lemma lem7564425 : term871 = term873.
Proof. exact (MK_COMB (@lem7564424) (@lem7564419)). Qed.
Lemma lem7564426 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7564428 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564429 : term818 = term824.
Proof. exact (@lem7564428 (NUMERAL 0) term470). Qed.
Lemma lem7564430 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564431 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564432 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564431 h1) (fun h1 : term824 = True => @lem7564430)). Qed.
Lemma lem7564433 : term824 = True.
Proof. exact (EQ_MP (@lem7564432) (@lem7564430)). Qed.
Lemma lem7564434 : term818 = True.
Proof. exact (TRANS (@lem7564429) (@lem7564433)). Qed.
Lemma lem7564435 : True = term818.
Proof. exact (SYM (@lem7564434)). Qed.
Lemma lem7564436 : term818.
Proof. exact (EQ_MP (@lem7564435) (@lem0)). Qed.
Lemma lem7564437 : term875.
Proof. exact (@lem7564426 (@lem7564436)). Qed.
Lemma lem7564439 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564440 : term818 = term824.
Proof. exact (@lem7564439 (NUMERAL 0) term470). Qed.
Lemma lem7564441 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564442 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564443 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564442 h1) (fun h1 : term824 = True => @lem7564441)). Qed.
Lemma lem7564444 : term824 = True.
Proof. exact (EQ_MP (@lem7564443) (@lem7564441)). Qed.
Lemma lem7564445 : term818 = True.
Proof. exact (TRANS (@lem7564440) (@lem7564444)). Qed.
Lemma lem7564446 : True = term818.
Proof. exact (SYM (@lem7564445)). Qed.
Lemma lem7564447 : term818.
Proof. exact (EQ_MP (@lem7564446) (@lem0)). Qed.
Lemma lem7564448 : term873 = term876.
Proof. exact (@lem7564437 (@lem7564447)). Qed.
Lemma lem7564450 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7564451 : term550 = term555.
Proof. exact (@lem7564450 term470 term470). Qed.
Lemma lem7564452 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564453 : term535 = term470.
Proof. exact (EQ_MP (@lem7564452) (@lem940073)). Qed.
Lemma lem7564454 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564455 : term533 = term469.
Proof. exact (MK_COMB (@lem7564454) (@lem7564453)). Qed.
Lemma lem7564456 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7564457 : term555 = term523.
Proof. exact (MK_COMB (@lem7564456) (@lem7564455)). Qed.
Lemma lem7564458 : term550 = term523.
Proof. exact (TRANS (@lem7564451) (@lem7564457)). Qed.
Lemma lem7564460 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564461 : term829 = term35.
Proof. exact (@lem7564460 term470). Qed.
Lemma lem7564462 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7564463 : term877 = term457.
Proof. exact (MK_COMB (@lem7564462) (@lem7564461)). Qed.
Lemma lem7564464 : term876 = term871.
Proof. exact (MK_COMB (@lem7564463) (@lem7564458)). Qed.
Lemma lem7564466 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7564467 : term871 = term880.
Proof. exact (@lem7564466 (NUMERAL 0) term470). Qed.
Lemma lem7564468 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564469 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7564470 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564469 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7564468)). Qed.
Lemma lem7564471 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7564470) (@lem7564468)). Qed.
Lemma lem7564472 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7564473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564474 : term881 = (and True).
Proof. exact (MK_COMB (@lem7564473) (@lem7564472)). Qed.
Lemma lem7564475 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7564474) (@lem7564471)). Qed.
Lemma lem7564477 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7564478 : term880 = False.
Proof. exact (TRANS (@lem7564475) (@lem7564477)). Qed.
Lemma lem7564479 : term871 = False.
Proof. exact (TRANS (@lem7564467) (@lem7564478)). Qed.
Lemma lem7564480 : term876 = False.
Proof. exact (TRANS (@lem7564464) (@lem7564479)). Qed.
Lemma lem7564481 : term873 = False.
Proof. exact (TRANS (@lem7564448) (@lem7564480)). Qed.
Lemma lem7564482 : term871 = False.
Proof. exact (TRANS (@lem7564425) (@lem7564481)). Qed.
Lemma lem7564483 : term870 = False.
Proof. exact (TRANS (@lem7564416) (@lem7564482)). Qed.
Lemma lem7564484 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1065 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7564483) (@lem7564413 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564485 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term1069 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7564486 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term1068 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7564485 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564488 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term1067 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7564486 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564490 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term731 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7564488 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564492 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term729 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7564490 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564494 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term726 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7564492 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564495 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term564 _97571.
Proof. exact (proj1 (@lem7564492 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564497 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term595 _97569 _97571.
Proof. exact (proj1 (@lem7564494 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564499 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term543 _97571.
Proof. exact (proj1 (@lem7564497 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564501 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7564502 : term817 = term818.
Proof. exact (@lem7564501 term35 term469). Qed.
Lemma lem7564504 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564505 : term469 = term549.
Proof. exact (@lem7564504 term470). Qed.
Lemma lem7564507 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564508 : term35 = term520.
Proof. exact (@lem7564507 (NUMERAL 0)). Qed.
Lemma lem7564509 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564510 : term819 = term820.
Proof. exact (MK_COMB (@lem7564509) (@lem7564508)). Qed.
Lemma lem7564511 : term818 = term821.
Proof. exact (MK_COMB (@lem7564510) (@lem7564505)). Qed.
Lemma lem7564512 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7564514 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564515 : term818 = term824.
Proof. exact (@lem7564514 (NUMERAL 0) term470). Qed.
Lemma lem7564516 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564517 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564518 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564517 h1) (fun h1 : term824 = True => @lem7564516)). Qed.
Lemma lem7564519 : term824 = True.
Proof. exact (EQ_MP (@lem7564518) (@lem7564516)). Qed.
Lemma lem7564520 : term818 = True.
Proof. exact (TRANS (@lem7564515) (@lem7564519)). Qed.
Lemma lem7564521 : True = term818.
Proof. exact (SYM (@lem7564520)). Qed.
Lemma lem7564522 : term818.
Proof. exact (EQ_MP (@lem7564521) (@lem0)). Qed.
Lemma lem7564523 : term826.
Proof. exact (@lem7564512 (@lem7564522)). Qed.
Lemma lem7564525 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564526 : term818 = term824.
Proof. exact (@lem7564525 (NUMERAL 0) term470). Qed.
Lemma lem7564527 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564528 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564529 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564528 h1) (fun h1 : term824 = True => @lem7564527)). Qed.
Lemma lem7564530 : term824 = True.
Proof. exact (EQ_MP (@lem7564529) (@lem7564527)). Qed.
Lemma lem7564531 : term818 = True.
Proof. exact (TRANS (@lem7564526) (@lem7564530)). Qed.
Lemma lem7564532 : True = term818.
Proof. exact (SYM (@lem7564531)). Qed.
Lemma lem7564533 : term818.
Proof. exact (EQ_MP (@lem7564532) (@lem0)). Qed.
Lemma lem7564534 : term821 = term827.
Proof. exact (@lem7564523 (@lem7564533)). Qed.
Lemma lem7564536 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564537 : term532 = term533.
Proof. exact (@lem7564536 term470 term470). Qed.
Lemma lem7564538 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564539 : term535 = term470.
Proof. exact (EQ_MP (@lem7564538) (@lem940073)). Qed.
Lemma lem7564540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564541 : term533 = term469.
Proof. exact (MK_COMB (@lem7564540) (@lem7564539)). Qed.
Lemma lem7564542 : term532 = term469.
Proof. exact (TRANS (@lem7564537) (@lem7564541)). Qed.
Lemma lem7564544 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564545 : term829 = term35.
Proof. exact (@lem7564544 term470). Qed.
Lemma lem7564546 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564547 : term830 = term819.
Proof. exact (MK_COMB (@lem7564546) (@lem7564545)). Qed.
Lemma lem7564548 : term827 = term818.
Proof. exact (MK_COMB (@lem7564547) (@lem7564542)). Qed.
Lemma lem7564550 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564551 : term818 = term824.
Proof. exact (@lem7564550 (NUMERAL 0) term470). Qed.
Lemma lem7564552 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564553 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564554 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564553 h1) (fun h1 : term824 = True => @lem7564552)). Qed.
Lemma lem7564555 : term824 = True.
Proof. exact (EQ_MP (@lem7564554) (@lem7564552)). Qed.
Lemma lem7564556 : term818 = True.
Proof. exact (TRANS (@lem7564551) (@lem7564555)). Qed.
Lemma lem7564557 : term827 = True.
Proof. exact (TRANS (@lem7564548) (@lem7564556)). Qed.
Lemma lem7564558 : term821 = True.
Proof. exact (TRANS (@lem7564534) (@lem7564557)). Qed.
Lemma lem7564559 : term818 = True.
Proof. exact (TRANS (@lem7564511) (@lem7564558)). Qed.
Lemma lem7564560 : term817 = True.
Proof. exact (TRANS (@lem7564502) (@lem7564559)). Qed.
Lemma lem7564561 : True = term817.
Proof. exact (SYM (@lem7564560)). Qed.
Lemma lem7564562 : term817.
Proof. exact (EQ_MP (@lem7564561) (@lem0)). Qed.
Lemma lem7564563 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term831 _97571.
Proof. exact (conj (@lem7564562) (@lem7564499 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564565 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7564566 (_97571 : int) : term833 _97571.
Proof. exact (@lem7564565 term469 (real_of_int _97571)). Qed.
Lemma lem7564567 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term834 _97571.
Proof. exact (@lem7564566 _97571 (@lem7564563 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564568 (_97571 : int) : (term835 _97571) = (real_of_int _97571).
Proof. exact (@lem1982733 (real_of_int _97571)). Qed.
Lemma lem7564569 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564570 (_97571 : int) : (term836 _97571) = (term542 _97571).
Proof. exact (MK_COMB (@lem7564569) (@lem7564568 _97571)). Qed.
Lemma lem7564571 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564572 (_97571 : int) : (term834 _97571) = (term543 _97571).
Proof. exact (MK_COMB (@lem7564570 _97571) (@lem7564571)). Qed.
Lemma lem7564573 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term543 _97571.
Proof. exact (EQ_MP (@lem7564572 _97571) (@lem7564567 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564575 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7564576 : term817 = term818.
Proof. exact (@lem7564575 term35 term469). Qed.
Lemma lem7564578 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564579 : term469 = term549.
Proof. exact (@lem7564578 term470). Qed.
Lemma lem7564581 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564582 : term35 = term520.
Proof. exact (@lem7564581 (NUMERAL 0)). Qed.
Lemma lem7564583 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564584 : term819 = term820.
Proof. exact (MK_COMB (@lem7564583) (@lem7564582)). Qed.
Lemma lem7564585 : term818 = term821.
Proof. exact (MK_COMB (@lem7564584) (@lem7564579)). Qed.
Lemma lem7564586 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7564588 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564589 : term818 = term824.
Proof. exact (@lem7564588 (NUMERAL 0) term470). Qed.
Lemma lem7564590 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564591 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564592 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564591 h1) (fun h1 : term824 = True => @lem7564590)). Qed.
Lemma lem7564593 : term824 = True.
Proof. exact (EQ_MP (@lem7564592) (@lem7564590)). Qed.
Lemma lem7564594 : term818 = True.
Proof. exact (TRANS (@lem7564589) (@lem7564593)). Qed.
Lemma lem7564595 : True = term818.
Proof. exact (SYM (@lem7564594)). Qed.
Lemma lem7564596 : term818.
Proof. exact (EQ_MP (@lem7564595) (@lem0)). Qed.
Lemma lem7564597 : term826.
Proof. exact (@lem7564586 (@lem7564596)). Qed.
Lemma lem7564599 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564600 : term818 = term824.
Proof. exact (@lem7564599 (NUMERAL 0) term470). Qed.
Lemma lem7564601 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564602 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564603 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564602 h1) (fun h1 : term824 = True => @lem7564601)). Qed.
Lemma lem7564604 : term824 = True.
Proof. exact (EQ_MP (@lem7564603) (@lem7564601)). Qed.
Lemma lem7564605 : term818 = True.
Proof. exact (TRANS (@lem7564600) (@lem7564604)). Qed.
Lemma lem7564606 : True = term818.
Proof. exact (SYM (@lem7564605)). Qed.
Lemma lem7564607 : term818.
Proof. exact (EQ_MP (@lem7564606) (@lem0)). Qed.
Lemma lem7564608 : term821 = term827.
Proof. exact (@lem7564597 (@lem7564607)). Qed.
Lemma lem7564610 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564611 : term532 = term533.
Proof. exact (@lem7564610 term470 term470). Qed.
Lemma lem7564612 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564613 : term535 = term470.
Proof. exact (EQ_MP (@lem7564612) (@lem940073)). Qed.
Lemma lem7564614 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564615 : term533 = term469.
Proof. exact (MK_COMB (@lem7564614) (@lem7564613)). Qed.
Lemma lem7564616 : term532 = term469.
Proof. exact (TRANS (@lem7564611) (@lem7564615)). Qed.
Lemma lem7564618 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564619 : term829 = term35.
Proof. exact (@lem7564618 term470). Qed.
Lemma lem7564620 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564621 : term830 = term819.
Proof. exact (MK_COMB (@lem7564620) (@lem7564619)). Qed.
Lemma lem7564622 : term827 = term818.
Proof. exact (MK_COMB (@lem7564621) (@lem7564616)). Qed.
Lemma lem7564624 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564625 : term818 = term824.
Proof. exact (@lem7564624 (NUMERAL 0) term470). Qed.
Lemma lem7564626 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564627 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564628 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564627 h1) (fun h1 : term824 = True => @lem7564626)). Qed.
Lemma lem7564629 : term824 = True.
Proof. exact (EQ_MP (@lem7564628) (@lem7564626)). Qed.
Lemma lem7564630 : term818 = True.
Proof. exact (TRANS (@lem7564625) (@lem7564629)). Qed.
Lemma lem7564631 : term827 = True.
Proof. exact (TRANS (@lem7564622) (@lem7564630)). Qed.
Lemma lem7564632 : term821 = True.
Proof. exact (TRANS (@lem7564608) (@lem7564631)). Qed.
Lemma lem7564633 : term818 = True.
Proof. exact (TRANS (@lem7564585) (@lem7564632)). Qed.
Lemma lem7564634 : term817 = True.
Proof. exact (TRANS (@lem7564576) (@lem7564633)). Qed.
Lemma lem7564635 : True = term817.
Proof. exact (SYM (@lem7564634)). Qed.
Lemma lem7564636 : term817.
Proof. exact (EQ_MP (@lem7564635) (@lem0)). Qed.
Lemma lem7564637 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term837 _97571.
Proof. exact (conj (@lem7564636) (@lem7564495 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564639 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7564640 (_97571 : int) : term838 _97571.
Proof. exact (@lem7564639 term469 (term559 _97571)). Qed.
Lemma lem7564641 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term839 _97571.
Proof. exact (@lem7564640 _97571 (@lem7564637 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564642 (_97571 : int) : (term840 _97571) = (term559 _97571).
Proof. exact (@lem1982733 (term559 _97571)). Qed.
Lemma lem7564643 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564644 (_97571 : int) : (term841 _97571) = (term563 _97571).
Proof. exact (MK_COMB (@lem7564643) (@lem7564642 _97571)). Qed.
Lemma lem7564645 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564646 (_97571 : int) : (term839 _97571) = (term564 _97571).
Proof. exact (MK_COMB (@lem7564644 _97571) (@lem7564645)). Qed.
Lemma lem7564647 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term564 _97571.
Proof. exact (EQ_MP (@lem7564646 _97571) (@lem7564641 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564648 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term842 _97571.
Proof. exact (conj (@lem7564647 _97569 _97570 _97571 h1) (@lem7564573 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564650 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7564651 (_97571 : int) : term844 _97571.
Proof. exact (@lem7564650 (term559 _97571) (real_of_int _97571)). Qed.
Lemma lem7564652 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term845 _97571.
Proof. exact (@lem7564651 _97571 (@lem7564648 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564653 (_97571 : int) : (term846 _97571) = (term847 _97571).
Proof. exact (@lem1982759 (term570 _97571) (real_of_int _97571) term523). Qed.
Lemma lem7564654 (_97571 : int) : (term848 _97571) = (term849 _97571).
Proof. exact (@lem1982713 term523 (real_of_int _97571)). Qed.
Lemma lem7564656 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564657 : term469 = term549.
Proof. exact (@lem7564656 term470). Qed.
Lemma lem7564659 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7564660 : term523 = term524.
Proof. exact (@lem7564659 term470). Qed.
Lemma lem7564661 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7564662 : term850 = term851.
Proof. exact (MK_COMB (@lem7564661) (@lem7564660)). Qed.
Lemma lem7564663 : term852 = term853.
Proof. exact (MK_COMB (@lem7564662) (@lem7564657)). Qed.
Lemma lem7564664 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7564666 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564667 : term818 = term824.
Proof. exact (@lem7564666 (NUMERAL 0) term470). Qed.
Lemma lem7564668 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564669 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564670 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564669 h1) (fun h1 : term824 = True => @lem7564668)). Qed.
Lemma lem7564671 : term824 = True.
Proof. exact (EQ_MP (@lem7564670) (@lem7564668)). Qed.
Lemma lem7564672 : term818 = True.
Proof. exact (TRANS (@lem7564667) (@lem7564671)). Qed.
Lemma lem7564673 : True = term818.
Proof. exact (SYM (@lem7564672)). Qed.
Lemma lem7564674 : term818.
Proof. exact (EQ_MP (@lem7564673) (@lem0)). Qed.
Lemma lem7564675 : term855.
Proof. exact (@lem7564664 (@lem7564674)). Qed.
Lemma lem7564677 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564678 : term818 = term824.
Proof. exact (@lem7564677 (NUMERAL 0) term470). Qed.
Lemma lem7564679 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564680 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564681 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564680 h1) (fun h1 : term824 = True => @lem7564679)). Qed.
Lemma lem7564682 : term824 = True.
Proof. exact (EQ_MP (@lem7564681) (@lem7564679)). Qed.
Lemma lem7564683 : term818 = True.
Proof. exact (TRANS (@lem7564678) (@lem7564682)). Qed.
Lemma lem7564684 : True = term818.
Proof. exact (SYM (@lem7564683)). Qed.
Lemma lem7564685 : term818.
Proof. exact (EQ_MP (@lem7564684) (@lem0)). Qed.
Lemma lem7564686 : term856.
Proof. exact (@lem7564675 (@lem7564685)). Qed.
Lemma lem7564688 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564689 : term818 = term824.
Proof. exact (@lem7564688 (NUMERAL 0) term470). Qed.
Lemma lem7564690 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564691 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564692 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564691 h1) (fun h1 : term824 = True => @lem7564690)). Qed.
Lemma lem7564693 : term824 = True.
Proof. exact (EQ_MP (@lem7564692) (@lem7564690)). Qed.
Lemma lem7564694 : term818 = True.
Proof. exact (TRANS (@lem7564689) (@lem7564693)). Qed.
Lemma lem7564695 : True = term818.
Proof. exact (SYM (@lem7564694)). Qed.
Lemma lem7564696 : term818.
Proof. exact (EQ_MP (@lem7564695) (@lem0)). Qed.
Lemma lem7564697 : term857.
Proof. exact (@lem7564686 (@lem7564696)). Qed.
Lemma lem7564699 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564700 : term532 = term533.
Proof. exact (@lem7564699 term470 term470). Qed.
Lemma lem7564701 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564702 : term535 = term470.
Proof. exact (EQ_MP (@lem7564701) (@lem940073)). Qed.
Lemma lem7564703 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564704 : term533 = term469.
Proof. exact (MK_COMB (@lem7564703) (@lem7564702)). Qed.
Lemma lem7564705 : term532 = term469.
Proof. exact (TRANS (@lem7564700) (@lem7564704)). Qed.
Lemma lem7564707 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7564708 : term550 = term555.
Proof. exact (@lem7564707 term470 term470). Qed.
Lemma lem7564709 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564710 : term535 = term470.
Proof. exact (EQ_MP (@lem7564709) (@lem940073)). Qed.
Lemma lem7564711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564712 : term533 = term469.
Proof. exact (MK_COMB (@lem7564711) (@lem7564710)). Qed.
Lemma lem7564713 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7564714 : term555 = term523.
Proof. exact (MK_COMB (@lem7564713) (@lem7564712)). Qed.
Lemma lem7564715 : term550 = term523.
Proof. exact (TRANS (@lem7564708) (@lem7564714)). Qed.
Lemma lem7564716 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7564717 : term858 = term850.
Proof. exact (MK_COMB (@lem7564716) (@lem7564715)). Qed.
Lemma lem7564718 : term859 = term852.
Proof. exact (MK_COMB (@lem7564717) (@lem7564705)). Qed.
Lemma lem7564720 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7564721 : term852 = term35.
Proof. exact (@lem7564720 term470). Qed.
Lemma lem7564722 : term859 = term35.
Proof. exact (TRANS (@lem7564718) (@lem7564721)). Qed.
Lemma lem7564723 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7564724 : term861 = term218.
Proof. exact (MK_COMB (@lem7564723) (@lem7564722)). Qed.
Lemma lem7564725 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7564726 : term862 = term829.
Proof. exact (MK_COMB (@lem7564724) (@lem7564725)). Qed.
Lemma lem7564728 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564729 : term829 = term35.
Proof. exact (@lem7564728 term470). Qed.
Lemma lem7564730 : term862 = term35.
Proof. exact (TRANS (@lem7564726) (@lem7564729)). Qed.
Lemma lem7564732 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564733 : term532 = term533.
Proof. exact (@lem7564732 term470 term470). Qed.
Lemma lem7564734 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564735 : term535 = term470.
Proof. exact (EQ_MP (@lem7564734) (@lem940073)). Qed.
Lemma lem7564736 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564737 : term533 = term469.
Proof. exact (MK_COMB (@lem7564736) (@lem7564735)). Qed.
Lemma lem7564738 : term532 = term469.
Proof. exact (TRANS (@lem7564733) (@lem7564737)). Qed.
Lemma lem7564739 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7564740 : term863 = term829.
Proof. exact (MK_COMB (@lem7564739) (@lem7564738)). Qed.
Lemma lem7564742 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564743 : term829 = term35.
Proof. exact (@lem7564742 term470). Qed.
Lemma lem7564744 : term863 = term35.
Proof. exact (TRANS (@lem7564740) (@lem7564743)). Qed.
Lemma lem7564745 : term35 = term863.
Proof. exact (SYM (@lem7564744)). Qed.
Lemma lem7564746 : term862 = term863.
Proof. exact (TRANS (@lem7564730) (@lem7564745)). Qed.
Lemma lem7564747 : term853 = term520.
Proof. exact (@lem7564697 (@lem7564746)). Qed.
Lemma lem7564748 : term852 = term520.
Proof. exact (TRANS (@lem7564663) (@lem7564747)). Qed.
Lemma lem7564750 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7564751 : term520 = term35.
Proof. exact (@lem7564750 term35). Qed.
Lemma lem7564752 : term852 = term35.
Proof. exact (TRANS (@lem7564748) (@lem7564751)). Qed.
Lemma lem7564753 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7564754 : term864 = term218.
Proof. exact (MK_COMB (@lem7564753) (@lem7564752)). Qed.
Lemma lem7564755 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7564756 (_97571 : int) : (term849 _97571) = (term865 _97571).
Proof. exact (MK_COMB (@lem7564754) (@lem7564755 _97571)). Qed.
Lemma lem7564757 (_97571 : int) : (term848 _97571) = (term865 _97571).
Proof. exact (TRANS (@lem7564654 _97571) (@lem7564756 _97571)). Qed.
Lemma lem7564758 (_97571 : int) : (term865 _97571) = term35.
Proof. exact (@lem1982719 (real_of_int _97571)). Qed.
Lemma lem7564759 (_97571 : int) : (term848 _97571) = term35.
Proof. exact (TRANS (@lem7564757 _97571) (@lem7564758 _97571)). Qed.
Lemma lem7564760 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7564761 (_97571 : int) : (term866 _97571) = term560.
Proof. exact (MK_COMB (@lem7564760) (@lem7564759 _97571)). Qed.
Lemma lem7564762 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7564763 (_97571 : int) : (term847 _97571) = term867.
Proof. exact (MK_COMB (@lem7564761 _97571) (@lem7564762)). Qed.
Lemma lem7564764 (_97571 : int) : (term846 _97571) = term867.
Proof. exact (TRANS (@lem7564653 _97571) (@lem7564763 _97571)). Qed.
Lemma lem7564765 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7564766 (_97571 : int) : (term846 _97571) = term523.
Proof. exact (TRANS (@lem7564764 _97571) (@lem7564765)). Qed.
Lemma lem7564767 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564768 (_97571 : int) : (term868 _97571) = term869.
Proof. exact (MK_COMB (@lem7564767) (@lem7564766 _97571)). Qed.
Lemma lem7564769 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564770 (_97571 : int) : (term845 _97571) = term870.
Proof. exact (MK_COMB (@lem7564768 _97571) (@lem7564769)). Qed.
Lemma lem7564771 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : term870.
Proof. exact (EQ_MP (@lem7564770 _97571) (@lem7564652 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564773 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7564774 : term870 = term871.
Proof. exact (@lem7564773 term35 term523). Qed.
Lemma lem7564776 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7564777 : term523 = term524.
Proof. exact (@lem7564776 term470). Qed.
Lemma lem7564779 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564780 : term35 = term520.
Proof. exact (@lem7564779 (NUMERAL 0)). Qed.
Lemma lem7564781 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7564782 : term457 = term872.
Proof. exact (MK_COMB (@lem7564781) (@lem7564780)). Qed.
Lemma lem7564783 : term871 = term873.
Proof. exact (MK_COMB (@lem7564782) (@lem7564777)). Qed.
Lemma lem7564784 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7564786 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564787 : term818 = term824.
Proof. exact (@lem7564786 (NUMERAL 0) term470). Qed.
Lemma lem7564788 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564789 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564790 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564789 h1) (fun h1 : term824 = True => @lem7564788)). Qed.
Lemma lem7564791 : term824 = True.
Proof. exact (EQ_MP (@lem7564790) (@lem7564788)). Qed.
Lemma lem7564792 : term818 = True.
Proof. exact (TRANS (@lem7564787) (@lem7564791)). Qed.
Lemma lem7564793 : True = term818.
Proof. exact (SYM (@lem7564792)). Qed.
Lemma lem7564794 : term818.
Proof. exact (EQ_MP (@lem7564793) (@lem0)). Qed.
Lemma lem7564795 : term875.
Proof. exact (@lem7564784 (@lem7564794)). Qed.
Lemma lem7564797 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564798 : term818 = term824.
Proof. exact (@lem7564797 (NUMERAL 0) term470). Qed.
Lemma lem7564799 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564800 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564801 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564800 h1) (fun h1 : term824 = True => @lem7564799)). Qed.
Lemma lem7564802 : term824 = True.
Proof. exact (EQ_MP (@lem7564801) (@lem7564799)). Qed.
Lemma lem7564803 : term818 = True.
Proof. exact (TRANS (@lem7564798) (@lem7564802)). Qed.
Lemma lem7564804 : True = term818.
Proof. exact (SYM (@lem7564803)). Qed.
Lemma lem7564805 : term818.
Proof. exact (EQ_MP (@lem7564804) (@lem0)). Qed.
Lemma lem7564806 : term873 = term876.
Proof. exact (@lem7564795 (@lem7564805)). Qed.
Lemma lem7564808 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7564809 : term550 = term555.
Proof. exact (@lem7564808 term470 term470). Qed.
Lemma lem7564810 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564811 : term535 = term470.
Proof. exact (EQ_MP (@lem7564810) (@lem940073)). Qed.
Lemma lem7564812 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564813 : term533 = term469.
Proof. exact (MK_COMB (@lem7564812) (@lem7564811)). Qed.
Lemma lem7564814 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7564815 : term555 = term523.
Proof. exact (MK_COMB (@lem7564814) (@lem7564813)). Qed.
Lemma lem7564816 : term550 = term523.
Proof. exact (TRANS (@lem7564809) (@lem7564815)). Qed.
Lemma lem7564818 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564819 : term829 = term35.
Proof. exact (@lem7564818 term470). Qed.
Lemma lem7564820 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7564821 : term877 = term457.
Proof. exact (MK_COMB (@lem7564820) (@lem7564819)). Qed.
Lemma lem7564822 : term876 = term871.
Proof. exact (MK_COMB (@lem7564821) (@lem7564816)). Qed.
Lemma lem7564824 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7564825 : term871 = term880.
Proof. exact (@lem7564824 (NUMERAL 0) term470). Qed.
Lemma lem7564826 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564827 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7564828 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564827 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7564826)). Qed.
Lemma lem7564829 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7564828) (@lem7564826)). Qed.
Lemma lem7564830 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7564831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7564832 : term881 = (and True).
Proof. exact (MK_COMB (@lem7564831) (@lem7564830)). Qed.
Lemma lem7564833 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7564832) (@lem7564829)). Qed.
Lemma lem7564835 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7564836 : term880 = False.
Proof. exact (TRANS (@lem7564833) (@lem7564835)). Qed.
Lemma lem7564837 : term871 = False.
Proof. exact (TRANS (@lem7564825) (@lem7564836)). Qed.
Lemma lem7564838 : term876 = False.
Proof. exact (TRANS (@lem7564822) (@lem7564837)). Qed.
Lemma lem7564839 : term873 = False.
Proof. exact (TRANS (@lem7564806) (@lem7564838)). Qed.
Lemma lem7564840 : term871 = False.
Proof. exact (TRANS (@lem7564783) (@lem7564839)). Qed.
Lemma lem7564841 : term870 = False.
Proof. exact (TRANS (@lem7564774) (@lem7564840)). Qed.
Lemma lem7564842 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1069 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7564841) (@lem7564771 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564843 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1071 _97569 _97570 _97571) : False.
Proof. exact (or_elim (@lem7564126 _97569 _97570 _97571 h1) (fun h0 : term1065 _97569 _97570 _97571 => @lem7564484 _97569 _97570 _97571 h0) (fun h0 : term1069 _97569 _97570 _97571 => @lem7564842 _97569 _97570 _97571 h0)). Qed.
Lemma lem7564844 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1097 _97569 _97570 _97571) : term1097 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7564845 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term1091 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7564846 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term1090 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7564845 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564848 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term1089 _97570 _97571.
Proof. exact (proj2 (@lem7564846 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564850 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term789 _97570 _97571.
Proof. exact (proj2 (@lem7564848 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564852 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term787 _97570 _97571.
Proof. exact (proj2 (@lem7564850 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564854 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term743 _97570 _97571.
Proof. exact (proj2 (@lem7564852 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564855 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (proj1 (@lem7564852 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564856 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (proj2 (@lem7564854 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564861 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7564862 : term817 = term818.
Proof. exact (@lem7564861 term35 term469). Qed.
Lemma lem7564864 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564865 : term469 = term549.
Proof. exact (@lem7564864 term470). Qed.
Lemma lem7564867 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564868 : term35 = term520.
Proof. exact (@lem7564867 (NUMERAL 0)). Qed.
Lemma lem7564869 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564870 : term819 = term820.
Proof. exact (MK_COMB (@lem7564869) (@lem7564868)). Qed.
Lemma lem7564871 : term818 = term821.
Proof. exact (MK_COMB (@lem7564870) (@lem7564865)). Qed.
Lemma lem7564872 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7564874 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564875 : term818 = term824.
Proof. exact (@lem7564874 (NUMERAL 0) term470). Qed.
Lemma lem7564876 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564877 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564878 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564877 h1) (fun h1 : term824 = True => @lem7564876)). Qed.
Lemma lem7564879 : term824 = True.
Proof. exact (EQ_MP (@lem7564878) (@lem7564876)). Qed.
Lemma lem7564880 : term818 = True.
Proof. exact (TRANS (@lem7564875) (@lem7564879)). Qed.
Lemma lem7564881 : True = term818.
Proof. exact (SYM (@lem7564880)). Qed.
Lemma lem7564882 : term818.
Proof. exact (EQ_MP (@lem7564881) (@lem0)). Qed.
Lemma lem7564883 : term826.
Proof. exact (@lem7564872 (@lem7564882)). Qed.
Lemma lem7564885 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564886 : term818 = term824.
Proof. exact (@lem7564885 (NUMERAL 0) term470). Qed.
Lemma lem7564887 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564888 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564889 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564888 h1) (fun h1 : term824 = True => @lem7564887)). Qed.
Lemma lem7564890 : term824 = True.
Proof. exact (EQ_MP (@lem7564889) (@lem7564887)). Qed.
Lemma lem7564891 : term818 = True.
Proof. exact (TRANS (@lem7564886) (@lem7564890)). Qed.
Lemma lem7564892 : True = term818.
Proof. exact (SYM (@lem7564891)). Qed.
Lemma lem7564893 : term818.
Proof. exact (EQ_MP (@lem7564892) (@lem0)). Qed.
Lemma lem7564894 : term821 = term827.
Proof. exact (@lem7564883 (@lem7564893)). Qed.
Lemma lem7564896 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564897 : term532 = term533.
Proof. exact (@lem7564896 term470 term470). Qed.
Lemma lem7564898 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564899 : term535 = term470.
Proof. exact (EQ_MP (@lem7564898) (@lem940073)). Qed.
Lemma lem7564900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564901 : term533 = term469.
Proof. exact (MK_COMB (@lem7564900) (@lem7564899)). Qed.
Lemma lem7564902 : term532 = term469.
Proof. exact (TRANS (@lem7564897) (@lem7564901)). Qed.
Lemma lem7564904 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564905 : term829 = term35.
Proof. exact (@lem7564904 term470). Qed.
Lemma lem7564906 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564907 : term830 = term819.
Proof. exact (MK_COMB (@lem7564906) (@lem7564905)). Qed.
Lemma lem7564908 : term827 = term818.
Proof. exact (MK_COMB (@lem7564907) (@lem7564902)). Qed.
Lemma lem7564910 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564911 : term818 = term824.
Proof. exact (@lem7564910 (NUMERAL 0) term470). Qed.
Lemma lem7564912 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564913 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564914 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564913 h1) (fun h1 : term824 = True => @lem7564912)). Qed.
Lemma lem7564915 : term824 = True.
Proof. exact (EQ_MP (@lem7564914) (@lem7564912)). Qed.
Lemma lem7564916 : term818 = True.
Proof. exact (TRANS (@lem7564911) (@lem7564915)). Qed.
Lemma lem7564917 : term827 = True.
Proof. exact (TRANS (@lem7564908) (@lem7564916)). Qed.
Lemma lem7564918 : term821 = True.
Proof. exact (TRANS (@lem7564894) (@lem7564917)). Qed.
Lemma lem7564919 : term818 = True.
Proof. exact (TRANS (@lem7564871) (@lem7564918)). Qed.
Lemma lem7564920 : term817 = True.
Proof. exact (TRANS (@lem7564862) (@lem7564919)). Qed.
Lemma lem7564921 : True = term817.
Proof. exact (SYM (@lem7564920)). Qed.
Lemma lem7564922 : term817.
Proof. exact (EQ_MP (@lem7564921) (@lem0)). Qed.
Lemma lem7564923 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term882 _97570 _97571.
Proof. exact (conj (@lem7564922) (@lem7564856 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564925 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7564926 (_97570 : int) (_97571 : int) : term883 _97570 _97571.
Proof. exact (@lem7564925 term469 (term587 _97570 _97571)). Qed.
Lemma lem7564927 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term884 _97570 _97571.
Proof. exact (@lem7564926 _97570 _97571 (@lem7564923 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564928 (_97570 : int) (_97571 : int) : (term885 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982733 (term587 _97570 _97571)). Qed.
Lemma lem7564929 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7564930 (_97570 : int) (_97571 : int) : (term886 _97570 _97571) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7564929) (@lem7564928 _97570 _97571)). Qed.
Lemma lem7564931 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7564932 (_97570 : int) (_97571 : int) : (term884 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7564930 _97570 _97571) (@lem7564931)). Qed.
Lemma lem7564933 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (EQ_MP (@lem7564932 _97570 _97571) (@lem7564927 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564935 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7564936 : term817 = term818.
Proof. exact (@lem7564935 term35 term469). Qed.
Lemma lem7564938 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564939 : term469 = term549.
Proof. exact (@lem7564938 term470). Qed.
Lemma lem7564941 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7564942 : term35 = term520.
Proof. exact (@lem7564941 (NUMERAL 0)). Qed.
Lemma lem7564943 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564944 : term819 = term820.
Proof. exact (MK_COMB (@lem7564943) (@lem7564942)). Qed.
Lemma lem7564945 : term818 = term821.
Proof. exact (MK_COMB (@lem7564944) (@lem7564939)). Qed.
Lemma lem7564946 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7564948 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564949 : term818 = term824.
Proof. exact (@lem7564948 (NUMERAL 0) term470). Qed.
Lemma lem7564950 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564951 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564952 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564951 h1) (fun h1 : term824 = True => @lem7564950)). Qed.
Lemma lem7564953 : term824 = True.
Proof. exact (EQ_MP (@lem7564952) (@lem7564950)). Qed.
Lemma lem7564954 : term818 = True.
Proof. exact (TRANS (@lem7564949) (@lem7564953)). Qed.
Lemma lem7564955 : True = term818.
Proof. exact (SYM (@lem7564954)). Qed.
Lemma lem7564956 : term818.
Proof. exact (EQ_MP (@lem7564955) (@lem0)). Qed.
Lemma lem7564957 : term826.
Proof. exact (@lem7564946 (@lem7564956)). Qed.
Lemma lem7564959 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564960 : term818 = term824.
Proof. exact (@lem7564959 (NUMERAL 0) term470). Qed.
Lemma lem7564961 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564962 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564963 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564962 h1) (fun h1 : term824 = True => @lem7564961)). Qed.
Lemma lem7564964 : term824 = True.
Proof. exact (EQ_MP (@lem7564963) (@lem7564961)). Qed.
Lemma lem7564965 : term818 = True.
Proof. exact (TRANS (@lem7564960) (@lem7564964)). Qed.
Lemma lem7564966 : True = term818.
Proof. exact (SYM (@lem7564965)). Qed.
Lemma lem7564967 : term818.
Proof. exact (EQ_MP (@lem7564966) (@lem0)). Qed.
Lemma lem7564968 : term821 = term827.
Proof. exact (@lem7564957 (@lem7564967)). Qed.
Lemma lem7564970 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7564971 : term532 = term533.
Proof. exact (@lem7564970 term470 term470). Qed.
Lemma lem7564972 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7564973 : term535 = term470.
Proof. exact (EQ_MP (@lem7564972) (@lem940073)). Qed.
Lemma lem7564974 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7564975 : term533 = term469.
Proof. exact (MK_COMB (@lem7564974) (@lem7564973)). Qed.
Lemma lem7564976 : term532 = term469.
Proof. exact (TRANS (@lem7564971) (@lem7564975)). Qed.
Lemma lem7564978 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7564979 : term829 = term35.
Proof. exact (@lem7564978 term470). Qed.
Lemma lem7564980 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7564981 : term830 = term819.
Proof. exact (MK_COMB (@lem7564980) (@lem7564979)). Qed.
Lemma lem7564982 : term827 = term818.
Proof. exact (MK_COMB (@lem7564981) (@lem7564976)). Qed.
Lemma lem7564984 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7564985 : term818 = term824.
Proof. exact (@lem7564984 (NUMERAL 0) term470). Qed.
Lemma lem7564986 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7564987 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7564988 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7564987 h1) (fun h1 : term824 = True => @lem7564986)). Qed.
Lemma lem7564989 : term824 = True.
Proof. exact (EQ_MP (@lem7564988) (@lem7564986)). Qed.
Lemma lem7564990 : term818 = True.
Proof. exact (TRANS (@lem7564985) (@lem7564989)). Qed.
Lemma lem7564991 : term827 = True.
Proof. exact (TRANS (@lem7564982) (@lem7564990)). Qed.
Lemma lem7564992 : term821 = True.
Proof. exact (TRANS (@lem7564968) (@lem7564991)). Qed.
Lemma lem7564993 : term818 = True.
Proof. exact (TRANS (@lem7564945) (@lem7564992)). Qed.
Lemma lem7564994 : term817 = True.
Proof. exact (TRANS (@lem7564936) (@lem7564993)). Qed.
Lemma lem7564995 : True = term817.
Proof. exact (SYM (@lem7564994)). Qed.
Lemma lem7564996 : term817.
Proof. exact (EQ_MP (@lem7564995) (@lem0)). Qed.
Lemma lem7564997 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term887 _97570 _97571.
Proof. exact (conj (@lem7564996) (@lem7564855 _97569 _97570 _97571 h1)). Qed.
Lemma lem7564999 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7565000 (_97570 : int) (_97571 : int) : term888 _97570 _97571.
Proof. exact (@lem7564999 term469 (term569 _97570 _97571)). Qed.
Lemma lem7565001 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term889 _97570 _97571.
Proof. exact (@lem7565000 _97570 _97571 (@lem7564997 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565002 (_97570 : int) (_97571 : int) : (term890 _97570 _97571) = (term569 _97570 _97571).
Proof. exact (@lem1982733 (term569 _97570 _97571)). Qed.
Lemma lem7565003 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7565004 (_97570 : int) (_97571 : int) : (term891 _97570 _97571) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7565003) (@lem7565002 _97570 _97571)). Qed.
Lemma lem7565005 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7565006 (_97570 : int) (_97571 : int) : (term889 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7565004 _97570 _97571) (@lem7565005)). Qed.
Lemma lem7565007 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (EQ_MP (@lem7565006 _97570 _97571) (@lem7565001 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565008 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term892 _97570 _97571.
Proof. exact (conj (@lem7565007 _97569 _97570 _97571 h1) (@lem7564933 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565010 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7565011 (_97570 : int) (_97571 : int) : term893 _97570 _97571.
Proof. exact (@lem7565010 (term569 _97570 _97571) (term587 _97570 _97571)). Qed.
Lemma lem7565012 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term894 _97570 _97571.
Proof. exact (@lem7565011 _97570 _97571 (@lem7565008 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565013 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = (term896 _97570 _97571).
Proof. exact (@lem1982753 (term570 _97570) (real_of_int _97570) (term897 _97571) (term570 _97571)). Qed.
Lemma lem7565014 (_97570 : int) : (term848 _97570) = (term849 _97570).
Proof. exact (@lem1982713 term523 (real_of_int _97570)). Qed.
Lemma lem7565016 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565017 : term469 = term549.
Proof. exact (@lem7565016 term470). Qed.
Lemma lem7565019 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7565020 : term523 = term524.
Proof. exact (@lem7565019 term470). Qed.
Lemma lem7565021 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565022 : term850 = term851.
Proof. exact (MK_COMB (@lem7565021) (@lem7565020)). Qed.
Lemma lem7565023 : term852 = term853.
Proof. exact (MK_COMB (@lem7565022) (@lem7565017)). Qed.
Lemma lem7565024 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7565026 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565027 : term818 = term824.
Proof. exact (@lem7565026 (NUMERAL 0) term470). Qed.
Lemma lem7565028 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565029 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565030 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565029 h1) (fun h1 : term824 = True => @lem7565028)). Qed.
Lemma lem7565031 : term824 = True.
Proof. exact (EQ_MP (@lem7565030) (@lem7565028)). Qed.
Lemma lem7565032 : term818 = True.
Proof. exact (TRANS (@lem7565027) (@lem7565031)). Qed.
Lemma lem7565033 : True = term818.
Proof. exact (SYM (@lem7565032)). Qed.
Lemma lem7565034 : term818.
Proof. exact (EQ_MP (@lem7565033) (@lem0)). Qed.
Lemma lem7565035 : term855.
Proof. exact (@lem7565024 (@lem7565034)). Qed.
Lemma lem7565037 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565038 : term818 = term824.
Proof. exact (@lem7565037 (NUMERAL 0) term470). Qed.
Lemma lem7565039 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565040 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565041 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565040 h1) (fun h1 : term824 = True => @lem7565039)). Qed.
Lemma lem7565042 : term824 = True.
Proof. exact (EQ_MP (@lem7565041) (@lem7565039)). Qed.
Lemma lem7565043 : term818 = True.
Proof. exact (TRANS (@lem7565038) (@lem7565042)). Qed.
Lemma lem7565044 : True = term818.
Proof. exact (SYM (@lem7565043)). Qed.
Lemma lem7565045 : term818.
Proof. exact (EQ_MP (@lem7565044) (@lem0)). Qed.
Lemma lem7565046 : term856.
Proof. exact (@lem7565035 (@lem7565045)). Qed.
Lemma lem7565048 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565049 : term818 = term824.
Proof. exact (@lem7565048 (NUMERAL 0) term470). Qed.
Lemma lem7565050 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565051 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565052 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565051 h1) (fun h1 : term824 = True => @lem7565050)). Qed.
Lemma lem7565053 : term824 = True.
Proof. exact (EQ_MP (@lem7565052) (@lem7565050)). Qed.
Lemma lem7565054 : term818 = True.
Proof. exact (TRANS (@lem7565049) (@lem7565053)). Qed.
Lemma lem7565055 : True = term818.
Proof. exact (SYM (@lem7565054)). Qed.
Lemma lem7565056 : term818.
Proof. exact (EQ_MP (@lem7565055) (@lem0)). Qed.
Lemma lem7565057 : term857.
Proof. exact (@lem7565046 (@lem7565056)). Qed.
Lemma lem7565059 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565060 : term532 = term533.
Proof. exact (@lem7565059 term470 term470). Qed.
Lemma lem7565061 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565062 : term535 = term470.
Proof. exact (EQ_MP (@lem7565061) (@lem940073)). Qed.
Lemma lem7565063 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565064 : term533 = term469.
Proof. exact (MK_COMB (@lem7565063) (@lem7565062)). Qed.
Lemma lem7565065 : term532 = term469.
Proof. exact (TRANS (@lem7565060) (@lem7565064)). Qed.
Lemma lem7565067 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7565068 : term550 = term555.
Proof. exact (@lem7565067 term470 term470). Qed.
Lemma lem7565069 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565070 : term535 = term470.
Proof. exact (EQ_MP (@lem7565069) (@lem940073)). Qed.
Lemma lem7565071 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565072 : term533 = term469.
Proof. exact (MK_COMB (@lem7565071) (@lem7565070)). Qed.
Lemma lem7565073 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7565074 : term555 = term523.
Proof. exact (MK_COMB (@lem7565073) (@lem7565072)). Qed.
Lemma lem7565075 : term550 = term523.
Proof. exact (TRANS (@lem7565068) (@lem7565074)). Qed.
Lemma lem7565076 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565077 : term858 = term850.
Proof. exact (MK_COMB (@lem7565076) (@lem7565075)). Qed.
Lemma lem7565078 : term859 = term852.
Proof. exact (MK_COMB (@lem7565077) (@lem7565065)). Qed.
Lemma lem7565080 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7565081 : term852 = term35.
Proof. exact (@lem7565080 term470). Qed.
Lemma lem7565082 : term859 = term35.
Proof. exact (TRANS (@lem7565078) (@lem7565081)). Qed.
Lemma lem7565083 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565084 : term861 = term218.
Proof. exact (MK_COMB (@lem7565083) (@lem7565082)). Qed.
Lemma lem7565085 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7565086 : term862 = term829.
Proof. exact (MK_COMB (@lem7565084) (@lem7565085)). Qed.
Lemma lem7565088 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565089 : term829 = term35.
Proof. exact (@lem7565088 term470). Qed.
Lemma lem7565090 : term862 = term35.
Proof. exact (TRANS (@lem7565086) (@lem7565089)). Qed.
Lemma lem7565092 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565093 : term532 = term533.
Proof. exact (@lem7565092 term470 term470). Qed.
Lemma lem7565094 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565095 : term535 = term470.
Proof. exact (EQ_MP (@lem7565094) (@lem940073)). Qed.
Lemma lem7565096 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565097 : term533 = term469.
Proof. exact (MK_COMB (@lem7565096) (@lem7565095)). Qed.
Lemma lem7565098 : term532 = term469.
Proof. exact (TRANS (@lem7565093) (@lem7565097)). Qed.
Lemma lem7565099 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7565100 : term863 = term829.
Proof. exact (MK_COMB (@lem7565099) (@lem7565098)). Qed.
Lemma lem7565102 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565103 : term829 = term35.
Proof. exact (@lem7565102 term470). Qed.
Lemma lem7565104 : term863 = term35.
Proof. exact (TRANS (@lem7565100) (@lem7565103)). Qed.
Lemma lem7565105 : term35 = term863.
Proof. exact (SYM (@lem7565104)). Qed.
Lemma lem7565106 : term862 = term863.
Proof. exact (TRANS (@lem7565090) (@lem7565105)). Qed.
Lemma lem7565107 : term853 = term520.
Proof. exact (@lem7565057 (@lem7565106)). Qed.
Lemma lem7565108 : term852 = term520.
Proof. exact (TRANS (@lem7565023) (@lem7565107)). Qed.
Lemma lem7565110 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7565111 : term520 = term35.
Proof. exact (@lem7565110 term35). Qed.
Lemma lem7565112 : term852 = term35.
Proof. exact (TRANS (@lem7565108) (@lem7565111)). Qed.
Lemma lem7565113 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565114 : term864 = term218.
Proof. exact (MK_COMB (@lem7565113) (@lem7565112)). Qed.
Lemma lem7565115 (_97570 : int) : (real_of_int _97570) = (real_of_int _97570).
Proof. exact (eq_refl (real_of_int _97570)). Qed.
Lemma lem7565116 (_97570 : int) : (term849 _97570) = (term865 _97570).
Proof. exact (MK_COMB (@lem7565114) (@lem7565115 _97570)). Qed.
Lemma lem7565117 (_97570 : int) : (term848 _97570) = (term865 _97570).
Proof. exact (TRANS (@lem7565014 _97570) (@lem7565116 _97570)). Qed.
Lemma lem7565118 (_97570 : int) : (term865 _97570) = term35.
Proof. exact (@lem1982719 (real_of_int _97570)). Qed.
Lemma lem7565119 (_97570 : int) : (term848 _97570) = term35.
Proof. exact (TRANS (@lem7565117 _97570) (@lem7565118 _97570)). Qed.
Lemma lem7565120 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565121 (_97570 : int) : (term866 _97570) = term560.
Proof. exact (MK_COMB (@lem7565120) (@lem7565119 _97570)). Qed.
Lemma lem7565122 (_97571 : int) : (term898 _97571) = (term899 _97571).
Proof. exact (@lem1982759 (real_of_int _97571) (term570 _97571) term523). Qed.
Lemma lem7565123 (_97571 : int) : (term900 _97571) = (term849 _97571).
Proof. exact (@lem1982715 term523 (real_of_int _97571)). Qed.
Lemma lem7565125 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565126 : term469 = term549.
Proof. exact (@lem7565125 term470). Qed.
Lemma lem7565128 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7565129 : term523 = term524.
Proof. exact (@lem7565128 term470). Qed.
Lemma lem7565130 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565131 : term850 = term851.
Proof. exact (MK_COMB (@lem7565130) (@lem7565129)). Qed.
Lemma lem7565132 : term852 = term853.
Proof. exact (MK_COMB (@lem7565131) (@lem7565126)). Qed.
Lemma lem7565133 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7565135 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565136 : term818 = term824.
Proof. exact (@lem7565135 (NUMERAL 0) term470). Qed.
Lemma lem7565137 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565138 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565139 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565138 h1) (fun h1 : term824 = True => @lem7565137)). Qed.
Lemma lem7565140 : term824 = True.
Proof. exact (EQ_MP (@lem7565139) (@lem7565137)). Qed.
Lemma lem7565141 : term818 = True.
Proof. exact (TRANS (@lem7565136) (@lem7565140)). Qed.
Lemma lem7565142 : True = term818.
Proof. exact (SYM (@lem7565141)). Qed.
Lemma lem7565143 : term818.
Proof. exact (EQ_MP (@lem7565142) (@lem0)). Qed.
Lemma lem7565144 : term855.
Proof. exact (@lem7565133 (@lem7565143)). Qed.
Lemma lem7565146 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565147 : term818 = term824.
Proof. exact (@lem7565146 (NUMERAL 0) term470). Qed.
Lemma lem7565148 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565149 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565150 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565149 h1) (fun h1 : term824 = True => @lem7565148)). Qed.
Lemma lem7565151 : term824 = True.
Proof. exact (EQ_MP (@lem7565150) (@lem7565148)). Qed.
Lemma lem7565152 : term818 = True.
Proof. exact (TRANS (@lem7565147) (@lem7565151)). Qed.
Lemma lem7565153 : True = term818.
Proof. exact (SYM (@lem7565152)). Qed.
Lemma lem7565154 : term818.
Proof. exact (EQ_MP (@lem7565153) (@lem0)). Qed.
Lemma lem7565155 : term856.
Proof. exact (@lem7565144 (@lem7565154)). Qed.
Lemma lem7565157 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565158 : term818 = term824.
Proof. exact (@lem7565157 (NUMERAL 0) term470). Qed.
Lemma lem7565159 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565160 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565161 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565160 h1) (fun h1 : term824 = True => @lem7565159)). Qed.
Lemma lem7565162 : term824 = True.
Proof. exact (EQ_MP (@lem7565161) (@lem7565159)). Qed.
Lemma lem7565163 : term818 = True.
Proof. exact (TRANS (@lem7565158) (@lem7565162)). Qed.
Lemma lem7565164 : True = term818.
Proof. exact (SYM (@lem7565163)). Qed.
Lemma lem7565165 : term818.
Proof. exact (EQ_MP (@lem7565164) (@lem0)). Qed.
Lemma lem7565166 : term857.
Proof. exact (@lem7565155 (@lem7565165)). Qed.
Lemma lem7565168 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565169 : term532 = term533.
Proof. exact (@lem7565168 term470 term470). Qed.
Lemma lem7565170 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565171 : term535 = term470.
Proof. exact (EQ_MP (@lem7565170) (@lem940073)). Qed.
Lemma lem7565172 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565173 : term533 = term469.
Proof. exact (MK_COMB (@lem7565172) (@lem7565171)). Qed.
Lemma lem7565174 : term532 = term469.
Proof. exact (TRANS (@lem7565169) (@lem7565173)). Qed.
Lemma lem7565176 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7565177 : term550 = term555.
Proof. exact (@lem7565176 term470 term470). Qed.
Lemma lem7565178 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565179 : term535 = term470.
Proof. exact (EQ_MP (@lem7565178) (@lem940073)). Qed.
Lemma lem7565180 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565181 : term533 = term469.
Proof. exact (MK_COMB (@lem7565180) (@lem7565179)). Qed.
Lemma lem7565182 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7565183 : term555 = term523.
Proof. exact (MK_COMB (@lem7565182) (@lem7565181)). Qed.
Lemma lem7565184 : term550 = term523.
Proof. exact (TRANS (@lem7565177) (@lem7565183)). Qed.
Lemma lem7565185 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565186 : term858 = term850.
Proof. exact (MK_COMB (@lem7565185) (@lem7565184)). Qed.
Lemma lem7565187 : term859 = term852.
Proof. exact (MK_COMB (@lem7565186) (@lem7565174)). Qed.
Lemma lem7565189 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7565190 : term852 = term35.
Proof. exact (@lem7565189 term470). Qed.
Lemma lem7565191 : term859 = term35.
Proof. exact (TRANS (@lem7565187) (@lem7565190)). Qed.
Lemma lem7565192 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565193 : term861 = term218.
Proof. exact (MK_COMB (@lem7565192) (@lem7565191)). Qed.
Lemma lem7565194 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7565195 : term862 = term829.
Proof. exact (MK_COMB (@lem7565193) (@lem7565194)). Qed.
Lemma lem7565197 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565198 : term829 = term35.
Proof. exact (@lem7565197 term470). Qed.
Lemma lem7565199 : term862 = term35.
Proof. exact (TRANS (@lem7565195) (@lem7565198)). Qed.
Lemma lem7565201 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565202 : term532 = term533.
Proof. exact (@lem7565201 term470 term470). Qed.
Lemma lem7565203 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565204 : term535 = term470.
Proof. exact (EQ_MP (@lem7565203) (@lem940073)). Qed.
Lemma lem7565205 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565206 : term533 = term469.
Proof. exact (MK_COMB (@lem7565205) (@lem7565204)). Qed.
Lemma lem7565207 : term532 = term469.
Proof. exact (TRANS (@lem7565202) (@lem7565206)). Qed.
Lemma lem7565208 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7565209 : term863 = term829.
Proof. exact (MK_COMB (@lem7565208) (@lem7565207)). Qed.
Lemma lem7565211 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565212 : term829 = term35.
Proof. exact (@lem7565211 term470). Qed.
Lemma lem7565213 : term863 = term35.
Proof. exact (TRANS (@lem7565209) (@lem7565212)). Qed.
Lemma lem7565214 : term35 = term863.
Proof. exact (SYM (@lem7565213)). Qed.
Lemma lem7565215 : term862 = term863.
Proof. exact (TRANS (@lem7565199) (@lem7565214)). Qed.
Lemma lem7565216 : term853 = term520.
Proof. exact (@lem7565166 (@lem7565215)). Qed.
Lemma lem7565217 : term852 = term520.
Proof. exact (TRANS (@lem7565132) (@lem7565216)). Qed.
Lemma lem7565219 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7565220 : term520 = term35.
Proof. exact (@lem7565219 term35). Qed.
Lemma lem7565221 : term852 = term35.
Proof. exact (TRANS (@lem7565217) (@lem7565220)). Qed.
Lemma lem7565222 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565223 : term864 = term218.
Proof. exact (MK_COMB (@lem7565222) (@lem7565221)). Qed.
Lemma lem7565224 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7565225 (_97571 : int) : (term849 _97571) = (term865 _97571).
Proof. exact (MK_COMB (@lem7565223) (@lem7565224 _97571)). Qed.
Lemma lem7565226 (_97571 : int) : (term900 _97571) = (term865 _97571).
Proof. exact (TRANS (@lem7565123 _97571) (@lem7565225 _97571)). Qed.
Lemma lem7565227 (_97571 : int) : (term865 _97571) = term35.
Proof. exact (@lem1982719 (real_of_int _97571)). Qed.
Lemma lem7565228 (_97571 : int) : (term900 _97571) = term35.
Proof. exact (TRANS (@lem7565226 _97571) (@lem7565227 _97571)). Qed.
Lemma lem7565229 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565230 (_97571 : int) : (term901 _97571) = term560.
Proof. exact (MK_COMB (@lem7565229) (@lem7565228 _97571)). Qed.
Lemma lem7565231 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7565232 (_97571 : int) : (term899 _97571) = term867.
Proof. exact (MK_COMB (@lem7565230 _97571) (@lem7565231)). Qed.
Lemma lem7565233 (_97571 : int) : (term898 _97571) = term867.
Proof. exact (TRANS (@lem7565122 _97571) (@lem7565232 _97571)). Qed.
Lemma lem7565234 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7565235 (_97571 : int) : (term898 _97571) = term523.
Proof. exact (TRANS (@lem7565233 _97571) (@lem7565234)). Qed.
Lemma lem7565236 (_97570 : int) (_97571 : int) : (term896 _97570 _97571) = term867.
Proof. exact (MK_COMB (@lem7565121 _97570) (@lem7565235 _97571)). Qed.
Lemma lem7565237 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term867.
Proof. exact (TRANS (@lem7565013 _97570 _97571) (@lem7565236 _97570 _97571)). Qed.
Lemma lem7565238 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7565239 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term523.
Proof. exact (TRANS (@lem7565237 _97570 _97571) (@lem7565238)). Qed.
Lemma lem7565240 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7565241 (_97570 : int) (_97571 : int) : (term902 _97570 _97571) = term869.
Proof. exact (MK_COMB (@lem7565240) (@lem7565239 _97570 _97571)). Qed.
Lemma lem7565242 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7565243 (_97570 : int) (_97571 : int) : (term894 _97570 _97571) = term870.
Proof. exact (MK_COMB (@lem7565241 _97570 _97571) (@lem7565242)). Qed.
Lemma lem7565244 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : term870.
Proof. exact (EQ_MP (@lem7565243 _97570 _97571) (@lem7565012 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565246 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7565247 : term870 = term871.
Proof. exact (@lem7565246 term35 term523). Qed.
Lemma lem7565249 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7565250 : term523 = term524.
Proof. exact (@lem7565249 term470). Qed.
Lemma lem7565252 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565253 : term35 = term520.
Proof. exact (@lem7565252 (NUMERAL 0)). Qed.
Lemma lem7565254 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7565255 : term457 = term872.
Proof. exact (MK_COMB (@lem7565254) (@lem7565253)). Qed.
Lemma lem7565256 : term871 = term873.
Proof. exact (MK_COMB (@lem7565255) (@lem7565250)). Qed.
Lemma lem7565257 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7565259 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565260 : term818 = term824.
Proof. exact (@lem7565259 (NUMERAL 0) term470). Qed.
Lemma lem7565261 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565262 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565263 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565262 h1) (fun h1 : term824 = True => @lem7565261)). Qed.
Lemma lem7565264 : term824 = True.
Proof. exact (EQ_MP (@lem7565263) (@lem7565261)). Qed.
Lemma lem7565265 : term818 = True.
Proof. exact (TRANS (@lem7565260) (@lem7565264)). Qed.
Lemma lem7565266 : True = term818.
Proof. exact (SYM (@lem7565265)). Qed.
Lemma lem7565267 : term818.
Proof. exact (EQ_MP (@lem7565266) (@lem0)). Qed.
Lemma lem7565268 : term875.
Proof. exact (@lem7565257 (@lem7565267)). Qed.
Lemma lem7565270 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565271 : term818 = term824.
Proof. exact (@lem7565270 (NUMERAL 0) term470). Qed.
Lemma lem7565272 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565273 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565274 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565273 h1) (fun h1 : term824 = True => @lem7565272)). Qed.
Lemma lem7565275 : term824 = True.
Proof. exact (EQ_MP (@lem7565274) (@lem7565272)). Qed.
Lemma lem7565276 : term818 = True.
Proof. exact (TRANS (@lem7565271) (@lem7565275)). Qed.
Lemma lem7565277 : True = term818.
Proof. exact (SYM (@lem7565276)). Qed.
Lemma lem7565278 : term818.
Proof. exact (EQ_MP (@lem7565277) (@lem0)). Qed.
Lemma lem7565279 : term873 = term876.
Proof. exact (@lem7565268 (@lem7565278)). Qed.
Lemma lem7565281 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7565282 : term550 = term555.
Proof. exact (@lem7565281 term470 term470). Qed.
Lemma lem7565283 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565284 : term535 = term470.
Proof. exact (EQ_MP (@lem7565283) (@lem940073)). Qed.
Lemma lem7565285 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565286 : term533 = term469.
Proof. exact (MK_COMB (@lem7565285) (@lem7565284)). Qed.
Lemma lem7565287 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7565288 : term555 = term523.
Proof. exact (MK_COMB (@lem7565287) (@lem7565286)). Qed.
Lemma lem7565289 : term550 = term523.
Proof. exact (TRANS (@lem7565282) (@lem7565288)). Qed.
Lemma lem7565291 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565292 : term829 = term35.
Proof. exact (@lem7565291 term470). Qed.
Lemma lem7565293 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7565294 : term877 = term457.
Proof. exact (MK_COMB (@lem7565293) (@lem7565292)). Qed.
Lemma lem7565295 : term876 = term871.
Proof. exact (MK_COMB (@lem7565294) (@lem7565289)). Qed.
Lemma lem7565297 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7565298 : term871 = term880.
Proof. exact (@lem7565297 (NUMERAL 0) term470). Qed.
Lemma lem7565299 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565300 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7565301 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565300 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7565299)). Qed.
Lemma lem7565302 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7565301) (@lem7565299)). Qed.
Lemma lem7565303 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7565304 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7565305 : term881 = (and True).
Proof. exact (MK_COMB (@lem7565304) (@lem7565303)). Qed.
Lemma lem7565306 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7565305) (@lem7565302)). Qed.
Lemma lem7565308 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7565309 : term880 = False.
Proof. exact (TRANS (@lem7565306) (@lem7565308)). Qed.
Lemma lem7565310 : term871 = False.
Proof. exact (TRANS (@lem7565298) (@lem7565309)). Qed.
Lemma lem7565311 : term876 = False.
Proof. exact (TRANS (@lem7565295) (@lem7565310)). Qed.
Lemma lem7565312 : term873 = False.
Proof. exact (TRANS (@lem7565279) (@lem7565311)). Qed.
Lemma lem7565313 : term871 = False.
Proof. exact (TRANS (@lem7565256) (@lem7565312)). Qed.
Lemma lem7565314 : term870 = False.
Proof. exact (TRANS (@lem7565247) (@lem7565313)). Qed.
Lemma lem7565315 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1091 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7565314) (@lem7565244 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565316 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term1095 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7565317 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term1094 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7565316 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565319 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term1093 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7565317 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565321 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term781 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7565319 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565323 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term779 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7565321 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565325 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term726 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7565323 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565326 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (proj1 (@lem7565323 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565327 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (proj2 (@lem7565325 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565332 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7565333 : term817 = term818.
Proof. exact (@lem7565332 term35 term469). Qed.
Lemma lem7565335 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565336 : term469 = term549.
Proof. exact (@lem7565335 term470). Qed.
Lemma lem7565338 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565339 : term35 = term520.
Proof. exact (@lem7565338 (NUMERAL 0)). Qed.
Lemma lem7565340 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565341 : term819 = term820.
Proof. exact (MK_COMB (@lem7565340) (@lem7565339)). Qed.
Lemma lem7565342 : term818 = term821.
Proof. exact (MK_COMB (@lem7565341) (@lem7565336)). Qed.
Lemma lem7565343 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7565345 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565346 : term818 = term824.
Proof. exact (@lem7565345 (NUMERAL 0) term470). Qed.
Lemma lem7565347 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565348 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565349 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565348 h1) (fun h1 : term824 = True => @lem7565347)). Qed.
Lemma lem7565350 : term824 = True.
Proof. exact (EQ_MP (@lem7565349) (@lem7565347)). Qed.
Lemma lem7565351 : term818 = True.
Proof. exact (TRANS (@lem7565346) (@lem7565350)). Qed.
Lemma lem7565352 : True = term818.
Proof. exact (SYM (@lem7565351)). Qed.
Lemma lem7565353 : term818.
Proof. exact (EQ_MP (@lem7565352) (@lem0)). Qed.
Lemma lem7565354 : term826.
Proof. exact (@lem7565343 (@lem7565353)). Qed.
Lemma lem7565356 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565357 : term818 = term824.
Proof. exact (@lem7565356 (NUMERAL 0) term470). Qed.
Lemma lem7565358 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565359 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565360 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565359 h1) (fun h1 : term824 = True => @lem7565358)). Qed.
Lemma lem7565361 : term824 = True.
Proof. exact (EQ_MP (@lem7565360) (@lem7565358)). Qed.
Lemma lem7565362 : term818 = True.
Proof. exact (TRANS (@lem7565357) (@lem7565361)). Qed.
Lemma lem7565363 : True = term818.
Proof. exact (SYM (@lem7565362)). Qed.
Lemma lem7565364 : term818.
Proof. exact (EQ_MP (@lem7565363) (@lem0)). Qed.
Lemma lem7565365 : term821 = term827.
Proof. exact (@lem7565354 (@lem7565364)). Qed.
Lemma lem7565367 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565368 : term532 = term533.
Proof. exact (@lem7565367 term470 term470). Qed.
Lemma lem7565369 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565370 : term535 = term470.
Proof. exact (EQ_MP (@lem7565369) (@lem940073)). Qed.
Lemma lem7565371 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565372 : term533 = term469.
Proof. exact (MK_COMB (@lem7565371) (@lem7565370)). Qed.
Lemma lem7565373 : term532 = term469.
Proof. exact (TRANS (@lem7565368) (@lem7565372)). Qed.
Lemma lem7565375 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565376 : term829 = term35.
Proof. exact (@lem7565375 term470). Qed.
Lemma lem7565377 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565378 : term830 = term819.
Proof. exact (MK_COMB (@lem7565377) (@lem7565376)). Qed.
Lemma lem7565379 : term827 = term818.
Proof. exact (MK_COMB (@lem7565378) (@lem7565373)). Qed.
Lemma lem7565381 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565382 : term818 = term824.
Proof. exact (@lem7565381 (NUMERAL 0) term470). Qed.
Lemma lem7565383 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565384 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565385 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565384 h1) (fun h1 : term824 = True => @lem7565383)). Qed.
Lemma lem7565386 : term824 = True.
Proof. exact (EQ_MP (@lem7565385) (@lem7565383)). Qed.
Lemma lem7565387 : term818 = True.
Proof. exact (TRANS (@lem7565382) (@lem7565386)). Qed.
Lemma lem7565388 : term827 = True.
Proof. exact (TRANS (@lem7565379) (@lem7565387)). Qed.
Lemma lem7565389 : term821 = True.
Proof. exact (TRANS (@lem7565365) (@lem7565388)). Qed.
Lemma lem7565390 : term818 = True.
Proof. exact (TRANS (@lem7565342) (@lem7565389)). Qed.
Lemma lem7565391 : term817 = True.
Proof. exact (TRANS (@lem7565333) (@lem7565390)). Qed.
Lemma lem7565392 : True = term817.
Proof. exact (SYM (@lem7565391)). Qed.
Lemma lem7565393 : term817.
Proof. exact (EQ_MP (@lem7565392) (@lem0)). Qed.
Lemma lem7565394 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term882 _97570 _97571.
Proof. exact (conj (@lem7565393) (@lem7565327 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565396 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7565397 (_97570 : int) (_97571 : int) : term883 _97570 _97571.
Proof. exact (@lem7565396 term469 (term587 _97570 _97571)). Qed.
Lemma lem7565398 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term884 _97570 _97571.
Proof. exact (@lem7565397 _97570 _97571 (@lem7565394 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565399 (_97570 : int) (_97571 : int) : (term885 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982733 (term587 _97570 _97571)). Qed.
Lemma lem7565400 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7565401 (_97570 : int) (_97571 : int) : (term886 _97570 _97571) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7565400) (@lem7565399 _97570 _97571)). Qed.
Lemma lem7565402 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7565403 (_97570 : int) (_97571 : int) : (term884 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7565401 _97570 _97571) (@lem7565402)). Qed.
Lemma lem7565404 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (EQ_MP (@lem7565403 _97570 _97571) (@lem7565398 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565406 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7565407 : term817 = term818.
Proof. exact (@lem7565406 term35 term469). Qed.
Lemma lem7565409 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565410 : term469 = term549.
Proof. exact (@lem7565409 term470). Qed.
Lemma lem7565412 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565413 : term35 = term520.
Proof. exact (@lem7565412 (NUMERAL 0)). Qed.
Lemma lem7565414 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565415 : term819 = term820.
Proof. exact (MK_COMB (@lem7565414) (@lem7565413)). Qed.
Lemma lem7565416 : term818 = term821.
Proof. exact (MK_COMB (@lem7565415) (@lem7565410)). Qed.
Lemma lem7565417 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7565419 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565420 : term818 = term824.
Proof. exact (@lem7565419 (NUMERAL 0) term470). Qed.
Lemma lem7565421 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565422 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565423 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565422 h1) (fun h1 : term824 = True => @lem7565421)). Qed.
Lemma lem7565424 : term824 = True.
Proof. exact (EQ_MP (@lem7565423) (@lem7565421)). Qed.
Lemma lem7565425 : term818 = True.
Proof. exact (TRANS (@lem7565420) (@lem7565424)). Qed.
Lemma lem7565426 : True = term818.
Proof. exact (SYM (@lem7565425)). Qed.
Lemma lem7565427 : term818.
Proof. exact (EQ_MP (@lem7565426) (@lem0)). Qed.
Lemma lem7565428 : term826.
Proof. exact (@lem7565417 (@lem7565427)). Qed.
Lemma lem7565430 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565431 : term818 = term824.
Proof. exact (@lem7565430 (NUMERAL 0) term470). Qed.
Lemma lem7565432 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565433 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565434 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565433 h1) (fun h1 : term824 = True => @lem7565432)). Qed.
Lemma lem7565435 : term824 = True.
Proof. exact (EQ_MP (@lem7565434) (@lem7565432)). Qed.
Lemma lem7565436 : term818 = True.
Proof. exact (TRANS (@lem7565431) (@lem7565435)). Qed.
Lemma lem7565437 : True = term818.
Proof. exact (SYM (@lem7565436)). Qed.
Lemma lem7565438 : term818.
Proof. exact (EQ_MP (@lem7565437) (@lem0)). Qed.
Lemma lem7565439 : term821 = term827.
Proof. exact (@lem7565428 (@lem7565438)). Qed.
Lemma lem7565441 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565442 : term532 = term533.
Proof. exact (@lem7565441 term470 term470). Qed.
Lemma lem7565443 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565444 : term535 = term470.
Proof. exact (EQ_MP (@lem7565443) (@lem940073)). Qed.
Lemma lem7565445 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565446 : term533 = term469.
Proof. exact (MK_COMB (@lem7565445) (@lem7565444)). Qed.
Lemma lem7565447 : term532 = term469.
Proof. exact (TRANS (@lem7565442) (@lem7565446)). Qed.
Lemma lem7565449 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565450 : term829 = term35.
Proof. exact (@lem7565449 term470). Qed.
Lemma lem7565451 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565452 : term830 = term819.
Proof. exact (MK_COMB (@lem7565451) (@lem7565450)). Qed.
Lemma lem7565453 : term827 = term818.
Proof. exact (MK_COMB (@lem7565452) (@lem7565447)). Qed.
Lemma lem7565455 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565456 : term818 = term824.
Proof. exact (@lem7565455 (NUMERAL 0) term470). Qed.
Lemma lem7565457 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565458 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565459 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565458 h1) (fun h1 : term824 = True => @lem7565457)). Qed.
Lemma lem7565460 : term824 = True.
Proof. exact (EQ_MP (@lem7565459) (@lem7565457)). Qed.
Lemma lem7565461 : term818 = True.
Proof. exact (TRANS (@lem7565456) (@lem7565460)). Qed.
Lemma lem7565462 : term827 = True.
Proof. exact (TRANS (@lem7565453) (@lem7565461)). Qed.
Lemma lem7565463 : term821 = True.
Proof. exact (TRANS (@lem7565439) (@lem7565462)). Qed.
Lemma lem7565464 : term818 = True.
Proof. exact (TRANS (@lem7565416) (@lem7565463)). Qed.
Lemma lem7565465 : term817 = True.
Proof. exact (TRANS (@lem7565407) (@lem7565464)). Qed.
Lemma lem7565466 : True = term817.
Proof. exact (SYM (@lem7565465)). Qed.
Lemma lem7565467 : term817.
Proof. exact (EQ_MP (@lem7565466) (@lem0)). Qed.
Lemma lem7565468 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term887 _97570 _97571.
Proof. exact (conj (@lem7565467) (@lem7565326 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565470 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7565471 (_97570 : int) (_97571 : int) : term888 _97570 _97571.
Proof. exact (@lem7565470 term469 (term569 _97570 _97571)). Qed.
Lemma lem7565472 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term889 _97570 _97571.
Proof. exact (@lem7565471 _97570 _97571 (@lem7565468 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565473 (_97570 : int) (_97571 : int) : (term890 _97570 _97571) = (term569 _97570 _97571).
Proof. exact (@lem1982733 (term569 _97570 _97571)). Qed.
Lemma lem7565474 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7565475 (_97570 : int) (_97571 : int) : (term891 _97570 _97571) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7565474) (@lem7565473 _97570 _97571)). Qed.
Lemma lem7565476 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7565477 (_97570 : int) (_97571 : int) : (term889 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7565475 _97570 _97571) (@lem7565476)). Qed.
Lemma lem7565478 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (EQ_MP (@lem7565477 _97570 _97571) (@lem7565472 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565479 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term892 _97570 _97571.
Proof. exact (conj (@lem7565478 _97569 _97570 _97571 h1) (@lem7565404 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565481 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7565482 (_97570 : int) (_97571 : int) : term893 _97570 _97571.
Proof. exact (@lem7565481 (term569 _97570 _97571) (term587 _97570 _97571)). Qed.
Lemma lem7565483 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term894 _97570 _97571.
Proof. exact (@lem7565482 _97570 _97571 (@lem7565479 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565484 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = (term896 _97570 _97571).
Proof. exact (@lem1982753 (term570 _97570) (real_of_int _97570) (term897 _97571) (term570 _97571)). Qed.
Lemma lem7565485 (_97570 : int) : (term848 _97570) = (term849 _97570).
Proof. exact (@lem1982713 term523 (real_of_int _97570)). Qed.
Lemma lem7565487 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565488 : term469 = term549.
Proof. exact (@lem7565487 term470). Qed.
Lemma lem7565490 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7565491 : term523 = term524.
Proof. exact (@lem7565490 term470). Qed.
Lemma lem7565492 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565493 : term850 = term851.
Proof. exact (MK_COMB (@lem7565492) (@lem7565491)). Qed.
Lemma lem7565494 : term852 = term853.
Proof. exact (MK_COMB (@lem7565493) (@lem7565488)). Qed.
Lemma lem7565495 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7565497 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565498 : term818 = term824.
Proof. exact (@lem7565497 (NUMERAL 0) term470). Qed.
Lemma lem7565499 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565500 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565501 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565500 h1) (fun h1 : term824 = True => @lem7565499)). Qed.
Lemma lem7565502 : term824 = True.
Proof. exact (EQ_MP (@lem7565501) (@lem7565499)). Qed.
Lemma lem7565503 : term818 = True.
Proof. exact (TRANS (@lem7565498) (@lem7565502)). Qed.
Lemma lem7565504 : True = term818.
Proof. exact (SYM (@lem7565503)). Qed.
Lemma lem7565505 : term818.
Proof. exact (EQ_MP (@lem7565504) (@lem0)). Qed.
Lemma lem7565506 : term855.
Proof. exact (@lem7565495 (@lem7565505)). Qed.
Lemma lem7565508 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565509 : term818 = term824.
Proof. exact (@lem7565508 (NUMERAL 0) term470). Qed.
Lemma lem7565510 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565511 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565512 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565511 h1) (fun h1 : term824 = True => @lem7565510)). Qed.
Lemma lem7565513 : term824 = True.
Proof. exact (EQ_MP (@lem7565512) (@lem7565510)). Qed.
Lemma lem7565514 : term818 = True.
Proof. exact (TRANS (@lem7565509) (@lem7565513)). Qed.
Lemma lem7565515 : True = term818.
Proof. exact (SYM (@lem7565514)). Qed.
Lemma lem7565516 : term818.
Proof. exact (EQ_MP (@lem7565515) (@lem0)). Qed.
Lemma lem7565517 : term856.
Proof. exact (@lem7565506 (@lem7565516)). Qed.
Lemma lem7565519 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565520 : term818 = term824.
Proof. exact (@lem7565519 (NUMERAL 0) term470). Qed.
Lemma lem7565521 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565522 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565523 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565522 h1) (fun h1 : term824 = True => @lem7565521)). Qed.
Lemma lem7565524 : term824 = True.
Proof. exact (EQ_MP (@lem7565523) (@lem7565521)). Qed.
Lemma lem7565525 : term818 = True.
Proof. exact (TRANS (@lem7565520) (@lem7565524)). Qed.
Lemma lem7565526 : True = term818.
Proof. exact (SYM (@lem7565525)). Qed.
Lemma lem7565527 : term818.
Proof. exact (EQ_MP (@lem7565526) (@lem0)). Qed.
Lemma lem7565528 : term857.
Proof. exact (@lem7565517 (@lem7565527)). Qed.
Lemma lem7565530 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565531 : term532 = term533.
Proof. exact (@lem7565530 term470 term470). Qed.
Lemma lem7565532 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565533 : term535 = term470.
Proof. exact (EQ_MP (@lem7565532) (@lem940073)). Qed.
Lemma lem7565534 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565535 : term533 = term469.
Proof. exact (MK_COMB (@lem7565534) (@lem7565533)). Qed.
Lemma lem7565536 : term532 = term469.
Proof. exact (TRANS (@lem7565531) (@lem7565535)). Qed.
Lemma lem7565538 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7565539 : term550 = term555.
Proof. exact (@lem7565538 term470 term470). Qed.
Lemma lem7565540 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565541 : term535 = term470.
Proof. exact (EQ_MP (@lem7565540) (@lem940073)). Qed.
Lemma lem7565542 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565543 : term533 = term469.
Proof. exact (MK_COMB (@lem7565542) (@lem7565541)). Qed.
Lemma lem7565544 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7565545 : term555 = term523.
Proof. exact (MK_COMB (@lem7565544) (@lem7565543)). Qed.
Lemma lem7565546 : term550 = term523.
Proof. exact (TRANS (@lem7565539) (@lem7565545)). Qed.
Lemma lem7565547 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565548 : term858 = term850.
Proof. exact (MK_COMB (@lem7565547) (@lem7565546)). Qed.
Lemma lem7565549 : term859 = term852.
Proof. exact (MK_COMB (@lem7565548) (@lem7565536)). Qed.
Lemma lem7565551 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7565552 : term852 = term35.
Proof. exact (@lem7565551 term470). Qed.
Lemma lem7565553 : term859 = term35.
Proof. exact (TRANS (@lem7565549) (@lem7565552)). Qed.
Lemma lem7565554 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565555 : term861 = term218.
Proof. exact (MK_COMB (@lem7565554) (@lem7565553)). Qed.
Lemma lem7565556 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7565557 : term862 = term829.
Proof. exact (MK_COMB (@lem7565555) (@lem7565556)). Qed.
Lemma lem7565559 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565560 : term829 = term35.
Proof. exact (@lem7565559 term470). Qed.
Lemma lem7565561 : term862 = term35.
Proof. exact (TRANS (@lem7565557) (@lem7565560)). Qed.
Lemma lem7565563 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565564 : term532 = term533.
Proof. exact (@lem7565563 term470 term470). Qed.
Lemma lem7565565 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565566 : term535 = term470.
Proof. exact (EQ_MP (@lem7565565) (@lem940073)). Qed.
Lemma lem7565567 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565568 : term533 = term469.
Proof. exact (MK_COMB (@lem7565567) (@lem7565566)). Qed.
Lemma lem7565569 : term532 = term469.
Proof. exact (TRANS (@lem7565564) (@lem7565568)). Qed.
Lemma lem7565570 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7565571 : term863 = term829.
Proof. exact (MK_COMB (@lem7565570) (@lem7565569)). Qed.
Lemma lem7565573 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565574 : term829 = term35.
Proof. exact (@lem7565573 term470). Qed.
Lemma lem7565575 : term863 = term35.
Proof. exact (TRANS (@lem7565571) (@lem7565574)). Qed.
Lemma lem7565576 : term35 = term863.
Proof. exact (SYM (@lem7565575)). Qed.
Lemma lem7565577 : term862 = term863.
Proof. exact (TRANS (@lem7565561) (@lem7565576)). Qed.
Lemma lem7565578 : term853 = term520.
Proof. exact (@lem7565528 (@lem7565577)). Qed.
Lemma lem7565579 : term852 = term520.
Proof. exact (TRANS (@lem7565494) (@lem7565578)). Qed.
Lemma lem7565581 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7565582 : term520 = term35.
Proof. exact (@lem7565581 term35). Qed.
Lemma lem7565583 : term852 = term35.
Proof. exact (TRANS (@lem7565579) (@lem7565582)). Qed.
Lemma lem7565584 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565585 : term864 = term218.
Proof. exact (MK_COMB (@lem7565584) (@lem7565583)). Qed.
Lemma lem7565586 (_97570 : int) : (real_of_int _97570) = (real_of_int _97570).
Proof. exact (eq_refl (real_of_int _97570)). Qed.
Lemma lem7565587 (_97570 : int) : (term849 _97570) = (term865 _97570).
Proof. exact (MK_COMB (@lem7565585) (@lem7565586 _97570)). Qed.
Lemma lem7565588 (_97570 : int) : (term848 _97570) = (term865 _97570).
Proof. exact (TRANS (@lem7565485 _97570) (@lem7565587 _97570)). Qed.
Lemma lem7565589 (_97570 : int) : (term865 _97570) = term35.
Proof. exact (@lem1982719 (real_of_int _97570)). Qed.
Lemma lem7565590 (_97570 : int) : (term848 _97570) = term35.
Proof. exact (TRANS (@lem7565588 _97570) (@lem7565589 _97570)). Qed.
Lemma lem7565591 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565592 (_97570 : int) : (term866 _97570) = term560.
Proof. exact (MK_COMB (@lem7565591) (@lem7565590 _97570)). Qed.
Lemma lem7565593 (_97571 : int) : (term898 _97571) = (term899 _97571).
Proof. exact (@lem1982759 (real_of_int _97571) (term570 _97571) term523). Qed.
Lemma lem7565594 (_97571 : int) : (term900 _97571) = (term849 _97571).
Proof. exact (@lem1982715 term523 (real_of_int _97571)). Qed.
Lemma lem7565596 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565597 : term469 = term549.
Proof. exact (@lem7565596 term470). Qed.
Lemma lem7565599 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7565600 : term523 = term524.
Proof. exact (@lem7565599 term470). Qed.
Lemma lem7565601 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565602 : term850 = term851.
Proof. exact (MK_COMB (@lem7565601) (@lem7565600)). Qed.
Lemma lem7565603 : term852 = term853.
Proof. exact (MK_COMB (@lem7565602) (@lem7565597)). Qed.
Lemma lem7565604 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7565606 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565607 : term818 = term824.
Proof. exact (@lem7565606 (NUMERAL 0) term470). Qed.
Lemma lem7565608 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565609 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565610 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565609 h1) (fun h1 : term824 = True => @lem7565608)). Qed.
Lemma lem7565611 : term824 = True.
Proof. exact (EQ_MP (@lem7565610) (@lem7565608)). Qed.
Lemma lem7565612 : term818 = True.
Proof. exact (TRANS (@lem7565607) (@lem7565611)). Qed.
Lemma lem7565613 : True = term818.
Proof. exact (SYM (@lem7565612)). Qed.
Lemma lem7565614 : term818.
Proof. exact (EQ_MP (@lem7565613) (@lem0)). Qed.
Lemma lem7565615 : term855.
Proof. exact (@lem7565604 (@lem7565614)). Qed.
Lemma lem7565617 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565618 : term818 = term824.
Proof. exact (@lem7565617 (NUMERAL 0) term470). Qed.
Lemma lem7565619 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565620 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565621 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565620 h1) (fun h1 : term824 = True => @lem7565619)). Qed.
Lemma lem7565622 : term824 = True.
Proof. exact (EQ_MP (@lem7565621) (@lem7565619)). Qed.
Lemma lem7565623 : term818 = True.
Proof. exact (TRANS (@lem7565618) (@lem7565622)). Qed.
Lemma lem7565624 : True = term818.
Proof. exact (SYM (@lem7565623)). Qed.
Lemma lem7565625 : term818.
Proof. exact (EQ_MP (@lem7565624) (@lem0)). Qed.
Lemma lem7565626 : term856.
Proof. exact (@lem7565615 (@lem7565625)). Qed.
Lemma lem7565628 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565629 : term818 = term824.
Proof. exact (@lem7565628 (NUMERAL 0) term470). Qed.
Lemma lem7565630 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565631 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565632 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565631 h1) (fun h1 : term824 = True => @lem7565630)). Qed.
Lemma lem7565633 : term824 = True.
Proof. exact (EQ_MP (@lem7565632) (@lem7565630)). Qed.
Lemma lem7565634 : term818 = True.
Proof. exact (TRANS (@lem7565629) (@lem7565633)). Qed.
Lemma lem7565635 : True = term818.
Proof. exact (SYM (@lem7565634)). Qed.
Lemma lem7565636 : term818.
Proof. exact (EQ_MP (@lem7565635) (@lem0)). Qed.
Lemma lem7565637 : term857.
Proof. exact (@lem7565626 (@lem7565636)). Qed.
Lemma lem7565639 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565640 : term532 = term533.
Proof. exact (@lem7565639 term470 term470). Qed.
Lemma lem7565641 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565642 : term535 = term470.
Proof. exact (EQ_MP (@lem7565641) (@lem940073)). Qed.
Lemma lem7565643 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565644 : term533 = term469.
Proof. exact (MK_COMB (@lem7565643) (@lem7565642)). Qed.
Lemma lem7565645 : term532 = term469.
Proof. exact (TRANS (@lem7565640) (@lem7565644)). Qed.
Lemma lem7565647 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7565648 : term550 = term555.
Proof. exact (@lem7565647 term470 term470). Qed.
Lemma lem7565649 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565650 : term535 = term470.
Proof. exact (EQ_MP (@lem7565649) (@lem940073)). Qed.
Lemma lem7565651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565652 : term533 = term469.
Proof. exact (MK_COMB (@lem7565651) (@lem7565650)). Qed.
Lemma lem7565653 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7565654 : term555 = term523.
Proof. exact (MK_COMB (@lem7565653) (@lem7565652)). Qed.
Lemma lem7565655 : term550 = term523.
Proof. exact (TRANS (@lem7565648) (@lem7565654)). Qed.
Lemma lem7565656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565657 : term858 = term850.
Proof. exact (MK_COMB (@lem7565656) (@lem7565655)). Qed.
Lemma lem7565658 : term859 = term852.
Proof. exact (MK_COMB (@lem7565657) (@lem7565645)). Qed.
Lemma lem7565660 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7565661 : term852 = term35.
Proof. exact (@lem7565660 term470). Qed.
Lemma lem7565662 : term859 = term35.
Proof. exact (TRANS (@lem7565658) (@lem7565661)). Qed.
Lemma lem7565663 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565664 : term861 = term218.
Proof. exact (MK_COMB (@lem7565663) (@lem7565662)). Qed.
Lemma lem7565665 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7565666 : term862 = term829.
Proof. exact (MK_COMB (@lem7565664) (@lem7565665)). Qed.
Lemma lem7565668 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565669 : term829 = term35.
Proof. exact (@lem7565668 term470). Qed.
Lemma lem7565670 : term862 = term35.
Proof. exact (TRANS (@lem7565666) (@lem7565669)). Qed.
Lemma lem7565672 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565673 : term532 = term533.
Proof. exact (@lem7565672 term470 term470). Qed.
Lemma lem7565674 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565675 : term535 = term470.
Proof. exact (EQ_MP (@lem7565674) (@lem940073)). Qed.
Lemma lem7565676 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565677 : term533 = term469.
Proof. exact (MK_COMB (@lem7565676) (@lem7565675)). Qed.
Lemma lem7565678 : term532 = term469.
Proof. exact (TRANS (@lem7565673) (@lem7565677)). Qed.
Lemma lem7565679 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7565680 : term863 = term829.
Proof. exact (MK_COMB (@lem7565679) (@lem7565678)). Qed.
Lemma lem7565682 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565683 : term829 = term35.
Proof. exact (@lem7565682 term470). Qed.
Lemma lem7565684 : term863 = term35.
Proof. exact (TRANS (@lem7565680) (@lem7565683)). Qed.
Lemma lem7565685 : term35 = term863.
Proof. exact (SYM (@lem7565684)). Qed.
Lemma lem7565686 : term862 = term863.
Proof. exact (TRANS (@lem7565670) (@lem7565685)). Qed.
Lemma lem7565687 : term853 = term520.
Proof. exact (@lem7565637 (@lem7565686)). Qed.
Lemma lem7565688 : term852 = term520.
Proof. exact (TRANS (@lem7565603) (@lem7565687)). Qed.
Lemma lem7565690 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7565691 : term520 = term35.
Proof. exact (@lem7565690 term35). Qed.
Lemma lem7565692 : term852 = term35.
Proof. exact (TRANS (@lem7565688) (@lem7565691)). Qed.
Lemma lem7565693 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7565694 : term864 = term218.
Proof. exact (MK_COMB (@lem7565693) (@lem7565692)). Qed.
Lemma lem7565695 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7565696 (_97571 : int) : (term849 _97571) = (term865 _97571).
Proof. exact (MK_COMB (@lem7565694) (@lem7565695 _97571)). Qed.
Lemma lem7565697 (_97571 : int) : (term900 _97571) = (term865 _97571).
Proof. exact (TRANS (@lem7565594 _97571) (@lem7565696 _97571)). Qed.
Lemma lem7565698 (_97571 : int) : (term865 _97571) = term35.
Proof. exact (@lem1982719 (real_of_int _97571)). Qed.
Lemma lem7565699 (_97571 : int) : (term900 _97571) = term35.
Proof. exact (TRANS (@lem7565697 _97571) (@lem7565698 _97571)). Qed.
Lemma lem7565700 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565701 (_97571 : int) : (term901 _97571) = term560.
Proof. exact (MK_COMB (@lem7565700) (@lem7565699 _97571)). Qed.
Lemma lem7565702 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7565703 (_97571 : int) : (term899 _97571) = term867.
Proof. exact (MK_COMB (@lem7565701 _97571) (@lem7565702)). Qed.
Lemma lem7565704 (_97571 : int) : (term898 _97571) = term867.
Proof. exact (TRANS (@lem7565593 _97571) (@lem7565703 _97571)). Qed.
Lemma lem7565705 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7565706 (_97571 : int) : (term898 _97571) = term523.
Proof. exact (TRANS (@lem7565704 _97571) (@lem7565705)). Qed.
Lemma lem7565707 (_97570 : int) (_97571 : int) : (term896 _97570 _97571) = term867.
Proof. exact (MK_COMB (@lem7565592 _97570) (@lem7565706 _97571)). Qed.
Lemma lem7565708 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term867.
Proof. exact (TRANS (@lem7565484 _97570 _97571) (@lem7565707 _97570 _97571)). Qed.
Lemma lem7565709 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7565710 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term523.
Proof. exact (TRANS (@lem7565708 _97570 _97571) (@lem7565709)). Qed.
Lemma lem7565711 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7565712 (_97570 : int) (_97571 : int) : (term902 _97570 _97571) = term869.
Proof. exact (MK_COMB (@lem7565711) (@lem7565710 _97570 _97571)). Qed.
Lemma lem7565713 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7565714 (_97570 : int) (_97571 : int) : (term894 _97570 _97571) = term870.
Proof. exact (MK_COMB (@lem7565712 _97570 _97571) (@lem7565713)). Qed.
Lemma lem7565715 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : term870.
Proof. exact (EQ_MP (@lem7565714 _97570 _97571) (@lem7565483 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565717 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7565718 : term870 = term871.
Proof. exact (@lem7565717 term35 term523). Qed.
Lemma lem7565720 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7565721 : term523 = term524.
Proof. exact (@lem7565720 term470). Qed.
Lemma lem7565723 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565724 : term35 = term520.
Proof. exact (@lem7565723 (NUMERAL 0)). Qed.
Lemma lem7565725 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7565726 : term457 = term872.
Proof. exact (MK_COMB (@lem7565725) (@lem7565724)). Qed.
Lemma lem7565727 : term871 = term873.
Proof. exact (MK_COMB (@lem7565726) (@lem7565721)). Qed.
Lemma lem7565728 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7565730 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565731 : term818 = term824.
Proof. exact (@lem7565730 (NUMERAL 0) term470). Qed.
Lemma lem7565732 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565733 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565734 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565733 h1) (fun h1 : term824 = True => @lem7565732)). Qed.
Lemma lem7565735 : term824 = True.
Proof. exact (EQ_MP (@lem7565734) (@lem7565732)). Qed.
Lemma lem7565736 : term818 = True.
Proof. exact (TRANS (@lem7565731) (@lem7565735)). Qed.
Lemma lem7565737 : True = term818.
Proof. exact (SYM (@lem7565736)). Qed.
Lemma lem7565738 : term818.
Proof. exact (EQ_MP (@lem7565737) (@lem0)). Qed.
Lemma lem7565739 : term875.
Proof. exact (@lem7565728 (@lem7565738)). Qed.
Lemma lem7565741 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565742 : term818 = term824.
Proof. exact (@lem7565741 (NUMERAL 0) term470). Qed.
Lemma lem7565743 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565744 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565745 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565744 h1) (fun h1 : term824 = True => @lem7565743)). Qed.
Lemma lem7565746 : term824 = True.
Proof. exact (EQ_MP (@lem7565745) (@lem7565743)). Qed.
Lemma lem7565747 : term818 = True.
Proof. exact (TRANS (@lem7565742) (@lem7565746)). Qed.
Lemma lem7565748 : True = term818.
Proof. exact (SYM (@lem7565747)). Qed.
Lemma lem7565749 : term818.
Proof. exact (EQ_MP (@lem7565748) (@lem0)). Qed.
Lemma lem7565750 : term873 = term876.
Proof. exact (@lem7565739 (@lem7565749)). Qed.
Lemma lem7565752 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7565753 : term550 = term555.
Proof. exact (@lem7565752 term470 term470). Qed.
Lemma lem7565754 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565755 : term535 = term470.
Proof. exact (EQ_MP (@lem7565754) (@lem940073)). Qed.
Lemma lem7565756 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565757 : term533 = term469.
Proof. exact (MK_COMB (@lem7565756) (@lem7565755)). Qed.
Lemma lem7565758 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7565759 : term555 = term523.
Proof. exact (MK_COMB (@lem7565758) (@lem7565757)). Qed.
Lemma lem7565760 : term550 = term523.
Proof. exact (TRANS (@lem7565753) (@lem7565759)). Qed.
Lemma lem7565762 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565763 : term829 = term35.
Proof. exact (@lem7565762 term470). Qed.
Lemma lem7565764 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7565765 : term877 = term457.
Proof. exact (MK_COMB (@lem7565764) (@lem7565763)). Qed.
Lemma lem7565766 : term876 = term871.
Proof. exact (MK_COMB (@lem7565765) (@lem7565760)). Qed.
Lemma lem7565768 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7565769 : term871 = term880.
Proof. exact (@lem7565768 (NUMERAL 0) term470). Qed.
Lemma lem7565770 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565771 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7565772 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565771 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7565770)). Qed.
Lemma lem7565773 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7565772) (@lem7565770)). Qed.
Lemma lem7565774 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7565775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7565776 : term881 = (and True).
Proof. exact (MK_COMB (@lem7565775) (@lem7565774)). Qed.
Lemma lem7565777 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7565776) (@lem7565773)). Qed.
Lemma lem7565779 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7565780 : term880 = False.
Proof. exact (TRANS (@lem7565777) (@lem7565779)). Qed.
Lemma lem7565781 : term871 = False.
Proof. exact (TRANS (@lem7565769) (@lem7565780)). Qed.
Lemma lem7565782 : term876 = False.
Proof. exact (TRANS (@lem7565766) (@lem7565781)). Qed.
Lemma lem7565783 : term873 = False.
Proof. exact (TRANS (@lem7565750) (@lem7565782)). Qed.
Lemma lem7565784 : term871 = False.
Proof. exact (TRANS (@lem7565727) (@lem7565783)). Qed.
Lemma lem7565785 : term870 = False.
Proof. exact (TRANS (@lem7565718) (@lem7565784)). Qed.
Lemma lem7565786 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1095 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7565785) (@lem7565715 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565787 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1097 _97569 _97570 _97571) : False.
Proof. exact (or_elim (@lem7564844 _97569 _97570 _97571 h1) (fun h0 : term1091 _97569 _97570 _97571 => @lem7565315 _97569 _97570 _97571 h0) (fun h0 : term1095 _97569 _97570 _97571 => @lem7565786 _97569 _97570 _97571 h0)). Qed.
Lemma lem7565788 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1100 _97569 _97570 _97571) : False.
Proof. exact (or_elim (@lem7564125 _97569 _97570 _97571 h1) (fun h0 : term1071 _97569 _97570 _97571 => @lem7564843 _97569 _97570 _97571 h0) (fun h0 : term1097 _97569 _97570 _97571 => @lem7565787 _97569 _97570 _97571 h0)). Qed.
Lemma lem7565789 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1109 _97569 _97570 _97571) : term1109 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7565790 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1107 _97569 _97570 _97571) : term1107 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7565791 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term1112 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7565792 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term1034 _97570 _97571.
Proof. exact (proj2 (@lem7565791 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565794 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term653 _97570 _97571.
Proof. exact (proj2 (@lem7565792 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565796 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term634 _97570 _97571.
Proof. exact (proj2 (@lem7565794 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565798 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term564 _97571.
Proof. exact (proj2 (@lem7565796 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565799 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term595 _97570 _97571.
Proof. exact (proj1 (@lem7565796 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565801 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term543 _97571.
Proof. exact (proj1 (@lem7565799 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565803 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7565804 : term817 = term818.
Proof. exact (@lem7565803 term35 term469). Qed.
Lemma lem7565806 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565807 : term469 = term549.
Proof. exact (@lem7565806 term470). Qed.
Lemma lem7565809 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565810 : term35 = term520.
Proof. exact (@lem7565809 (NUMERAL 0)). Qed.
Lemma lem7565811 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565812 : term819 = term820.
Proof. exact (MK_COMB (@lem7565811) (@lem7565810)). Qed.
Lemma lem7565813 : term818 = term821.
Proof. exact (MK_COMB (@lem7565812) (@lem7565807)). Qed.
Lemma lem7565814 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7565816 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565817 : term818 = term824.
Proof. exact (@lem7565816 (NUMERAL 0) term470). Qed.
Lemma lem7565818 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565819 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565820 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565819 h1) (fun h1 : term824 = True => @lem7565818)). Qed.
Lemma lem7565821 : term824 = True.
Proof. exact (EQ_MP (@lem7565820) (@lem7565818)). Qed.
Lemma lem7565822 : term818 = True.
Proof. exact (TRANS (@lem7565817) (@lem7565821)). Qed.
Lemma lem7565823 : True = term818.
Proof. exact (SYM (@lem7565822)). Qed.
Lemma lem7565824 : term818.
Proof. exact (EQ_MP (@lem7565823) (@lem0)). Qed.
Lemma lem7565825 : term826.
Proof. exact (@lem7565814 (@lem7565824)). Qed.
Lemma lem7565827 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565828 : term818 = term824.
Proof. exact (@lem7565827 (NUMERAL 0) term470). Qed.
Lemma lem7565829 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565830 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565831 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565830 h1) (fun h1 : term824 = True => @lem7565829)). Qed.
Lemma lem7565832 : term824 = True.
Proof. exact (EQ_MP (@lem7565831) (@lem7565829)). Qed.
Lemma lem7565833 : term818 = True.
Proof. exact (TRANS (@lem7565828) (@lem7565832)). Qed.
Lemma lem7565834 : True = term818.
Proof. exact (SYM (@lem7565833)). Qed.
Lemma lem7565835 : term818.
Proof. exact (EQ_MP (@lem7565834) (@lem0)). Qed.
Lemma lem7565836 : term821 = term827.
Proof. exact (@lem7565825 (@lem7565835)). Qed.
Lemma lem7565838 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565839 : term532 = term533.
Proof. exact (@lem7565838 term470 term470). Qed.
Lemma lem7565840 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565841 : term535 = term470.
Proof. exact (EQ_MP (@lem7565840) (@lem940073)). Qed.
Lemma lem7565842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565843 : term533 = term469.
Proof. exact (MK_COMB (@lem7565842) (@lem7565841)). Qed.
Lemma lem7565844 : term532 = term469.
Proof. exact (TRANS (@lem7565839) (@lem7565843)). Qed.
Lemma lem7565846 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565847 : term829 = term35.
Proof. exact (@lem7565846 term470). Qed.
Lemma lem7565848 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565849 : term830 = term819.
Proof. exact (MK_COMB (@lem7565848) (@lem7565847)). Qed.
Lemma lem7565850 : term827 = term818.
Proof. exact (MK_COMB (@lem7565849) (@lem7565844)). Qed.
Lemma lem7565852 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565853 : term818 = term824.
Proof. exact (@lem7565852 (NUMERAL 0) term470). Qed.
Lemma lem7565854 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565855 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565856 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565855 h1) (fun h1 : term824 = True => @lem7565854)). Qed.
Lemma lem7565857 : term824 = True.
Proof. exact (EQ_MP (@lem7565856) (@lem7565854)). Qed.
Lemma lem7565858 : term818 = True.
Proof. exact (TRANS (@lem7565853) (@lem7565857)). Qed.
Lemma lem7565859 : term827 = True.
Proof. exact (TRANS (@lem7565850) (@lem7565858)). Qed.
Lemma lem7565860 : term821 = True.
Proof. exact (TRANS (@lem7565836) (@lem7565859)). Qed.
Lemma lem7565861 : term818 = True.
Proof. exact (TRANS (@lem7565813) (@lem7565860)). Qed.
Lemma lem7565862 : term817 = True.
Proof. exact (TRANS (@lem7565804) (@lem7565861)). Qed.
Lemma lem7565863 : True = term817.
Proof. exact (SYM (@lem7565862)). Qed.
Lemma lem7565864 : term817.
Proof. exact (EQ_MP (@lem7565863) (@lem0)). Qed.
Lemma lem7565865 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term831 _97571.
Proof. exact (conj (@lem7565864) (@lem7565801 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565867 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7565868 (_97571 : int) : term833 _97571.
Proof. exact (@lem7565867 term469 (real_of_int _97571)). Qed.
Lemma lem7565869 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term834 _97571.
Proof. exact (@lem7565868 _97571 (@lem7565865 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565870 (_97571 : int) : (term835 _97571) = (real_of_int _97571).
Proof. exact (@lem1982733 (real_of_int _97571)). Qed.
Lemma lem7565871 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7565872 (_97571 : int) : (term836 _97571) = (term542 _97571).
Proof. exact (MK_COMB (@lem7565871) (@lem7565870 _97571)). Qed.
Lemma lem7565873 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7565874 (_97571 : int) : (term834 _97571) = (term543 _97571).
Proof. exact (MK_COMB (@lem7565872 _97571) (@lem7565873)). Qed.
Lemma lem7565875 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term543 _97571.
Proof. exact (EQ_MP (@lem7565874 _97571) (@lem7565869 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565877 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7565878 : term817 = term818.
Proof. exact (@lem7565877 term35 term469). Qed.
Lemma lem7565880 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565881 : term469 = term549.
Proof. exact (@lem7565880 term470). Qed.
Lemma lem7565883 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565884 : term35 = term520.
Proof. exact (@lem7565883 (NUMERAL 0)). Qed.
Lemma lem7565885 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565886 : term819 = term820.
Proof. exact (MK_COMB (@lem7565885) (@lem7565884)). Qed.
Lemma lem7565887 : term818 = term821.
Proof. exact (MK_COMB (@lem7565886) (@lem7565881)). Qed.
Lemma lem7565888 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7565890 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565891 : term818 = term824.
Proof. exact (@lem7565890 (NUMERAL 0) term470). Qed.
Lemma lem7565892 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565893 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565894 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565893 h1) (fun h1 : term824 = True => @lem7565892)). Qed.
Lemma lem7565895 : term824 = True.
Proof. exact (EQ_MP (@lem7565894) (@lem7565892)). Qed.
Lemma lem7565896 : term818 = True.
Proof. exact (TRANS (@lem7565891) (@lem7565895)). Qed.
Lemma lem7565897 : True = term818.
Proof. exact (SYM (@lem7565896)). Qed.
Lemma lem7565898 : term818.
Proof. exact (EQ_MP (@lem7565897) (@lem0)). Qed.
Lemma lem7565899 : term826.
Proof. exact (@lem7565888 (@lem7565898)). Qed.
Lemma lem7565901 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565902 : term818 = term824.
Proof. exact (@lem7565901 (NUMERAL 0) term470). Qed.
Lemma lem7565903 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565904 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565905 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565904 h1) (fun h1 : term824 = True => @lem7565903)). Qed.
Lemma lem7565906 : term824 = True.
Proof. exact (EQ_MP (@lem7565905) (@lem7565903)). Qed.
Lemma lem7565907 : term818 = True.
Proof. exact (TRANS (@lem7565902) (@lem7565906)). Qed.
Lemma lem7565908 : True = term818.
Proof. exact (SYM (@lem7565907)). Qed.
Lemma lem7565909 : term818.
Proof. exact (EQ_MP (@lem7565908) (@lem0)). Qed.
Lemma lem7565910 : term821 = term827.
Proof. exact (@lem7565899 (@lem7565909)). Qed.
Lemma lem7565912 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7565913 : term532 = term533.
Proof. exact (@lem7565912 term470 term470). Qed.
Lemma lem7565914 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7565915 : term535 = term470.
Proof. exact (EQ_MP (@lem7565914) (@lem940073)). Qed.
Lemma lem7565916 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7565917 : term533 = term469.
Proof. exact (MK_COMB (@lem7565916) (@lem7565915)). Qed.
Lemma lem7565918 : term532 = term469.
Proof. exact (TRANS (@lem7565913) (@lem7565917)). Qed.
Lemma lem7565920 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7565921 : term829 = term35.
Proof. exact (@lem7565920 term470). Qed.
Lemma lem7565922 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7565923 : term830 = term819.
Proof. exact (MK_COMB (@lem7565922) (@lem7565921)). Qed.
Lemma lem7565924 : term827 = term818.
Proof. exact (MK_COMB (@lem7565923) (@lem7565918)). Qed.
Lemma lem7565926 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565927 : term818 = term824.
Proof. exact (@lem7565926 (NUMERAL 0) term470). Qed.
Lemma lem7565928 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565929 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565930 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565929 h1) (fun h1 : term824 = True => @lem7565928)). Qed.
Lemma lem7565931 : term824 = True.
Proof. exact (EQ_MP (@lem7565930) (@lem7565928)). Qed.
Lemma lem7565932 : term818 = True.
Proof. exact (TRANS (@lem7565927) (@lem7565931)). Qed.
Lemma lem7565933 : term827 = True.
Proof. exact (TRANS (@lem7565924) (@lem7565932)). Qed.
Lemma lem7565934 : term821 = True.
Proof. exact (TRANS (@lem7565910) (@lem7565933)). Qed.
Lemma lem7565935 : term818 = True.
Proof. exact (TRANS (@lem7565887) (@lem7565934)). Qed.
Lemma lem7565936 : term817 = True.
Proof. exact (TRANS (@lem7565878) (@lem7565935)). Qed.
Lemma lem7565937 : True = term817.
Proof. exact (SYM (@lem7565936)). Qed.
Lemma lem7565938 : term817.
Proof. exact (EQ_MP (@lem7565937) (@lem0)). Qed.
Lemma lem7565939 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term837 _97571.
Proof. exact (conj (@lem7565938) (@lem7565798 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565941 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7565942 (_97571 : int) : term838 _97571.
Proof. exact (@lem7565941 term469 (term559 _97571)). Qed.
Lemma lem7565943 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term839 _97571.
Proof. exact (@lem7565942 _97571 (@lem7565939 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565944 (_97571 : int) : (term840 _97571) = (term559 _97571).
Proof. exact (@lem1982733 (term559 _97571)). Qed.
Lemma lem7565945 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7565946 (_97571 : int) : (term841 _97571) = (term563 _97571).
Proof. exact (MK_COMB (@lem7565945) (@lem7565944 _97571)). Qed.
Lemma lem7565947 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7565948 (_97571 : int) : (term839 _97571) = (term564 _97571).
Proof. exact (MK_COMB (@lem7565946 _97571) (@lem7565947)). Qed.
Lemma lem7565949 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term564 _97571.
Proof. exact (EQ_MP (@lem7565948 _97571) (@lem7565943 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565950 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term842 _97571.
Proof. exact (conj (@lem7565949 _97569 _97570 _97571 h1) (@lem7565875 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565952 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7565953 (_97571 : int) : term844 _97571.
Proof. exact (@lem7565952 (term559 _97571) (real_of_int _97571)). Qed.
Lemma lem7565954 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term845 _97571.
Proof. exact (@lem7565953 _97571 (@lem7565950 _97569 _97570 _97571 h1)). Qed.
Lemma lem7565955 (_97571 : int) : (term846 _97571) = (term847 _97571).
Proof. exact (@lem1982759 (term570 _97571) (real_of_int _97571) term523). Qed.
Lemma lem7565956 (_97571 : int) : (term848 _97571) = (term849 _97571).
Proof. exact (@lem1982713 term523 (real_of_int _97571)). Qed.
Lemma lem7565958 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7565959 : term469 = term549.
Proof. exact (@lem7565958 term470). Qed.
Lemma lem7565961 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7565962 : term523 = term524.
Proof. exact (@lem7565961 term470). Qed.
Lemma lem7565963 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7565964 : term850 = term851.
Proof. exact (MK_COMB (@lem7565963) (@lem7565962)). Qed.
Lemma lem7565965 : term852 = term853.
Proof. exact (MK_COMB (@lem7565964) (@lem7565959)). Qed.
Lemma lem7565966 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7565968 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565969 : term818 = term824.
Proof. exact (@lem7565968 (NUMERAL 0) term470). Qed.
Lemma lem7565970 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565971 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565972 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565971 h1) (fun h1 : term824 = True => @lem7565970)). Qed.
Lemma lem7565973 : term824 = True.
Proof. exact (EQ_MP (@lem7565972) (@lem7565970)). Qed.
Lemma lem7565974 : term818 = True.
Proof. exact (TRANS (@lem7565969) (@lem7565973)). Qed.
Lemma lem7565975 : True = term818.
Proof. exact (SYM (@lem7565974)). Qed.
Lemma lem7565976 : term818.
Proof. exact (EQ_MP (@lem7565975) (@lem0)). Qed.
Lemma lem7565977 : term855.
Proof. exact (@lem7565966 (@lem7565976)). Qed.
Lemma lem7565979 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565980 : term818 = term824.
Proof. exact (@lem7565979 (NUMERAL 0) term470). Qed.
Lemma lem7565981 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565982 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565983 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565982 h1) (fun h1 : term824 = True => @lem7565981)). Qed.
Lemma lem7565984 : term824 = True.
Proof. exact (EQ_MP (@lem7565983) (@lem7565981)). Qed.
Lemma lem7565985 : term818 = True.
Proof. exact (TRANS (@lem7565980) (@lem7565984)). Qed.
Lemma lem7565986 : True = term818.
Proof. exact (SYM (@lem7565985)). Qed.
Lemma lem7565987 : term818.
Proof. exact (EQ_MP (@lem7565986) (@lem0)). Qed.
Lemma lem7565988 : term856.
Proof. exact (@lem7565977 (@lem7565987)). Qed.
Lemma lem7565990 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7565991 : term818 = term824.
Proof. exact (@lem7565990 (NUMERAL 0) term470). Qed.
Lemma lem7565992 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7565993 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7565994 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7565993 h1) (fun h1 : term824 = True => @lem7565992)). Qed.
Lemma lem7565995 : term824 = True.
Proof. exact (EQ_MP (@lem7565994) (@lem7565992)). Qed.
Lemma lem7565996 : term818 = True.
Proof. exact (TRANS (@lem7565991) (@lem7565995)). Qed.
Lemma lem7565997 : True = term818.
Proof. exact (SYM (@lem7565996)). Qed.
Lemma lem7565998 : term818.
Proof. exact (EQ_MP (@lem7565997) (@lem0)). Qed.
Lemma lem7565999 : term857.
Proof. exact (@lem7565988 (@lem7565998)). Qed.
Lemma lem7566001 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566002 : term532 = term533.
Proof. exact (@lem7566001 term470 term470). Qed.
Lemma lem7566003 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566004 : term535 = term470.
Proof. exact (EQ_MP (@lem7566003) (@lem940073)). Qed.
Lemma lem7566005 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566006 : term533 = term469.
Proof. exact (MK_COMB (@lem7566005) (@lem7566004)). Qed.
Lemma lem7566007 : term532 = term469.
Proof. exact (TRANS (@lem7566002) (@lem7566006)). Qed.
Lemma lem7566009 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7566010 : term550 = term555.
Proof. exact (@lem7566009 term470 term470). Qed.
Lemma lem7566011 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566012 : term535 = term470.
Proof. exact (EQ_MP (@lem7566011) (@lem940073)). Qed.
Lemma lem7566013 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566014 : term533 = term469.
Proof. exact (MK_COMB (@lem7566013) (@lem7566012)). Qed.
Lemma lem7566015 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7566016 : term555 = term523.
Proof. exact (MK_COMB (@lem7566015) (@lem7566014)). Qed.
Lemma lem7566017 : term550 = term523.
Proof. exact (TRANS (@lem7566010) (@lem7566016)). Qed.
Lemma lem7566018 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566019 : term858 = term850.
Proof. exact (MK_COMB (@lem7566018) (@lem7566017)). Qed.
Lemma lem7566020 : term859 = term852.
Proof. exact (MK_COMB (@lem7566019) (@lem7566007)). Qed.
Lemma lem7566022 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7566023 : term852 = term35.
Proof. exact (@lem7566022 term470). Qed.
Lemma lem7566024 : term859 = term35.
Proof. exact (TRANS (@lem7566020) (@lem7566023)). Qed.
Lemma lem7566025 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566026 : term861 = term218.
Proof. exact (MK_COMB (@lem7566025) (@lem7566024)). Qed.
Lemma lem7566027 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7566028 : term862 = term829.
Proof. exact (MK_COMB (@lem7566026) (@lem7566027)). Qed.
Lemma lem7566030 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566031 : term829 = term35.
Proof. exact (@lem7566030 term470). Qed.
Lemma lem7566032 : term862 = term35.
Proof. exact (TRANS (@lem7566028) (@lem7566031)). Qed.
Lemma lem7566034 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566035 : term532 = term533.
Proof. exact (@lem7566034 term470 term470). Qed.
Lemma lem7566036 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566037 : term535 = term470.
Proof. exact (EQ_MP (@lem7566036) (@lem940073)). Qed.
Lemma lem7566038 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566039 : term533 = term469.
Proof. exact (MK_COMB (@lem7566038) (@lem7566037)). Qed.
Lemma lem7566040 : term532 = term469.
Proof. exact (TRANS (@lem7566035) (@lem7566039)). Qed.
Lemma lem7566041 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7566042 : term863 = term829.
Proof. exact (MK_COMB (@lem7566041) (@lem7566040)). Qed.
Lemma lem7566044 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566045 : term829 = term35.
Proof. exact (@lem7566044 term470). Qed.
Lemma lem7566046 : term863 = term35.
Proof. exact (TRANS (@lem7566042) (@lem7566045)). Qed.
Lemma lem7566047 : term35 = term863.
Proof. exact (SYM (@lem7566046)). Qed.
Lemma lem7566048 : term862 = term863.
Proof. exact (TRANS (@lem7566032) (@lem7566047)). Qed.
Lemma lem7566049 : term853 = term520.
Proof. exact (@lem7565999 (@lem7566048)). Qed.
Lemma lem7566050 : term852 = term520.
Proof. exact (TRANS (@lem7565965) (@lem7566049)). Qed.
Lemma lem7566052 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7566053 : term520 = term35.
Proof. exact (@lem7566052 term35). Qed.
Lemma lem7566054 : term852 = term35.
Proof. exact (TRANS (@lem7566050) (@lem7566053)). Qed.
Lemma lem7566055 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566056 : term864 = term218.
Proof. exact (MK_COMB (@lem7566055) (@lem7566054)). Qed.
Lemma lem7566057 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7566058 (_97571 : int) : (term849 _97571) = (term865 _97571).
Proof. exact (MK_COMB (@lem7566056) (@lem7566057 _97571)). Qed.
Lemma lem7566059 (_97571 : int) : (term848 _97571) = (term865 _97571).
Proof. exact (TRANS (@lem7565956 _97571) (@lem7566058 _97571)). Qed.
Lemma lem7566060 (_97571 : int) : (term865 _97571) = term35.
Proof. exact (@lem1982719 (real_of_int _97571)). Qed.
Lemma lem7566061 (_97571 : int) : (term848 _97571) = term35.
Proof. exact (TRANS (@lem7566059 _97571) (@lem7566060 _97571)). Qed.
Lemma lem7566062 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566063 (_97571 : int) : (term866 _97571) = term560.
Proof. exact (MK_COMB (@lem7566062) (@lem7566061 _97571)). Qed.
Lemma lem7566064 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7566065 (_97571 : int) : (term847 _97571) = term867.
Proof. exact (MK_COMB (@lem7566063 _97571) (@lem7566064)). Qed.
Lemma lem7566066 (_97571 : int) : (term846 _97571) = term867.
Proof. exact (TRANS (@lem7565955 _97571) (@lem7566065 _97571)). Qed.
Lemma lem7566067 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7566068 (_97571 : int) : (term846 _97571) = term523.
Proof. exact (TRANS (@lem7566066 _97571) (@lem7566067)). Qed.
Lemma lem7566069 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7566070 (_97571 : int) : (term868 _97571) = term869.
Proof. exact (MK_COMB (@lem7566069) (@lem7566068 _97571)). Qed.
Lemma lem7566071 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7566072 (_97571 : int) : (term845 _97571) = term870.
Proof. exact (MK_COMB (@lem7566070 _97571) (@lem7566071)). Qed.
Lemma lem7566073 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : term870.
Proof. exact (EQ_MP (@lem7566072 _97571) (@lem7565954 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566075 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7566076 : term870 = term871.
Proof. exact (@lem7566075 term35 term523). Qed.
Lemma lem7566078 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7566079 : term523 = term524.
Proof. exact (@lem7566078 term470). Qed.
Lemma lem7566081 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566082 : term35 = term520.
Proof. exact (@lem7566081 (NUMERAL 0)). Qed.
Lemma lem7566083 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7566084 : term457 = term872.
Proof. exact (MK_COMB (@lem7566083) (@lem7566082)). Qed.
Lemma lem7566085 : term871 = term873.
Proof. exact (MK_COMB (@lem7566084) (@lem7566079)). Qed.
Lemma lem7566086 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7566088 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566089 : term818 = term824.
Proof. exact (@lem7566088 (NUMERAL 0) term470). Qed.
Lemma lem7566090 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566091 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566092 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566091 h1) (fun h1 : term824 = True => @lem7566090)). Qed.
Lemma lem7566093 : term824 = True.
Proof. exact (EQ_MP (@lem7566092) (@lem7566090)). Qed.
Lemma lem7566094 : term818 = True.
Proof. exact (TRANS (@lem7566089) (@lem7566093)). Qed.
Lemma lem7566095 : True = term818.
Proof. exact (SYM (@lem7566094)). Qed.
Lemma lem7566096 : term818.
Proof. exact (EQ_MP (@lem7566095) (@lem0)). Qed.
Lemma lem7566097 : term875.
Proof. exact (@lem7566086 (@lem7566096)). Qed.
Lemma lem7566099 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566100 : term818 = term824.
Proof. exact (@lem7566099 (NUMERAL 0) term470). Qed.
Lemma lem7566101 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566102 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566103 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566102 h1) (fun h1 : term824 = True => @lem7566101)). Qed.
Lemma lem7566104 : term824 = True.
Proof. exact (EQ_MP (@lem7566103) (@lem7566101)). Qed.
Lemma lem7566105 : term818 = True.
Proof. exact (TRANS (@lem7566100) (@lem7566104)). Qed.
Lemma lem7566106 : True = term818.
Proof. exact (SYM (@lem7566105)). Qed.
Lemma lem7566107 : term818.
Proof. exact (EQ_MP (@lem7566106) (@lem0)). Qed.
Lemma lem7566108 : term873 = term876.
Proof. exact (@lem7566097 (@lem7566107)). Qed.
Lemma lem7566110 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7566111 : term550 = term555.
Proof. exact (@lem7566110 term470 term470). Qed.
Lemma lem7566112 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566113 : term535 = term470.
Proof. exact (EQ_MP (@lem7566112) (@lem940073)). Qed.
Lemma lem7566114 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566115 : term533 = term469.
Proof. exact (MK_COMB (@lem7566114) (@lem7566113)). Qed.
Lemma lem7566116 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7566117 : term555 = term523.
Proof. exact (MK_COMB (@lem7566116) (@lem7566115)). Qed.
Lemma lem7566118 : term550 = term523.
Proof. exact (TRANS (@lem7566111) (@lem7566117)). Qed.
Lemma lem7566120 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566121 : term829 = term35.
Proof. exact (@lem7566120 term470). Qed.
Lemma lem7566122 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7566123 : term877 = term457.
Proof. exact (MK_COMB (@lem7566122) (@lem7566121)). Qed.
Lemma lem7566124 : term876 = term871.
Proof. exact (MK_COMB (@lem7566123) (@lem7566118)). Qed.
Lemma lem7566126 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7566127 : term871 = term880.
Proof. exact (@lem7566126 (NUMERAL 0) term470). Qed.
Lemma lem7566128 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566129 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7566130 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566129 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7566128)). Qed.
Lemma lem7566131 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7566130) (@lem7566128)). Qed.
Lemma lem7566132 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7566133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7566134 : term881 = (and True).
Proof. exact (MK_COMB (@lem7566133) (@lem7566132)). Qed.
Lemma lem7566135 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7566134) (@lem7566131)). Qed.
Lemma lem7566137 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7566138 : term880 = False.
Proof. exact (TRANS (@lem7566135) (@lem7566137)). Qed.
Lemma lem7566139 : term871 = False.
Proof. exact (TRANS (@lem7566127) (@lem7566138)). Qed.
Lemma lem7566140 : term876 = False.
Proof. exact (TRANS (@lem7566124) (@lem7566139)). Qed.
Lemma lem7566141 : term873 = False.
Proof. exact (TRANS (@lem7566108) (@lem7566140)). Qed.
Lemma lem7566142 : term871 = False.
Proof. exact (TRANS (@lem7566085) (@lem7566141)). Qed.
Lemma lem7566143 : term870 = False.
Proof. exact (TRANS (@lem7566076) (@lem7566142)). Qed.
Lemma lem7566144 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1112 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7566143) (@lem7566073 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566145 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term1105 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7566146 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term1103 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7566145 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566148 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term1102 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7566146 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566150 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term1101 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7566148 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566152 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term805 _97569 _97570 _97571.
Proof. exact (proj2 (@lem7566150 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566153 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term595 _97570 _97571.
Proof. exact (proj1 (@lem7566150 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566154 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (proj2 (@lem7566153 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566156 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (proj2 (@lem7566152 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566159 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7566160 : term817 = term818.
Proof. exact (@lem7566159 term35 term469). Qed.
Lemma lem7566162 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566163 : term469 = term549.
Proof. exact (@lem7566162 term470). Qed.
Lemma lem7566165 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566166 : term35 = term520.
Proof. exact (@lem7566165 (NUMERAL 0)). Qed.
Lemma lem7566167 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566168 : term819 = term820.
Proof. exact (MK_COMB (@lem7566167) (@lem7566166)). Qed.
Lemma lem7566169 : term818 = term821.
Proof. exact (MK_COMB (@lem7566168) (@lem7566163)). Qed.
Lemma lem7566170 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7566172 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566173 : term818 = term824.
Proof. exact (@lem7566172 (NUMERAL 0) term470). Qed.
Lemma lem7566174 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566175 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566176 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566175 h1) (fun h1 : term824 = True => @lem7566174)). Qed.
Lemma lem7566177 : term824 = True.
Proof. exact (EQ_MP (@lem7566176) (@lem7566174)). Qed.
Lemma lem7566178 : term818 = True.
Proof. exact (TRANS (@lem7566173) (@lem7566177)). Qed.
Lemma lem7566179 : True = term818.
Proof. exact (SYM (@lem7566178)). Qed.
Lemma lem7566180 : term818.
Proof. exact (EQ_MP (@lem7566179) (@lem0)). Qed.
Lemma lem7566181 : term826.
Proof. exact (@lem7566170 (@lem7566180)). Qed.
Lemma lem7566183 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566184 : term818 = term824.
Proof. exact (@lem7566183 (NUMERAL 0) term470). Qed.
Lemma lem7566185 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566186 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566187 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566186 h1) (fun h1 : term824 = True => @lem7566185)). Qed.
Lemma lem7566188 : term824 = True.
Proof. exact (EQ_MP (@lem7566187) (@lem7566185)). Qed.
Lemma lem7566189 : term818 = True.
Proof. exact (TRANS (@lem7566184) (@lem7566188)). Qed.
Lemma lem7566190 : True = term818.
Proof. exact (SYM (@lem7566189)). Qed.
Lemma lem7566191 : term818.
Proof. exact (EQ_MP (@lem7566190) (@lem0)). Qed.
Lemma lem7566192 : term821 = term827.
Proof. exact (@lem7566181 (@lem7566191)). Qed.
Lemma lem7566194 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566195 : term532 = term533.
Proof. exact (@lem7566194 term470 term470). Qed.
Lemma lem7566196 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566197 : term535 = term470.
Proof. exact (EQ_MP (@lem7566196) (@lem940073)). Qed.
Lemma lem7566198 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566199 : term533 = term469.
Proof. exact (MK_COMB (@lem7566198) (@lem7566197)). Qed.
Lemma lem7566200 : term532 = term469.
Proof. exact (TRANS (@lem7566195) (@lem7566199)). Qed.
Lemma lem7566202 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566203 : term829 = term35.
Proof. exact (@lem7566202 term470). Qed.
Lemma lem7566204 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566205 : term830 = term819.
Proof. exact (MK_COMB (@lem7566204) (@lem7566203)). Qed.
Lemma lem7566206 : term827 = term818.
Proof. exact (MK_COMB (@lem7566205) (@lem7566200)). Qed.
Lemma lem7566208 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566209 : term818 = term824.
Proof. exact (@lem7566208 (NUMERAL 0) term470). Qed.
Lemma lem7566210 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566211 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566212 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566211 h1) (fun h1 : term824 = True => @lem7566210)). Qed.
Lemma lem7566213 : term824 = True.
Proof. exact (EQ_MP (@lem7566212) (@lem7566210)). Qed.
Lemma lem7566214 : term818 = True.
Proof. exact (TRANS (@lem7566209) (@lem7566213)). Qed.
Lemma lem7566215 : term827 = True.
Proof. exact (TRANS (@lem7566206) (@lem7566214)). Qed.
Lemma lem7566216 : term821 = True.
Proof. exact (TRANS (@lem7566192) (@lem7566215)). Qed.
Lemma lem7566217 : term818 = True.
Proof. exact (TRANS (@lem7566169) (@lem7566216)). Qed.
Lemma lem7566218 : term817 = True.
Proof. exact (TRANS (@lem7566160) (@lem7566217)). Qed.
Lemma lem7566219 : True = term817.
Proof. exact (SYM (@lem7566218)). Qed.
Lemma lem7566220 : term817.
Proof. exact (EQ_MP (@lem7566219) (@lem0)). Qed.
Lemma lem7566221 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term882 _97570 _97571.
Proof. exact (conj (@lem7566220) (@lem7566154 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566223 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7566224 (_97570 : int) (_97571 : int) : term883 _97570 _97571.
Proof. exact (@lem7566223 term469 (term587 _97570 _97571)). Qed.
Lemma lem7566225 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term884 _97570 _97571.
Proof. exact (@lem7566224 _97570 _97571 (@lem7566221 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566226 (_97570 : int) (_97571 : int) : (term885 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982733 (term587 _97570 _97571)). Qed.
Lemma lem7566227 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7566228 (_97570 : int) (_97571 : int) : (term886 _97570 _97571) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7566227) (@lem7566226 _97570 _97571)). Qed.
Lemma lem7566229 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7566230 (_97570 : int) (_97571 : int) : (term884 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7566228 _97570 _97571) (@lem7566229)). Qed.
Lemma lem7566231 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (EQ_MP (@lem7566230 _97570 _97571) (@lem7566225 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566233 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7566234 : term817 = term818.
Proof. exact (@lem7566233 term35 term469). Qed.
Lemma lem7566236 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566237 : term469 = term549.
Proof. exact (@lem7566236 term470). Qed.
Lemma lem7566239 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566240 : term35 = term520.
Proof. exact (@lem7566239 (NUMERAL 0)). Qed.
Lemma lem7566241 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566242 : term819 = term820.
Proof. exact (MK_COMB (@lem7566241) (@lem7566240)). Qed.
Lemma lem7566243 : term818 = term821.
Proof. exact (MK_COMB (@lem7566242) (@lem7566237)). Qed.
Lemma lem7566244 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7566246 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566247 : term818 = term824.
Proof. exact (@lem7566246 (NUMERAL 0) term470). Qed.
Lemma lem7566248 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566249 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566250 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566249 h1) (fun h1 : term824 = True => @lem7566248)). Qed.
Lemma lem7566251 : term824 = True.
Proof. exact (EQ_MP (@lem7566250) (@lem7566248)). Qed.
Lemma lem7566252 : term818 = True.
Proof. exact (TRANS (@lem7566247) (@lem7566251)). Qed.
Lemma lem7566253 : True = term818.
Proof. exact (SYM (@lem7566252)). Qed.
Lemma lem7566254 : term818.
Proof. exact (EQ_MP (@lem7566253) (@lem0)). Qed.
Lemma lem7566255 : term826.
Proof. exact (@lem7566244 (@lem7566254)). Qed.
Lemma lem7566257 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566258 : term818 = term824.
Proof. exact (@lem7566257 (NUMERAL 0) term470). Qed.
Lemma lem7566259 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566260 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566261 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566260 h1) (fun h1 : term824 = True => @lem7566259)). Qed.
Lemma lem7566262 : term824 = True.
Proof. exact (EQ_MP (@lem7566261) (@lem7566259)). Qed.
Lemma lem7566263 : term818 = True.
Proof. exact (TRANS (@lem7566258) (@lem7566262)). Qed.
Lemma lem7566264 : True = term818.
Proof. exact (SYM (@lem7566263)). Qed.
Lemma lem7566265 : term818.
Proof. exact (EQ_MP (@lem7566264) (@lem0)). Qed.
Lemma lem7566266 : term821 = term827.
Proof. exact (@lem7566255 (@lem7566265)). Qed.
Lemma lem7566268 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566269 : term532 = term533.
Proof. exact (@lem7566268 term470 term470). Qed.
Lemma lem7566270 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566271 : term535 = term470.
Proof. exact (EQ_MP (@lem7566270) (@lem940073)). Qed.
Lemma lem7566272 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566273 : term533 = term469.
Proof. exact (MK_COMB (@lem7566272) (@lem7566271)). Qed.
Lemma lem7566274 : term532 = term469.
Proof. exact (TRANS (@lem7566269) (@lem7566273)). Qed.
Lemma lem7566276 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566277 : term829 = term35.
Proof. exact (@lem7566276 term470). Qed.
Lemma lem7566278 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566279 : term830 = term819.
Proof. exact (MK_COMB (@lem7566278) (@lem7566277)). Qed.
Lemma lem7566280 : term827 = term818.
Proof. exact (MK_COMB (@lem7566279) (@lem7566274)). Qed.
Lemma lem7566282 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566283 : term818 = term824.
Proof. exact (@lem7566282 (NUMERAL 0) term470). Qed.
Lemma lem7566284 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566285 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566286 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566285 h1) (fun h1 : term824 = True => @lem7566284)). Qed.
Lemma lem7566287 : term824 = True.
Proof. exact (EQ_MP (@lem7566286) (@lem7566284)). Qed.
Lemma lem7566288 : term818 = True.
Proof. exact (TRANS (@lem7566283) (@lem7566287)). Qed.
Lemma lem7566289 : term827 = True.
Proof. exact (TRANS (@lem7566280) (@lem7566288)). Qed.
Lemma lem7566290 : term821 = True.
Proof. exact (TRANS (@lem7566266) (@lem7566289)). Qed.
Lemma lem7566291 : term818 = True.
Proof. exact (TRANS (@lem7566243) (@lem7566290)). Qed.
Lemma lem7566292 : term817 = True.
Proof. exact (TRANS (@lem7566234) (@lem7566291)). Qed.
Lemma lem7566293 : True = term817.
Proof. exact (SYM (@lem7566292)). Qed.
Lemma lem7566294 : term817.
Proof. exact (EQ_MP (@lem7566293) (@lem0)). Qed.
Lemma lem7566295 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term887 _97570 _97571.
Proof. exact (conj (@lem7566294) (@lem7566156 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566297 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7566298 (_97570 : int) (_97571 : int) : term888 _97570 _97571.
Proof. exact (@lem7566297 term469 (term569 _97570 _97571)). Qed.
Lemma lem7566299 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term889 _97570 _97571.
Proof. exact (@lem7566298 _97570 _97571 (@lem7566295 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566300 (_97570 : int) (_97571 : int) : (term890 _97570 _97571) = (term569 _97570 _97571).
Proof. exact (@lem1982733 (term569 _97570 _97571)). Qed.
Lemma lem7566301 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7566302 (_97570 : int) (_97571 : int) : (term891 _97570 _97571) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7566301) (@lem7566300 _97570 _97571)). Qed.
Lemma lem7566303 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7566304 (_97570 : int) (_97571 : int) : (term889 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7566302 _97570 _97571) (@lem7566303)). Qed.
Lemma lem7566305 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (EQ_MP (@lem7566304 _97570 _97571) (@lem7566299 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566306 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term892 _97570 _97571.
Proof. exact (conj (@lem7566305 _97569 _97570 _97571 h1) (@lem7566231 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566308 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7566309 (_97570 : int) (_97571 : int) : term893 _97570 _97571.
Proof. exact (@lem7566308 (term569 _97570 _97571) (term587 _97570 _97571)). Qed.
Lemma lem7566310 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term894 _97570 _97571.
Proof. exact (@lem7566309 _97570 _97571 (@lem7566306 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566311 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = (term896 _97570 _97571).
Proof. exact (@lem1982753 (term570 _97570) (real_of_int _97570) (term897 _97571) (term570 _97571)). Qed.
Lemma lem7566312 (_97570 : int) : (term848 _97570) = (term849 _97570).
Proof. exact (@lem1982713 term523 (real_of_int _97570)). Qed.
Lemma lem7566314 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566315 : term469 = term549.
Proof. exact (@lem7566314 term470). Qed.
Lemma lem7566317 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7566318 : term523 = term524.
Proof. exact (@lem7566317 term470). Qed.
Lemma lem7566319 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566320 : term850 = term851.
Proof. exact (MK_COMB (@lem7566319) (@lem7566318)). Qed.
Lemma lem7566321 : term852 = term853.
Proof. exact (MK_COMB (@lem7566320) (@lem7566315)). Qed.
Lemma lem7566322 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7566324 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566325 : term818 = term824.
Proof. exact (@lem7566324 (NUMERAL 0) term470). Qed.
Lemma lem7566326 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566327 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566328 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566327 h1) (fun h1 : term824 = True => @lem7566326)). Qed.
Lemma lem7566329 : term824 = True.
Proof. exact (EQ_MP (@lem7566328) (@lem7566326)). Qed.
Lemma lem7566330 : term818 = True.
Proof. exact (TRANS (@lem7566325) (@lem7566329)). Qed.
Lemma lem7566331 : True = term818.
Proof. exact (SYM (@lem7566330)). Qed.
Lemma lem7566332 : term818.
Proof. exact (EQ_MP (@lem7566331) (@lem0)). Qed.
Lemma lem7566333 : term855.
Proof. exact (@lem7566322 (@lem7566332)). Qed.
Lemma lem7566335 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566336 : term818 = term824.
Proof. exact (@lem7566335 (NUMERAL 0) term470). Qed.
Lemma lem7566337 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566338 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566339 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566338 h1) (fun h1 : term824 = True => @lem7566337)). Qed.
Lemma lem7566340 : term824 = True.
Proof. exact (EQ_MP (@lem7566339) (@lem7566337)). Qed.
Lemma lem7566341 : term818 = True.
Proof. exact (TRANS (@lem7566336) (@lem7566340)). Qed.
Lemma lem7566342 : True = term818.
Proof. exact (SYM (@lem7566341)). Qed.
Lemma lem7566343 : term818.
Proof. exact (EQ_MP (@lem7566342) (@lem0)). Qed.
Lemma lem7566344 : term856.
Proof. exact (@lem7566333 (@lem7566343)). Qed.
Lemma lem7566346 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566347 : term818 = term824.
Proof. exact (@lem7566346 (NUMERAL 0) term470). Qed.
Lemma lem7566348 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566349 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566350 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566349 h1) (fun h1 : term824 = True => @lem7566348)). Qed.
Lemma lem7566351 : term824 = True.
Proof. exact (EQ_MP (@lem7566350) (@lem7566348)). Qed.
Lemma lem7566352 : term818 = True.
Proof. exact (TRANS (@lem7566347) (@lem7566351)). Qed.
Lemma lem7566353 : True = term818.
Proof. exact (SYM (@lem7566352)). Qed.
Lemma lem7566354 : term818.
Proof. exact (EQ_MP (@lem7566353) (@lem0)). Qed.
Lemma lem7566355 : term857.
Proof. exact (@lem7566344 (@lem7566354)). Qed.
Lemma lem7566357 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566358 : term532 = term533.
Proof. exact (@lem7566357 term470 term470). Qed.
Lemma lem7566359 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566360 : term535 = term470.
Proof. exact (EQ_MP (@lem7566359) (@lem940073)). Qed.
Lemma lem7566361 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566362 : term533 = term469.
Proof. exact (MK_COMB (@lem7566361) (@lem7566360)). Qed.
Lemma lem7566363 : term532 = term469.
Proof. exact (TRANS (@lem7566358) (@lem7566362)). Qed.
Lemma lem7566365 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7566366 : term550 = term555.
Proof. exact (@lem7566365 term470 term470). Qed.
Lemma lem7566367 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566368 : term535 = term470.
Proof. exact (EQ_MP (@lem7566367) (@lem940073)). Qed.
Lemma lem7566369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566370 : term533 = term469.
Proof. exact (MK_COMB (@lem7566369) (@lem7566368)). Qed.
Lemma lem7566371 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7566372 : term555 = term523.
Proof. exact (MK_COMB (@lem7566371) (@lem7566370)). Qed.
Lemma lem7566373 : term550 = term523.
Proof. exact (TRANS (@lem7566366) (@lem7566372)). Qed.
Lemma lem7566374 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566375 : term858 = term850.
Proof. exact (MK_COMB (@lem7566374) (@lem7566373)). Qed.
Lemma lem7566376 : term859 = term852.
Proof. exact (MK_COMB (@lem7566375) (@lem7566363)). Qed.
Lemma lem7566378 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7566379 : term852 = term35.
Proof. exact (@lem7566378 term470). Qed.
Lemma lem7566380 : term859 = term35.
Proof. exact (TRANS (@lem7566376) (@lem7566379)). Qed.
Lemma lem7566381 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566382 : term861 = term218.
Proof. exact (MK_COMB (@lem7566381) (@lem7566380)). Qed.
Lemma lem7566383 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7566384 : term862 = term829.
Proof. exact (MK_COMB (@lem7566382) (@lem7566383)). Qed.
Lemma lem7566386 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566387 : term829 = term35.
Proof. exact (@lem7566386 term470). Qed.
Lemma lem7566388 : term862 = term35.
Proof. exact (TRANS (@lem7566384) (@lem7566387)). Qed.
Lemma lem7566390 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566391 : term532 = term533.
Proof. exact (@lem7566390 term470 term470). Qed.
Lemma lem7566392 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566393 : term535 = term470.
Proof. exact (EQ_MP (@lem7566392) (@lem940073)). Qed.
Lemma lem7566394 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566395 : term533 = term469.
Proof. exact (MK_COMB (@lem7566394) (@lem7566393)). Qed.
Lemma lem7566396 : term532 = term469.
Proof. exact (TRANS (@lem7566391) (@lem7566395)). Qed.
Lemma lem7566397 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7566398 : term863 = term829.
Proof. exact (MK_COMB (@lem7566397) (@lem7566396)). Qed.
Lemma lem7566400 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566401 : term829 = term35.
Proof. exact (@lem7566400 term470). Qed.
Lemma lem7566402 : term863 = term35.
Proof. exact (TRANS (@lem7566398) (@lem7566401)). Qed.
Lemma lem7566403 : term35 = term863.
Proof. exact (SYM (@lem7566402)). Qed.
Lemma lem7566404 : term862 = term863.
Proof. exact (TRANS (@lem7566388) (@lem7566403)). Qed.
Lemma lem7566405 : term853 = term520.
Proof. exact (@lem7566355 (@lem7566404)). Qed.
Lemma lem7566406 : term852 = term520.
Proof. exact (TRANS (@lem7566321) (@lem7566405)). Qed.
Lemma lem7566408 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7566409 : term520 = term35.
Proof. exact (@lem7566408 term35). Qed.
Lemma lem7566410 : term852 = term35.
Proof. exact (TRANS (@lem7566406) (@lem7566409)). Qed.
Lemma lem7566411 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566412 : term864 = term218.
Proof. exact (MK_COMB (@lem7566411) (@lem7566410)). Qed.
Lemma lem7566413 (_97570 : int) : (real_of_int _97570) = (real_of_int _97570).
Proof. exact (eq_refl (real_of_int _97570)). Qed.
Lemma lem7566414 (_97570 : int) : (term849 _97570) = (term865 _97570).
Proof. exact (MK_COMB (@lem7566412) (@lem7566413 _97570)). Qed.
Lemma lem7566415 (_97570 : int) : (term848 _97570) = (term865 _97570).
Proof. exact (TRANS (@lem7566312 _97570) (@lem7566414 _97570)). Qed.
Lemma lem7566416 (_97570 : int) : (term865 _97570) = term35.
Proof. exact (@lem1982719 (real_of_int _97570)). Qed.
Lemma lem7566417 (_97570 : int) : (term848 _97570) = term35.
Proof. exact (TRANS (@lem7566415 _97570) (@lem7566416 _97570)). Qed.
Lemma lem7566418 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566419 (_97570 : int) : (term866 _97570) = term560.
Proof. exact (MK_COMB (@lem7566418) (@lem7566417 _97570)). Qed.
Lemma lem7566420 (_97571 : int) : (term898 _97571) = (term899 _97571).
Proof. exact (@lem1982759 (real_of_int _97571) (term570 _97571) term523). Qed.
Lemma lem7566421 (_97571 : int) : (term900 _97571) = (term849 _97571).
Proof. exact (@lem1982715 term523 (real_of_int _97571)). Qed.
Lemma lem7566423 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566424 : term469 = term549.
Proof. exact (@lem7566423 term470). Qed.
Lemma lem7566426 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7566427 : term523 = term524.
Proof. exact (@lem7566426 term470). Qed.
Lemma lem7566428 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566429 : term850 = term851.
Proof. exact (MK_COMB (@lem7566428) (@lem7566427)). Qed.
Lemma lem7566430 : term852 = term853.
Proof. exact (MK_COMB (@lem7566429) (@lem7566424)). Qed.
Lemma lem7566431 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7566433 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566434 : term818 = term824.
Proof. exact (@lem7566433 (NUMERAL 0) term470). Qed.
Lemma lem7566435 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566436 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566437 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566436 h1) (fun h1 : term824 = True => @lem7566435)). Qed.
Lemma lem7566438 : term824 = True.
Proof. exact (EQ_MP (@lem7566437) (@lem7566435)). Qed.
Lemma lem7566439 : term818 = True.
Proof. exact (TRANS (@lem7566434) (@lem7566438)). Qed.
Lemma lem7566440 : True = term818.
Proof. exact (SYM (@lem7566439)). Qed.
Lemma lem7566441 : term818.
Proof. exact (EQ_MP (@lem7566440) (@lem0)). Qed.
Lemma lem7566442 : term855.
Proof. exact (@lem7566431 (@lem7566441)). Qed.
Lemma lem7566444 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566445 : term818 = term824.
Proof. exact (@lem7566444 (NUMERAL 0) term470). Qed.
Lemma lem7566446 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566447 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566448 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566447 h1) (fun h1 : term824 = True => @lem7566446)). Qed.
Lemma lem7566449 : term824 = True.
Proof. exact (EQ_MP (@lem7566448) (@lem7566446)). Qed.
Lemma lem7566450 : term818 = True.
Proof. exact (TRANS (@lem7566445) (@lem7566449)). Qed.
Lemma lem7566451 : True = term818.
Proof. exact (SYM (@lem7566450)). Qed.
Lemma lem7566452 : term818.
Proof. exact (EQ_MP (@lem7566451) (@lem0)). Qed.
Lemma lem7566453 : term856.
Proof. exact (@lem7566442 (@lem7566452)). Qed.
Lemma lem7566455 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566456 : term818 = term824.
Proof. exact (@lem7566455 (NUMERAL 0) term470). Qed.
Lemma lem7566457 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566458 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566459 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566458 h1) (fun h1 : term824 = True => @lem7566457)). Qed.
Lemma lem7566460 : term824 = True.
Proof. exact (EQ_MP (@lem7566459) (@lem7566457)). Qed.
Lemma lem7566461 : term818 = True.
Proof. exact (TRANS (@lem7566456) (@lem7566460)). Qed.
Lemma lem7566462 : True = term818.
Proof. exact (SYM (@lem7566461)). Qed.
Lemma lem7566463 : term818.
Proof. exact (EQ_MP (@lem7566462) (@lem0)). Qed.
Lemma lem7566464 : term857.
Proof. exact (@lem7566453 (@lem7566463)). Qed.
Lemma lem7566466 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566467 : term532 = term533.
Proof. exact (@lem7566466 term470 term470). Qed.
Lemma lem7566468 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566469 : term535 = term470.
Proof. exact (EQ_MP (@lem7566468) (@lem940073)). Qed.
Lemma lem7566470 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566471 : term533 = term469.
Proof. exact (MK_COMB (@lem7566470) (@lem7566469)). Qed.
Lemma lem7566472 : term532 = term469.
Proof. exact (TRANS (@lem7566467) (@lem7566471)). Qed.
Lemma lem7566474 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7566475 : term550 = term555.
Proof. exact (@lem7566474 term470 term470). Qed.
Lemma lem7566476 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566477 : term535 = term470.
Proof. exact (EQ_MP (@lem7566476) (@lem940073)). Qed.
Lemma lem7566478 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566479 : term533 = term469.
Proof. exact (MK_COMB (@lem7566478) (@lem7566477)). Qed.
Lemma lem7566480 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7566481 : term555 = term523.
Proof. exact (MK_COMB (@lem7566480) (@lem7566479)). Qed.
Lemma lem7566482 : term550 = term523.
Proof. exact (TRANS (@lem7566475) (@lem7566481)). Qed.
Lemma lem7566483 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566484 : term858 = term850.
Proof. exact (MK_COMB (@lem7566483) (@lem7566482)). Qed.
Lemma lem7566485 : term859 = term852.
Proof. exact (MK_COMB (@lem7566484) (@lem7566472)). Qed.
Lemma lem7566487 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7566488 : term852 = term35.
Proof. exact (@lem7566487 term470). Qed.
Lemma lem7566489 : term859 = term35.
Proof. exact (TRANS (@lem7566485) (@lem7566488)). Qed.
Lemma lem7566490 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566491 : term861 = term218.
Proof. exact (MK_COMB (@lem7566490) (@lem7566489)). Qed.
Lemma lem7566492 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7566493 : term862 = term829.
Proof. exact (MK_COMB (@lem7566491) (@lem7566492)). Qed.
Lemma lem7566495 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566496 : term829 = term35.
Proof. exact (@lem7566495 term470). Qed.
Lemma lem7566497 : term862 = term35.
Proof. exact (TRANS (@lem7566493) (@lem7566496)). Qed.
Lemma lem7566499 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566500 : term532 = term533.
Proof. exact (@lem7566499 term470 term470). Qed.
Lemma lem7566501 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566502 : term535 = term470.
Proof. exact (EQ_MP (@lem7566501) (@lem940073)). Qed.
Lemma lem7566503 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566504 : term533 = term469.
Proof. exact (MK_COMB (@lem7566503) (@lem7566502)). Qed.
Lemma lem7566505 : term532 = term469.
Proof. exact (TRANS (@lem7566500) (@lem7566504)). Qed.
Lemma lem7566506 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7566507 : term863 = term829.
Proof. exact (MK_COMB (@lem7566506) (@lem7566505)). Qed.
Lemma lem7566509 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566510 : term829 = term35.
Proof. exact (@lem7566509 term470). Qed.
Lemma lem7566511 : term863 = term35.
Proof. exact (TRANS (@lem7566507) (@lem7566510)). Qed.
Lemma lem7566512 : term35 = term863.
Proof. exact (SYM (@lem7566511)). Qed.
Lemma lem7566513 : term862 = term863.
Proof. exact (TRANS (@lem7566497) (@lem7566512)). Qed.
Lemma lem7566514 : term853 = term520.
Proof. exact (@lem7566464 (@lem7566513)). Qed.
Lemma lem7566515 : term852 = term520.
Proof. exact (TRANS (@lem7566430) (@lem7566514)). Qed.
Lemma lem7566517 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7566518 : term520 = term35.
Proof. exact (@lem7566517 term35). Qed.
Lemma lem7566519 : term852 = term35.
Proof. exact (TRANS (@lem7566515) (@lem7566518)). Qed.
Lemma lem7566520 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566521 : term864 = term218.
Proof. exact (MK_COMB (@lem7566520) (@lem7566519)). Qed.
Lemma lem7566522 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7566523 (_97571 : int) : (term849 _97571) = (term865 _97571).
Proof. exact (MK_COMB (@lem7566521) (@lem7566522 _97571)). Qed.
Lemma lem7566524 (_97571 : int) : (term900 _97571) = (term865 _97571).
Proof. exact (TRANS (@lem7566421 _97571) (@lem7566523 _97571)). Qed.
Lemma lem7566525 (_97571 : int) : (term865 _97571) = term35.
Proof. exact (@lem1982719 (real_of_int _97571)). Qed.
Lemma lem7566526 (_97571 : int) : (term900 _97571) = term35.
Proof. exact (TRANS (@lem7566524 _97571) (@lem7566525 _97571)). Qed.
Lemma lem7566527 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566528 (_97571 : int) : (term901 _97571) = term560.
Proof. exact (MK_COMB (@lem7566527) (@lem7566526 _97571)). Qed.
Lemma lem7566529 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7566530 (_97571 : int) : (term899 _97571) = term867.
Proof. exact (MK_COMB (@lem7566528 _97571) (@lem7566529)). Qed.
Lemma lem7566531 (_97571 : int) : (term898 _97571) = term867.
Proof. exact (TRANS (@lem7566420 _97571) (@lem7566530 _97571)). Qed.
Lemma lem7566532 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7566533 (_97571 : int) : (term898 _97571) = term523.
Proof. exact (TRANS (@lem7566531 _97571) (@lem7566532)). Qed.
Lemma lem7566534 (_97570 : int) (_97571 : int) : (term896 _97570 _97571) = term867.
Proof. exact (MK_COMB (@lem7566419 _97570) (@lem7566533 _97571)). Qed.
Lemma lem7566535 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term867.
Proof. exact (TRANS (@lem7566311 _97570 _97571) (@lem7566534 _97570 _97571)). Qed.
Lemma lem7566536 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7566537 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term523.
Proof. exact (TRANS (@lem7566535 _97570 _97571) (@lem7566536)). Qed.
Lemma lem7566538 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7566539 (_97570 : int) (_97571 : int) : (term902 _97570 _97571) = term869.
Proof. exact (MK_COMB (@lem7566538) (@lem7566537 _97570 _97571)). Qed.
Lemma lem7566540 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7566541 (_97570 : int) (_97571 : int) : (term894 _97570 _97571) = term870.
Proof. exact (MK_COMB (@lem7566539 _97570 _97571) (@lem7566540)). Qed.
Lemma lem7566542 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : term870.
Proof. exact (EQ_MP (@lem7566541 _97570 _97571) (@lem7566310 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566544 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7566545 : term870 = term871.
Proof. exact (@lem7566544 term35 term523). Qed.
Lemma lem7566547 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7566548 : term523 = term524.
Proof. exact (@lem7566547 term470). Qed.
Lemma lem7566550 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566551 : term35 = term520.
Proof. exact (@lem7566550 (NUMERAL 0)). Qed.
Lemma lem7566552 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7566553 : term457 = term872.
Proof. exact (MK_COMB (@lem7566552) (@lem7566551)). Qed.
Lemma lem7566554 : term871 = term873.
Proof. exact (MK_COMB (@lem7566553) (@lem7566548)). Qed.
Lemma lem7566555 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7566557 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566558 : term818 = term824.
Proof. exact (@lem7566557 (NUMERAL 0) term470). Qed.
Lemma lem7566559 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566560 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566561 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566560 h1) (fun h1 : term824 = True => @lem7566559)). Qed.
Lemma lem7566562 : term824 = True.
Proof. exact (EQ_MP (@lem7566561) (@lem7566559)). Qed.
Lemma lem7566563 : term818 = True.
Proof. exact (TRANS (@lem7566558) (@lem7566562)). Qed.
Lemma lem7566564 : True = term818.
Proof. exact (SYM (@lem7566563)). Qed.
Lemma lem7566565 : term818.
Proof. exact (EQ_MP (@lem7566564) (@lem0)). Qed.
Lemma lem7566566 : term875.
Proof. exact (@lem7566555 (@lem7566565)). Qed.
Lemma lem7566568 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566569 : term818 = term824.
Proof. exact (@lem7566568 (NUMERAL 0) term470). Qed.
Lemma lem7566570 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566571 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566572 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566571 h1) (fun h1 : term824 = True => @lem7566570)). Qed.
Lemma lem7566573 : term824 = True.
Proof. exact (EQ_MP (@lem7566572) (@lem7566570)). Qed.
Lemma lem7566574 : term818 = True.
Proof. exact (TRANS (@lem7566569) (@lem7566573)). Qed.
Lemma lem7566575 : True = term818.
Proof. exact (SYM (@lem7566574)). Qed.
Lemma lem7566576 : term818.
Proof. exact (EQ_MP (@lem7566575) (@lem0)). Qed.
Lemma lem7566577 : term873 = term876.
Proof. exact (@lem7566566 (@lem7566576)). Qed.
Lemma lem7566579 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7566580 : term550 = term555.
Proof. exact (@lem7566579 term470 term470). Qed.
Lemma lem7566581 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566582 : term535 = term470.
Proof. exact (EQ_MP (@lem7566581) (@lem940073)). Qed.
Lemma lem7566583 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566584 : term533 = term469.
Proof. exact (MK_COMB (@lem7566583) (@lem7566582)). Qed.
Lemma lem7566585 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7566586 : term555 = term523.
Proof. exact (MK_COMB (@lem7566585) (@lem7566584)). Qed.
Lemma lem7566587 : term550 = term523.
Proof. exact (TRANS (@lem7566580) (@lem7566586)). Qed.
Lemma lem7566589 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566590 : term829 = term35.
Proof. exact (@lem7566589 term470). Qed.
Lemma lem7566591 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7566592 : term877 = term457.
Proof. exact (MK_COMB (@lem7566591) (@lem7566590)). Qed.
Lemma lem7566593 : term876 = term871.
Proof. exact (MK_COMB (@lem7566592) (@lem7566587)). Qed.
Lemma lem7566595 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7566596 : term871 = term880.
Proof. exact (@lem7566595 (NUMERAL 0) term470). Qed.
Lemma lem7566597 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566598 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7566599 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566598 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7566597)). Qed.
Lemma lem7566600 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7566599) (@lem7566597)). Qed.
Lemma lem7566601 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7566602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7566603 : term881 = (and True).
Proof. exact (MK_COMB (@lem7566602) (@lem7566601)). Qed.
Lemma lem7566604 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7566603) (@lem7566600)). Qed.
Lemma lem7566606 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7566607 : term880 = False.
Proof. exact (TRANS (@lem7566604) (@lem7566606)). Qed.
Lemma lem7566608 : term871 = False.
Proof. exact (TRANS (@lem7566596) (@lem7566607)). Qed.
Lemma lem7566609 : term876 = False.
Proof. exact (TRANS (@lem7566593) (@lem7566608)). Qed.
Lemma lem7566610 : term873 = False.
Proof. exact (TRANS (@lem7566577) (@lem7566609)). Qed.
Lemma lem7566611 : term871 = False.
Proof. exact (TRANS (@lem7566554) (@lem7566610)). Qed.
Lemma lem7566612 : term870 = False.
Proof. exact (TRANS (@lem7566545) (@lem7566611)). Qed.
Lemma lem7566613 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1105 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7566612) (@lem7566542 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566614 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1107 _97569 _97570 _97571) : False.
Proof. exact (or_elim (@lem7565790 _97569 _97570 _97571 h1) (fun h0 : term1112 _97569 _97570 _97571 => @lem7566144 _97569 _97570 _97571 h0) (fun h0 : term1105 _97569 _97570 _97571 => @lem7566613 _97569 _97570 _97571 h0)). Qed.
Lemma lem7566615 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term1031 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7566616 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term1013 _97570 _97571.
Proof. exact (proj2 (@lem7566615 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566618 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term631 _97570 _97571.
Proof. exact (proj2 (@lem7566616 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566620 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term618 _97570 _97571.
Proof. exact (proj2 (@lem7566618 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566622 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (proj2 (@lem7566620 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566623 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term595 _97570 _97571.
Proof. exact (proj1 (@lem7566620 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566624 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (proj2 (@lem7566623 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566627 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7566628 : term817 = term818.
Proof. exact (@lem7566627 term35 term469). Qed.
Lemma lem7566630 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566631 : term469 = term549.
Proof. exact (@lem7566630 term470). Qed.
Lemma lem7566633 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566634 : term35 = term520.
Proof. exact (@lem7566633 (NUMERAL 0)). Qed.
Lemma lem7566635 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566636 : term819 = term820.
Proof. exact (MK_COMB (@lem7566635) (@lem7566634)). Qed.
Lemma lem7566637 : term818 = term821.
Proof. exact (MK_COMB (@lem7566636) (@lem7566631)). Qed.
Lemma lem7566638 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7566640 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566641 : term818 = term824.
Proof. exact (@lem7566640 (NUMERAL 0) term470). Qed.
Lemma lem7566642 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566643 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566644 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566643 h1) (fun h1 : term824 = True => @lem7566642)). Qed.
Lemma lem7566645 : term824 = True.
Proof. exact (EQ_MP (@lem7566644) (@lem7566642)). Qed.
Lemma lem7566646 : term818 = True.
Proof. exact (TRANS (@lem7566641) (@lem7566645)). Qed.
Lemma lem7566647 : True = term818.
Proof. exact (SYM (@lem7566646)). Qed.
Lemma lem7566648 : term818.
Proof. exact (EQ_MP (@lem7566647) (@lem0)). Qed.
Lemma lem7566649 : term826.
Proof. exact (@lem7566638 (@lem7566648)). Qed.
Lemma lem7566651 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566652 : term818 = term824.
Proof. exact (@lem7566651 (NUMERAL 0) term470). Qed.
Lemma lem7566653 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566654 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566655 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566654 h1) (fun h1 : term824 = True => @lem7566653)). Qed.
Lemma lem7566656 : term824 = True.
Proof. exact (EQ_MP (@lem7566655) (@lem7566653)). Qed.
Lemma lem7566657 : term818 = True.
Proof. exact (TRANS (@lem7566652) (@lem7566656)). Qed.
Lemma lem7566658 : True = term818.
Proof. exact (SYM (@lem7566657)). Qed.
Lemma lem7566659 : term818.
Proof. exact (EQ_MP (@lem7566658) (@lem0)). Qed.
Lemma lem7566660 : term821 = term827.
Proof. exact (@lem7566649 (@lem7566659)). Qed.
Lemma lem7566662 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566663 : term532 = term533.
Proof. exact (@lem7566662 term470 term470). Qed.
Lemma lem7566664 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566665 : term535 = term470.
Proof. exact (EQ_MP (@lem7566664) (@lem940073)). Qed.
Lemma lem7566666 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566667 : term533 = term469.
Proof. exact (MK_COMB (@lem7566666) (@lem7566665)). Qed.
Lemma lem7566668 : term532 = term469.
Proof. exact (TRANS (@lem7566663) (@lem7566667)). Qed.
Lemma lem7566670 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566671 : term829 = term35.
Proof. exact (@lem7566670 term470). Qed.
Lemma lem7566672 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566673 : term830 = term819.
Proof. exact (MK_COMB (@lem7566672) (@lem7566671)). Qed.
Lemma lem7566674 : term827 = term818.
Proof. exact (MK_COMB (@lem7566673) (@lem7566668)). Qed.
Lemma lem7566676 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566677 : term818 = term824.
Proof. exact (@lem7566676 (NUMERAL 0) term470). Qed.
Lemma lem7566678 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566679 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566680 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566679 h1) (fun h1 : term824 = True => @lem7566678)). Qed.
Lemma lem7566681 : term824 = True.
Proof. exact (EQ_MP (@lem7566680) (@lem7566678)). Qed.
Lemma lem7566682 : term818 = True.
Proof. exact (TRANS (@lem7566677) (@lem7566681)). Qed.
Lemma lem7566683 : term827 = True.
Proof. exact (TRANS (@lem7566674) (@lem7566682)). Qed.
Lemma lem7566684 : term821 = True.
Proof. exact (TRANS (@lem7566660) (@lem7566683)). Qed.
Lemma lem7566685 : term818 = True.
Proof. exact (TRANS (@lem7566637) (@lem7566684)). Qed.
Lemma lem7566686 : term817 = True.
Proof. exact (TRANS (@lem7566628) (@lem7566685)). Qed.
Lemma lem7566687 : True = term817.
Proof. exact (SYM (@lem7566686)). Qed.
Lemma lem7566688 : term817.
Proof. exact (EQ_MP (@lem7566687) (@lem0)). Qed.
Lemma lem7566689 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term882 _97570 _97571.
Proof. exact (conj (@lem7566688) (@lem7566624 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566691 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7566692 (_97570 : int) (_97571 : int) : term883 _97570 _97571.
Proof. exact (@lem7566691 term469 (term587 _97570 _97571)). Qed.
Lemma lem7566693 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term884 _97570 _97571.
Proof. exact (@lem7566692 _97570 _97571 (@lem7566689 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566694 (_97570 : int) (_97571 : int) : (term885 _97570 _97571) = (term587 _97570 _97571).
Proof. exact (@lem1982733 (term587 _97570 _97571)). Qed.
Lemma lem7566695 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7566696 (_97570 : int) (_97571 : int) : (term886 _97570 _97571) = (term589 _97570 _97571).
Proof. exact (MK_COMB (@lem7566695) (@lem7566694 _97570 _97571)). Qed.
Lemma lem7566697 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7566698 (_97570 : int) (_97571 : int) : (term884 _97570 _97571) = (term590 _97570 _97571).
Proof. exact (MK_COMB (@lem7566696 _97570 _97571) (@lem7566697)). Qed.
Lemma lem7566699 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term590 _97570 _97571.
Proof. exact (EQ_MP (@lem7566698 _97570 _97571) (@lem7566693 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566701 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem7566702 : term817 = term818.
Proof. exact (@lem7566701 term35 term469). Qed.
Lemma lem7566704 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566705 : term469 = term549.
Proof. exact (@lem7566704 term470). Qed.
Lemma lem7566707 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566708 : term35 = term520.
Proof. exact (@lem7566707 (NUMERAL 0)). Qed.
Lemma lem7566709 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566710 : term819 = term820.
Proof. exact (MK_COMB (@lem7566709) (@lem7566708)). Qed.
Lemma lem7566711 : term818 = term821.
Proof. exact (MK_COMB (@lem7566710) (@lem7566705)). Qed.
Lemma lem7566712 : term822.
Proof. exact (@lem1980255 term35 term469 term469 term469). Qed.
Lemma lem7566714 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566715 : term818 = term824.
Proof. exact (@lem7566714 (NUMERAL 0) term470). Qed.
Lemma lem7566716 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566717 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566718 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566717 h1) (fun h1 : term824 = True => @lem7566716)). Qed.
Lemma lem7566719 : term824 = True.
Proof. exact (EQ_MP (@lem7566718) (@lem7566716)). Qed.
Lemma lem7566720 : term818 = True.
Proof. exact (TRANS (@lem7566715) (@lem7566719)). Qed.
Lemma lem7566721 : True = term818.
Proof. exact (SYM (@lem7566720)). Qed.
Lemma lem7566722 : term818.
Proof. exact (EQ_MP (@lem7566721) (@lem0)). Qed.
Lemma lem7566723 : term826.
Proof. exact (@lem7566712 (@lem7566722)). Qed.
Lemma lem7566725 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566726 : term818 = term824.
Proof. exact (@lem7566725 (NUMERAL 0) term470). Qed.
Lemma lem7566727 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566728 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566729 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566728 h1) (fun h1 : term824 = True => @lem7566727)). Qed.
Lemma lem7566730 : term824 = True.
Proof. exact (EQ_MP (@lem7566729) (@lem7566727)). Qed.
Lemma lem7566731 : term818 = True.
Proof. exact (TRANS (@lem7566726) (@lem7566730)). Qed.
Lemma lem7566732 : True = term818.
Proof. exact (SYM (@lem7566731)). Qed.
Lemma lem7566733 : term818.
Proof. exact (EQ_MP (@lem7566732) (@lem0)). Qed.
Lemma lem7566734 : term821 = term827.
Proof. exact (@lem7566723 (@lem7566733)). Qed.
Lemma lem7566736 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566737 : term532 = term533.
Proof. exact (@lem7566736 term470 term470). Qed.
Lemma lem7566738 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566739 : term535 = term470.
Proof. exact (EQ_MP (@lem7566738) (@lem940073)). Qed.
Lemma lem7566740 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566741 : term533 = term469.
Proof. exact (MK_COMB (@lem7566740) (@lem7566739)). Qed.
Lemma lem7566742 : term532 = term469.
Proof. exact (TRANS (@lem7566737) (@lem7566741)). Qed.
Lemma lem7566744 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566745 : term829 = term35.
Proof. exact (@lem7566744 term470). Qed.
Lemma lem7566746 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem7566747 : term830 = term819.
Proof. exact (MK_COMB (@lem7566746) (@lem7566745)). Qed.
Lemma lem7566748 : term827 = term818.
Proof. exact (MK_COMB (@lem7566747) (@lem7566742)). Qed.
Lemma lem7566750 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566751 : term818 = term824.
Proof. exact (@lem7566750 (NUMERAL 0) term470). Qed.
Lemma lem7566752 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566753 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566754 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566753 h1) (fun h1 : term824 = True => @lem7566752)). Qed.
Lemma lem7566755 : term824 = True.
Proof. exact (EQ_MP (@lem7566754) (@lem7566752)). Qed.
Lemma lem7566756 : term818 = True.
Proof. exact (TRANS (@lem7566751) (@lem7566755)). Qed.
Lemma lem7566757 : term827 = True.
Proof. exact (TRANS (@lem7566748) (@lem7566756)). Qed.
Lemma lem7566758 : term821 = True.
Proof. exact (TRANS (@lem7566734) (@lem7566757)). Qed.
Lemma lem7566759 : term818 = True.
Proof. exact (TRANS (@lem7566711) (@lem7566758)). Qed.
Lemma lem7566760 : term817 = True.
Proof. exact (TRANS (@lem7566702) (@lem7566759)). Qed.
Lemma lem7566761 : True = term817.
Proof. exact (SYM (@lem7566760)). Qed.
Lemma lem7566762 : term817.
Proof. exact (EQ_MP (@lem7566761) (@lem0)). Qed.
Lemma lem7566763 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term887 _97570 _97571.
Proof. exact (conj (@lem7566762) (@lem7566622 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566765 (x : real) (y : real) : term832 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem7566766 (_97570 : int) (_97571 : int) : term888 _97570 _97571.
Proof. exact (@lem7566765 term469 (term569 _97570 _97571)). Qed.
Lemma lem7566767 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term889 _97570 _97571.
Proof. exact (@lem7566766 _97570 _97571 (@lem7566763 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566768 (_97570 : int) (_97571 : int) : (term890 _97570 _97571) = (term569 _97570 _97571).
Proof. exact (@lem1982733 (term569 _97570 _97571)). Qed.
Lemma lem7566769 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7566770 (_97570 : int) (_97571 : int) : (term891 _97570 _97571) = (term572 _97570 _97571).
Proof. exact (MK_COMB (@lem7566769) (@lem7566768 _97570 _97571)). Qed.
Lemma lem7566771 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7566772 (_97570 : int) (_97571 : int) : (term889 _97570 _97571) = (term573 _97570 _97571).
Proof. exact (MK_COMB (@lem7566770 _97570 _97571) (@lem7566771)). Qed.
Lemma lem7566773 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term573 _97570 _97571.
Proof. exact (EQ_MP (@lem7566772 _97570 _97571) (@lem7566767 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566774 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term892 _97570 _97571.
Proof. exact (conj (@lem7566773 _97569 _97570 _97571 h1) (@lem7566699 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566776 (x : real) (y : real) : term843 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem7566777 (_97570 : int) (_97571 : int) : term893 _97570 _97571.
Proof. exact (@lem7566776 (term569 _97570 _97571) (term587 _97570 _97571)). Qed.
Lemma lem7566778 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term894 _97570 _97571.
Proof. exact (@lem7566777 _97570 _97571 (@lem7566774 _97569 _97570 _97571 h1)). Qed.
Lemma lem7566779 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = (term896 _97570 _97571).
Proof. exact (@lem1982753 (term570 _97570) (real_of_int _97570) (term897 _97571) (term570 _97571)). Qed.
Lemma lem7566780 (_97570 : int) : (term848 _97570) = (term849 _97570).
Proof. exact (@lem1982713 term523 (real_of_int _97570)). Qed.
Lemma lem7566782 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566783 : term469 = term549.
Proof. exact (@lem7566782 term470). Qed.
Lemma lem7566785 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7566786 : term523 = term524.
Proof. exact (@lem7566785 term470). Qed.
Lemma lem7566787 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566788 : term850 = term851.
Proof. exact (MK_COMB (@lem7566787) (@lem7566786)). Qed.
Lemma lem7566789 : term852 = term853.
Proof. exact (MK_COMB (@lem7566788) (@lem7566783)). Qed.
Lemma lem7566790 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7566792 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566793 : term818 = term824.
Proof. exact (@lem7566792 (NUMERAL 0) term470). Qed.
Lemma lem7566794 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566795 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566796 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566795 h1) (fun h1 : term824 = True => @lem7566794)). Qed.
Lemma lem7566797 : term824 = True.
Proof. exact (EQ_MP (@lem7566796) (@lem7566794)). Qed.
Lemma lem7566798 : term818 = True.
Proof. exact (TRANS (@lem7566793) (@lem7566797)). Qed.
Lemma lem7566799 : True = term818.
Proof. exact (SYM (@lem7566798)). Qed.
Lemma lem7566800 : term818.
Proof. exact (EQ_MP (@lem7566799) (@lem0)). Qed.
Lemma lem7566801 : term855.
Proof. exact (@lem7566790 (@lem7566800)). Qed.
Lemma lem7566803 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566804 : term818 = term824.
Proof. exact (@lem7566803 (NUMERAL 0) term470). Qed.
Lemma lem7566805 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566806 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566807 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566806 h1) (fun h1 : term824 = True => @lem7566805)). Qed.
Lemma lem7566808 : term824 = True.
Proof. exact (EQ_MP (@lem7566807) (@lem7566805)). Qed.
Lemma lem7566809 : term818 = True.
Proof. exact (TRANS (@lem7566804) (@lem7566808)). Qed.
Lemma lem7566810 : True = term818.
Proof. exact (SYM (@lem7566809)). Qed.
Lemma lem7566811 : term818.
Proof. exact (EQ_MP (@lem7566810) (@lem0)). Qed.
Lemma lem7566812 : term856.
Proof. exact (@lem7566801 (@lem7566811)). Qed.
Lemma lem7566814 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566815 : term818 = term824.
Proof. exact (@lem7566814 (NUMERAL 0) term470). Qed.
Lemma lem7566816 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566817 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566818 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566817 h1) (fun h1 : term824 = True => @lem7566816)). Qed.
Lemma lem7566819 : term824 = True.
Proof. exact (EQ_MP (@lem7566818) (@lem7566816)). Qed.
Lemma lem7566820 : term818 = True.
Proof. exact (TRANS (@lem7566815) (@lem7566819)). Qed.
Lemma lem7566821 : True = term818.
Proof. exact (SYM (@lem7566820)). Qed.
Lemma lem7566822 : term818.
Proof. exact (EQ_MP (@lem7566821) (@lem0)). Qed.
Lemma lem7566823 : term857.
Proof. exact (@lem7566812 (@lem7566822)). Qed.
Lemma lem7566825 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566826 : term532 = term533.
Proof. exact (@lem7566825 term470 term470). Qed.
Lemma lem7566827 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566828 : term535 = term470.
Proof. exact (EQ_MP (@lem7566827) (@lem940073)). Qed.
Lemma lem7566829 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566830 : term533 = term469.
Proof. exact (MK_COMB (@lem7566829) (@lem7566828)). Qed.
Lemma lem7566831 : term532 = term469.
Proof. exact (TRANS (@lem7566826) (@lem7566830)). Qed.
Lemma lem7566833 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7566834 : term550 = term555.
Proof. exact (@lem7566833 term470 term470). Qed.
Lemma lem7566835 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566836 : term535 = term470.
Proof. exact (EQ_MP (@lem7566835) (@lem940073)). Qed.
Lemma lem7566837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566838 : term533 = term469.
Proof. exact (MK_COMB (@lem7566837) (@lem7566836)). Qed.
Lemma lem7566839 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7566840 : term555 = term523.
Proof. exact (MK_COMB (@lem7566839) (@lem7566838)). Qed.
Lemma lem7566841 : term550 = term523.
Proof. exact (TRANS (@lem7566834) (@lem7566840)). Qed.
Lemma lem7566842 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566843 : term858 = term850.
Proof. exact (MK_COMB (@lem7566842) (@lem7566841)). Qed.
Lemma lem7566844 : term859 = term852.
Proof. exact (MK_COMB (@lem7566843) (@lem7566831)). Qed.
Lemma lem7566846 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7566847 : term852 = term35.
Proof. exact (@lem7566846 term470). Qed.
Lemma lem7566848 : term859 = term35.
Proof. exact (TRANS (@lem7566844) (@lem7566847)). Qed.
Lemma lem7566849 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566850 : term861 = term218.
Proof. exact (MK_COMB (@lem7566849) (@lem7566848)). Qed.
Lemma lem7566851 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7566852 : term862 = term829.
Proof. exact (MK_COMB (@lem7566850) (@lem7566851)). Qed.
Lemma lem7566854 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566855 : term829 = term35.
Proof. exact (@lem7566854 term470). Qed.
Lemma lem7566856 : term862 = term35.
Proof. exact (TRANS (@lem7566852) (@lem7566855)). Qed.
Lemma lem7566858 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566859 : term532 = term533.
Proof. exact (@lem7566858 term470 term470). Qed.
Lemma lem7566860 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566861 : term535 = term470.
Proof. exact (EQ_MP (@lem7566860) (@lem940073)). Qed.
Lemma lem7566862 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566863 : term533 = term469.
Proof. exact (MK_COMB (@lem7566862) (@lem7566861)). Qed.
Lemma lem7566864 : term532 = term469.
Proof. exact (TRANS (@lem7566859) (@lem7566863)). Qed.
Lemma lem7566865 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7566866 : term863 = term829.
Proof. exact (MK_COMB (@lem7566865) (@lem7566864)). Qed.
Lemma lem7566868 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566869 : term829 = term35.
Proof. exact (@lem7566868 term470). Qed.
Lemma lem7566870 : term863 = term35.
Proof. exact (TRANS (@lem7566866) (@lem7566869)). Qed.
Lemma lem7566871 : term35 = term863.
Proof. exact (SYM (@lem7566870)). Qed.
Lemma lem7566872 : term862 = term863.
Proof. exact (TRANS (@lem7566856) (@lem7566871)). Qed.
Lemma lem7566873 : term853 = term520.
Proof. exact (@lem7566823 (@lem7566872)). Qed.
Lemma lem7566874 : term852 = term520.
Proof. exact (TRANS (@lem7566789) (@lem7566873)). Qed.
Lemma lem7566876 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7566877 : term520 = term35.
Proof. exact (@lem7566876 term35). Qed.
Lemma lem7566878 : term852 = term35.
Proof. exact (TRANS (@lem7566874) (@lem7566877)). Qed.
Lemma lem7566879 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566880 : term864 = term218.
Proof. exact (MK_COMB (@lem7566879) (@lem7566878)). Qed.
Lemma lem7566881 (_97570 : int) : (real_of_int _97570) = (real_of_int _97570).
Proof. exact (eq_refl (real_of_int _97570)). Qed.
Lemma lem7566882 (_97570 : int) : (term849 _97570) = (term865 _97570).
Proof. exact (MK_COMB (@lem7566880) (@lem7566881 _97570)). Qed.
Lemma lem7566883 (_97570 : int) : (term848 _97570) = (term865 _97570).
Proof. exact (TRANS (@lem7566780 _97570) (@lem7566882 _97570)). Qed.
Lemma lem7566884 (_97570 : int) : (term865 _97570) = term35.
Proof. exact (@lem1982719 (real_of_int _97570)). Qed.
Lemma lem7566885 (_97570 : int) : (term848 _97570) = term35.
Proof. exact (TRANS (@lem7566883 _97570) (@lem7566884 _97570)). Qed.
Lemma lem7566886 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566887 (_97570 : int) : (term866 _97570) = term560.
Proof. exact (MK_COMB (@lem7566886) (@lem7566885 _97570)). Qed.
Lemma lem7566888 (_97571 : int) : (term898 _97571) = (term899 _97571).
Proof. exact (@lem1982759 (real_of_int _97571) (term570 _97571) term523). Qed.
Lemma lem7566889 (_97571 : int) : (term900 _97571) = (term849 _97571).
Proof. exact (@lem1982715 term523 (real_of_int _97571)). Qed.
Lemma lem7566891 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7566892 : term469 = term549.
Proof. exact (@lem7566891 term470). Qed.
Lemma lem7566894 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7566895 : term523 = term524.
Proof. exact (@lem7566894 term470). Qed.
Lemma lem7566896 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566897 : term850 = term851.
Proof. exact (MK_COMB (@lem7566896) (@lem7566895)). Qed.
Lemma lem7566898 : term852 = term853.
Proof. exact (MK_COMB (@lem7566897) (@lem7566892)). Qed.
Lemma lem7566899 : term854.
Proof. exact (@lem1981473 term523 term469 term469 term469 term35 term469). Qed.
Lemma lem7566901 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566902 : term818 = term824.
Proof. exact (@lem7566901 (NUMERAL 0) term470). Qed.
Lemma lem7566903 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566904 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566905 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566904 h1) (fun h1 : term824 = True => @lem7566903)). Qed.
Lemma lem7566906 : term824 = True.
Proof. exact (EQ_MP (@lem7566905) (@lem7566903)). Qed.
Lemma lem7566907 : term818 = True.
Proof. exact (TRANS (@lem7566902) (@lem7566906)). Qed.
Lemma lem7566908 : True = term818.
Proof. exact (SYM (@lem7566907)). Qed.
Lemma lem7566909 : term818.
Proof. exact (EQ_MP (@lem7566908) (@lem0)). Qed.
Lemma lem7566910 : term855.
Proof. exact (@lem7566899 (@lem7566909)). Qed.
Lemma lem7566912 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566913 : term818 = term824.
Proof. exact (@lem7566912 (NUMERAL 0) term470). Qed.
Lemma lem7566914 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566915 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566916 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566915 h1) (fun h1 : term824 = True => @lem7566914)). Qed.
Lemma lem7566917 : term824 = True.
Proof. exact (EQ_MP (@lem7566916) (@lem7566914)). Qed.
Lemma lem7566918 : term818 = True.
Proof. exact (TRANS (@lem7566913) (@lem7566917)). Qed.
Lemma lem7566919 : True = term818.
Proof. exact (SYM (@lem7566918)). Qed.
Lemma lem7566920 : term818.
Proof. exact (EQ_MP (@lem7566919) (@lem0)). Qed.
Lemma lem7566921 : term856.
Proof. exact (@lem7566910 (@lem7566920)). Qed.
Lemma lem7566923 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7566924 : term818 = term824.
Proof. exact (@lem7566923 (NUMERAL 0) term470). Qed.
Lemma lem7566925 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7566926 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7566927 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7566926 h1) (fun h1 : term824 = True => @lem7566925)). Qed.
Lemma lem7566928 : term824 = True.
Proof. exact (EQ_MP (@lem7566927) (@lem7566925)). Qed.
Lemma lem7566929 : term818 = True.
Proof. exact (TRANS (@lem7566924) (@lem7566928)). Qed.
Lemma lem7566930 : True = term818.
Proof. exact (SYM (@lem7566929)). Qed.
Lemma lem7566931 : term818.
Proof. exact (EQ_MP (@lem7566930) (@lem0)). Qed.
Lemma lem7566932 : term857.
Proof. exact (@lem7566921 (@lem7566931)). Qed.
Lemma lem7566934 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566935 : term532 = term533.
Proof. exact (@lem7566934 term470 term470). Qed.
Lemma lem7566936 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566937 : term535 = term470.
Proof. exact (EQ_MP (@lem7566936) (@lem940073)). Qed.
Lemma lem7566938 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566939 : term533 = term469.
Proof. exact (MK_COMB (@lem7566938) (@lem7566937)). Qed.
Lemma lem7566940 : term532 = term469.
Proof. exact (TRANS (@lem7566935) (@lem7566939)). Qed.
Lemma lem7566942 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7566943 : term550 = term555.
Proof. exact (@lem7566942 term470 term470). Qed.
Lemma lem7566944 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566945 : term535 = term470.
Proof. exact (EQ_MP (@lem7566944) (@lem940073)). Qed.
Lemma lem7566946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566947 : term533 = term469.
Proof. exact (MK_COMB (@lem7566946) (@lem7566945)). Qed.
Lemma lem7566948 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7566949 : term555 = term523.
Proof. exact (MK_COMB (@lem7566948) (@lem7566947)). Qed.
Lemma lem7566950 : term550 = term523.
Proof. exact (TRANS (@lem7566943) (@lem7566949)). Qed.
Lemma lem7566951 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566952 : term858 = term850.
Proof. exact (MK_COMB (@lem7566951) (@lem7566950)). Qed.
Lemma lem7566953 : term859 = term852.
Proof. exact (MK_COMB (@lem7566952) (@lem7566940)). Qed.
Lemma lem7566955 (m : nat) : (term860 m) = term35.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem7566956 : term852 = term35.
Proof. exact (@lem7566955 term470). Qed.
Lemma lem7566957 : term859 = term35.
Proof. exact (TRANS (@lem7566953) (@lem7566956)). Qed.
Lemma lem7566958 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566959 : term861 = term218.
Proof. exact (MK_COMB (@lem7566958) (@lem7566957)). Qed.
Lemma lem7566960 : term469 = term469.
Proof. exact (eq_refl term469). Qed.
Lemma lem7566961 : term862 = term829.
Proof. exact (MK_COMB (@lem7566959) (@lem7566960)). Qed.
Lemma lem7566963 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566964 : term829 = term35.
Proof. exact (@lem7566963 term470). Qed.
Lemma lem7566965 : term862 = term35.
Proof. exact (TRANS (@lem7566961) (@lem7566964)). Qed.
Lemma lem7566967 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem7566968 : term532 = term533.
Proof. exact (@lem7566967 term470 term470). Qed.
Lemma lem7566969 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7566970 : term535 = term470.
Proof. exact (EQ_MP (@lem7566969) (@lem940073)). Qed.
Lemma lem7566971 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7566972 : term533 = term469.
Proof. exact (MK_COMB (@lem7566971) (@lem7566970)). Qed.
Lemma lem7566973 : term532 = term469.
Proof. exact (TRANS (@lem7566968) (@lem7566972)). Qed.
Lemma lem7566974 : term218 = term218.
Proof. exact (eq_refl term218). Qed.
Lemma lem7566975 : term863 = term829.
Proof. exact (MK_COMB (@lem7566974) (@lem7566973)). Qed.
Lemma lem7566977 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7566978 : term829 = term35.
Proof. exact (@lem7566977 term470). Qed.
Lemma lem7566979 : term863 = term35.
Proof. exact (TRANS (@lem7566975) (@lem7566978)). Qed.
Lemma lem7566980 : term35 = term863.
Proof. exact (SYM (@lem7566979)). Qed.
Lemma lem7566981 : term862 = term863.
Proof. exact (TRANS (@lem7566965) (@lem7566980)). Qed.
Lemma lem7566982 : term853 = term520.
Proof. exact (@lem7566932 (@lem7566981)). Qed.
Lemma lem7566983 : term852 = term520.
Proof. exact (TRANS (@lem7566898) (@lem7566982)). Qed.
Lemma lem7566985 (x : real) : (term539 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem7566986 : term520 = term35.
Proof. exact (@lem7566985 term35). Qed.
Lemma lem7566987 : term852 = term35.
Proof. exact (TRANS (@lem7566983) (@lem7566986)). Qed.
Lemma lem7566988 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem7566989 : term864 = term218.
Proof. exact (MK_COMB (@lem7566988) (@lem7566987)). Qed.
Lemma lem7566990 (_97571 : int) : (real_of_int _97571) = (real_of_int _97571).
Proof. exact (eq_refl (real_of_int _97571)). Qed.
Lemma lem7566991 (_97571 : int) : (term849 _97571) = (term865 _97571).
Proof. exact (MK_COMB (@lem7566989) (@lem7566990 _97571)). Qed.
Lemma lem7566992 (_97571 : int) : (term900 _97571) = (term865 _97571).
Proof. exact (TRANS (@lem7566889 _97571) (@lem7566991 _97571)). Qed.
Lemma lem7566993 (_97571 : int) : (term865 _97571) = term35.
Proof. exact (@lem1982719 (real_of_int _97571)). Qed.
Lemma lem7566994 (_97571 : int) : (term900 _97571) = term35.
Proof. exact (TRANS (@lem7566992 _97571) (@lem7566993 _97571)). Qed.
Lemma lem7566995 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7566996 (_97571 : int) : (term901 _97571) = term560.
Proof. exact (MK_COMB (@lem7566995) (@lem7566994 _97571)). Qed.
Lemma lem7566997 : term523 = term523.
Proof. exact (eq_refl term523). Qed.
Lemma lem7566998 (_97571 : int) : (term899 _97571) = term867.
Proof. exact (MK_COMB (@lem7566996 _97571) (@lem7566997)). Qed.
Lemma lem7566999 (_97571 : int) : (term898 _97571) = term867.
Proof. exact (TRANS (@lem7566888 _97571) (@lem7566998 _97571)). Qed.
Lemma lem7567000 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7567001 (_97571 : int) : (term898 _97571) = term523.
Proof. exact (TRANS (@lem7566999 _97571) (@lem7567000)). Qed.
Lemma lem7567002 (_97570 : int) (_97571 : int) : (term896 _97570 _97571) = term867.
Proof. exact (MK_COMB (@lem7566887 _97570) (@lem7567001 _97571)). Qed.
Lemma lem7567003 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term867.
Proof. exact (TRANS (@lem7566779 _97570 _97571) (@lem7567002 _97570 _97571)). Qed.
Lemma lem7567004 : term867 = term523.
Proof. exact (@lem1982721 term523). Qed.
Lemma lem7567005 (_97570 : int) (_97571 : int) : (term895 _97570 _97571) = term523.
Proof. exact (TRANS (@lem7567003 _97570 _97571) (@lem7567004)). Qed.
Lemma lem7567006 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem7567007 (_97570 : int) (_97571 : int) : (term902 _97570 _97571) = term869.
Proof. exact (MK_COMB (@lem7567006) (@lem7567005 _97570 _97571)). Qed.
Lemma lem7567008 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem7567009 (_97570 : int) (_97571 : int) : (term894 _97570 _97571) = term870.
Proof. exact (MK_COMB (@lem7567007 _97570 _97571) (@lem7567008)). Qed.
Lemma lem7567010 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : term870.
Proof. exact (EQ_MP (@lem7567009 _97570 _97571) (@lem7566778 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567012 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem7567013 : term870 = term871.
Proof. exact (@lem7567012 term35 term523). Qed.
Lemma lem7567015 (x : nat) : (term521 x) = (term522 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem7567016 : term523 = term524.
Proof. exact (@lem7567015 term470). Qed.
Lemma lem7567018 (x : nat) : (real_of_num x) = (term519 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem7567019 : term35 = term520.
Proof. exact (@lem7567018 (NUMERAL 0)). Qed.
Lemma lem7567020 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7567021 : term457 = term872.
Proof. exact (MK_COMB (@lem7567020) (@lem7567019)). Qed.
Lemma lem7567022 : term871 = term873.
Proof. exact (MK_COMB (@lem7567021) (@lem7567016)). Qed.
Lemma lem7567023 : term874.
Proof. exact (@lem1980026 term35 term469 term523 term469). Qed.
Lemma lem7567025 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7567026 : term818 = term824.
Proof. exact (@lem7567025 (NUMERAL 0) term470). Qed.
Lemma lem7567027 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7567028 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7567029 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7567028 h1) (fun h1 : term824 = True => @lem7567027)). Qed.
Lemma lem7567030 : term824 = True.
Proof. exact (EQ_MP (@lem7567029) (@lem7567027)). Qed.
Lemma lem7567031 : term818 = True.
Proof. exact (TRANS (@lem7567026) (@lem7567030)). Qed.
Lemma lem7567032 : True = term818.
Proof. exact (SYM (@lem7567031)). Qed.
Lemma lem7567033 : term818.
Proof. exact (EQ_MP (@lem7567032) (@lem0)). Qed.
Lemma lem7567034 : term875.
Proof. exact (@lem7567023 (@lem7567033)). Qed.
Lemma lem7567036 (m : nat) (n : nat) : (term823 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem7567037 : term818 = term824.
Proof. exact (@lem7567036 (NUMERAL 0) term470). Qed.
Lemma lem7567038 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7567039 (h1 : term825 = (BIT1 0)) : term824 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem7567040 : (term825 = (BIT1 0)) = (term824 = True).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7567039 h1) (fun h1 : term824 = True => @lem7567038)). Qed.
Lemma lem7567041 : term824 = True.
Proof. exact (EQ_MP (@lem7567040) (@lem7567038)). Qed.
Lemma lem7567042 : term818 = True.
Proof. exact (TRANS (@lem7567037) (@lem7567041)). Qed.
Lemma lem7567043 : True = term818.
Proof. exact (SYM (@lem7567042)). Qed.
Lemma lem7567044 : term818.
Proof. exact (EQ_MP (@lem7567043) (@lem0)). Qed.
Lemma lem7567045 : term873 = term876.
Proof. exact (@lem7567034 (@lem7567044)). Qed.
Lemma lem7567047 (m : nat) (n : nat) : (term553 m n) = (term554 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem7567048 : term550 = term555.
Proof. exact (@lem7567047 term470 term470). Qed.
Lemma lem7567049 : (term534 = (BIT1 0)) = (term535 = term470).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem7567050 : term535 = term470.
Proof. exact (EQ_MP (@lem7567049) (@lem940073)). Qed.
Lemma lem7567051 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem7567052 : term533 = term469.
Proof. exact (MK_COMB (@lem7567051) (@lem7567050)). Qed.
Lemma lem7567053 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7567054 : term555 = term523.
Proof. exact (MK_COMB (@lem7567053) (@lem7567052)). Qed.
Lemma lem7567055 : term550 = term523.
Proof. exact (TRANS (@lem7567048) (@lem7567054)). Qed.
Lemma lem7567057 (x : nat) : (term828 x) = term35.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem7567058 : term829 = term35.
Proof. exact (@lem7567057 term470). Qed.
Lemma lem7567059 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem7567060 : term877 = term457.
Proof. exact (MK_COMB (@lem7567059) (@lem7567058)). Qed.
Lemma lem7567061 : term876 = term871.
Proof. exact (MK_COMB (@lem7567060) (@lem7567055)). Qed.
Lemma lem7567063 (m : nat) (n : nat) : (term878 m n) = (term879 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem7567064 : term871 = term880.
Proof. exact (@lem7567063 (NUMERAL 0) term470). Qed.
Lemma lem7567065 : term825 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem7567066 (h1 : term825 = (BIT1 0)) : (term470 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem7567067 : (term825 = (BIT1 0)) = ((term470 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term825 = (BIT1 0) => @lem7567066 h1) (fun h1 : (term470 = (NUMERAL 0)) = False => @lem7567065)). Qed.
Lemma lem7567068 : (term470 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem7567067) (@lem7567065)). Qed.
Lemma lem7567069 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem7567070 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7567071 : term881 = (and True).
Proof. exact (MK_COMB (@lem7567070) (@lem7567069)). Qed.
Lemma lem7567072 : term880 = (True /\ False).
Proof. exact (MK_COMB (@lem7567071) (@lem7567068)). Qed.
Lemma lem7567074 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem7567075 : term880 = False.
Proof. exact (TRANS (@lem7567072) (@lem7567074)). Qed.
Lemma lem7567076 : term871 = False.
Proof. exact (TRANS (@lem7567064) (@lem7567075)). Qed.
Lemma lem7567077 : term876 = False.
Proof. exact (TRANS (@lem7567061) (@lem7567076)). Qed.
Lemma lem7567078 : term873 = False.
Proof. exact (TRANS (@lem7567045) (@lem7567077)). Qed.
Lemma lem7567079 : term871 = False.
Proof. exact (TRANS (@lem7567022) (@lem7567078)). Qed.
Lemma lem7567080 : term870 = False.
Proof. exact (TRANS (@lem7567013) (@lem7567079)). Qed.
Lemma lem7567081 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1031 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7567080) (@lem7567010 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567082 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1109 _97569 _97570 _97571) : False.
Proof. exact (or_elim (@lem7565789 _97569 _97570 _97571 h1) (fun h0 : term1107 _97569 _97570 _97571 => @lem7566614 _97569 _97570 _97571 h0) (fun h0 : term1031 _97569 _97570 _97571 => @lem7567081 _97569 _97570 _97571 h0)). Qed.
Lemma lem7567083 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1111 _97569 _97570 _97571) : False.
Proof. exact (or_elim (@lem7564124 _97569 _97570 _97571 h1) (fun h0 : term1100 _97569 _97570 _97571 => @lem7565788 _97569 _97570 _97571 h0) (fun h0 : term1109 _97569 _97570 _97571 => @lem7567082 _97569 _97570 _97571 h0)). Qed.
Lemma lem7567084 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1045 _97569 _97570 _97571) : term1045 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7567085 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1045 _97569 _97570 _97571) : term1111 _97569 _97570 _97571.
Proof. exact (EQ_MP (@lem7564123 _97569 _97570 _97571) (@lem7567084 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567086 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1045 _97569 _97570 _97571) : (term1111 _97569 _97570 _97571) = False.
Proof. exact (prop_ext (fun h2 : term1111 _97569 _97570 _97571 => @lem7567083 _97569 _97570 _97571 h2) (fun h2 : False => @lem7567085 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567087 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term1045 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7567086 _97569 _97570 _97571 h1) (@lem7567085 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567088 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term973 _97569 _97570 _97571) : term973 _97569 _97570 _97571.
Proof. exact (h1). Qed.
Lemma lem7567089 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term973 _97569 _97570 _97571) : term1045 _97569 _97570 _97571.
Proof. exact (EQ_MP (@lem7563398 _97569 _97570 _97571) (@lem7567088 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567090 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term973 _97569 _97570 _97571) : (term1045 _97569 _97570 _97571) = False.
Proof. exact (prop_ext (fun h2 : term1045 _97569 _97570 _97571 => @lem7567087 _97569 _97570 _97571 h2) (fun h2 : False => @lem7567089 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567091 (_97569 : int) (_97570 : int) (_97571 : int) (h1 : term973 _97569 _97570 _97571) : False.
Proof. exact (EQ_MP (@lem7567090 _97569 _97570 _97571 h1) (@lem7567089 _97569 _97570 _97571 h1)). Qed.
Lemma lem7567092 (_97569 : int) (_97570 : int) (_97571 : int) : term1113 _97569 _97570 _97571.
Proof. exact (fun h0 : term973 _97569 _97570 _97571 => @lem7567091 _97569 _97570 _97571 h0). Qed.
Lemma lem7567093 (_97569 : int) (_97570 : int) (_97571 : int) : term1114 _97569 _97570 _97571.
Proof. exact (@lem1386578 (term1115 _97569 _97570 _97571)). Qed.
Lemma lem7567096 (_97569 : int) (_97570 : int) (_97571 : int) : term1115 _97569 _97570 _97571.
Proof. exact (@lem7567093 _97569 _97570 _97571 (@lem7567092 _97569 _97570 _97571)). Qed.
Lemma lem7567097 (_97569 : int) (_97571 : int) (_97570 : int) : (term972 _97569 _97570 _97571) = (term962 _97569 _97571 _97570).
Proof. exact (SYM (@lem7562421 _97569 _97570 _97571)). Qed.
Lemma lem7567098 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7567099 (_97569 : int) (_97571 : int) (_97570 : int) : (term1115 _97569 _97570 _97571) = (term931 _97569 _97571 _97570).
Proof. exact (MK_COMB (@lem7567098) (@lem7567097 _97569 _97571 _97570)). Qed.
Lemma lem7567100 (_97569 : int) (_97571 : int) (_97570 : int) : term931 _97569 _97571 _97570.
Proof. exact (EQ_MP (@lem7567099 _97569 _97571 _97570) (@lem7567096 _97569 _97570 _97571)). Qed.
Lemma lem7567101 (_97569 : int) (_97571 : int) (_97570 : int) : term932 _97569 _97571 _97570.
Proof. exact (EQ_MP (@lem7562012 _97569 _97571 _97570) (@lem7567100 _97569 _97571 _97570)). Qed.
Lemma lem7567102 (m : nat) (x : nat) (n : nat) : term1116 m x n.
Proof. exact (@lem7567101 (int_of_num m) (int_of_num x) (int_of_num n)). Qed.
Lemma lem7567103 (m : nat) (x : nat) (n : nat) : term1117 m x n.
Proof. exact (@lem7567102 m x n (@lem7562005 m)). Qed.
Lemma lem7567104 (m : nat) (x : nat) (n : nat) : term1118 m x n.
Proof. exact (@lem7567103 m x n (@lem7562008 n)). Qed.
Lemma lem7567105 (m : nat) (x : nat) (n : nat) : term928 m x n.
Proof. exact (@lem7567104 m x n (@lem7562011 x)). Qed.
Lemma lem7567106 (m : nat) (n : nat) : term930 m n.
Proof. exact (fun x : nat => @lem7567105 m x n). Qed.
Lemma lem7567107 (m : nat) (n : nat) : (term930 m n) = (term331 m n).
Proof. exact (SYM (@lem7562002 m n)). Qed.
Lemma lem7567108 (m : nat) (n : nat) : term331 m n.
Proof. exact (EQ_MP (@lem7567107 m n) (@lem7567106 m n)). Qed.
Lemma lem7567109 (m : nat) (n : nat) : (term331 m n) = ((term331 m n) = True).
Proof. exact (@lem7 (term331 m n)). Qed.
Lemma lem7567110 (m : nat) (n : nat) : (term331 m n) = True.
Proof. exact (EQ_MP (@lem7567109 m n) (@lem7567108 m n)). Qed.
Lemma lem7567111 (m : nat) (n : nat) : True = (term331 m n).
Proof. exact (SYM (@lem7567110 m n)). Qed.
Lemma lem7567112 (m : nat) (n : nat) : term331 m n.
Proof. exact (EQ_MP (@lem7567111 m n) (@lem0)). Qed.
Lemma lem7567115 (m : nat) (n : nat) : (term289 n) = (term283 m n).
Proof. exact (EQ_MP (@lem7556312 m n) (@lem7567112 m n)). Qed.
Lemma lem7567116 (n : nat) (m : nat) : (term289 m) = (term261 n m).
Proof. exact (EQ_MP (@lem7556241 n m) (@lem7561712 n m)). Qed.
Lemma lem7567117 (m : nat) (n : nat) : (term1119 n) = (term285 m n).
Proof. exact (MK_COMB (@lem7556138) (@lem7567115 m n)). Qed.
Lemma lem7567118 (m : nat) (n : nat) (b : nat -> real) (x : real) : (term94 n b x) = (term286 m n b x).
Proof. exact (MK_COMB (@lem7567117 m n) (@lem7556170 b x)). Qed.
Lemma lem7567119 (n : nat) (m : nat) : (term1119 m) = (term263 n m).
Proof. exact (MK_COMB (@lem7556137) (@lem7567116 n m)). Qed.
Lemma lem7567120 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term94 m a x) = (term264 n m a x).
Proof. exact (MK_COMB (@lem7567119 n m) (@lem7556154 a x)). Qed.
Lemma lem7567121 (n : nat) (m : nat) (a : nat -> real) (x : real) : (term171 m a x) = (term265 n m a x).
Proof. exact (MK_COMB (@lem7556136) (@lem7567120 n m a x)). Qed.
Lemma lem7567122 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term172 m a n b x) = (term287 a m n b x).
Proof. exact (MK_COMB (@lem7567121 n m a x) (@lem7567118 m n b x)). Qed.
Lemma lem7567123 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term172 m a n b x) = (term229 a m n b x).
Proof. exact (EQ_MP (@lem7556135 a m n b x) (@lem7567122 a m n b x)). Qed.
Lemma lem7567124 (a : nat -> real) (m : nat) (n : nat) (b : nat -> real) (x : real) : (term172 m a n b x) = (term200 a m n b x).
Proof. exact (EQ_MP (@lem7556043 a m n b x) (@lem7567123 a m n b x)). Qed.
Lemma lem7567125 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) (x : real) : (term172 m a n b x) = (term197 m a n b x).
Proof. exact (EQ_MP (@lem7555601 m a n b x) (@lem7567124 a m n b x)). Qed.
Lemma lem7567130 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) : term1120 m a n b.
Proof. exact (fun x : real => @lem7567125 m a n b x). Qed.
Lemma lem7567131 (a : nat -> real) (b : nat -> real) (m : nat) (n : nat) : term1121 a b m n.
Proof. exact (ex_intro (term1122 a b m n) (term183 m a n b) (@lem7567130 m a n b)). Qed.
Lemma lem7567132 (m : nat) (a : nat -> real) (n : nat) (b : nat -> real) : term179 m a n b.
Proof. exact (ex_intro (term178 m a n b) (Nat.max m n) (@lem7567131 a b m n)). Qed.
Lemma lem7567133 (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : term105 p q.
Proof. exact (EQ_MP (@lem7555553 p m a q n b h1 h2) (@lem7567132 m a n b)). Qed.
Lemma lem7567134 (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : (term133 q n b) = (term105 p q).
Proof. exact (prop_ext (fun h3 : term133 q n b => @lem7567133 p m a q n b h1 h2) (fun h3 : term105 p q => @lem7555459 q n b h2)). Qed.
Lemma lem7567135 (p : real -> real) (m : nat) (a : nat -> real) (q : real -> real) (n : nat) (b : nat -> real) (h1 : term133 p m a) (h2 : term133 q n b) : term105 p q.
Proof. exact (EQ_MP (@lem7567134 p m a q n b h1 h2) (@lem7555459 q n b h2)). Qed.
Lemma lem7567136 (n : nat) (b : nat -> real) (q : real -> real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : term142 n b p q.
Proof. exact (fun h0 : term133 q n b => @lem7567135 p m a q n b h1 h0). Qed.
Lemma lem7567141 (n : nat) (q : real -> real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : term145 n p q.
Proof. exact (fun b : nat -> real => @lem7567136 n b q p m a h1). Qed.
Lemma lem7567146 (q : real -> real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : term147 p q.
Proof. exact (fun n : nat => @lem7567141 n q p m a h1). Qed.
Lemma lem7567147 (q : real -> real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : (term133 p m a) = (term147 p q).
Proof. exact (prop_ext (fun h2 : term133 p m a => @lem7567146 q p m a h1) (fun h2 : term147 p q => @lem7555458 p m a h1)). Qed.
Lemma lem7567148 (q : real -> real) (p : real -> real) (m : nat) (a : nat -> real) (h1 : term133 p m a) : term147 p q.
Proof. exact (EQ_MP (@lem7567147 q p m a h1) (@lem7555458 p m a h1)). Qed.
Lemma lem7567149 (m : nat) (a : nat -> real) (p : real -> real) (q : real -> real) : term163 m a p q.
Proof. exact (fun h0 : term133 p m a => @lem7567148 q p m a h0). Qed.
Lemma lem7567154 (m : nat) (p : real -> real) (q : real -> real) : term166 m p q.
Proof. exact (fun a : nat -> real => @lem7567149 m a p q). Qed.
Lemma lem7567159 (p : real -> real) (q : real -> real) : term168 p q.
Proof. exact (fun m : nat => @lem7567154 m p q). Qed.
Lemma lem7567160 (p : real -> real) (q : real -> real) : term78 p q.
Proof. exact (EQ_MP (@lem7555457 p q) (@lem7567159 p q)). Qed.
Lemma lem7567165 (p : real -> real) : term1123 p.
Proof. exact (fun q : real -> real => @lem7567160 p q). Qed.
Lemma lem7567170 : term1124.
Proof. exact (fun p : real -> real => @lem7567165 p). Qed.
