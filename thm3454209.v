Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3454209_term_abbrevs.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm3453886_spec.
Require Import thm3453887_spec.
Require Import thm3453893_spec.
Require Import thm3453894_spec.
Require Import thm3453899_spec.
Require Import thm3453900_spec.
Lemma lem3454067 {A : Type'} (s : type686 A) (x : A) : (term0 A x s) = (term1 A s x).
Proof. exact (EQ_MP (@lem3453900 A s x) (@lem3453899 A s x)). Qed.
Lemma lem3454068 {_89578 : Type'} (s : type686 _89578) (x : _89578) : (term0 _89578 x s) = (term1 _89578 s x).
Proof. exact (@lem3454067 _89578 s x). Qed.
Lemma lem3454069 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term2 _89578 _89597 _89598 x P f) = (term3 _89578 _89597 _89598 P f x).
Proof. exact (@lem3454068 _89578 (term4 _89578 _89597 _89598 P f) x). Qed.
Lemma lem3454077 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term5 _83064 x P) = (term6 _83064 P x).
Proof. exact (EQ_MP (@lem3453894 _83064 P x) (@lem3453893 _83064 P x)). Qed.
Lemma lem3454078 {_89578 : Type'} (P : type909 _89578) (x : _89578 -> Prop) : (term7 _89578 x P) = (term8 _89578 P x).
Proof. exact (@lem3454077 (_89578 -> Prop) P x). Qed.
Lemma lem3454079 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (t : _89578 -> Prop) : (term9 _89578 _89597 _89598 t P f) = (term10 _89578 _89597 _89598 P f t).
Proof. exact (@lem3454078 _89578 (term11 _89578 _89597 _89598 P f) t). Qed.
Lemma lem3454080 {_89578 _89597 _89598 : Type'} (GEN_PVAR_51 : _89578 -> Prop) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term12 _89578 _89597 _89598 P f GEN_PVAR_51) = (term13 _89578 _89597 _89598 GEN_PVAR_51 P f).
Proof. exact (eq_refl (term12 _89578 _89597 _89598 P f GEN_PVAR_51)). Qed.
Lemma lem3454081 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term14 _89578 _89597 _89598 P f) = (term15 _89578 _89597 _89598 P f).
Proof. exact (fun_ext (fun GEN_PVAR_51 : _89578 -> Prop => @lem3454080 _89578 _89597 _89598 GEN_PVAR_51 P f)). Qed.
Lemma lem3454082 {_89578 : Type'} : (@GSPEC (_89578 -> Prop)) = (@GSPEC (_89578 -> Prop)).
Proof. exact (eq_refl (@GSPEC (_89578 -> Prop))). Qed.
Lemma lem3454083 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term16 _89578 _89597 _89598 P f) = (term4 _89578 _89597 _89598 P f).
Proof. exact (MK_COMB (@lem3454082 _89578) (@lem3454081 _89578 _89597 _89598 P f)). Qed.
Lemma lem3454084 {_89578 : Type'} (t : _89578 -> Prop) : (@IN (_89578 -> Prop) t) = (@IN (_89578 -> Prop) t).
Proof. exact (eq_refl (@IN (_89578 -> Prop) t)). Qed.
Lemma lem3454085 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term9 _89578 _89597 _89598 t P f) = (term17 _89578 _89597 _89598 t P f).
Proof. exact (MK_COMB (@lem3454084 _89578 t) (@lem3454083 _89578 _89597 _89598 P f)). Qed.
Lemma lem3454086 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454087 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term18 _89578 _89597 _89598 t P f) = (term19 _89578 _89597 _89598 t P f).
Proof. exact (MK_COMB (@lem3454086) (@lem3454085 _89578 _89597 _89598 t P f)). Qed.
Lemma lem3454088 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term10 _89578 _89597 _89598 P f t) = (term20 _89578 _89597 _89598 t P f).
Proof. exact (eq_refl (term10 _89578 _89597 _89598 P f t)). Qed.
Lemma lem3454089 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : ((term9 _89578 _89597 _89598 t P f) = (term10 _89578 _89597 _89598 P f t)) = ((term17 _89578 _89597 _89598 t P f) = (term20 _89578 _89597 _89598 t P f)).
Proof. exact (MK_COMB (@lem3454087 _89578 _89597 _89598 t P f) (@lem3454088 _89578 _89597 _89598 t P f)). Qed.
Lemma lem3454090 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term17 _89578 _89597 _89598 t P f) = (term20 _89578 _89597 _89598 t P f).
Proof. exact (EQ_MP (@lem3454089 _89578 _89597 _89598 t P f) (@lem3454079 _89578 _89597 _89598 P f t)). Qed.
Lemma lem3454100 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3454101 {_89578 : Type'} (f : type1527 _89578) (y : Prop) : (term22 _89578 f y) = (f y).
Proof. exact (@lem3454100 Prop (type686 _89578) f y). Qed.
Lemma lem3454102 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89598) (y : _89597) : (term23 _89578 _89597 _89598 t P x y) = (term24 _89578 _89597 _89598 t P x y).
Proof. exact (@lem3454101 _89578 (term25 _89578 t) (P x y)). Qed.
Lemma lem3454103 {_89578 : Type'} (p : Prop) (t : _89578 -> Prop) : (term26 _89578 t p) = (term27 _89578 p t).
Proof. exact (eq_refl (term26 _89578 t p)). Qed.
Lemma lem3454104 {_89578 : Type'} (t : _89578 -> Prop) : (term28 _89578 t) = (term25 _89578 t).
Proof. exact (fun_ext (fun p : Prop => @lem3454103 _89578 p t)). Qed.
Lemma lem3454105 {_89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89598) (y : _89597) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem3454106 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89598) (y : _89597) : (term23 _89578 _89597 _89598 t P x y) = (term24 _89578 _89597 _89598 t P x y).
Proof. exact (MK_COMB (@lem3454104 _89578 t) (@lem3454105 _89597 _89598 P x y)). Qed.
Lemma lem3454107 {_89578 : Type'} : (@eq ((_89578 -> Prop) -> Prop)) = (@eq ((_89578 -> Prop) -> Prop)).
Proof. exact (eq_refl (@eq ((_89578 -> Prop) -> Prop))). Qed.
Lemma lem3454108 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89598) (y : _89597) : (term29 _89578 _89597 _89598 t P x y) = (term30 _89578 _89597 _89598 t P x y).
Proof. exact (MK_COMB (@lem3454107 _89578) (@lem3454106 _89578 _89597 _89598 t P x y)). Qed.
Lemma lem3454109 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89598) (y : _89597) (t : _89578 -> Prop) : (term24 _89578 _89597 _89598 t P x y) = (term31 _89578 _89597 _89598 P x y t).
Proof. exact (eq_refl (term24 _89578 _89597 _89598 t P x y)). Qed.
Lemma lem3454110 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89598) (y : _89597) (t : _89578 -> Prop) : ((term23 _89578 _89597 _89598 t P x y) = (term24 _89578 _89597 _89598 t P x y)) = ((term24 _89578 _89597 _89598 t P x y) = (term31 _89578 _89597 _89598 P x y t)).
Proof. exact (MK_COMB (@lem3454108 _89578 _89597 _89598 t P x y) (@lem3454109 _89578 _89597 _89598 P x y t)). Qed.
Lemma lem3454111 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89598) (y : _89597) (t : _89578 -> Prop) : (term24 _89578 _89597 _89598 t P x y) = (term31 _89578 _89597 _89598 P x y t).
Proof. exact (EQ_MP (@lem3454110 _89578 _89597 _89598 P x y t) (@lem3454102 _89578 _89597 _89598 t P x y)). Qed.
Lemma lem3454116 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (f x y) = (f x y).
Proof. exact (eq_refl (f x y)). Qed.
Lemma lem3454117 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term32 _89578 _89597 _89598 t P f x y) = (term33 _89578 _89597 _89598 P t f x y).
Proof. exact (MK_COMB (@lem3454111 _89578 _89597 _89598 P x y t) (@lem3454116 _89578 _89597 _89598 f x y)). Qed.
Lemma lem3454119 {A B : Type'} (f : A -> B) (y : A) : (term21 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem3454120 {_89578 : Type'} (f : type686 _89578) (y : _89578 -> Prop) : (term34 _89578 f y) = (f y).
Proof. exact (@lem3454119 (_89578 -> Prop) Prop f y). Qed.
Lemma lem3454121 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term35 _89578 _89597 _89598 P t f x y) = (term33 _89578 _89597 _89598 P t f x y).
Proof. exact (@lem3454120 _89578 (term31 _89578 _89597 _89598 P x y t) (f x y)). Qed.
Lemma lem3454122 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89598) (y : _89597) (t : _89578 -> Prop) (t' : _89578 -> Prop) : (term36 _89578 _89597 _89598 P x y t t') = (term37 _89578 _89597 _89598 P x y t t').
Proof. exact (eq_refl (term36 _89578 _89597 _89598 P x y t t')). Qed.
Lemma lem3454123 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89598) (y : _89597) (t : _89578 -> Prop) : (term38 _89578 _89597 _89598 P x y t) = (term31 _89578 _89597 _89598 P x y t).
Proof. exact (fun_ext (fun t' : _89578 -> Prop => @lem3454122 _89578 _89597 _89598 P x y t t')). Qed.
Lemma lem3454124 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (f x y) = (f x y).
Proof. exact (eq_refl (f x y)). Qed.
Lemma lem3454125 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term35 _89578 _89597 _89598 P t f x y) = (term33 _89578 _89597 _89598 P t f x y).
Proof. exact (MK_COMB (@lem3454123 _89578 _89597 _89598 P x y t) (@lem3454124 _89578 _89597 _89598 f x y)). Qed.
Lemma lem3454126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454127 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term39 _89578 _89597 _89598 P t f x y) = (term40 _89578 _89597 _89598 P t f x y).
Proof. exact (MK_COMB (@lem3454126) (@lem3454125 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3454128 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term33 _89578 _89597 _89598 P t f x y) = (term41 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term33 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3454129 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : ((term35 _89578 _89597 _89598 P t f x y) = (term33 _89578 _89597 _89598 P t f x y)) = ((term33 _89578 _89597 _89598 P t f x y) = (term41 _89578 _89597 _89598 P t f x y)).
Proof. exact (MK_COMB (@lem3454127 _89578 _89597 _89598 P t f x y) (@lem3454128 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3454130 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term33 _89578 _89597 _89598 P t f x y) = (term41 _89578 _89597 _89598 P t f x y).
Proof. exact (EQ_MP (@lem3454129 _89578 _89597 _89598 P t f x y) (@lem3454121 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3454135 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term32 _89578 _89597 _89598 t P f x y) = (term41 _89578 _89597 _89598 P t f x y).
Proof. exact (TRANS (@lem3454117 _89578 _89597 _89598 P t f x y) (@lem3454130 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3454136 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term42 _89578 _89597 _89598 t P f x) = (term43 _89578 _89597 _89598 P t f x).
Proof. exact (fun_ext (fun y : _89597 => @lem3454135 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3454137 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3454138 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term44 _89578 _89597 _89598 t P f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3454137 _89597) (@lem3454136 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3454143 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term46 _89578 _89597 _89598 t P f) = (term47 _89578 _89597 _89598 P t f).
Proof. exact (fun_ext (fun x : _89598 => @lem3454138 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3454144 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3454145 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term20 _89578 _89597 _89598 t P f) = (term48 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3454144 _89598) (@lem3454143 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3454150 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term17 _89578 _89597 _89598 t P f) = (term48 _89578 _89597 _89598 P t f).
Proof. exact (TRANS (@lem3454090 _89578 _89597 _89598 t P f) (@lem3454145 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3454151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3454152 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term49 _89578 _89597 _89598 t P f) = (term50 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3454151) (@lem3454150 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3454153 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (@IN _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (@IN _89578 x t)). Qed.
Lemma lem3454154 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term51 _89578 _89597 _89598 P f x t) = (term52 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3454152 _89578 _89597 _89598 P t f) (@lem3454153 _89578 x t)). Qed.
Lemma lem3454157 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term53 _89578 _89597 _89598 P f x) = (term54 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3454154 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3454158 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3454159 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term3 _89578 _89597 _89598 P f x) = (term55 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3454158 _89578) (@lem3454157 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3454164 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term2 _89578 _89597 _89598 x P f) = (term55 _89578 _89597 _89598 P f x).
Proof. exact (TRANS (@lem3454069 _89578 _89597 _89598 P f x) (@lem3454159 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3454165 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454166 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term56 _89578 _89597 _89598 x P f) = (term57 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3454165) (@lem3454164 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3454168 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term58 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem3453887 _83095 p x) (@lem3453886 _83095 p x)). Qed.
Lemma lem3454169 {_89578 : Type'} (p : _89578 -> Prop) (x : _89578) : (term58 _89578 x p) = (p x).
Proof. exact (@lem3454168 _89578 p x). Qed.
Lemma lem3454170 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term59 _89578 _89597 _89598 x P f) = (term60 _89578 _89597 _89598 P f x).
Proof. exact (@lem3454169 _89578 (term61 _89578 _89597 _89598 P f) x). Qed.
Lemma lem3454171 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (a : _89578) (f : type1517 _89578 _89597 _89598) : (term60 _89578 _89597 _89598 P f a) = (term62 _89578 _89597 _89598 P a f).
Proof. exact (eq_refl (term60 _89578 _89597 _89598 P f a)). Qed.
Lemma lem3454172 {_89578 : Type'} (GEN_PVAR_52 : _89578) : (@SETSPEC _89578 GEN_PVAR_52) = (@SETSPEC _89578 GEN_PVAR_52).
Proof. exact (eq_refl (@SETSPEC _89578 GEN_PVAR_52)). Qed.
Lemma lem3454173 {_89578 _89597 _89598 : Type'} (GEN_PVAR_52 : _89578) (P : type1470 _89597 _89598) (a : _89578) (f : type1517 _89578 _89597 _89598) : (term63 _89578 _89597 _89598 GEN_PVAR_52 P f a) = (term64 _89578 _89597 _89598 GEN_PVAR_52 P a f).
Proof. exact (MK_COMB (@lem3454172 _89578 GEN_PVAR_52) (@lem3454171 _89578 _89597 _89598 P a f)). Qed.
Lemma lem3454174 {_89578 : Type'} (a : _89578) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3454175 {_89578 _89597 _89598 : Type'} (GEN_PVAR_52 : _89578) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (a : _89578) : (term65 _89578 _89597 _89598 GEN_PVAR_52 P f a) = (term66 _89578 _89597 _89598 GEN_PVAR_52 P f a).
Proof. exact (MK_COMB (@lem3454173 _89578 _89597 _89598 GEN_PVAR_52 P a f) (@lem3454174 _89578 a)). Qed.
Lemma lem3454176 {_89578 _89597 _89598 : Type'} (GEN_PVAR_52 : _89578) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term67 _89578 _89597 _89598 GEN_PVAR_52 P f) = (term68 _89578 _89597 _89598 GEN_PVAR_52 P f).
Proof. exact (fun_ext (fun a : _89578 => @lem3454175 _89578 _89597 _89598 GEN_PVAR_52 P f a)). Qed.
Lemma lem3454177 {_89578 : Type'} : (@ex _89578) = (@ex _89578).
Proof. exact (eq_refl (@ex _89578)). Qed.
Lemma lem3454178 {_89578 _89597 _89598 : Type'} (GEN_PVAR_52 : _89578) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term69 _89578 _89597 _89598 GEN_PVAR_52 P f) = (term70 _89578 _89597 _89598 GEN_PVAR_52 P f).
Proof. exact (MK_COMB (@lem3454177 _89578) (@lem3454176 _89578 _89597 _89598 GEN_PVAR_52 P f)). Qed.
Lemma lem3454179 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term71 _89578 _89597 _89598 P f) = (term72 _89578 _89597 _89598 P f).
Proof. exact (fun_ext (fun GEN_PVAR_52 : _89578 => @lem3454178 _89578 _89597 _89598 GEN_PVAR_52 P f)). Qed.
Lemma lem3454180 {_89578 : Type'} : (@GSPEC _89578) = (@GSPEC _89578).
Proof. exact (eq_refl (@GSPEC _89578)). Qed.
Lemma lem3454181 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term73 _89578 _89597 _89598 P f) = (term74 _89578 _89597 _89598 P f).
Proof. exact (MK_COMB (@lem3454180 _89578) (@lem3454179 _89578 _89597 _89598 P f)). Qed.
Lemma lem3454182 {_89578 : Type'} (x : _89578) : (@IN _89578 x) = (@IN _89578 x).
Proof. exact (eq_refl (@IN _89578 x)). Qed.
Lemma lem3454183 {_89578 _89597 _89598 : Type'} (x : _89578) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term59 _89578 _89597 _89598 x P f) = (term75 _89578 _89597 _89598 x P f).
Proof. exact (MK_COMB (@lem3454182 _89578 x) (@lem3454181 _89578 _89597 _89598 P f)). Qed.
Lemma lem3454184 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3454185 {_89578 _89597 _89598 : Type'} (x : _89578) (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term76 _89578 _89597 _89598 x P f) = (term77 _89578 _89597 _89598 x P f).
Proof. exact (MK_COMB (@lem3454184) (@lem3454183 _89578 _89597 _89598 x P f)). Qed.
Lemma lem3454186 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term60 _89578 _89597 _89598 P f x) = (term62 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term60 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3454187 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term59 _89578 _89597 _89598 x P f) = (term60 _89578 _89597 _89598 P f x)) = ((term75 _89578 _89597 _89598 x P f) = (term62 _89578 _89597 _89598 P x f)).
Proof. exact (MK_COMB (@lem3454185 _89578 _89597 _89598 x P f) (@lem3454186 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3454188 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term75 _89578 _89597 _89598 x P f) = (term62 _89578 _89597 _89598 P x f).
Proof. exact (EQ_MP (@lem3454187 _89578 _89597 _89598 P x f) (@lem3454170 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3454199 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term2 _89578 _89597 _89598 x P f) = (term75 _89578 _89597 _89598 x P f)) = ((term55 _89578 _89597 _89598 P f x) = (term62 _89578 _89597 _89598 P x f)).
Proof. exact (MK_COMB (@lem3454166 _89578 _89597 _89598 P f x) (@lem3454188 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3454202 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term78 _89578 _89597 _89598 P f) = (term79 _89578 _89597 _89598 P f).
Proof. exact (fun_ext (fun x : _89578 => @lem3454199 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3454203 {_89578 : Type'} : (@all _89578) = (@all _89578).
Proof. exact (eq_refl (@all _89578)). Qed.
Lemma lem3454204 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term80 _89578 _89597 _89598 P f) = (term81 _89578 _89597 _89598 P f).
Proof. exact (MK_COMB (@lem3454203 _89578) (@lem3454202 _89578 _89597 _89598 P f)). Qed.
Lemma lem3454209 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term81 _89578 _89597 _89598 P f) = (term80 _89578 _89597 _89598 P f).
Proof. exact (SYM (@lem3454204 _89578 _89597 _89598 P f)). Qed.
