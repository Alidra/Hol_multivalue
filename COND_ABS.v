Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import COND_ABS_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import ETA_AX_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem13057 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem13058 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem13059 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem13058 A B t) (@lem13057 A B t)). Qed.
Lemma lem13060 (b : Prop) : term2 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem13061 (b : Prop) : (term2 b) = (term3 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem13062 (b : Prop) : term3 b.
Proof. exact (EQ_MP (@lem13061 b) (@lem13060 b)). Qed.
Lemma lem13063 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem13064 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem13065 {A B : Type'} (f : A -> B) (g : A -> B) : (term4 A B f g) = (term4 A B f g).
Proof. exact (eq_refl (term4 A B f g)). Qed.
Lemma lem13066 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = True) : (term5 A B f g b) = (term6 A B f g).
Proof. exact (MK_COMB (@lem13065 A B f g) (@lem13063 b h1)). Qed.
Lemma lem13067 {A B : Type'} (f : A -> B) (g : A -> B) : (term6 A B f g) = ((term7 A B f g) = (@COND (A -> B) True f g)).
Proof. exact (eq_refl (term6 A B f g)). Qed.
Lemma lem13068 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) : (term8 A B f g b) = (term8 A B f g b).
Proof. exact (eq_refl (term8 A B f g b)). Qed.
Lemma lem13069 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : ((term5 A B f g b) = (term6 A B f g)) = ((term5 A B f g b) = ((term7 A B f g) = (@COND (A -> B) True f g))).
Proof. exact (MK_COMB (@lem13068 A B f g b) (@lem13067 A B f g)). Qed.
Lemma lem13070 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : (term5 A B f g b) = ((term9 A B b f g) = (@COND (A -> B) b f g)).
Proof. exact (eq_refl (term5 A B f g b)). Qed.
Lemma lem13071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13072 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : (term8 A B f g b) = (term10 A B b f g).
Proof. exact (MK_COMB (@lem13071) (@lem13070 A B b f g)). Qed.
Lemma lem13073 {A B : Type'} (f : A -> B) (g : A -> B) : ((term7 A B f g) = (@COND (A -> B) True f g)) = ((term7 A B f g) = (@COND (A -> B) True f g)).
Proof. exact (eq_refl ((term7 A B f g) = (@COND (A -> B) True f g))). Qed.
Lemma lem13074 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : ((term5 A B f g b) = ((term7 A B f g) = (@COND (A -> B) True f g))) = (((term9 A B b f g) = (@COND (A -> B) b f g)) = ((term7 A B f g) = (@COND (A -> B) True f g))).
Proof. exact (MK_COMB (@lem13072 A B b f g) (@lem13073 A B f g)). Qed.
Lemma lem13075 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : ((term5 A B f g b) = (term6 A B f g)) = (((term9 A B b f g) = (@COND (A -> B) b f g)) = ((term7 A B f g) = (@COND (A -> B) True f g))).
Proof. exact (TRANS (@lem13069 A B b f g) (@lem13074 A B b f g)). Qed.
Lemma lem13076 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = True) : ((term9 A B b f g) = (@COND (A -> B) b f g)) = ((term7 A B f g) = (@COND (A -> B) True f g)).
Proof. exact (EQ_MP (@lem13075 A B b f g) (@lem13066 A B f g b h1)). Qed.
Lemma lem13077 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = True) : ((term7 A B f g) = (@COND (A -> B) True f g)) = ((term9 A B b f g) = (@COND (A -> B) b f g)).
Proof. exact (SYM (@lem13076 A B f g b h1)). Qed.
Lemma lem13078 {A B : Type'} (f : A -> B) (g : A -> B) : (term4 A B f g) = (term4 A B f g).
Proof. exact (eq_refl (term4 A B f g)). Qed.
Lemma lem13079 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = False) : (term5 A B f g b) = (term11 A B f g).
Proof. exact (MK_COMB (@lem13078 A B f g) (@lem13064 b h1)). Qed.
Lemma lem13080 {A B : Type'} (f : A -> B) (g : A -> B) : (term11 A B f g) = ((term12 A B f g) = (@COND (A -> B) False f g)).
Proof. exact (eq_refl (term11 A B f g)). Qed.
Lemma lem13081 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) : (term8 A B f g b) = (term8 A B f g b).
Proof. exact (eq_refl (term8 A B f g b)). Qed.
Lemma lem13082 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : ((term5 A B f g b) = (term11 A B f g)) = ((term5 A B f g b) = ((term12 A B f g) = (@COND (A -> B) False f g))).
Proof. exact (MK_COMB (@lem13081 A B f g b) (@lem13080 A B f g)). Qed.
Lemma lem13083 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : (term5 A B f g b) = ((term9 A B b f g) = (@COND (A -> B) b f g)).
Proof. exact (eq_refl (term5 A B f g b)). Qed.
Lemma lem13084 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem13085 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : (term8 A B f g b) = (term10 A B b f g).
Proof. exact (MK_COMB (@lem13084) (@lem13083 A B b f g)). Qed.
Lemma lem13086 {A B : Type'} (f : A -> B) (g : A -> B) : ((term12 A B f g) = (@COND (A -> B) False f g)) = ((term12 A B f g) = (@COND (A -> B) False f g)).
Proof. exact (eq_refl ((term12 A B f g) = (@COND (A -> B) False f g))). Qed.
Lemma lem13087 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : ((term5 A B f g b) = ((term12 A B f g) = (@COND (A -> B) False f g))) = (((term9 A B b f g) = (@COND (A -> B) b f g)) = ((term12 A B f g) = (@COND (A -> B) False f g))).
Proof. exact (MK_COMB (@lem13085 A B b f g) (@lem13086 A B f g)). Qed.
Lemma lem13088 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : ((term5 A B f g b) = (term11 A B f g)) = (((term9 A B b f g) = (@COND (A -> B) b f g)) = ((term12 A B f g) = (@COND (A -> B) False f g))).
Proof. exact (TRANS (@lem13082 A B b f g) (@lem13087 A B b f g)). Qed.
Lemma lem13089 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = False) : ((term9 A B b f g) = (@COND (A -> B) b f g)) = ((term12 A B f g) = (@COND (A -> B) False f g)).
Proof. exact (EQ_MP (@lem13088 A B b f g) (@lem13079 A B f g b h1)). Qed.
Lemma lem13090 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = False) : ((term12 A B f g) = (@COND (A -> B) False f g)) = ((term9 A B b f g) = (@COND (A -> B) b f g)).
Proof. exact (SYM (@lem13089 A B f g b h1)). Qed.
Lemma lem13094 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13095 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem13094 B t2 t1). Qed.
Lemma lem13096 {A B : Type'} (g : A -> B) (f : A -> B) (x : A) : (term13 A B f g x) = (f x).
Proof. exact (@lem13095 B (g x) (f x)). Qed.
Lemma lem13097 {A B : Type'} (g : A -> B) (f : A -> B) : (term7 A B f g) = (term1 A B f).
Proof. exact (fun_ext (fun x : A => @lem13096 A B g f x)). Qed.
Lemma lem13098 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (@lem13059 A B t). Qed.
Lemma lem13099 {A B : Type'} (f : A -> B) : (term1 A B f) = f.
Proof. exact (@lem13098 A B f). Qed.
Lemma lem13100 {A B : Type'} (g : A -> B) (f : A -> B) : (term7 A B f g) = f.
Proof. exact (TRANS (@lem13097 A B g f) (@lem13099 A B f)). Qed.
Lemma lem13101 {A B : Type'} : (@eq (A -> B)) = (@eq (A -> B)).
Proof. exact (eq_refl (@eq (A -> B))). Qed.
Lemma lem13102 {A B : Type'} (g : A -> B) (f : A -> B) : (term14 A B f g) = (@eq (A -> B) f).
Proof. exact (MK_COMB (@lem13101 A B) (@lem13100 A B g f)). Qed.
Lemma lem13104 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem13105 {A B : Type'} (t2 : A -> B) (t1 : A -> B) : (@COND (A -> B) True t1 t2) = t1.
Proof. exact (@lem13104 (A -> B) t2 t1). Qed.
Lemma lem13106 {A B : Type'} (g : A -> B) (f : A -> B) : (@COND (A -> B) True f g) = f.
Proof. exact (@lem13105 A B g f). Qed.
Lemma lem13107 {A B : Type'} (g : A -> B) (f : A -> B) : ((term7 A B f g) = (@COND (A -> B) True f g)) = (f = f).
Proof. exact (MK_COMB (@lem13102 A B g f) (@lem13106 A B g f)). Qed.
Lemma lem13109 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13110 {A B : Type'} (x : A -> B) : (x = x) = True.
Proof. exact (@lem13109 (A -> B) x). Qed.
Lemma lem13111 {A B : Type'} (f : A -> B) : (f = f) = True.
Proof. exact (@lem13110 A B f). Qed.
Lemma lem13112 {A B : Type'} (f : A -> B) (g : A -> B) : ((term7 A B f g) = (@COND (A -> B) True f g)) = True.
Proof. exact (TRANS (@lem13107 A B g f) (@lem13111 A B f)). Qed.
Lemma lem13113 {A B : Type'} (f : A -> B) (g : A -> B) : True = ((term7 A B f g) = (@COND (A -> B) True f g)).
Proof. exact (SYM (@lem13112 A B f g)). Qed.
Lemma lem13114 {A B : Type'} (f : A -> B) (g : A -> B) : (term7 A B f g) = (@COND (A -> B) True f g).
Proof. exact (EQ_MP (@lem13113 A B f g) (@lem0)). Qed.
Lemma lem13118 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13119 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem13118 B t1 t2). Qed.
Lemma lem13120 {A B : Type'} (f : A -> B) (g : A -> B) (x : A) : (term15 A B f g x) = (g x).
Proof. exact (@lem13119 B (f x) (g x)). Qed.
Lemma lem13121 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = (term1 A B g).
Proof. exact (fun_ext (fun x : A => @lem13120 A B f g x)). Qed.
Lemma lem13122 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (@lem13059 A B t). Qed.
Lemma lem13123 {A B : Type'} (g : A -> B) : (term1 A B g) = g.
Proof. exact (@lem13122 A B g). Qed.
Lemma lem13124 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = g.
Proof. exact (TRANS (@lem13121 A B f g) (@lem13123 A B g)). Qed.
Lemma lem13125 {A B : Type'} : (@eq (A -> B)) = (@eq (A -> B)).
Proof. exact (eq_refl (@eq (A -> B))). Qed.
Lemma lem13126 {A B : Type'} (f : A -> B) (g : A -> B) : (term16 A B f g) = (@eq (A -> B) g).
Proof. exact (MK_COMB (@lem13125 A B) (@lem13124 A B f g)). Qed.
Lemma lem13128 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem13129 {A B : Type'} (t1 : A -> B) (t2 : A -> B) : (@COND (A -> B) False t1 t2) = t2.
Proof. exact (@lem13128 (A -> B) t1 t2). Qed.
Lemma lem13130 {A B : Type'} (f : A -> B) (g : A -> B) : (@COND (A -> B) False f g) = g.
Proof. exact (@lem13129 A B f g). Qed.
Lemma lem13131 {A B : Type'} (f : A -> B) (g : A -> B) : ((term12 A B f g) = (@COND (A -> B) False f g)) = (g = g).
Proof. exact (MK_COMB (@lem13126 A B f g) (@lem13130 A B f g)). Qed.
Lemma lem13133 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem13134 {A B : Type'} (x : A -> B) : (x = x) = True.
Proof. exact (@lem13133 (A -> B) x). Qed.
Lemma lem13135 {A B : Type'} (g : A -> B) : (g = g) = True.
Proof. exact (@lem13134 A B g). Qed.
Lemma lem13136 {A B : Type'} (f : A -> B) (g : A -> B) : ((term12 A B f g) = (@COND (A -> B) False f g)) = True.
Proof. exact (TRANS (@lem13131 A B f g) (@lem13135 A B g)). Qed.
Lemma lem13137 {A B : Type'} (f : A -> B) (g : A -> B) : True = ((term12 A B f g) = (@COND (A -> B) False f g)).
Proof. exact (SYM (@lem13136 A B f g)). Qed.
Lemma lem13138 {A B : Type'} (f : A -> B) (g : A -> B) : (term12 A B f g) = (@COND (A -> B) False f g).
Proof. exact (EQ_MP (@lem13137 A B f g) (@lem0)). Qed.
Lemma lem13139 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = False) : (term9 A B b f g) = (@COND (A -> B) b f g).
Proof. exact (EQ_MP (@lem13090 A B f g b h1) (@lem13138 A B f g)). Qed.
Lemma lem13140 {A B : Type'} (f : A -> B) (g : A -> B) (b : Prop) (h1 : b = True) : (term9 A B b f g) = (@COND (A -> B) b f g).
Proof. exact (EQ_MP (@lem13077 A B f g b h1) (@lem13114 A B f g)). Qed.
Lemma lem13141 {A B : Type'} (b : Prop) (f : A -> B) (g : A -> B) : (term9 A B b f g) = (@COND (A -> B) b f g).
Proof. exact (or_elim (@lem13062 b) (fun h0 : b = True => @lem13140 A B f g b h0) (fun h0 : b = False => @lem13139 A B f g b h0)). Qed.
Lemma lem13146 {A B : Type'} (b : Prop) (f : A -> B) : term17 A B b f.
Proof. exact (fun g : A -> B => @lem13141 A B b f g). Qed.
Lemma lem13151 {A B : Type'} (b : Prop) : term18 A B b.
Proof. exact (fun f : A -> B => @lem13146 A B b f). Qed.
Lemma lem13156 {A B : Type'} : term19 A B.
Proof. exact (fun b : Prop => @lem13151 A B b). Qed.
