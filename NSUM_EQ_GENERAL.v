Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NSUM_EQ_GENERAL_term_abbrevs.
Require Import ITERATE_EQ_GENERAL_spec.
Require Import MONOIDAL_ADD_spec.
Require Import thm0_spec.
Require Import thm6920357_spec.
Require Import thm6920371_spec.
Require Import thm7_spec.
Lemma lem7018073 : (@monoidal nat Nat.add) = ((@monoidal nat Nat.add) = True).
Proof. exact (@lem7 (@monoidal nat Nat.add)). Qed.
Lemma lem7018075 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7018076 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term1 A B C op.
Proof. exact (@lem7018075 A B C h1 op). Qed.
Lemma lem7018077 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7018078 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7018077 A B C op) (@lem7018076 A B C op h1)). Qed.
Lemma lem7018079 {C : Type'} (op : type1400 C) (h1 : @monoidal C op) : @monoidal C op.
Proof. exact (h1). Qed.
Lemma lem7018080 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7018078 A B C op h1 (@lem7018079 C op h2)). Qed.
Lemma lem7018081 {A B C : Type'} (op : type1400 C) (h1 : @monoidal C op) : term4 A B C op.
Proof. exact (fun h0 : term0 A B C => @lem7018080 A B C op h0 h1). Qed.
Lemma lem7018082 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (h1). Qed.
Lemma lem7018083 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) (h2 : @monoidal C op) : term3 A B C op.
Proof. exact (@lem7018081 A B C op h2 (@lem7018082 A B C h1)). Qed.
Lemma lem7018084 {A B C : Type'} (op : type1400 C) (h1 : term0 A B C) : term2 A B C op.
Proof. exact (fun h0 : @monoidal C op => @lem7018083 A B C op h1 h0). Qed.
Lemma lem7018085 {A B C : Type'} (h1 : term0 A B C) : term0 A B C.
Proof. exact (fun op : type1400 C => @lem7018084 A B C op h1). Qed.
Lemma lem7018086 {A B C : Type'} : term5 A B C.
Proof. exact (fun h0 : term0 A B C => @lem7018085 A B C h0). Qed.
Lemma lem7018087 {A B C : Type'} : term0 A B C.
Proof. exact (@lem7018086 A B C (@lem5997003 A B C)). Qed.
Lemma lem7018088 {A B C : Type'} (op : type1400 C) : term1 A B C op.
Proof. exact (@lem7018087 A B C op). Qed.
Lemma lem7018089 {A B C : Type'} (op : type1400 C) : (term1 A B C op) = (term2 A B C op).
Proof. exact (eq_refl (term1 A B C op)). Qed.
Lemma lem7018138 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018139 {A : Type'} : (@nsum A) = (@iterate nat A Nat.add).
Proof. exact (@lem7018138 A). Qed.
Lemma lem7018140 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem7018141 {A : Type'} (s : A -> Prop) : (@nsum A s) = (@iterate nat A Nat.add s).
Proof. exact (MK_COMB (@lem7018139 A) (@lem7018140 A s)). Qed.
Lemma lem7018142 {A : Type'} (f : A -> nat) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7018143 {A : Type'} (s : A -> Prop) (f : A -> nat) : (@nsum A s f) = (@iterate nat A Nat.add s f).
Proof. exact (MK_COMB (@lem7018141 A s) (@lem7018142 A f)). Qed.
Lemma lem7018144 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem7018145 {A : Type'} (s : A -> Prop) (f : A -> nat) : (term6 A s f) = (term7 A s f).
Proof. exact (MK_COMB (@lem7018144) (@lem7018143 A s f)). Qed.
Lemma lem7018147 {_126417 : Type'} : (@nsum _126417) = (@iterate nat _126417 Nat.add).
Proof. exact (TRANS (@lem6920357 _126417) (@lem6920371 _126417)). Qed.
Lemma lem7018148 {B : Type'} : (@nsum B) = (@iterate nat B Nat.add).
Proof. exact (@lem7018147 B). Qed.
Lemma lem7018149 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem7018150 {B : Type'} (t : B -> Prop) : (@nsum B t) = (@iterate nat B Nat.add t).
Proof. exact (MK_COMB (@lem7018148 B) (@lem7018149 B t)). Qed.
Lemma lem7018151 {B : Type'} (g : B -> nat) : g = g.
Proof. exact (eq_refl g). Qed.
Lemma lem7018152 {B : Type'} (t : B -> Prop) (g : B -> nat) : (@nsum B t g) = (@iterate nat B Nat.add t g).
Proof. exact (MK_COMB (@lem7018150 B t) (@lem7018151 B g)). Qed.
Lemma lem7018153 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : ((@nsum A s f) = (@nsum B t g)) = ((@iterate nat A Nat.add s f) = (@iterate nat B Nat.add t g)).
Proof. exact (MK_COMB (@lem7018145 A s f) (@lem7018152 B t g)). Qed.
Lemma lem7018156 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> nat) (h : A -> B) (f : A -> nat) : (term8 A B s t g h f) = (term8 A B s t g h f).
Proof. exact (eq_refl (term8 A B s t g h f)). Qed.
Lemma lem7018157 {A B : Type'} (h : A -> B) (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term9 A B h s f t g) = (term10 A B h s f t g).
Proof. exact (MK_COMB (@lem7018156 A B s t g h f) (@lem7018153 A B s f t g)). Qed.
Lemma lem7018160 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term11 A B s f t g) = (term12 A B s f t g).
Proof. exact (fun_ext (fun h : A -> B => @lem7018157 A B h s f t g)). Qed.
Lemma lem7018161 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem7018162 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) (g : B -> nat) : (term13 A B s f t g) = (term14 A B s f t g).
Proof. exact (MK_COMB (@lem7018161 A B) (@lem7018160 A B s f t g)). Qed.
Lemma lem7018167 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) : (term15 A B s f t) = (term16 A B s f t).
Proof. exact (fun_ext (fun g : B -> nat => @lem7018162 A B s f t g)). Qed.
Lemma lem7018168 {B : Type'} : (@all (B -> nat)) = (@all (B -> nat)).
Proof. exact (eq_refl (@all (B -> nat))). Qed.
Lemma lem7018169 {A B : Type'} (s : A -> Prop) (f : A -> nat) (t : B -> Prop) : (term17 A B s f t) = (term18 A B s f t).
Proof. exact (MK_COMB (@lem7018168 B) (@lem7018167 A B s f t)). Qed.
Lemma lem7018174 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term19 A B s t) = (term20 A B s t).
Proof. exact (fun_ext (fun f : A -> nat => @lem7018169 A B s f t)). Qed.
Lemma lem7018175 {A : Type'} : (@all (A -> nat)) = (@all (A -> nat)).
Proof. exact (eq_refl (@all (A -> nat))). Qed.
Lemma lem7018176 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term21 A B s t) = (term22 A B s t).
Proof. exact (MK_COMB (@lem7018175 A) (@lem7018174 A B s t)). Qed.
Lemma lem7018181 {A B : Type'} (s : A -> Prop) : (term23 A B s) = (term24 A B s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7018176 A B s t)). Qed.
Lemma lem7018182 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7018183 {A B : Type'} (s : A -> Prop) : (term25 A B s) = (term26 A B s).
Proof. exact (MK_COMB (@lem7018182 B) (@lem7018181 A B s)). Qed.
Lemma lem7018188 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7018183 A B s)). Qed.
Lemma lem7018189 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7018190 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem7018189 A) (@lem7018188 A B)). Qed.
Lemma lem7018195 {A B : Type'} : (term30 A B) = (term29 A B).
Proof. exact (SYM (@lem7018190 A B)). Qed.
Lemma lem7018197 {A B C : Type'} (op : type1400 C) : term2 A B C op.
Proof. exact (EQ_MP (@lem7018089 A B C op) (@lem7018088 A B C op)). Qed.
Lemma lem7018198 {A B : Type'} (op : type1606) : term31 A B op.
Proof. exact (@lem7018197 A B nat op). Qed.
Lemma lem7018199 {A B : Type'} : term32 A B.
Proof. exact (@lem7018198 A B Nat.add). Qed.
Lemma lem7018201 : (@monoidal nat Nat.add) = True.
Proof. exact (EQ_MP (@lem7018073) (@lem6924403)). Qed.
Lemma lem7018202 : True = (@monoidal nat Nat.add).
Proof. exact (SYM (@lem7018201)). Qed.
Lemma lem7018203 : @monoidal nat Nat.add.
Proof. exact (EQ_MP (@lem7018202) (@lem0)). Qed.
Lemma lem7018204 {A B : Type'} : term30 A B.
Proof. exact (@lem7018199 A B (@lem7018203)). Qed.
Lemma lem7018205 {A B : Type'} : term29 A B.
Proof. exact (EQ_MP (@lem7018195 A B) (@lem7018204 A B)). Qed.
