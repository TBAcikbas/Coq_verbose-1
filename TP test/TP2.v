(*** TP 2 : Loqique, booléens, propositions et IMP ***)


(** Note : si au bout d'une heure votre TP-man oublie de le dire, passez à la partie sur les listes !! *)


(** * Logique "avancée" et Coq : négation, booléens et Prop **)

(* Négation *)
(* On peut voir le faux, noté False, comme un connecteur logique, qui
peut être inséré dans le "tableau" où figuraient la conjonction et
l'existentielle dans l'énoncé du TP 1 : 

    connecteur    | pour utiliser |  pour construire
  ----------------|---------------|---------------------
      P /\ Q      |  destruct H.  |  split.
      P \/ Q      |  destruct H.  |  left. / right.
  exists x:nat, P |  destruct H.  |  exists 17.
      False       |  destruct H.  |

Devinez :
- pourquoi il n'y a pas de tactique dans la colonne "pour construire" de ce tableau.
- ce que fait "destruct H." si H est une hypothèse qui dit False. *)

(* A vous de jouer : prouvez les lemmes suivants *)

Lemma ex_falso: forall P : Prop, False -> P.
Abort.


(* Si l'on a A:Prop, alors ~A, la négation de A, est une notation pour "A -> False". *)
(* Si la notation vous perturbe, vous pouvez toujours utiliser la tactique [unfold not.] *)

Lemma not_not : forall P : Prop, P -> ~~P.
Abort.

Lemma morgan1 : forall P Q : Prop, ~P \/ ~Q -> ~(P /\ Q).
Abort.

Lemma morgan2 : forall P Q : Prop, ~P /\ ~Q -> ~(P \/ Q).
Abort.


(* Pour la prochaine preuve, vous aurez besoin d'une nouvelle tactique : 
  [inversion H.]
Formellement, lorsque l'on appelle [inversion H], Coq essaye de 
trouver les conditions nécessaires pour que l'hypothèse H soit vérifiée.
Coq fait aussi quelques simplifications lorsque l'on utilise inversion : si H est fausse, alors 
il termine automatiquement la preuve, si H implique une égalité entre 2 expressions, il fait 
parfois automatiquement le remplacement. 
Essayez cette tactique sur les prochains lemmes pour comprendre comment elle marche en pratique  *)

Lemma zero_un : ~(0=1).
intros.
inversion 
(*Notez que "x <> y" est un raccourci de "x = y -> False".*)

(* Un autre exemple d'application de la tactique inversion, indépendamment de la négation *)
Lemma S_out :  forall n m : nat, S n = S m -> n = m.
  [...]
Qed.


(* Dans le même style, les différents constructeurs d'un type inductif ne peuvent pas renvoyer la même valeur.
Revenons sur la tentative de définition  des entiers avec le successeur ET le prédécesseur, vue en cours. *)
Inductive t : Set :=
  Ze : t | Pr : t -> t | Su : t -> t.

Lemma S_et_P : forall x y, Su x = Pr y -> False.
  [...]
Qed.

(** Food for thought : à méditer après ce TP, ou si par hasard vous avez fini 
le reste avant la fin. Avec la syntaxe au-dessus, il est évident que le 
"prédécesseur" du "successeur" de "zéro" et "zéro" ne définissent pas le même
 objet: *)

Lemma PSZ: Pr (Su Ze) = Ze -> False.
  intros H. inversion H.
Qed.

Require Export ZArith.

(** Sauriez-vous montrer la même chose en remplaçant "zéro" par un x (de type t)
quelconque ? 
On insiste sur le fait que cette question est plutôt pour emmener à la maison 
que pour pendant le TP. Nous serons par ailleurs ravis de recevoir des mails 
si vous avez des questions là-dessus.
Un indice : souvenez-vous de vos cours de maths, où vous avez sûrement été déjà 
amené.e.s à prouver des résultats plus forts et plus généraux pour parvenir à
vos fins. 
Si besoin, vous pourrez vous servir de la tactique [omega] (chargée avec la 
librairie ZArith au-dessus, pour résoudre de buts arithmétiques (notamment 
obtenir faux à partir d'une hypothèse évidemment fausse comme x < x ou 2 < 0), 
et vous pouvez aussi invoquer la tactique [Search bla] pour chercher des lemmes
contenant "bla", comme dans: *)

Search "<" "S".



Lemma inj_PS: forall x, Pr (Su x) = x -> False.
[...]
Qed.




(** * Les booléens et les propositions **)

(* Il y a en Coq deux moyens d'exprimer des affirmations logiques, avec des booléens (le type bool) ou
des propositions (le type prop *)
Check True. 
Check False.
Check true.
Check false.

(*Un booléen est soit "true" soit "false". Ainsi, si on définit la fonction "and" suivante : *)

Definition Booland a b := match a,b with 
  | true,true => true
  | true,false => false
  | false,true => false
  | false,false => false
end.

(* Et qu'on l'évalue, on obtient soit true, soit false *)

Eval compute in (Booland false true).
Eval compute in (Booland true true).


(* Il est important de garder à l'esprit que ceci est spécifiqueau type "bool".
En effet, un objet de type "Prop" n'est pas quelque chose que l'on peut 
simplifier soit en True soit en False, mais plutôt un énoncé dont on peut 
avoir une preuve (preuve que l'on peut construire en Coq à l'aide de tactiques).
*)


Eval compute in (False /\ True).

(* On va travailler un peu sur ces différences dans un exemple *) 
(* On donne deux moyens de prouver qu'un entier est pair. *)

Definition not a := match a with 
  |false => true
  |true => false
end.

Fixpoint evenb n := match n with 
  | 0 => true
  | S n' => not (evenb n')
end.

Definition even_bool n := evenb n = true.

(* Prouvez que 42 est pair avec cette définition *)

Lemma even_42_bool : even_bool 42.
  [...]
Qed.

(* Une seconde définition avec une fonction "double" *)

Fixpoint double n := match n with 
  |0 => 0
  |S n' => S (S (double n'))
end.

Definition even_prop n := exists k, n = double k.

(* Prouvez une nouvelle fois que 42 est pair *)

Lemma even_42_prop : even_prop 42.
[...]
Qed.

(* Et maintenant, on va prouvez que finalement, ces deux définitions sont équivalentes *)
(* On aura besoin pour cela de lemmes auxiliaires, prouvez les. *)
(* Indice : Vous pouvez utiliser la tactique [case a] quand "a" est un booléen pour traiter les deux cas "true" et "false".
Cela ne modifiera que dans l'objectif.*)

Lemma Not_invol : forall a, not (not a) = a.
 [...]
Qed.

Lemma Not_false : forall a, not a = false -> a = true.
 [...]
Qed.

Lemma Not_true : forall a, not a = true -> a = false. 
 [...]
Qed.

Lemma evenb_double : forall k, even_bool (double k).
 [...]

Qed.

(*Tentez de prouver que la définition booléenne implique la définition propositionnelle*)
Lemma even_bool_to_prop : forall n, even_bool n -> even_prop n.

Abort.

(* Dans certains cas, on aura besoin d'une hypothèse d'induction plus forte que ce l'on souhaite prouver.
Note : Comme l'hypothèse d'induction 'est' notre objectif, "intro H. induction x" donnera une hypothèse d'induction
plus faible que "induction x" puis "intro H" dans les sous-cas.*)
(* Comprenez et completez la preuve à trous suivante: *)

Lemma evenb_double_conv : forall n, 
(evenb n = true -> exists k, n = double k) /\ (evenb n = false -> exists k, n = S (double k)).
induction n.
  (* Traitez le cas n = 0 de l'induction *)
[...]
  (* Début du cas successeur : *)
    simpl. destruct IHn. split.
    intros. destruct H0. [...] (* Premier cas du split à traiter. Si vous avez du mal à lire l'intérface Coq, n'hésitez pas à demander de l'aide *)
    intros. destruct H. [...] (* Deuxième cas du split à traiter *)
Qed.

(* On peut maintenant prouver l'équivalence entre les deux *)
Lemma even_bool_prop : forall n, even_prop n <-> even_bool n.
  [...]
Qed.

(* Sur cet exemple, vous avez normalement constaté qu'il est plus difficile de travailler sur 
les preuves avec les booléens que les propositions.
En effet, on est passé assez facilement des propositions aux booléens (evenb_double) mais l'inverse était plus compliqué. *)

(* En revanche, sur la preuve que 42 est paire, sur les booléens il n'y a presque rien à faire, mais pour les propositions, 
il faut au minimum donner l'entier correspondant à l'existentiel... *)
(* Ou bien, si on ne veut pas donner l'entier, on peut faire la preuve suivante... *)

Lemma even_42_prop_bis : even_prop 42.
apply even_bool_prop. reflexivity. Qed.

(* Sur cet exemple, on ne gagne pas vraiment à utiliser cette preuve. Mais sur certains cas, il peut être utile de connaitre cette 
technique. Un exemple extreme serait la preuve en Coq du théorème des 4 couleurs, 
dans laquelle ce procédé est utilisé pour qu'une preuve qui aurait eu besoin d'une analyse de centaines de cas soit 
capturé par un calcul sur les booléens. *)

(* Un exemple plus simple serait le suivant. Prouvez ce lemme *)

Lemma not_even_1001 : ~(even_bool 1001).
[...]
Qed.

(* Et celui-ci ? Voyez-vous le problème ?*)

Lemma not_even_1001_bis : ~(even_prop 1001).
[...]
Qed.



(* Petit bonus : La fin de cette partie permet de vous familiariser d'avantager aux équivalences bool/Prop.
Il n'est pas nécessaire de la faire en TP, particulièrement si vous avez l'impression d'être en retard.*)
(* Si Coq râle, n'hésitez à commenter les parties non faites *)

(* Prouvez le lemme suivant *)

Lemma andb_true_iff : forall a b, Booland a b = true <-> (a = true /\ b = true).
  [...]
Qed.

(* Définissez la fonction "Boolor" pour les booléens *)

Definition Boolor a b := [...].

(* Prouvez comme ci-dessus l'équivalence avec \/ *)

[...]

(* Fin du bonus. *)




(** * Prédicats inductifs, listes et relations **)

Require Import List.

(* On va définir des prédicats sur des listes. Pour simplifier, on supposera qu'il s'agit de listes d'entiers.*)

Definition listn := list nat.

(* Inspirez vous de ce que vous avez vu en cours pour écrire le prédicat inductif (is_size l n) qui signifie que l est de taille n *)
Inductive is_size : listn -> nat -> Prop := 
[...]

(* La tactique [inversion H] ne sert pas que dans les égalités, en fait, elle fonctionne aussi sur tous les prédicats inductifs.
Elle va vérifier quels cas sont possibles. Cela se voit dans le lemme suivant: *)

Lemma non_empty_size : forall p l n, is_size (p::l) n -> n <> 0.
  [...]
Qed.

(* Définissez un prédicat (mem l x) qui signifie que x ∈ l *)
Inductive mem : listn -> nat -> Prop := 
[...]

(* Le prédicat (update l x y l') signifie que l' est obtenu en 
   remplaçant la première occurence de x dans l' par y. *)

(* On vous donne un des cas :

  ──────────────────────────────── head 
  update (x::l) x y (y::l)

*)

(* Ecrivez ce prédicat *)
Inductive update : listn -> nat -> nat -> listn -> Prop := 
[...]


(* Pour montrer une cohérence entre les deux prédicats, prouvez le lemme suivant *)
Lemma update_mem : forall l x y l', update l x y l' -> mem l x.
[...]
Qed.

(* On pourrait prouver de manière similaire "forall l' l x y, update l x y l' -> mem l' y." *)

(* Petit bonus *)
(* Pour prouver une implication dans l'autre sens, vous pourrez avoir besoin du lemme suivant: *)
Lemma eq_dec : forall n m : nat, n = m \/ n <> m.
[...]
Qed.

Lemma mem_update : forall l x, mem l x -> forall y, exists l', update l x y l'.
[...]
Qed.

(* P.S : Si vous avez réussi à le prouver sans utiliser le lemme au-dessus, 
votre définition de mem aurait probablement pu être plus simple. *)

(* Fin du petit bonus *)

(* On considère les listes et on définit une relation binaire inductive sur les listes. On note 
"perm l1 l2" cette relation, avec l'idée que "perm l1 l2" représente le fait que l2 est une 
permutation de l1.
  Cette définition inductive est donnée par les quatres règles d'inférence suivantes : 

                                       perm l₁ l₂      perm l₂ l₃
  ───────────── (refl)                 ──────s────────────────────── (trans) 
    perm l l                                   perm l₁ l₃


        perm l₁ l₂
────────────────────── (tail)          ────────────────────────── (head) 
  perm (x::l₁) (x::l₂)                  perm (x::y::l) (y::x::l)


*)

Inductive perm  : [...]:=
[...].

(* Petit bonus *)
(* Vous vous êtes peut être demandé pourquoi est-ce que l'on a pris cette règle-là pour head et pas une autre ? 
  Notamment, on aurait pu penser à prendre cette règle-ci : 

           perm l₁ l₂
   ─────────────────────────────(head')
     perm (x::y::l₁) (y::x::l₂) 

On peut cependant prouver que l'on a pas besoin de cette règle. 
Pour vous aider à comprendre pourquoi, montrez d'abord l'exemple suivant. *)

Lemma perm_example : perm (1::2::4::5::3::nil) (2::1::4::3::5::nil).
[...]
Qed.

(* Prouvez maintenant le lemme suivant, montrant que la règle donnée
 précédemment est vraie dans notre définition. *)

Lemma perm_head_alt : forall x y l1 l2, perm l1 l2 -> perm (x::y::l1) (y::x::l2).

Abort.
(* Fin du petit bonus *)


Parameter X : Set.
Definition relation:= X -> X -> Prop.


(* Définir le prédicat inductif union R1 R2 qui est l'union de deux relations *)
Inductive union : relation -> relation -> X -> X -> Prop := 
  | union_left : forall (Rl Rr : relation) (x y : X), Rl x y -> union Rl Rr x y
  | union_right : forall (Rl Rr : relation) (x y : X), Rr x y -> union Rl Rr x y.

(* De même pour l'intersection *)
Inductive inter : relation -> relation -> relation :=
  | inter_ax : forall (R1 R2 : relation) (x y : X), R1 x y -> R2 x y -> inter R1 R2 x y.

(* Pour comparer des relations entre elles, il faut définir la notion d'égalité, '=' est trop fort ici.*)
Definition equal : relation -> relation -> Prop := fun R1 R2 =>
  forall x y, R1 x y <-> R2 x y.

(* On peut maintenant prouver la distributivité entre les deux par exemple *)
Lemma distr : forall R1 R2 R3, equal (inter (union R1 R2) R3) (union (inter R1 R3) (inter R2 R3)).
  intros. split.
    intro. inversion H. subst. destruct H0.
      apply union_left. split. trivial. trivial.
      apply union_right. split. trivial. trivial.
    intro. apply inter_ax.
      inversion H.
        inversion H0.  subst. apply union_left. trivial.
        inversion H0.  subst. apply union_right. trivial.
      inversion H.
        inversion H0.  subst. trivial.
        inversion H0.  subst. trivial.
Qed.

