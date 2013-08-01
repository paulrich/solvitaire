(ns solitaire.core
  (require clojure.edn))

(defmethod print-method clojure.lang.PersistentQueue [q w] (print-method '<- w) (print-method (seq q) w) (print-method '-< w))

(def red #{:hearts :diamonds :d :h})

(defn red? [suit] (boolean (red suit)))

(def black? (complement red?))

(defn named [i]
  (if (nil? i)
    "empty space"
    (-> i name clojure.string/capitalize)))

(defn to-s [[rank suit]]
  (->> [(if (nil? rank) "an" "the") ({11 "Jack" 12 "Queen" 13 "King" 1 "Ace"} rank rank)
        (if-not (nil? rank) "of") ({:h "Hearts" :d "Diamonds" :s "Spades" :c "Clubs"} suit (named suit))]
       (remove nil?)
       (clojure.string/join " ")))

(defn card-range
  ([suit end] (card-range suit 1 end))
  ([suit] (card-range suit 13))
  ([suit begin end]
     (->> (range begin (inc end))
          (map #(vector % suit))
          vec)))

(defn peek-pop
  ([stack]
     (peek-pop stack 1))
  ([stack n]
     (loop [x n
            result [[] stack]]
       (let [[_ stack] result]
         (if-let [next-item (and (> x 0) (peek stack))]
           (recur (dec x)
                  (-> result
                      (update-in [0] conj next-item)
                      (update-in [1] pop)))
           result)))))

(defn normalize [{:keys [waste foundation tableau]}]
  "Internal representation:
     :f Foundation: up to four sequences of cards
     :tableau a sequence of maps: {:h index of next hidden :i index (refers to which stack of hidden cards) :s stack}
     :w Waste: a stack of cards
     :s Stock: a queue of cards
   Extra:
     :h Hidden Tableau: a sequence of up to seven (possibly nil) sequences of cards (possibly nil). Can
          be queried for cards, and remembered so that the user doens't need to repeatedly input the same
          card(s). The parameterized value in the state describes how the down-stacks are initalized."
  {:foundation (map (fn [[rank suit]] (card-range suit rank)) foundation)
   :tableau (into tableau (repeat (- 7 (count tableau)) []))})
;;  either make sure foundation always has count of 4 or check for count of 4 in winning?

(letfn [(move-type [& defns]
          (fn [state]
            (for [[op source-pred destination-pred] defns
                  :let [find-movables (source-filter source-pred op)]
                  source (find-movables state)
                  destination (find-destinations source destination-pred state)]
              (move state source destination))))
        (source-filter [pred op]
          (fn [{:keys [tableau]}]
            (->> tableau
                 (filter pred)
                 (filter stack-seq?)
                 (map (tableau-key op)))))
        (orphan [{[[rank]] :stack}] (not= 13 rank))
        (orphan-parent [[top-card] tableau]
          (filter (parent? top-card) tableau))
        (obscuring-king [{[[rank]] :stack hidden-index :hidden}]
          (and (= rank 13) (> hidden-index 0)))
        (empty-tableau [_ tableau]
          (->> tableau
               (remove stack-seq?)
               (take 1)))
        (tableau-card [])
        (stack-seq? [{:keys [stack]}] (seq stack))
        (tableau-key [& args]
          (fn [{:keys [index]}] (list* [:tableau index :stack] args)))
        (find-destinations [[source-key] pred {:keys [tableau] :as state}]
          (let [stack (get-in state source-key)] 
            (->> tableau
                 (pred stack)
                 (map (tableau-key into stack)))))
        (parent? [[rank suit]]
          (fn [{parent-stack :stack}]
            (let [[parent-rank parent-suit] (peek parent-stack)]
              (and (= (red? parent-suit) (black? suit))
                   (= parent-rank (inc rank))))))
        (move [state source destination]
          (-> state
              (apply-update source)
              (apply-update destination)))
        (apply-update [state args]
          (apply update-in state args))
        (stock-to-waste [state]
          (let [[new-waste new-stock] (-> state :stock (peek-pop 3))]
            (if (seq new-waste)
              (-> state
                  (update-in [:waste] into new-waste)
                  (assoc-in [:stock] new-stock))
              (if-let [waste (-> state :waste seq)]
                (-> state
                    (update-in [:stock] into waste)
                    (assoc-in [:waste] [])
                    recur)))))]
  (defn find-moves [{:keys [tableau] :as state}]
    (let [moves (;apply
                 move-type
                       [empty orphan orphan-parent]
                       [empty obscuring-king empty-tableau]
                    ;   [pop tableau-card to-foundation]
                    ;   (map #(vector pop % to-tableau) [waste-card foundation-card])
                       )]
      (conj (moves state)
            (stock-to-waste state)))))

(defn solve
  "Takes a state (including a sequence of previous states) plus a description of the current move; returns a sequence of moves or nil.
  Keys: t (tableau) sequence of seven cards, the initial showing ones (or a sequence of card sequences, if partially played)
        f (foundation) optional; sequence of four cards, the top ones showing
        w (waste) optional (defaults to empty); a sequence of cards
        s (stock) sequence of cards in the stock, nil for unknown
   ** A card is a sequence of rank, suit; where rank: int (0, 13) inclusive, suit: #{:c :d :h :s}
      e.g. [12 :s] -> Queen of Spades
   Jack -> 11
   Queen -> 12
   King -> 13
   Ace -> 1"
  [initial-state]
  (letfn [(add-layouts [previous state]
            (conj previous (without-history state)))
          (without-history [state]
            (select-keys state [:foundation :tableau :hidden :stock :waste]))
          (winning? [state]
            (if (every? #(= 13 (count %)) (state :foundation))
              (state :history)))
          (in? [previous]
            (fn [state] (previous (without-history state))))]
    (loop [moves (normalize initial-state)
           previous-layouts #{}]
      (if-let [winning-moves (some winning? moves)]
        winning-moves
        (if (seq moves)
          (let [uninteresting? (some-fn nil? (in? previous-layouts))  ; might not need to check for nil here (flatten nil) -> ()
                next-moves (->> moves
                                (mapcat find-moves)
                                (remove uninteresting?))]
            (recur next-moves (reduce add-layouts previous-layouts next-moves))))))))
