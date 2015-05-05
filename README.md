Power Penguins
Created by Ryan Morgenlander
Modeled by Zachs Zagorski & Olstein

Power Penguins (currently out of development and attempting to get funded by a Kickstarter) is a "fast-paced strategy game" in which players act simultaneously, trying to make their penguin navigate the board and hit other players' penguins with snowballs while dodging those thrown by other players.
We chose to model this game in Spin because we predicted that an Alloy model would quickly become unwieldy whereas Spin would allow us to explore the state space effectively. Of course, we did not expect to encounter quite as large a state space as we did, which has made verifying some of our claims difficult.
Namely, we can say with certainty that nothing we expected to be true in every state is violated in the first 30 million states Spin's analyzer can reach, though we ran out of memory in trying to move beyond that.

Each turn of the game consists of three fundamental blocks - penguins move, shoot, and turn. We expanded this somewhat to allow for some small things to be factored in, such as the option of playing a card, the moving off the board of penguins that have been frozen, and the checking for a win condition being satisfied. As a result, each turn now looks like this:
	- Pick cards: penguins have three special power cards, each of which can be used up to once per game. During this step, penguins choose to use one or none of those cards. In addition, one of the cards (if selected) activates before the move phase - to represent that, we added the use of that card immediately after card selection.
	- Move: While human players would choose their card use, move distance, shooting direction, and turn direction at the same time and then make them known simultaneously to prevent strategic advantage going to any one player, for the purpose of this model we can randomly choose each of those values as needed. For the moving case, we choose a distance up to the maximum allowable move, then modify to account for passing through the snowdrift in the center of the board and ensuring that penguins remain on the board at all times*. We then move the penguin by that amount in the direction it is currently facing.
	A second power card allowing for an extra move in any direction is also handled here after the normal move is completed.
	Finally, we check for collisions between two penguins. This is important, as penguins which have collided (occupy the same space) "drop their snowballs" (cannot shoot that turn). Immediately after this check, we ensure that penguins who have become frozen as a result of collisions are marked as such, as they should be treated as if they aren't on the board.
	* except when stunned/frozen (which is handled separately).
	- Shoot: Penguins choose a direction in which to throw a snowball and then throw said snowball. To represent this, we move a snowball point in a given direction until it encounters the snowdrift or the edge of the board, dealing damage to penguins if it occupies the same space as them and awarding points to the penguin who threw the snowball. For each point the snowball occupies, we cycle through penguins and check if their coordinates are the same.
	We handle the last of the power cards, which allows for diagonal shooting, here.
	- Cleanup ("big cleanup"): At this point, it is possible that some penguins have become frozen as a result of being hit by snowballs. Those are moved to an off-board location to "warm up" (/not be on the board for a turn), while penguins that were off the board warming up are moved back to their home positions. All penguins not off the board are given snowballs for their next turns.
	- Turn: Each penguin chooses a direction, then turns to face that direction (or continues to face in their current direction if that is the direction chosen).
	- Check victory: We check if the maximum number of points amassed by any penguin is at least the number of points required to win, and if so, if it has been amassed by only penguin. If both of these conditions are met, we indicate that the game is over; otherwise, gameplay continues.

We attempt to show that the following properties are always true at the end of a turn:
	- Penguins are either on the board or stunned, but not both.
	- Penguins that are stunned have health <= 0 and penguins that have positive health are not stunned.
	- For every card possessed by each penguin, that penguin has either used the card or has the ability to use that card (but not both).

We have also included in our program the following claim, which we explicitly know to be untrue and can trivially find examples that violate:
	- The game eventually ends.
	There are in fact many sequences of decisions that can lead to infinite gameplay. One simple case is that in which penguins stand still, never turn, and always fire their snowballs into the edge of the board behind them, as this results in no victory points being amassed by any penguin and therefore the win condition never being satisfied.