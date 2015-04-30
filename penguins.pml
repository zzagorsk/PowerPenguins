#define NORTH 1
#define EAST 2
#define SOUTH 3
#define WEST 4

typedef Point {
	int x;
	int y;
}

typedef Penguin {
	Point currPos;
	int dir;
	int health;
	int points;
	Point home;
	bool stunned;
}

Penguin[] penguins;

active proctype game () {
	//Instantiate penguins.

	do
	:: move;
	   shoot;
	   cleanup;
	   turn;
	od
}

inline move () {
	Penguin p;
	for (p in penguins) {
		int move;
		select (move : 0 .. 5);
		//perform move
	}
	check_collisions();
}

inline check_collisions() {
	//perform collision checks
}

inline shoot () {
	Penguin p;
	for (p in penguins){
		int shoot_dir;
		select (shoot_dir : 1 .. 4);
		//check for penguins in targeted squares
		//deal damage.
		//gain points.
	}
}

inline turn () {
	Penguin p;
	for (p in penguins){
		int turn_dir;
		select (turn_dir : 1 .. 4);
		p.dir = turn_dir;
	}
}

//LTL Assertions
//Penguins are on board.
//Points strictly increase.
//Stunned penguin implies 0 health.
//Always possible to reach a winning state.