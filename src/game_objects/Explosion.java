package game_objects;

import core.Game;

public class Explosion extends GameObject {

	private /*@ spec_public @*/ static double LIFETIME = 500;
	private /*@ spec_public @*/ double timeElapsed = 0;
	//@ public initially timeElapsed == 0;
	
	private /*@ spec_public @*/ Bomb bomb;
	
	//@ public invariant LIFETIME = 500;
	
	/*@ also
	 @ requires true;
	 @ assignable this.trepassable;
	 @ assignable this.bomb;
	 @ ensures this.trepassable== true;
	 @ ensures this.bomb== bomb;
	 @*/
	public Explosion(Game game, int x, int y, Bomb bomb) {
		super(game, x, y);
		this.trepassable = true;
		this.bomb = bomb;
	}

	/*@ requires delta >= 0;
	@ assignable timeElapsed;
	@ also
	@ requires timeElapsed <= LIFETIME;
	@ assignable getGame().getMap;
	@ ensures getGame().getMap().bomb(bomb, getX(), getY());
	@ also
	@ requires timeElapsed > LIFETIME;
	@ ensures setToRemove(true);
	@*/
	public void update(double delta) {
		timeElapsed += delta * 28;
		
		if (timeElapsed <= LIFETIME)
			getGame().getMap().bomb(bomb, getX(), getY());
		else {
			setToRemove(true);
		}
	}

}
