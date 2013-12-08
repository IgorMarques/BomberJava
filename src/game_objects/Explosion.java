package game_objects;

import core.Game;

public class Explosion extends GameObject {

	private static double LIFETIME = 500;
	private double timeElapsed = 0;
	
	private Bomb bomb;
	
	public Explosion(Game game, int x, int y, Bomb bomb) {
		super(game, x, y);
		this.trepassable = true;
		this.bomb = bomb;
	}

	public void update(double delta) {
		timeElapsed += delta * 28;
		
		if (timeElapsed <= LIFETIME)
			getGame().getMap().bomb(bomb, getX(), getY());
		else {
			setToRemove(true);
		}
	}

}
