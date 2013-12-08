package graphics.objects;

import static constants.Constants.TILESIZE;

import java.awt.Color;
import java.awt.Font;
import java.awt.Graphics;
import java.awt.Graphics2D;

import game_objects.Explosion;
import game_objects.GameObject;

public class ExplosionGraphics extends GameObjectGraphics {
	private Explosion explosion;
	
	public ExplosionGraphics(GameObject explosion) {
		super(explosion);
		this.explosion = (Explosion) explosion;
	}

	public void draw(Graphics g) {
		if (explosion.isToRemove())
			return;
		
		Graphics2D g2d = (Graphics2D) g;
		
		g2d.setColor(Color.red);
		g2d.setFont(new Font("Courier New", Font.BOLD, 20));
		
		g2d.drawString("X", explosion.getX() * TILESIZE + TILESIZE/2 - 5, explosion.getY() * TILESIZE + TILESIZE/2 + 6);
	}
}
