package graphics.objects;

import static constants.Constants.TILESIZE;

import java.awt.Color;
import java.awt.Graphics;
import java.awt.Graphics2D;
import java.awt.image.BufferedImage;
import java.io.File;
import java.io.IOException;

import javax.imageio.ImageIO;

import game_objects.Bomb;
import game_objects.GameObject;

public class BombGraphics extends GameObjectGraphics {
	
	private Bomb bomb;
	
	public BombGraphics(GameObject bomb) {
		super(bomb);
		this.bomb = (Bomb) bomb;
	}

	public void draw(Graphics g) {
		Graphics2D g2d = (Graphics2D) g;
		g2d.setColor(bomb.isExploded() ? Color.YELLOW : Color.black);
		
		BufferedImage img = null;
		String url = System.getProperty("user.dir");
		url+="/src/sprites/bomb.gif";
		
		try {
		    img = ImageIO.read(new File(url));
		} catch (IOException e) {
		}
		
		g2d.drawImage(img, bomb.getX() * TILESIZE, bomb.getY() * TILESIZE, null);
		
		//g2d.fillOval(bomb.getX() * TILESIZE + 4, bomb.getY() * TILESIZE + 4, 32 - 8, 32 - 8);
	}
}
